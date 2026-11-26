/-
Trazar.lean · el trazador de metas del libro «Mirar y ver · Lean 4 · cómo piensa tu código» (AC Institut)

Elabora un archivo de Lean con el propio Lean y escribe en JSON, para cada táctica que aparece
en el texto, las metas antes y después, tal como las enseña el panel de Lean. También guarda los
mensajes (#eval, #check, avisos y errores) con su línea.

Uso (desde herramientas/lean):  lake env lean --run Trazar.lean archivo.lean > traza.json
-/
import Lean
open Lean Elab Meta

/-- Una meta, escrita como en el panel de Lean. -/
def metaTexto (ctx : ContextInfo) (mctx : MetavarContext) (g : MVarId) : IO String := do
  let some d := mctx.findDecl? g | return "?"
  let fmt ← ({ ctx with mctx := mctx } : ContextInfo).runMetaM d.lctx (ppGoal g)
  return toString fmt

/-- Nodos que no son tácticas que el lector escribe: secuencias, `by`, la puntuación… -/
def nodoSinInteres (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == nullKind || k == identKind || k == ``Lean.calcSteps || k == ``Lean.Parser.Tactic.tacticSeq || k == ``Lean.Parser.Tactic.tacticSeq1Indented ||
  k == ``Lean.Parser.Tactic.tacticSeqBracketed || k == ``Lean.Parser.Term.byTactic ||
  k == ``Lean.cdot || k == ``Lean.cdotTk || k == ``Lean.Parser.Tactic.case || k == `«]» || k == `«;» || k == `by

/-- El texto de la táctica en el archivo; vacío si Lean la ha fabricado (macros). -/
def textoOriginal (stx : Syntax) : String :=
  match stx.getHeadInfo with
  | .original .. => (stx.getSubstring? (withLeading := false) (withTrailing := false)).map (·.toString) |>.getD ""
  | _ => ""

/-- Traza un archivo con el entorno ya importado y devuelve el JSON. -/
unsafe def trazar (entrada texto : String) (env : Environment) (mensajes : MessageLog)
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) : IO Json := do
  let commandState := { Command.mkState env mensajes {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let mut vistos : Std.HashSet (Nat × Nat) := {}
  let mut pasos : Array (Nat × Int × Json) := #[]
  -- bloques: las metas que siguen abiertas al acabar cada nodo de tácticas
  let mut focos : Array Json := #[]
  let mut rangos : Std.HashSet (Nat × Nat) := {}
  for t in s.commandState.infoState.trees do
    let infos := t.foldInfo (init := #[]) fun ctx info acc =>
      match info with
      | .ofTacticInfo ti => acc.push (ctx, ti)
      | _ => acc
    for (ctx, ti) in infos do
      -- cada nodo es un posible «bloque»: lo que queda abierto cuando termina
      if let (some i, some f) := (ti.stx.getPos?, ti.stx.getTailPos?) then
        if !rangos.contains (i.byteIdx, f.byteIdx) then
          rangos := rangos.insert (i.byteIdx, f.byteIdx)
            let pI := inputCtx.fileMap.toPosition i
            let pF := inputCtx.fileMap.toPosition f
            let despues ← ti.goalsAfter.mapM (metaTexto ctx ti.mctxAfter)
            focos := focos.push <| Json.mkObj [("linea", Json.num pI.line), ("col", Json.num pI.column),
              ("lineaFin", Json.num pF.line), ("colFin", Json.num pF.column),
              ("despues", Json.arr (despues.toArray.map Json.str))]
      if nodoSinInteres ti.stx then continue
      let tac := textoOriginal ti.stx
      if tac.isEmpty then continue
      let some ini := ti.stx.getPos? | continue
      let some fin := ti.stx.getTailPos? | continue
      if vistos.contains (ini.byteIdx, fin.byteIdx) then continue
      vistos := vistos.insert (ini.byteIdx, fin.byteIdx)
      let pIni := inputCtx.fileMap.toPosition ini
      let pFin := inputCtx.fileMap.toPosition fin
      let antes ← ti.goalsBefore.mapM (metaTexto ctx ti.mctxBefore)
      let despues ← ti.goalsAfter.mapM (metaTexto ctx ti.mctxAfter)
      let j := Json.mkObj [
        ("tactica", Json.str tac), ("tipo", Json.str (toString ti.stx.getKind)),
        ("linea", Json.num pIni.line), ("col", Json.num pIni.column),
        ("lineaFin", Json.num pFin.line), ("colFin", Json.num pFin.column),
        ("antes", Json.arr (antes.toArray.map Json.str)),
        ("despues", Json.arr (despues.toArray.map Json.str))]
      -- en orden de lectura; si dos empiezan en el mismo sitio, primero la que abarca más
      pasos := pasos.push (ini.byteIdx, -(fin.byteIdx : Int), j)
  let ordenados := pasos.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let msgs ← s.commandState.messages.toList.mapM fun m => do
    let grave := match m.severity with | .error => "error" | .warning => "aviso" | _ => "info"
    return Json.mkObj [("linea", Json.num m.pos.line), ("col", Json.num m.pos.column),
      ("grave", Json.str grave), ("texto", Json.str (← m.data.toString))]
  return Json.mkObj [("archivo", Json.str entrada), ("codigo", Json.str texto),
    ("pasos", Json.arr (ordenados.map (·.2.2))), ("focos", Json.arr focos), ("mensajes", Json.arr msgs.toArray)]

/-- Traza cada archivo y escribe su JSON al lado (archivo.lean → archivo.json). Los archivos con
la misma cabecera (los mismos `import`) comparten el entorno: Mathlib se importa una sola vez. -/
unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then throw <| IO.userError "uso: lake env lean --run Trazar.lean a.lean b.lean …"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mut cache : Std.HashMap String (Environment × MessageLog) := {}
  for entrada in args do
    let texto ← IO.FS.readFile entrada
    let inputCtx := Parser.mkInputContext texto entrada
    let (cabecera, parserState, mensajes) ← Parser.parseHeader inputCtx
    let clave := toString cabecera.raw.reprint
    let (env, mensajes) ← match cache.get? clave with
      | some e => pure e
      | none => do
        if !cache.isEmpty then
          throw <| IO.userError "Lean solo importa una vez por proceso: traza por separado los archivos con otra cabecera"
        let r ← processHeader cabecera {} mensajes inputCtx
        cache := cache.insert clave r
        pure r
    let j ← trazar entrada texto env mensajes inputCtx parserState
    IO.FS.writeFile ((System.FilePath.mk entrada).withExtension "json") j.compress
    IO.eprintln s!"trazado: {entrada}"
