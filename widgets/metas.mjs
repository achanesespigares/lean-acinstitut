// metas.mjs · Visualizador de metas de Lean de AC Institut (anywidget para MyST / Jupyter Book 2)
// Enseña una demostración táctica a táctica, como el panel de Lean: las hipótesis y lo que falta
// por demostrar antes y después de cada paso. La traza la genera herramientas/trazar.py con Lean de
// verdad (herramientas/lean/Trazar.lean) y se carga de datos/trazas/ al abrir la página.
// Directiva:  {"archivo": "datos/trazas/<capítulo>-<n>.json", "config": {titulo, etiqueta, idea, notas?}}

const ESTILOS = `
.lm{
  --acento:#7A1F36; --suave:#F6F0EE; --oscuro:#5A1628; --banda:#6B6B6B; --filete:#9A9A9A; --fila:#D4D4D4;
  --fondo:#F4F4F4; --sub:#333; --tinta:#111; --si:#2D5A48; --sisuave:#E8F1EC;
  --titulo:"Montserrat","Helvetica Neue",Arial,sans-serif; --texto:"Arimo","Liberation Sans",Arial,sans-serif; --mono:"IBM Plex Mono",ui-monospace,Menlo,monospace;
  font:400 15px/1.55 var(--texto); color:var(--tinta); background:#fff;
  display:flex; flex-direction:column; gap:16px; padding:16px; border:1px solid var(--fila); border-radius:10px; margin:1.25rem 0;
}
.lm *{ box-sizing:border-box; }
.lm p{ margin:0; }
.lm-cab{ display:flex; justify-content:space-between; align-items:baseline; gap:10px; flex-wrap:wrap; }
.lm-tit{ font:700 18px/1.2 var(--titulo); }
.lm-etq{ font:600 10.5px/1 var(--titulo); letter-spacing:.1em; text-transform:uppercase; color:var(--acento); border:1.5px solid var(--acento); border-radius:6px; padding:5px 8px; }
.lm-idea{ border-left:4px solid var(--acento); padding:2px 0 2px 12px; color:var(--sub); }
.lm-escena{ display:grid; grid-template-columns:minmax(0,1fr) minmax(0,1fr); gap:16px; align-items:start; }
@media (max-width:760px){ .lm-escena{ grid-template-columns:minmax(0,1fr); } }
.lm-col{ display:flex; flex-direction:column; gap:12px; min-width:0; }
.lm-caja{ border:2px solid var(--tinta); background:#fff; }
.lm-barra{ background:var(--acento); color:#fff; padding:6px 12px; font:600 10.5px/1.2 var(--titulo); letter-spacing:.12em; text-transform:uppercase; display:flex; justify-content:space-between; gap:8px; }
.lm-barra.negro{ background:var(--tinta); }
.lm-micro{ font:600 10.5px/1.2 var(--titulo); letter-spacing:.12em; text-transform:uppercase; color:var(--banda); margin:0 0 6px !important; }
pre.lm-codigo{ margin:0; font:400 13.5px/1.8 var(--mono); overflow-x:auto; background:var(--fondo); padding:6px 0; border:0; border-radius:0; }
.lm .ln{ display:flex; white-space:pre; padding-right:12px; border-left:4px solid transparent; }
.lm .ln .no{ width:2.4ch; flex:none; text-align:right; color:var(--filete); margin:0 12px 0 6px; }
.lm .ln.activa{ border-left-color:var(--acento); background:var(--suave); }
.lm .ln.hecha .tx{ color:var(--sub); }
.lm .tac{ background:color-mix(in srgb,var(--acento) 16%,transparent); outline:1.5px solid var(--acento); border-radius:3px; }
.lm .kw{ color:var(--acento); font-weight:600; }
.lm .cm{ color:var(--banda); font-style:italic; }
.lm-narr{ min-height:4.4em; padding:10px 12px; background:var(--suave); border-left:4px solid var(--acento); font-size:15px; }
.lm-narr code, .lm-idea code{ font:500 13.5px var(--mono); background:#fff; padding:0 3px; border-radius:3px; }
.lm-panel{ padding:10px 12px; display:flex; flex-direction:column; gap:10px; }
.lm-meta{ border:1px solid var(--fila); border-radius:6px; padding:8px 10px; font:400 13.5px/1.6 var(--mono); background:#fff; overflow-x:auto; }
.lm-meta .caso{ font:600 10.5px/1.2 var(--titulo); letter-spacing:.08em; text-transform:uppercase; color:var(--banda); margin-bottom:4px; }
.lm-meta .hip{ white-space:pre; }
.lm-meta .hip.nueva{ background:var(--sisuave); box-shadow:-6px 0 0 var(--si); }
.lm-meta .obj{ white-space:pre; margin-top:4px; padding-top:4px; border-top:1px dashed var(--fila); color:var(--acento); font-weight:600; }
.lm-meta .obj.solo{ margin-top:0; padding-top:0; border-top:0; }
.lm-meta .obj.cambia{ background:color-mix(in srgb,var(--acento) 10%,transparent); }
.lm-hecho{ padding:10px 12px; border:1.5px solid var(--si); background:var(--sisuave); color:var(--si); font:600 14px/1.4 var(--titulo); border-radius:6px; }
.lm-sorry{ padding:10px 12px; border:1.5px solid #8a5a00; background:#fbf1dc; color:#6b4500; font:600 14px/1.4 var(--titulo); border-radius:6px; }
.lm-siguen{ margin:12px 0 6px !important; }
.lm-tapado{ padding:14px; border:1.5px dashed var(--filete); color:var(--banda); text-align:center; font:600 14px var(--titulo); border-radius:6px; }
.lm-vacio{ color:var(--banda); font-style:italic; }
.lm-consola{ font:400 13.5px/1.6 var(--mono); background:var(--tinta); color:#f4f4f4; padding:8px 12px; white-space:pre-wrap; min-height:2.6em; }
.lm-consola .info{ color:#f4f4f4; } .lm-consola .aviso{ color:#f0c674; } .lm-consola .error{ color:#ff8a8a; }
.lm-consola .lin{ color:#9a9a9a; }
.lm-consola .actual{ background:#3a2a2f; box-shadow:-12px 0 0 #3a2a2f, 12px 0 0 #3a2a2f; }
.lm-mandos{ display:flex; gap:8px; align-items:center; flex-wrap:wrap; border-top:1px solid var(--fila); padding-top:12px; }
.lm-b{ font:600 14px/1 var(--titulo); color:var(--tinta); background:#fff; border:1px solid var(--tinta); border-radius:999px; padding:10px 15px; cursor:pointer; text-decoration:none; display:inline-block; }
.lm-b:hover{ background:var(--suave); }
.lm-b.prim{ background:var(--acento); border-color:var(--acento); color:#fff; }
.lm-b.prim:hover{ background:var(--oscuro); }
.lm-b:disabled{ opacity:.35; cursor:default; }
.lm-cuenta{ font:600 13px var(--titulo); color:var(--banda); }
.lm-toggle{ font:400 14px var(--texto); display:inline-flex; gap:6px; align-items:center; margin-left:auto; }
.lm-teclas{ font-size:12px; color:var(--banda); flex-basis:100%; }
@media (max-width:760px){ .lm-teclas{ display:none; } }
.lm:fullscreen{ overflow:auto; margin:0; border-radius:0; font-size:19px; padding:24px 32px; }
.lm:fullscreen pre.lm-codigo, .lm:fullscreen .lm-meta, .lm:fullscreen .lm-consola{ font-size:18px; }
.lm:fullscreen .lm-tit{ font-size:26px; }
.lm:fullscreen .lm-narr{ font-size:19px; }
.lm:fullscreen .lm-mandos{ position:sticky; bottom:0; background:#fff; padding:12px 0 16px; z-index:5; }
`;

const PLANTILLA = `
<div class="lm">
  <div class="lm-cab"><span class="lm-tit"></span><span class="lm-etq"></span></div>
  <p class="lm-idea"></p>
  <div class="lm-escena">
    <div class="lm-col">
      <div class="lm-caja">
        <div class="lm-barra"><span>Prueba</span><span class="lm-donde">al empezar</span></div>
        <pre class="lm-codigo" aria-label="Código de Lean"></pre>
      </div>
      <p class="lm-narr" aria-live="polite"></p>
    </div>
    <div class="lm-col">
      <div class="lm-caja">
        <div class="lm-barra negro"><span>Panel de metas</span><span class="lm-num"></span></div>
        <div class="lm-panel">
          <div class="lm-antes-bloque"><p class="lm-micro">Antes de la táctica</p><div class="lm-antes"></div></div>
          <div><p class="lm-micro lm-ahora-tit">Ahora</p><div class="lm-ahora"></div></div>
        </div>
      </div>
      <div class="lm-cons-bloque"><p class="lm-micro">Mensajes de Lean</p><div class="lm-consola" aria-live="polite"></div></div>
    </div>
  </div>
  <div class="lm-mandos">
    <button type="button" class="lm-b lm-atras" aria-label="Paso anterior">◀</button>
    <button type="button" class="lm-b prim lm-sigue">Paso ▶</button>
    <button type="button" class="lm-b lm-play">Reproducir</button>
    <button type="button" class="lm-b lm-reinicia">Reiniciar</button>
    <button type="button" class="lm-b lm-proy" aria-pressed="false" title="Pantalla completa para proyectar en clase (tecla F)">Proyectar</button>
    <span class="lm-cuenta"></span>
    <a class="lm-b lm-real" target="_blank" rel="noopener" title="Abre esta misma prueba en el editor de Lean en el navegador (live.lean-lang.org)">Lean real ↗</a>
    <label class="lm-toggle"><input type="checkbox" class="lm-pred"> Modo predicción</label>
    <span class="lm-teclas">→ paso · ← atrás · P reproducir · Inicio reiniciar · F proyectar · Esc salir</span>
  </div>
</div>`;

const esc = s => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
// Markdown mínimo: `código`, **negrita** y *cursiva* (lo de dentro del código no se toca)
const md = t => String(t).split("`").map((s, i) => i % 2 ? "<code>" + esc(s) + "</code>"
  : esc(s).replace(/\*\*([^*]+)\*\*/g, "<b>$1</b>").replace(/\*([^*]+)\*/g, "<i>$1</i>")).join("");

// Palabras clave de Lean que se colorean en el código
const CLAVES = /\b(theorem|lemma|example|def|by|fun|have|show|from|calc|match|with|let|import|open|namespace|end|variable|section|if|then|else|at|using|Type|Prop)\b/g;
function colorea(linea) {
  const i = linea.indexOf("--");
  const codigo = i >= 0 ? linea.slice(0, i) : linea, com = i >= 0 ? linea.slice(i) : "";
  return esc(codigo).replace(CLAVES, '<span class="kw">$1</span>') + (com ? '<span class="cm">' + esc(com) + "</span>" : "");
}

// Una meta tal como la escribe Lean («case left», hipótesis «h : p» y «⊢ objetivo») → sus partes
function parteMeta(texto) {
  const lineas = texto.split("\n");
  let caso = null;
  if (lineas[0].startsWith("case ")) caso = lineas.shift().slice(5);
  const i = lineas.findIndex(l => l.startsWith("⊢ "));
  const hip = [];
  for (const l of (i >= 0 ? lineas.slice(0, i) : lineas)) {
    if (/^\s/.test(l) && hip.length) hip[hip.length - 1] += "\n" + l; else hip.push(l);
  }
  const obj = i >= 0 ? lineas.slice(i).join("\n") : "";
  return { caso, hip, obj };
}

// Qué hace cada táctica, en una frase (se elige por la primera palabra)
const TACTICAS = {
  intro: "introduce lo que hay a la izquierda de la flecha como hipótesis, con el nombre que le das, y la meta pasa a ser lo de la derecha.",
  intros: "introduce todas las hipótesis que puede.",
  exact: "da exactamente la prueba de la meta: un término cuyo tipo es justo lo que se pide.",
  apply: "usa un resultado cuya conclusión encaja con la meta; lo que queda por demostrar son sus premisas.",
  rw: "reescribe: cambia el lado izquierdo de la igualdad por el derecho allí donde aparezca.",
  nth_rewrite: "reescribe solo una de las apariciones: la que dice el número.",
  subst: "sustituye una variable por su valor en todo el panel y quita la hipótesis.",
  rewrite: "reescribe con una igualdad.",
  simp: "simplifica con las reglas de simplificación que conoce Lean (y las que le des).",
  constructor: "parte la meta en sus piezas: para un «y», hay que demostrar cada lado por separado.",
  rfl: "cierra la meta porque los dos lados son iguales por definición.",
  decide: "deja que Lean lo compruebe calculando: sirve para afirmaciones que se pueden decidir haciendo la cuenta.",
  norm_num: "hace las cuentas con números y cierra lo que queda.",
  ring: "demuestra igualdades de anillos conmutativos: desarrolla los dos lados y comprueba que coinciden.",
  linarith: "combina las desigualdades lineales de las hipótesis para llegar a la meta.",
  nlinarith: "como linarith, pero también multiplica hipótesis entre sí.",
  positivity: "demuestra que algo es positivo (o no negativo) mirando cómo está construido.",
  omega: "resuelve aritmética lineal con enteros y naturales.",
  induction: "demuestra la afirmación por inducción: un caso base y un paso inductivo, cada uno con su meta.",
  cases: "separa los casos posibles de una hipótesis.",
  rcases: "desmonta una hipótesis en sus piezas (un «y», un «o», un «existe»…).",
  obtain: "desmonta una hipótesis en sus piezas y les pone nombre.",
  use: "da el testigo de un «existe»: la meta pasa a ser que ese valor cumple la propiedad.",
  left: "elige demostrar el lado izquierdo del «o».",
  right: "elige demostrar el lado derecho del «o».",
  exfalso: "cambia la meta por False: si se llega a una contradicción, cualquier cosa queda demostrada.",
  contradiction: "encuentra entre las hipótesis una contradicción y cierra la meta.",
  by_contra: "supone lo contrario de la meta como hipótesis; ahora hay que llegar a False.",
  push_neg: "empuja la negación hacia dentro: ¬∀ pasa a ∃¬, ¬(a ≤ b) pasa a b < a…",
  have: "demuestra un resultado intermedio y lo añade como hipótesis.",
  show: "dice en voz alta cuál es la meta (y Lean comprueba que coincide).",
  calc: "encadena igualdades o desigualdades paso a paso, cada una con su justificación.",
  unfold: "despliega una definición.",
  specialize: "aplica una hipótesis general a un caso concreto.",
  field_simp: "quita denominadores (sabiendo que no son cero).",
  gcongr: "reduce una desigualdad entre expresiones parecidas a desigualdades entre sus piezas.",
  ext: "para demostrar que dos funciones o conjuntos son iguales, toma un elemento cualquiera.",
  funext: "para demostrar que dos funciones son iguales, toma un valor cualquiera.",
  trivial: "cierra metas sencillas.",
  assumption: "busca entre las hipótesis una que sea justo la meta.",
  sorry: "deja la meta sin demostrar: Lean lo acepta, pero avisa.",
  rename_i: "pone nombre a las variables inaccesibles (las de la cruz ✝).",
};
// Qué hace cada orden de Lean (para los programas sin tácticas)
const ORDENES = {
  "#eval": "<code>#eval</code> calcula la expresión y escribe su valor.",
  "#check": "<code>#check</code> no calcula: escribe la expresión y, después de los dos puntos, su tipo.",
  "#print": "<code>#print</code> enseña cómo está definido algo.",
  "#reduce": "<code>#reduce</code> simplifica la expresión desplegando las definiciones.",
  example: "<code>example</code> es una afirmación con su demostración, sin nombre.",
  theorem: "<code>theorem</code> es una afirmación con nombre y su demostración.",
  def: "<code>def</code> define algo con nombre.",
};
// La primera frase de un mensaje de Lean, en una línea (los errores largos siguen enteros en la consola)
const resumen = s => { const p = s.split("\n\n")[0].replace(/\s+/g, " ").trim(); return p.length > 90 ? p.slice(0, 88) + "…" : p; };
const nombreTactica = t => (t.match(/^[A-Za-z_]+[!?]?/) || [""])[0];
const plural = (n, a, b) => n + " " + (n === 1 ? a : b);

function render({ model, el }) {
  const archivo = model.get("archivo");
  if (!model.get("traza") && archivo) {
    el.textContent = "Cargando el visualizador…";
    let limpia = null;
    fetch(new URL("../" + archivo, import.meta.url))
      .then(r => { if (!r.ok) throw new Error(r.status); return r.json(); })
      .then(D => { limpia = renderMetas({ model: { get: k => k === "traza" ? D : model.get(k) }, el }); },
            () => { el.textContent = "No se ha podido cargar el visualizador (" + archivo + ")."; })
      .catch(e => { el.textContent = "El visualizador ha fallado: " + e.message; console.error(e); });
    return () => { if (typeof limpia === "function") limpia(); };
  }
  return renderMetas({ model, el });
}

function renderMetas({ model, el }) {
  const C = model.get("config") || {};
  const D = model.get("traza");
  if (!D || !D.codigo) { el.textContent = "Falta la traza: ejecuta herramientas/trazar.py sobre este capítulo."; return; }
  el.innerHTML = "<style>" + ESTILOS + "</style>" + PLANTILLA;
  const q = s => el.querySelector(s);
  const L = D.codigo.replace(/\n$/, "").split("\n");
  const P = D.pasos || [];
  const M = D.mensajes || [];
  const notas = C.notas || {};
  const F = D.focos || [];
  // Las metas que siguen abiertas fuera del bloque «·» que acaba con el paso p (el bloque más grande)
  function pendientes(p) {
    const fs = F.filter(f => f.lineaFin === p.lineaFin && f.colFin === p.colFin)
      .sort((a, b) => (a.linea - b.linea) || (a.col - b.col));
    return fs.length ? fs[0].despues : [];
  }
  q(".lm-tit").textContent = C.titulo || "Paso a paso";
  q(".lm-etq").textContent = C.etiqueta || "Lean";
  if (C.idea) q(".lm-idea").innerHTML = md(C.idea); else q(".lm-idea").remove();
  q(".lm-real").href = "https://live.lean-lang.org/#project=mathlib-stable&code=" + encodeURIComponent(D.codigo);
  if (!M.length) q(".lm-cons-bloque").remove();

  // Estados: 0 = al empezar (la meta del enunciado); k = la táctica k ya hecha.
  // Sin tácticas (solo #eval, #check…), se recorren las líneas en las que Lean escribe algo
  const modoMsg = P.length === 0 && M.length > 0;
  const E = [...new Set(M.map(m => m.linea))].sort((a, b) => a - b);
  const N = modoMsg ? E.length : P.length;
  if (modoMsg) { q(".lm-panel").closest(".lm-caja").remove(); q(".lm-pred").closest("label").style.display = "none"; }
  let k = 0, oculto = false, timer = null;
  const pred = () => q(".lm-pred").checked;

  function pintaCodigo() {
    const p = k === 0 ? null : modoMsg ? { linea: E[k - 1], lineaFin: E[k - 1], col: 0, colFin: L[E[k - 1] - 1].length } : P[k - 1];
    q(".lm-codigo").innerHTML = L.map((l, i) => {
      const n = i + 1;
      let html = colorea(l), clase = "ln";
      if (p && n >= p.linea && n <= p.lineaFin) {
        clase += " activa";
        if (p.linea === p.lineaFin) {
          const a = p.col, b = p.colFin;
          html = colorea(l.slice(0, a)) + '<span class="tac">' + colorea(l.slice(a, b)) + "</span>" + colorea(l.slice(b));
        }
      } else if (p && n < p.linea) clase += " hecha";
      return '<span class="' + clase + '"><span class="no">' + n + '</span><span class="tx">' + (html || " ") + "</span></span>";
    }).join("");
    q(".lm-donde").textContent = p ? "línea " + p.linea : "al empezar";
  }

  function tarjeta(texto, ref) {
    const m = parteMeta(texto), r = ref ? parteMeta(ref) : null;
    const hips = m.hip.map(h => '<div class="hip' + (r && !r.hip.includes(h) ? " nueva" : "") + '">' + esc(h) + "</div>").join("");
    return '<div class="lm-meta">' + (m.caso ? '<div class="caso">caso ' + esc(m.caso) + "</div>" : "") + hips +
      '<div class="obj' + (r && r.obj !== m.obj ? " cambia" : "") + (m.hip.length ? "" : " solo") + '">' + esc(m.obj) + "</div></div>";
  }

  function narracion() {
    if (modoMsg) {
      if (k === 0) return "Cada línea es una orden para Lean. Pulsa <b>Paso ▶</b> y mira qué contesta Lean a cada una en <b>Mensajes de Lean</b>.";
      const n = E[k - 1], orden = (L[n - 1].trim().match(/^#?\w+/) || [""])[0];
      const ms = M.filter(m => m.linea === n);
      let t = (ORDENES[orden] || "") + " Lean contesta " + ms.map(m => (m.grave === "error" ? "con un error: " : m.grave === "aviso" ? "con un aviso: " : "") + "<code>" + esc(resumen(m.texto)) + "</code>").join(" y ") + ".";
      if (notas[k]) t += " " + md(notas[k]);
      return t;
    }
    if (N === 0) return "Este programa no tiene tácticas ni mensajes.";
    if (k === 0) {
      const g = P[0].antes.length;
      return "Al empezar, Lean pone en el panel lo que hay que demostrar: " + (g === 1 ? "una meta" : g + " metas") +
        ". Encima de la raya, lo que tienes (las hipótesis); en la línea de <code>⊢</code>, lo que te piden. Pulsa <b>Paso ▶</b>." + (notas[0] ? " " + md(notas[0]) : "");
    }
    const p = P[k - 1], nom = nombreTactica(p.tactica);
    const base = nom.replace(/[!?]$/, "");
    let t = "<code>" + esc(p.tactica.split("\n")[0]) + (p.tactica.includes("\n") ? " …" : "") + "</code> " + (TACTICAS[nom] || TACTICAS[base] || "es una táctica: cambia las metas.");
    if (nom.endsWith("?") && TACTICAS[base]) t += " Con <code>?</code> al final, además, escribe en <b>Mensajes de Lean</b> cómo lo ha hecho.";
    if (/\sat\s+\S/.test(p.tactica.split("\n")[0])) t += " Con <code>at</code>, lo hace en una hipótesis en lugar de en la meta.";
    const a = p.antes.length, d = p.despues.length;
    const err = M.find(m => m.grave === "error" && m.linea >= p.linea && m.linea <= p.lineaFin);
    if (err) return t + " Pero aquí no funciona: <b>Lean marca un error</b> en esta línea y la meta sigue abierta. Lo que dice Lean está en <b>Mensajes de Lean</b>." + (notas[k] ? " " + md(notas[k]) : "");
    if (nom === "sorry") return t + " La meta desaparece del panel, pero <b>no está demostrada</b>: Lean marca la declaración con un aviso." + (notas[k] ? " " + md(notas[k]) : "");
    const resto = d === 0 ? pendientes(p) : [];
    if (d === 0 && resto.length) t += " Esta meta queda <b>demostrada</b>. " + (resto.length === 1 ? "Sigue abierta una meta" : "Siguen abiertas " + resto.length + " metas") + ": la" + (resto.length === 1 ? "" : "s") + " ves debajo.";
    else if (d === 0) t += k === N ? " <b>No queda ninguna meta: la demostración está completa.</b>" : " Esta meta queda <b>demostrada</b>.";
    else if (d > a) t += " Ahora hay " + plural(d, "meta", "metas") + " donde " + (a === 1 ? "había una" : "había " + a) + ".";
    else if (d < a) t += " Quedan " + plural(d, "meta", "metas") + ".";
    if (notas[k]) t += " " + md(notas[k]);
    return t;
  }

  function pinta() {
    pintaCodigo();
    q(".lm-narr").innerHTML = narracion();
    if (modoMsg) { pintaMensajes(); return; }
    const antesB = q(".lm-antes-bloque");
    if (k === 0) {
      antesB.style.display = "none";
      q(".lm-ahora-tit").textContent = "Lo que hay que demostrar";
      q(".lm-ahora").innerHTML = N ? P[0].antes.map(g => tarjeta(g)).join("") : '<p class="lm-vacio">Sin metas.</p>';
      q(".lm-num").textContent = N ? plural(P[0].antes.length, "meta", "metas") : "";
    } else {
      const p = P[k - 1];
      antesB.style.display = "";
      q(".lm-antes").innerHTML = p.antes.map(g => tarjeta(g)).join("");
      q(".lm-ahora-tit").textContent = "Después de " + nombreTactica(p.tactica);
      if (oculto) q(".lm-ahora").innerHTML = '<div class="lm-tapado">¿Qué metas quedarán? Piénsalo y pulsa Paso ▶</div>';
      else q(".lm-ahora").innerHTML = p.despues.length
        ? p.despues.map(g => tarjeta(g, p.antes[0])).join("")
        : nombreTactica(p.tactica) === "sorry" ? '<div class="lm-sorry">⚠ Meta tapada con sorry: sin demostrar.</div>'
        : '<div class="lm-hecho">' + (k === N ? "✓ No quedan metas: demostrado." : "✓ Meta cerrada.") + "</div>" +
          (pendientes(p).length ? '<p class="lm-micro lm-siguen">' + (pendientes(p).length === 1 ? "Sigue abierta" : "Siguen abiertas") + '</p>' + pendientes(p).map(g => tarjeta(g)).join("") : "");
      q(".lm-num").textContent = oculto ? "?" : plural(p.despues.length || pendientes(p).length, "meta", "metas");
    }
    pintaMensajes();
  }

  // Mensajes de Lean: los de las líneas ya alcanzadas (todos al final)
  function pintaMensajes() {
    if (M.length) {
      const hasta = k === 0 ? 0 : modoMsg ? E[k - 1] : (k === N ? Infinity : P[k - 1].lineaFin);
      const vis = M.filter(m => m.linea <= hasta);
      q(".lm-consola").innerHTML = vis.length ? vis.map(m => '<div class="' + m.grave + (modoMsg && m.linea === hasta ? " actual" : "") + '"><span class="lin">línea ' + m.linea + " · </span>" + esc(m.texto) + "</div>").join("") : '<span class="lin">(todavía nada)</span>';
    }
    q(".lm-cuenta").textContent = N ? "Paso " + k + " de " + N : "";
    q(".lm-atras").disabled = k === 0;
    q(".lm-sigue").disabled = k === N && !oculto;
  }

  function avanza() {
    if (oculto) { oculto = false; pinta(); return; }
    if (k >= N) { para(); return; }
    k++;
    oculto = pred();
    pinta();
  }
  function para() { if (timer) { clearInterval(timer); timer = null; q(".lm-play").textContent = "Reproducir"; } }
  q(".lm-sigue").addEventListener("click", () => { para(); avanza(); });
  q(".lm-atras").addEventListener("click", () => { para(); oculto = false; if (k > 0) k--; pinta(); });
  q(".lm-reinicia").addEventListener("click", () => { para(); oculto = false; k = 0; pinta(); });
  q(".lm-pred").addEventListener("change", () => { oculto = false; pinta(); });
  q(".lm-play").addEventListener("click", () => {
    if (timer) { para(); return; }
    if (k === N) { k = 0; oculto = false; }
    q(".lm-play").textContent = "Pausa";
    timer = setInterval(() => { avanza(); if (oculto || k === N) para(); }, 1400);
  });
  const raiz = q(".lm"), proy = q(".lm-proy");
  raiz.tabIndex = -1;
  const proyectando = () => ((raiz.getRootNode().fullscreenElement || document.fullscreenElement) === raiz);
  if (!document.fullscreenEnabled || !raiz.requestFullscreen) proy.remove();
  else proy.addEventListener("click", () => { if (proyectando()) document.exitFullscreen(); else raiz.requestFullscreen().then(() => raiz.focus()).catch(() => {}); });
  const alCambiarPantalla = () => {
    const on = proyectando();
    proy.setAttribute("aria-pressed", on ? "true" : "false");
    proy.textContent = on ? "Salir de la proyección" : "Proyectar";
  };
  document.addEventListener("fullscreenchange", alCambiarPantalla);
  raiz.addEventListener("keydown", e => {
    if (e.target.matches && e.target.matches("input, textarea, select")) return;
    const acciones = { ArrowRight: () => q(".lm-sigue").click(), PageDown: () => q(".lm-sigue").click(),
      ArrowLeft: () => q(".lm-atras").click(), PageUp: () => q(".lm-atras").click(),
      Home: () => q(".lm-reinicia").click(), p: () => q(".lm-play").click(), P: () => q(".lm-play").click(),
      f: () => proy.isConnected && proy.click(), F: () => proy.isConnected && proy.click() };
    if (acciones[e.key] && !e.ctrlKey && !e.metaKey && !e.altKey) { e.preventDefault(); acciones[e.key](); }
  });
  pinta();
  return () => { para(); document.removeEventListener("fullscreenchange", alCambiarPantalla); };
}

export default { render };
