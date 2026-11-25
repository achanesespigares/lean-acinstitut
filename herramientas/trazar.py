#!/usr/bin/env python3
"""trazar.py · genera las trazas de los visualizadores de metas del libro de Lean (AC Institut).

En cada capítulo, cada visualizador ``{anywidget} ../widgets/metas.mjs`` traza el bloque
```lean que tiene justo encima. El programa se elabora con Lean de verdad (herramientas/lean,
con Mathlib) y el trazador Trazar.lean guarda, para cada táctica, las metas antes y después.
La traza va a datos/trazas/<capítulo>-<n>.json y el visualizador la carga al abrir la página.

Uso:  python3 herramientas/trazar.py capitulos/*.md
Si un programa da un error de Lean y su visualizador no lleva "espera_error": true, se para.
"""
import json, pathlib, re, subprocess, sys, tempfile, os

RAIZ = pathlib.Path(__file__).resolve().parent.parent
LEAN = RAIZ / "herramientas" / "lean"
TRAZAS = RAIZ / "datos" / "trazas"
BLOQUE = re.compile(r"```lean\n(.*?)```", re.S)
WIDGET = re.compile(r"```\{anywidget\} \.\./widgets/metas\.mjs\n(.*?)\n```", re.S)


def lake() -> str:
    for c in (os.environ.get("LAKE"), str(pathlib.Path.home() / ".elan" / "bin" / "lake")):
        if c and pathlib.Path(c).exists():
            return c
    return "lake"


def version_lean() -> str:
    r = subprocess.run([lake(), "env", "lean", "--version"], cwd=LEAN, capture_output=True, text=True)
    return r.stdout.strip()


def main(capitulos):
    TRAZAS.mkdir(parents=True, exist_ok=True)
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="trazas-lean-"))
    trabajos = []          # (capítulo, nombre, código, config, inicio, fin) por visualizador
    textos = {}
    for cap in capitulos:
        cap = pathlib.Path(cap)
        texto = cap.read_text(encoding="utf-8")
        textos[cap] = texto
        n = 0
        for w in WIDGET.finditer(texto):
            previos = list(BLOQUE.finditer(texto, 0, w.start()))
            if not previos:
                sys.exit(f"{cap}: visualizador sin bloque ```lean encima")
            n += 1
            nombre = f"{cap.stem}-{n}"
            cuerpo = json.loads(w.group(1))
            trabajos.append((cap, nombre, previos[-1].group(1), cuerpo, w.start(1), w.end(1)))
    if not trabajos:
        print("No hay visualizadores de metas."); return
    # Lean solo puede importar una vez por proceso: un proceso por cada cabecera (los import)
    grupos = {}
    for cap, nombre, codigo, *_ in trabajos:
        f = tmp / f"{nombre}.lean"
        f.write_text(codigo, encoding="utf-8")
        cabecera = "\n".join(l for l in codigo.splitlines() if l.startswith("import "))
        grupos.setdefault(cabecera, []).append(str(f))
    for archivos in grupos.values():
        r = subprocess.run([lake(), "env", "lean", "--run", "Trazar.lean", *archivos], cwd=LEAN, text=True, capture_output=True)
        if r.returncode != 0:
            sys.exit("Lean ha fallado:\n" + r.stderr[-3000:])
    version = version_lean()
    nuevos = {}
    for cap, nombre, codigo, cuerpo, i, j in trabajos:
        D = json.loads((tmp / f"{nombre}.json").read_text(encoding="utf-8"))
        D.pop("archivo", None)
        D["lean"] = version
        errores = [m for m in D["mensajes"] if m["grave"] == "error"]
        if errores and not cuerpo.get("config", {}).get("espera_error"):
            sys.exit(f"{nombre}: error de Lean en la línea {errores[0]['linea']}: {errores[0]['texto']}")
        (TRAZAS / f"{nombre}.json").write_text(json.dumps(D, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
        cuerpo["archivo"] = f"datos/trazas/{nombre}.json"
        nuevos.setdefault(cap, []).append((i, j, json.dumps(cuerpo, ensure_ascii=False, separators=(",", ":"))))
        print(f"  · {nombre}: {len(D['pasos'])} pasos, {len(D['mensajes'])} mensajes")
    for cap, cambios in nuevos.items():
        texto = textos[cap]
        for i, j, nuevo in sorted(cambios, reverse=True):
            texto = texto[:i] + nuevo + texto[j:]
        if texto != textos[cap]:
            cap.write_text(texto, encoding="utf-8")
        print(f"{cap}: {len(cambios)} visualizador(es)")


if __name__ == "__main__":
    main(sys.argv[1:])
