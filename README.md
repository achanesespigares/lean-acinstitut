# Mirar y ver · Lean 4 · cómo piensa tu código

Aprender a demostrar con Lean 4 viendo cómo piensa cada demostración, táctica a táctica, con el panel de metas a la vista. Es el quinto libro de la colección, después de los de Python, R, Julia y SageMath. Está hecho con Jupyter Book 2 (motor MyST) y se publica en GitHub Pages.

## Las dos rutas

Cada capítulo tiene una **ruta base** (para el aula y el autoestudio) y apartados **A fondo** (cómo funciona Lean por dentro y cómo se trabaja como profesional), como los niveles SL y HL del IB. Un apartado «A fondo» se escribe así:

```markdown
:::{div}
:class: afondo
### Cómo comprueba Lean una demostración
…
:::
```

Si el apartado lleva dentro otra directiva (un bloque de código, un visualizador), se abre y se cierra con `::::{div}`. El interruptor `widgets/rutas.mjs` oculta o muestra esos bloques.

## Estructura

```
myst.yml                      configuración e índice del libro
index.md                      portada
capitulos/                    un fichero por capítulo
widgets/metas.mjs             el visualizador de metas (panel de Lean paso a paso, botón «Lean real»)
widgets/rutas.mjs             el interruptor de las dos rutas
herramientas/trazar.py        traza las demostraciones de los capítulos y escribe datos/trazas/
herramientas/lean/            proyecto de Lean con Mathlib y el trazador Trazar.lean
estilo/ac-institut.css        piel AC Institut (vino, Montserrat, Arimo, IBM Plex Mono) y cápsulas «A fondo»
.github/workflows/            publicación automática
```

## Cómo se hace un visualizador

En un capítulo, el visualizador va justo debajo del bloque de Lean que enseña:

````markdown
```lean
import Mathlib

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"…","etiqueta":"…","idea":"…","notas":{"1":"nota del paso 1"}}}
```
````

`herramientas/trazar.py` pasa cada bloque por Lean, guarda para cada táctica las metas antes y después en `datos/trazas/<capítulo>-<n>.json` y escribe en la directiva la ruta del archivo. Si Lean da un error y la directiva no lleva `"espera_error": true`, se para.

## Trabajar con el libro

Requisitos: Node 18 o superior, Python 3 y Lean 4.36.0 con elan.

```bash
npm ci                                   # instala MyST en la versión fijada
cd herramientas/lean && lake update      # baja Mathlib ya compilada (unos 7 GB)
cd ../.. && npm run trazas               # traza las demostraciones con Lean
npx myst start                           # vista previa en el navegador
```

## Licencia

Texto y código del libro: CC BY-NC-SA 4.0. © Antonio Chanes Espigares · AC Institut.
