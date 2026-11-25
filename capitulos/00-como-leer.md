---
title: Cómo leer este libro
subtitle: El panel de metas, las dos rutas y Lean en el navegador
---

Cada capítulo sigue el mismo recorrido, el del método genético-constructivo:

1. Un **punto de partida** conocido.
2. La **pregunta** que lo generaliza.
3. La **idea** mínima que lo sostiene.
4. La **construcción**, con Lean.
5. Las **conexiones** con otros temas.
6. Una **grieta**: algo que el capítulo deja abierto y que lleva al siguiente.

## Las dos rutas

Lo que no es imprescindible va en apartados marcados **A fondo**, con su cápsula negra y un filete a la izquierda. Si sigues la ruta base, puedes ocultarlos con el interruptor que hay al principio de cada capítulo. Así lo que lees nunca da un salto.

```{anywidget} ../widgets/rutas.mjs
{}
```

:::{div}
:class: afondo
Esto es un apartado «A fondo». Si eliges la ruta base, desaparece de la página.
:::

## Demostrar con un ordenador

En los libros anteriores, el visualizador enseñaba la **memoria** de un programa: qué valor tenía cada variable en cada línea. Una demostración en Lean no se mira así. Lo que importa en cada momento es otra cosa:

- **qué sabes**: los datos y las hipótesis;
- **qué te falta**: lo que todavía hay que demostrar, la **meta**.

Cada línea de una demostración es una **táctica**: una orden que transforma la meta en otra más sencilla, o la parte en varias, o la cierra. Cuando no queda ninguna meta, Lean da la demostración por buena. Y si una táctica no vale, Lean lo dice en esa misma línea.

Esto es lo que enseña el panel de metas del editor de Lean, y lo que enseña el visualizador de este libro.

## El visualizador

Debajo de las demostraciones clave hay un visualizador. Lo que ves no está dibujado a mano: sale de pasar la demostración por Lean de verdad, con Mathlib, y guardar el panel de metas antes y después de cada táctica.

Este es el primero. Demuestra que el cuadrado de un número par es par. No hace falta entender todavía cada táctica: basta con mirar cómo cambia el panel.

:::{tip} Predice
Si *n* = *k* + *k*, ¿cómo se escribe *n*² como un número más sí mismo?
:::

```lean
import Mathlib

theorem cuadrado_de_par (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k ^ 2
  rw [hk]
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El cuadrado de un par es par","etiqueta":"obtain · use · rw · ring","idea":"Cuatro tácticas, cuatro cambios en el panel. Fíjate en qué aparece encima de la raya (lo que sabes) y en qué cambia en la línea de `⊢` (lo que te falta).","notas":{"1":"En Mathlib, `Even n` significa que *n* es un número más sí mismo: existe un `k` con `n = k + k`. `obtain` saca ese `k` y esa igualdad, que llama `hk`.","2":"Para que `n ^ 2` sea par, hay que dar el número que sumado consigo mismo da `n ^ 2`. Se propone `2 * k ^ 2`.","3":"Donde ponía `n`, ahora pone `k + k`: es lo que dice `hk`.","4":"Queda una identidad de álgebra, (*k* + *k*)² = 2*k*² + 2*k*², y `ring` la comprueba desarrollando los dos lados."}},"archivo":"datos/trazas/00-como-leer-1.json"}
```

Así se usa:

- **Paso ▶** ejecuta la siguiente táctica; **◀** vuelve atrás; **Reproducir** avanza solo.
- En **Prueba**, la táctica que se acaba de ejecutar va recuadrada en vino, y su línea, marcada.
- El **panel de metas** enseña cada meta como la escribe Lean. Encima de la raya, lo que sabes: `n k : ℕ` dice que *n* y *k* son números naturales; `hk : n = k + k` es una hipótesis que se llama `hk`. Debajo, después de `⊢`, lo que te falta.
- Arriba ves las metas **antes de la táctica**, y abajo, las de **después**. Una hipótesis nueva se resalta en verde; si la meta cambia, se resalta en vino.
- Si una táctica deja varias metas, salen todas, cada una con el nombre de su **caso**. Cuando no queda ninguna, el panel lo dice: **demostrado**.
- En **Mensajes de Lean** aparece lo que Lean escribe: los resultados de `#eval`, los avisos y los errores, en su línea.
- **Modo predicción** tapa las metas de después hasta el paso siguiente, para que las pienses antes de verlas. **Proyectar** pone el visualizador a pantalla completa, para la clase.
- **Lean real ↗** abre la misma demostración en el editor de Lean en el navegador, en [live.lean-lang.org](https://live.lean-lang.org), con la versión estable de Lean y Mathlib, la misma que usa el libro. Allí puedes cambiarla y ver qué dice Lean: si pones el cursor al final de una línea, el panel de la derecha enseña las metas en ese punto. No hace falta instalar nada.

En este ejemplo, `obtain` saca de la hipótesis el número *k* con *n* = *k* + *k*. `use` propone 2*k*², porque (*k* + *k*)² = 4*k*² = 2*k*² + 2*k*². `rw` sustituye *n* por *k* + *k*, y `ring` comprueba la cuenta.

Lean no se fía de nadie: si en lugar de 2*k*² hubieras propuesto 3*k*², `ring` habría fallado, y Lean marcaría el error en esa línea.

## La misma idea en tres lenguajes

Lean no es el único demostrador. En algunos capítulos hay un recuadro con la misma demostración escrita en **Lean**, en **Rocq** (antes llamado Coq) y en **Isabelle**. Sirve para ver qué es propio de Lean y qué es común a todos.

## Lo que necesitas

Nada instalado: cada visualizador tiene su botón **Lean real ↗**. Para trabajar en tu ordenador, el libro está comprobado con **Lean 4.36.0** y **Mathlib** en su versión v4.36.0.
