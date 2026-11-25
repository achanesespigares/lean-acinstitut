---
title: El panel de metas
subtitle: Lo que Lean sabe, lo que falta y cómo moverse entre las dos cosas
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En una demostración a mano hay dos cosas a la vista todo el rato, aunque no se escriban: lo que ya sabes (los datos, las hipótesis, lo que has deducido) y lo que te falta por demostrar.

Lean las escribe siempre. Después de cada táctica, el **panel de metas** dice qué tienes y qué te falta. En los capítulos anteriores lo hemos mirado de pasada. En este lo leemos con calma, porque es la herramienta con la que se trabaja en todo el resto del libro.

## La pregunta

¿Qué significa cada línea del panel? ¿Qué pasa cuando hay que demostrar dos cosas a la vez? ¿Y cómo se le dice a Lean «ahora me ocupo de esta»?

## La idea

El panel tiene dos partes, separadas por el símbolo `⊢`:

```text
x y : ℕ           ← dos naturales: se agrupan si son del mismo tipo
hx : x = 3        ← una hipótesis: su nombre y lo que afirma
hy : y = 2 * x
⊢ y = 6           ← la meta: lo que falta demostrar
```

- **Encima** de `⊢` está el **contexto**: las variables y las hipótesis que puedes usar. Cada línea es `nombre : tipo`. Para un número, el tipo dice qué clase de número es. Para una hipótesis, el tipo es lo que afirma.
- **Detrás** de `⊢` está la **meta**, lo que falta demostrar.
- Cada táctica cambia el panel: añade hipótesis, cambia la meta, la parte en varias o la cierra. Cuando no queda ninguna meta, la demostración está hecha.

:::{important} Varias metas, una cada vez
A veces hay que demostrar varias cosas: por ejemplo, las dos mitades de una «y». Entonces el panel tiene varias metas, cada una con su contexto. Lean trabaja siempre en la **primera**. Con el punto `·` le dices «ahora, solo esta», y no puedes salir del punto hasta cerrarla.
:::

## Construcción

### 1 · Leer el panel

:::{tip} Predice
Si en la meta `y = 6` cambias `y` por lo que dice `hy`, ¿qué meta queda?
:::

```lean
import Mathlib

example (x y : ℕ) (hx : x = 3) (hy : y = 2 * x) : y = 6 := by
  rw [hy]
  rw [hx]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que sabes y lo que te falta","etiqueta":"contexto · ⊢ · meta","idea":"Antes de la primera táctica, el panel copia el enunciado: los datos y las hipótesis van encima de `⊢`, y lo que hay que demostrar, detrás.","notas":{"0":"`x y : ℕ`: dos naturales. `hx` y `hy`: dos hipótesis, con lo que afirman. Detrás de `⊢`, la meta.","1":"`rw [hy]` cambia `y` por `2 * x` en la meta. El contexto no cambia.","2":"Ahora `x` por `3`: queda `2 * 3 = 6`, que Lean comprueba calculando. No quedan metas."}},"archivo":"datos/trazas/04-panel-1.json"}
```

- Antes de la primera táctica, el panel es el enunciado puesto en vertical. Los datos `(x y : ℕ)` y las hipótesis `(hx : x = 3)` y `(hy : y = 2 * x)` pasan encima de la raya. Lo que va detrás de los dos puntos, `y = 6`, es la meta.
- `x y : ℕ` ocupa una sola línea: Lean agrupa las variables seguidas del mismo tipo.
- `rw [hy]` (de *rewrite*, reescribir) cambia en la meta lo de la izquierda de `hy` por lo de la derecha. El capítulo siguiente lo cuenta con detalle.
- Tras `rw [hx]`, la meta sería `2 * 3 = 6`. Después de reescribir, `rw` prueba `rfl`, que cierra la meta calculando.

### 2 · Varias metas a la vez

Para demostrar «*A* y *B*» hay que demostrar *A* y, aparte, *B*. La táctica `constructor` parte la meta en esas dos.

:::{tip} Predice
La meta es `n > 3 ∧ n < 5 ∧ n ≠ 0`, con tres partes. ¿En cuántas metas la parte `constructor`?
:::

```lean
import Mathlib

example (n : ℕ) (h : n = 4) : n > 3 ∧ n < 5 ∧ n ≠ 0 := by
  constructor
  · omega
  · constructor
    · omega
    · omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Partir la meta y cerrarla por trozos","etiqueta":"constructor · ·","idea":"`constructor` parte una «y» en dos metas. Cada punto `·` trabaja una sola meta y no termina hasta cerrarla; las demás siguen esperando.","notas":{"1":"Dos metas, no tres: `∧` agrupa por la derecha, así que la meta era `n > 3 ∧ (n < 5 ∧ n ≠ 0)`. Cada una lleva su nombre: `left` y `right`.","2":"Dentro del primer punto, Lean solo ve la meta `left`, y `omega` la cierra usando `h`.","3":"Dentro del segundo punto, otra «y»: otro `constructor`. Los nombres se encadenan: `right.left` y `right.right`.","4":"Se cierra `right.left`. Queda `right.right`.","5":"Y la última."}},"archivo":"datos/trazas/04-panel-2.json"}
```

- `constructor` da **dos** metas: `∧` agrupa por la derecha, y la meta era `n > 3 ∧ (n < 5 ∧ n ≠ 0)`. La primera es `n > 3` y la segunda, el resto.
- Cada meta tiene su contexto, aquí igual en las dos, y un nombre, `case left` y `case right`. Los nombres se encadenan: al partir `right` salen `right.left` y `right.right`.
- El punto `·` encierra el trabajo de una meta. Lean muestra solo esa, y avisa si el punto acaba sin cerrarla. La sangría indica dónde acaba cada punto, como en una lista.
- `omega` resuelve igualdades y desigualdades con sumas de naturales y enteros, usando las hipótesis del contexto. Aquí basta con `h : n = 4`.

### 3 · Elegir la meta por su nombre

El punto trabaja la primera meta. Con `case` eliges cuál, por su nombre.

```lean
import Mathlib

example (n : ℕ) (h : n = 4) : n > 3 ∧ n < 5 := by
  constructor
  case left => omega
  case right => omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"case: la meta por su nombre","etiqueta":"case · =>","idea":"`case left =>` busca la meta que se llama `left` y aplica lo que va detrás de `=>` solo a ella.","notas":{"1":"Dos metas: `left` y `right`.","2":"`case left =>` ha elegido la meta `left`. Lo que va detrás de la flecha, `omega`, trabaja solo con ella.","3":"Y ahora la meta `right`."}},"archivo":"datos/trazas/04-panel-3.json"}
```

- `case left => omega` hace lo mismo que `· omega`, pero dice a qué meta se refiere. Si ninguna se llama `left`, Lean da un error.
- Con `case` se pueden trabajar las metas en cualquier orden: `case right` primero y `case left` después también vale.
- En demostraciones largas, `case` ayuda a leerlas: dice qué parte se está demostrando sin tener que contar metas.

### 4 · Añadir lo que sabes: `have` y `show`

En la pizarra, a mitad de demostración, uno escribe «primero veamos que *a* = 7». En Lean, eso es `have`.

```lean
import Mathlib

example (a : ℕ) (h : a + 3 = 10) : a * 2 = 14 := by
  have ha : a = 7 := by omega
  rw [ha]

example (a : ℕ) (h : a + 3 = 10) : a * 2 = 14 := by
  show a * 2 = 14
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un resultado intermedio","etiqueta":"have · show","idea":"`have` demuestra algo aparte y lo añade al contexto con un nombre. `show` escribe la meta que crees tener: si no coincide, Lean protesta.","notas":{"1":"`have ha : a = 7 := by omega`: una línea nueva en el contexto, `ha : a = 7`. La meta no cambia.","2":"Por dentro, `have` abre una meta propia, `a = 7`, y `omega` la cierra con `h`.","3":"Con `ha`, la meta `a * 2 = 14` pasa a `7 * 2 = 14`, y se cierra calculando.","4":"`show a * 2 = 14` no cambia nada: confirma que la meta es esa. Sirve de recordatorio para quien lee.","5":"`omega` sola también llega, sin el paso intermedio."}},"archivo":"datos/trazas/04-panel-4.json"}
```

- `have ha : a = 7 := by omega` tiene tres partes: el nombre, `ha`; lo que afirma, `a = 7`; y su demostración, detrás de `:=`. Al acabar, `ha` está en el contexto.
- La demostración de `have` es una meta aparte, con el mismo contexto. El visualizador la enseña en su propio paso.
- `show` escribe la meta que esperas. Si no es esa, Lean da un error. Sirve para leer la prueba sin el panel delante y para comprobar que vas por donde crees.
- `show` también admite una meta que sea igual **por definición**: con la meta `2 + 2 = 4`, `show 4 = 4` funciona, porque Lean calcula `2 + 2`.

::::{div}
:class: afondo
### 5 · Nombres que no se pueden escribir

Si haces `intro` sin dar un nombre, ¿cómo llama Lean al número?

```lean
import Mathlib

example : ∀ n : ℕ, n + 0 = n := by
  intro
  rfl

example : ∀ n : ℕ, n + 0 = n := by
  intro
  rename_i m
  rfl
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El nombre con daga","etiqueta":"a fondo · intro · rename_i","idea":"Sin nombre, `intro` deja una variable con una cruz detrás, `n✝`. Se ve en el panel, pero no se puede escribir en una táctica. `rename_i` le pone nombre.","notas":{"1":"`n✝`: Lean conserva el nombre del enunciado y le añade la cruz. Esa variable no se puede nombrar.","2":"`rfl` no necesita nombrarla.","3":"Otra vez `n✝`…","4":"…y `rename_i m` le da un nombre utilizable: `m`.","5":"Igual que antes."}},"archivo":"datos/trazas/04-panel-5.json"}
```

Sin nombre, `intro` deja en el contexto `n✝ : ℕ`. La cruz (✝) marca un nombre **inaccesible**: Lean lo enseña en el panel, pero no se puede escribir en una táctica. `n✝` no es un nombre válido en el código, así que `rw [n✝]` o `omega` con `n✝` no tienen forma de referirse a él.

Pasa porque `intro` sin nombre fabrica la variable por su cuenta. Lean reutiliza el nombre del enunciado, `n`, para que se reconozca, y lo marca para que no choque con ningún `n` que escribas tú.

`rename_i m` pone nombre a la última variable inaccesible. En la práctica es mejor escribir `intro n` desde el principio: la demostración se lee mejor y no hace falta renombrar.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Partir «*n* > 3 y *n* < 5» en dos metas, sabiendo que *n* = 4 (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026). Los tres enseñan el panel de forma parecida:

```text
-- Lean, tras constructor
case left                case right
n : ℕ                    n : ℕ
h : n = 4                h : n = 4
⊢ n > 3                  ⊢ n < 5
```

```coq
(* Rocq (Coq): split parte la meta; Show enseña el panel *)
Require Import Arith Lia.
Goal forall n : nat, n = 4 -> n > 3 /\ n < 5.
Proof.
  intros n h. split.
  - lia.
  - lia.
Qed.
```

```text
(* Rocq, tras split *)
2 goals

  n : nat
  h : n = 4
  ============================
  n > 3

goal 2 is:
 n < 5
```

```isabelle
(* Isabelle: la regla conjI parte la «y» *)
lemma "(n::nat) = 4 ==> n > 3 & n < 5"
  apply (rule conjI)
  apply simp
  apply simp
  done
```

```text
(* Isabelle, tras rule conjI *)
goal (2 subgoals):
 1. n = 4 ⟹ 3 < n
 2. n = 4 ⟹ n < 5
```

Rocq usa una raya de iguales donde Lean pone `⊢`, y de la segunda meta solo enseña lo que falta. Isabelle no separa el contexto: cada submeta lleva delante sus hipótesis, unidas con `⟹`. Y escribe `3 < n` donde Lean escribe `n > 3`: para Isabelle, `>` es solo otra forma de escribir `<`.
:::

## Conexiones

- En el capítulo 3, `intro n` añadía `n : ℕ` al contexto y quitaba el ∀ de la meta. Ahora sabes leerlo: una línea más encima de la raya.
- `constructor` y el punto `·` vuelven en la parte II, con la conjunción y la disyunción. Cada regla lógica dice cómo cambia el panel.
- `have` es la forma de escribir demostraciones largas por pasos. La usaremos en casi todos los capítulos de matemáticas.
- `rw` ha salido dos veces. El capítulo siguiente explica qué busca y qué cambia.

## La grieta

`rw [hy]` cambió `y` por `2 * x`, y `rw [hx]` cerró la meta sin pedir nada más. ¿Por qué la cerró? ¿Qué pasa si lo que quieres cambiar no aparece en la meta, o aparece al revés? ¿Y qué hace `simp`, que en el capítulo 3 demostró `0 + n = n` sin decirle cómo? Lo vemos en el capítulo siguiente, **Reescribir: rw y simp**.

## Ejercicios

1. **Leer un panel.** En este panel, ¿cuántas variables hay, cuántas hipótesis y cuál es la meta?

   ```text
   a b : ℕ
   h : a < b
   ⊢ a ≤ b
   ```

2. **Contar metas.** Con `p q r : Prop`, ¿cuántas metas deja `constructor` en `p ∧ q ∧ r`? ¿Cómo se llaman?

3. **Dos metas.** Demuestra, con `constructor` y dos puntos, que si *n* = 2 entonces *n* + *n* = 4 y *n* · *n* = 4.

4. **Un paso intermedio.** Sabiendo que 2*a* = 10, demuestra que *a* + 1 = 6 con un `have` que diga cuánto vale *a*.

5. **Al revés.** Repite el ejercicio 3 con `case`, demostrando primero la segunda meta.

6. **Lo que crees que falta.** En `example (x : ℕ) (h : x + 1 = 5) : x = 4`, escribe `show` con la meta antes de cerrarla con `omega`. ¿Qué pasa si escribes `show x = 5`?

::::{div}
:class: afondo
7. **La cruz.** Demuestra `∀ x : ℕ, x * 0 = 0` empezando con `intro`, sin nombre. ¿Qué enseña el panel? Ponle nombre y termina.

8. **Hipótesis en cada submeta.** En Isabelle, tras `rule conjI`, la hipótesis `n = 4` aparece dos veces. ¿Por qué? ¿Dónde está en Lean?
::::

## Solucionario

1. Dos variables, `a` y `b`, naturales y en la misma línea. Una hipótesis, `h : a < b`. La meta es `a ≤ b`.
2. Dos: `case left`, con meta `p`, y `case right`, con meta `q ∧ r`. `∧` agrupa por la derecha.
3. ```lean
   example (n : ℕ) (h : n = 2) : n + n = 4 ∧ n * n = 4 := by
     constructor
     · rw [h]
     · rw [h]
   ```
   Tras `rw [h]`, las metas son `2 + 2 = 4` y `2 * 2 = 4`, y el `rfl` que prueba `rw` al terminar las cierra.
4. ```lean
   example (a : ℕ) (h : 2 * a = 10) : a + 1 = 6 := by
     have ha : a = 5 := by omega
     rw [ha]
   ```
5. ```lean
   example (n : ℕ) (h : n = 2) : n + n = 4 ∧ n * n = 4 := by
     constructor
     case right => rw [h]
     case left => rw [h]
   ```
6. `show x = 4` y después `omega`. Con `show x = 5`, Lean da un error: esa no es la meta, ni es igual a ella por definición.

::::{div}
:class: afondo
7. Tras `intro`, el panel enseña `x✝ : ℕ ⊢ x✝ * 0 = 0`. Con `rename_i y` pasa a `y : ℕ ⊢ y * 0 = 0`, y `rfl` cierra: el producto de naturales está definido mirando el segundo factor, y *y* · 0 = 0 es una de sus reglas.
   ```lean
   example : ∀ x : ℕ, x * 0 = 0 := by
     intro
     rename_i y
     rfl
   ```
8. Isabelle no tiene un contexto común: cada submeta es una afirmación completa, «si *n* = 4, entonces…», así que cada una lleva la hipótesis delante. En Lean, `h : n = 4` está en el contexto de cada meta, encima de `⊢`.
::::
