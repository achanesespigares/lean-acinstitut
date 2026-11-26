---
title: Tus propias tácticas
subtitle: Las tácticas son programas en Lean, y puedes escribir las tuyas
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

El capítulo 24 dejó claro el reparto: el núcleo comprueba, las tácticas fabrican. Y las tácticas no son parte del núcleo, sino **programas escritos en Lean**. `omega`, `simp`, `linarith`, `get_elem_tactic`… todas están escritas en el mismo lenguaje que usamos para demostrar.

A lo largo del libro hay secuencias que se repiten: «prueba `omega`, y si no, `linarith`»; «da este testigo y haz la cuenta». En clase, cuando un razonamiento se repite, se le pone nombre («por el lema de antes…»). En Lean se puede hacer lo mismo con las tácticas.

## La pregunta

¿Cómo se define una táctica nueva? ¿Puede recibir argumentos? ¿Puede ampliarse después, como `get_elem_tactic`? ¿Y se puede escribir una que mire de verdad dentro de la meta?

## La idea

Hay tres niveles, de menos a más poder:

| Herramienta | Qué hace | Ejemplo |
|---|---|---|
| `macro` | pone nombre a una combinación de tácticas que ya existen | `macro "lineal" : tactic => `(tactic| first \| omega \| linarith)` |
| `syntax` + `macro_rules` | declara una táctica y le da varias formas de actuar, que se pueden ampliar después | `auto_mio`, con una regla para `omega` y otra para `positivity` |
| `elab` | un programa que lee la meta y las hipótesis y construye la prueba a mano | `mi_assumption`: busca una hipótesis que coincida con la meta |

Y para combinar tácticas, unas cuantas piezas: `first | t₁ | t₂` (la primera que funcione), `t₁ <;> t₂` (*t₂* en todas las metas que deja *t₁*), `all_goals t` (en todas las metas abiertas), `try t` (si falla, no pasa nada) y `repeat' t` (mientras funcione).

:::{important} Una táctica nueva no añade riesgo
Una táctica tuya, por mal escrita que esté, solo puede **fabricar un término**. El núcleo lo comprueba igual que todos los demás. Si la táctica se equivoca, el resultado es un error, nunca un teorema falso. Por eso cualquiera puede escribir tácticas sin poner en peligro lo que Lean demuestra: es la ventaja del criterio de de Bruijn del capítulo 24.
:::

## Construcción

### 1 · Una táctica con nombre

:::{tip} Predice
`lineal` prueba `omega` y, si falla, `linarith`. ¿Podrá demostrar 0 ≤ *x*² con *x* real?
:::

```lean
import Mathlib

macro "lineal" : tactic => `(tactic| first | omega | linarith)

example (x y : ℕ) (h : x + y ≤ 10) : x ≤ 10 := by
  lineal

example (a b : ℝ) (h : a < b) : a ≤ b + 1 := by
  lineal

example (x : ℝ) : 0 ≤ x ^ 2 := by
  lineal
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Ponerle nombre a una combinación","etiqueta":"macro · first","espera_error":true,"idea":"`macro` define una palabra nueva que Lean sustituye por las tácticas que dices. `lineal` es `first | omega | linarith`: prueba la primera y, si falla, la segunda.","notas":{"1":"Naturales: funciona `omega`, la primera de la lista.","2":"Reales: `omega` no sabe de reales y falla; `first` pasa a `linarith`, que sí puede.","3":"*x*² no es lineal: fallan las dos. El error que se ve es el de la última, `linarith`."}},"archivo":"datos/trazas/25-tacticas-1.json"}
```

- `macro "lineal" : tactic => …` dice tres cosas: el nombre (`"lineal"`), qué clase de cosa es (una táctica) y por qué se sustituye. Lo que va dentro de `` `(tactic| …) `` es código de tácticas normal.
- `first | omega | linarith` prueba las alternativas en orden y se queda con la primera que funciona. Si fallan todas, enseña el error de la última.
- El tercer ejemplo es útil precisamente porque falla: `lineal` solo sabe hacer lo que hacen `omega` y `linarith`. Para 0 ≤ *x*² haría falta `positivity` (ejercicio 4).

### 2 · Combinar tácticas

```lean
import Mathlib

example (n : ℕ) : n ≤ n + 1 ∧ n < n + 2 := by
  constructor <;> omega

example (a b : ℕ) (ha : a = 2) (hb : b = 3) : a + b = 5 ∧ a * b = 6 ∧ b - a = 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals subst ha hb
  all_goals rfl

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  repeat' constructor
  all_goals assumption
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una táctica para muchas metas","etiqueta":"<;> · all_goals · repeat'","idea":"Cuando una táctica deja varias metas parecidas, no hace falta tratarlas una a una: `<;>` y `all_goals` aplican la misma táctica a todas, y `repeat'` repite una táctica mientras siga funcionando.","notas":{"1":"`constructor` deja dos metas, y `<;> omega` cierra las dos.","2":"`refine` deja tres huecos, uno por cada parte del «y».","3":"En las tres metas, se sustituyen *a* y *b* por sus valores…","4":"…y las tres son cuentas que se cierran con `rfl`.","5":"`repeat'` aplica `constructor` mientras puede, también a las metas que van saliendo: quedan *p*, *q* y *r* por separado.","6":"Y cada una está entre las hipótesis."}},"archivo":"datos/trazas/25-tacticas-2.json"}
```

- `t₁ <;> t₂` aplica *t₂* a **todas** las metas que deja *t₁*. Es la forma más compacta cuando una táctica parte la meta en trozos que se resuelven igual.
- `all_goals t` hace lo mismo, pero sobre todas las metas abiertas en ese momento, sean de donde sean.
- `repeat'` repite una táctica mientras funcione, también en las metas nuevas. Con `repeat` a secas no basta aquí: se para en cuanto falla en la primera meta (*p*, que no se puede partir), y deja *q* ∧ *r* sin tocar.

### 3 · Una táctica con argumentos

Una táctica puede recibir lo que le escribas detrás: un término, un nombre, un número.

```lean
import Mathlib

macro "usa_y_calcula " t:term : tactic => `(tactic| (refine ⟨$t, ?_⟩; norm_num))

example : ∃ n : ℕ, n * n = 49 := by
  usa_y_calcula 7

example : ∃ x : ℝ, 2 * x + 1 = 8 := by
  usa_y_calcula 7 / 2
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una táctica que recibe un testigo","etiqueta":"macro · argumentos · $t","idea":"`t:term` dice que, detrás del nombre, la táctica espera un término. Dentro, `$t` es ese término: `usa_y_calcula 7` se convierte en `refine ⟨7, ?_⟩; norm_num`.","notas":{"1":"El testigo es 7, y `norm_num` comprueba 7 · 7 = 49.","2":"Con reales: el testigo es 7/2, y `norm_num` comprueba 2 · (7/2) + 1 = 8."}},"archivo":"datos/trazas/25-tacticas-3.json"}
```

- `t:term` declara el argumento: un término de Lean, que dentro de la definición se escribe `$t`. Es como el parámetro de una función, pero para código.
- `refine ⟨$t, ?_⟩` da el testigo del «existe» y deja un hueco para la propiedad; `norm_num` lo rellena haciendo la cuenta. Es la pareja `use` + `norm_num` de muchos capítulos, con un nombre.
- Lean sustituye la macro **antes** de ejecutar nada: para él, `usa_y_calcula 7` y `refine ⟨7, ?_⟩; norm_num` son exactamente lo mismo.

### 4 · Una táctica que se puede ampliar

`macro` define una táctica de una vez. Con `syntax` y `macro_rules` se separan las dos cosas: primero se declara el nombre, y después se le van añadiendo **reglas**, incluso en otros archivos. Es justo como está hecha `get_elem_tactic` (capítulo 23).

```lean
import Mathlib

syntax "auto_mio" : tactic
macro_rules | `(tactic| auto_mio) => `(tactic| omega)
macro_rules | `(tactic| auto_mio) => `(tactic| positivity)

example (n : ℕ) (h : n % 4 = 3) : n % 2 = 1 := by
  auto_mio

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  auto_mio

example (x : ℝ) : x ≤ x ^ 2 + 1 := by
  auto_mio
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Reglas que se acumulan","etiqueta":"syntax · macro_rules","espera_error":true,"idea":"`auto_mio` tiene dos reglas. Lean las prueba empezando por la **última** que se añadió (`positivity`) y, si falla, pasa a la anterior (`omega`). Cada regla nueva amplía lo que sabe hacer la táctica.","notas":{"1":"`positivity` no sirve para restos; Lean pasa a la regla anterior, `omega`, que sí.","2":"Aquí funciona la última regla, `positivity`.","3":"No funciona ninguna: *x* ≤ *x*² + 1 no es positividad ni aritmética lineal de naturales. El error es el de la última que se probó, `omega`."}},"archivo":"datos/trazas/25-tacticas-4.json"}
```

- `syntax "auto_mio" : tactic` solo declara que existe una táctica con ese nombre. Sin ninguna regla, usarla daría el error «has not been implemented».
- Cada `macro_rules` añade una forma de expandirla. Lean prueba **de la más nueva a la más antigua**, y se queda con la primera que no falla.
- Así crece `get_elem_tactic`: Lean trae unas reglas, y Mathlib (o tú) puede añadir otras sin tocar las originales. Una táctica abierta, que cada biblioteca va enseñando a hacer cosas nuevas.

::::{div}
:class: afondo
### 5 · `elab`: una táctica que mira dentro

`macro` solo combina tácticas que ya existen. Con `elab` se escribe un **programa** que tiene acceso a todo: la meta, las hipótesis, el núcleo. Es así como están hechas `omega`, `simp` o `linarith`.

```lean
import Mathlib

open Lean Elab Tactic Meta in
elab "mira_meta" : tactic => do
  let g ← getMainGoal
  logInfo m!"La meta es: {← g.getType}"

open Lean Elab Tactic Meta in
elab "mi_assumption" : tactic => withMainContext do
  let g ← getMainGoal
  let objetivo ← g.getType
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      if ← isDefEq d.type objetivo then
        g.assign d.toExpr
        replaceMainGoal []
        return
  throwError "ninguna hipótesis coincide con la meta"

example (a b : ℕ) (h1 : a < b) (h2 : b < 10) : b < 10 := by
  mira_meta
  mi_assumption

example (a b : ℕ) (h1 : a < b) : b < 10 := by
  mi_assumption

theorem conMi (p : Prop) (hp : p) : p := by
  mi_assumption

#print conMi
#print axioms conMi
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un programa que construye la prueba","etiqueta":"a fondo · elab · TacticM · isDefEq · assign","espera_error":true,"idea":"`mi_assumption` recorre las hipótesis una a una. Cuando encuentra una cuyo tipo es la meta, la usa como prueba: rellena la meta con ella (`assign`) y la da por cerrada. Si no encuentra ninguna, da un error con el mensaje que tú has escrito.","notas":{"1":"`mira_meta` no cambia nada: solo escribe la meta en los mensajes. Lean avisa, con razón, de que no cambia la meta.","2":"`mi_assumption` recorre *a*, *b*, `h1`, `h2`… y `h2` coincide con la meta. Lean avisa de que `h1` no se ha usado: es verdad, la táctica eligió `h2`.","3":"Sin una hipótesis `b < 10`, la táctica no encuentra nada y lanza su propio error.","4":"El término que fabricó es `fun p hp => hp`, y no depende de ningún axioma: el núcleo lo ha comprobado como cualquier otro."}},"archivo":"datos/trazas/25-tacticas-5.json"}
```

Línea a línea, `mi_assumption` hace esto:

- `getMainGoal` coge la meta principal, y `g.getType` su enunciado: lo que va después de `⊢`.
- `getLCtx` es el **contexto local**: todo lo que hay encima de la raya del panel. El bucle `for` lo recorre, saltándose las piezas internas que Lean no enseña (`isImplementationDetail`).
- `isDefEq d.type objetivo` pregunta si el tipo de la hipótesis es, por definición, el de la meta. Es la misma comparación que hace el núcleo, calculando si hace falta.
- Si coincide, `g.assign d.toExpr` **rellena el hueco** de la meta con la hipótesis: ese es el término de la prueba. `replaceMainGoal []` dice que ya no quedan metas.
- Si no coincide ninguna, `throwError` da un error con el mensaje que queramos.

Al final, `#print conMi` enseña lo fabricado: `fun p hp => hp`, el mismo término que habríamos escrito a mano en el capítulo 21. Y `#print axioms conMi` dice que no depende de ningún axioma. La táctica es nuestra, pero la prueba la ha comprobado el núcleo. Es la idea de toda la parte V, vista desde dentro: **las tácticas proponen, el núcleo dispone**.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Una táctica propia que prueba la aritmética lineal y, si no, otra cosa (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: macro
macro "lineal" : tactic => `(tactic| first | omega | linarith)
example (x y : ℕ) (h : x + y ≤ 10) : x ≤ 10 := by lineal
```

```coq
(* Rocq (Coq): Ltac *)
Require Import Lia.
Ltac lineal := first [ lia | reflexivity ].
Lemma l1 (x y : nat) : x + y <= 10 -> x <= 10.
Proof. lineal. Qed.
Ltac usa_y_calcula t := exists t; reflexivity.
Lemma l2 : exists n : nat, n * n = 49.
Proof. usa_y_calcula 7. Qed.
```

```isabelle
(* Isabelle: Eisbach (en ROOT: sessions "HOL-Eisbach") *)
theory Prueba imports Main "HOL-Eisbach.Eisbach" begin
method lineal = (arith | simp)
lemma l1: "(x::nat) + y \<le> 10 \<Longrightarrow> x \<le> 10" by lineal
end
```

Los tres sistemas dejan que el usuario defina sus propias tácticas, con un lenguaje pensado para eso: `macro` y `elab` en Lean, Ltac en Rocq, Eisbach en Isabelle. Y en los tres se cumple lo mismo: la táctica nueva solo propone pasos, y el núcleo de cada sistema los comprueba. En Lean, además, el lenguaje de las tácticas es el propio Lean: la misma herramienta sirve para demostrar teoremas, para escribir programas y para escribir las tácticas que los demuestran.
:::

## Conexiones

- El reparto núcleo/tácticas del capítulo 24 es lo que permite escribir tácticas sin riesgo.
- `get_elem_tactic` del capítulo 23 está hecha con `macro_rules`, como `auto_mio`.
- `refine ⟨?_, ?_⟩` (capítulos 12 y 19) y los huecos `?_` son las metas que una táctica deja abiertas; `g.assign` es rellenar uno.
- El término `fun p hp => hp` es el del capítulo 21: una táctica, al final, fabrica un objeto.

## La grieta

La parte V termina aquí: ya sabemos qué es una prueba (un objeto), dónde vive (en una escalera de universos), quién la fabrica (las tácticas, también las nuestras) y quién la comprueba (el núcleo, con tres axiomas). Falta usarlo todo junto en algo de verdad. Los dos proyectos finales cierran lo que el libro de SageMath dejó abierto: demostrar que el **fabricante de ejercicios** funciona siempre, y demostrar que **RSA** descifra lo que cifra. Empezamos por el primero.

## Ejercicios

1. **Una táctica para cerrar.** Define `cierra` como `first | rfl | decide | omega` y úsala en `2 + 2 = 4`, `7 ∣ 91` y en `n ≠ 3` a partir de `h : n > 5`.

2. **Tres metas de golpe.** Demuestra `n < n + 1 ∧ n < n + 2 ∧ n < n + 3` en una sola línea, con `refine` y `<;>`.

3. **Un testigo para la divisibilidad.** Usa `usa_y_calcula` para demostrar `3 ∣ 12`. ¿Por qué funciona, si `3 ∣ 12` no tiene un «existe» a la vista?

4. **Arreglar `lineal`.** Define `lineal2`, que pruebe también `positivity`, y demuestra con ella `0 ≤ x ^ 2`.

5. **Una regla más.** Añade a `auto_mio` una regla con `norm_num` y demuestra `(2 : ℝ) ^ 10 = 1024`. Comprueba que el primer ejemplo del apartado 4 (`n % 2 = 1`) sigue funcionando. Si no, ¿qué falla, y cómo se arregla?

6. **`repeat` y `repeat'`.** En el apartado 2, ¿qué metas quedan si se cambia `repeat'` por `repeat`? ¿Por qué?

::::{div}
:class: afondo
7. **Contar hipótesis.** Escribe con `elab` una táctica `cuenta_hipotesis` que escriba en los mensajes cuántas cosas hay encima de la raya. Pruébala con `(a b : ℕ) (h : a < b) : a ≤ b`.

8. **¿Y si la táctica se equivoca?** Imagina que `mi_assumption` tuviera un error y asignara a la meta una hipótesis que **no** coincide. ¿Qué pasaría? ¿Podría acabar demostrando algo falso?
::::

## Solucionario

1. Una línea por ejemplo:
   ```lean
   macro "cierra" : tactic => `(tactic| first | rfl | decide | omega)
   example : 2 + 2 = 4 := by cierra
   example : 7 ∣ 91 := by cierra
   example (n : ℕ) (h : n > 5) : n ≠ 3 := by cierra
   ```
   La primera la cierra `rfl`, la segunda `decide` y la tercera `omega`.
2. `example (n : ℕ) : n < n + 1 ∧ n < n + 2 ∧ n < n + 3 := by refine ⟨?_, ?_, ?_⟩ <;> omega`.
3. `example : 3 ∣ 12 := by usa_y_calcula 4`. Funciona porque, por definición, `3 ∣ 12` significa «existe *c* con 12 = 3 · *c*»: `refine ⟨4, ?_⟩` ve ese «existe» al desplegar la definición, y `norm_num` comprueba 12 = 3 · 4.
4. `macro "lineal2" : tactic => `(tactic| first | omega | linarith | positivity)` y `example (x : ℝ) : 0 ≤ x ^ 2 := by lineal2`.
5. Con `macro_rules | `(tactic| auto_mio) => `(tactic| norm_num)` se demuestra `(2 : ℝ) ^ 10 = 1024`, pero el ejemplo de los restos **deja de funcionar**: la regla nueva se prueba primero, y `norm_num` no falla en `n % 2 = 1`, pero tampoco la cierra. Para `macro_rules`, «no fallar» basta, así que no pasa a las demás reglas, y la meta queda sin demostrar. El arreglo es exigir que la regla cierre la meta, con `done`:
   ```lean
   macro_rules | `(tactic| auto_mio) => `(tactic| (norm_num; done))
   ```
   Es el mismo truco que usa Lean en `get_elem_tactic`, con su regla `simp +arith; done`.
6. Con `repeat constructor` quedan *p* y *q* ∧ *r*. `repeat` sigue aplicando `constructor` a la **primera** meta; cuando llega a *p*, que no se puede partir, falla y se para, sin mirar *q* ∧ *r*. Por eso `all_goals assumption` falla en *q* ∧ *r*. `repeat'` en cambio sigue también por las demás metas.

::::{div}
:class: afondo
7. Una forma de escribirla:
   ```lean
   open Lean Elab Tactic Meta in
   elab "cuenta_hipotesis" : tactic => withMainContext do
     let n := (← getLCtx).foldl
       (fun (k : Nat) d => if d.isImplementationDetail then k else k + 1) 0
     logInfo m!"Hay {n} hipótesis"
   ```
   Con `(a b : ℕ) (h : a < b)`, escribe «Hay 3 hipótesis»: cuenta todo lo que hay encima de la raya, *a*, *b* y `h`. (El `(k : Nat)` hace falta para que Lean sepa que el 0 es un número.)
8. El núcleo lo rechazaría. La táctica solo propone un término; al final, el núcleo comprueba que su tipo es el enunciado del teorema, y si no coincide, da un error. Una táctica con errores puede fallar, pero no puede hacer pasar por bueno un teorema falso. (La única forma de colar algo falso es un axioma, y `#print axioms` lo delata, como en el capítulo 24.)
::::
