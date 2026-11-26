---
title: Inducción
subtitle: El efecto dominó, o cómo demostrar algo para todos los naturales
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En el capítulo 3 dejamos un teorema tapado con `sorry`: 2 · (1 + 2 + ⋯ + *n*) = *n*(*n* + 1). Para *n* = 3 es fácil comprobarlo (2 · 6 = 3 · 4), y para *n* = 100 también, con paciencia. Pero ¿para **todo** *n*?

Con `intro n`, *n* es un natural cualquiera, y no hay cuenta que valga para todos a la vez. Hace falta una idea distinta, la del **dominó**:

- Si cae la primera ficha,
- y cada ficha, al caer, tira la siguiente,
- entonces caen todas.

Eso es la **inducción**. Se demuestra el caso *n* = 0 (la primera ficha). Después se demuestra que, si vale para un *k*, también vale para *k* + 1 (cada ficha tira la siguiente). Y con eso vale para todos los naturales.

## La pregunta

¿Cómo se hace una inducción en Lean? ¿Qué metas quedan, y qué es eso de la «hipótesis de inducción» en el panel? ¿Y se puede usar para desigualdades y para sumas con Σ?

## La idea

`induction n` cambia una meta sobre *n* por **dos metas**:

| Caso | Se llama | Qué hay que demostrar | Qué tienes |
|---|---|---|---|
| Base | `zero` | la afirmación para *n* = 0 | nada nuevo |
| Paso | `succ` | la afirmación para *k* + 1 | la afirmación para *k*: la **hipótesis de inducción** |

Cada caso se trabaja con `case`, como en el capítulo 4, que además pone nombre a lo que trae: `case succ k ih =>` llama `k` al número e `ih` a la hipótesis de inducción (de *induction hypothesis*).

:::{important} La hipótesis de inducción no es trampa
En el paso no se supone lo que se quiere demostrar. Se supone la afirmación para un *k* concreto y se demuestra para *k* + 1. El truco del paso es siempre el mismo: escribir lo de *k* + 1 de forma que aparezca lo de *k*, y ahí usar `ih`.
:::

## Construcción

### 1 · La primera inducción

En el capítulo 3, `rfl` no pudo con 0 + *n* = *n*: la suma de Lean mira el segundo sumando, y con un *n* cualquiera no sabe qué hacer. Por inducción sale.

:::{tip} Predice
Tras `induction n`, ¿cuántas metas habrá? ¿Qué dirá la del caso `succ`?
:::

```lean
import Mathlib

theorem cero_mas (n : ℕ) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ k ih => rw [Nat.add_succ, ih]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Base y paso","etiqueta":"induction · zero · succ · ih","idea":"`induction n` parte la meta en dos: el caso base, con *n* = 0, y el paso, que lleva como hipótesis la misma afirmación para el número anterior.","notas":{"1":"En `succ`, Lean aún no ha puesto nombres: `n✝` es el número y `a✝` la hipótesis de inducción (la cruz del capítulo 4).","2":"Base: 0 + 0 = 0, por cálculo.","3":"`case succ k ih` pone nombres: `k` y `ih : 0 + k = k`. `Nat.add_succ` saca el + 1 fuera: 0 + (*k* + 1) = (0 + *k*) + 1. Ahí aparece lo de *k*, y `ih` lo cambia por *k*."}},"archivo":"datos/trazas/11-induccion-1.json"}
```

- Tras `induction n`, el panel tiene dos metas. La del caso `zero` es `0 + 0 = 0`. La del caso `succ` es `0 + (n✝ + 1) = n✝ + 1`, con la hipótesis `0 + n✝ = n✝`.
- Los nombres con cruz son los que pone Lean cuando no se los das. `case succ k ih =>` los cambia por `k` e `ih`, que sí se pueden escribir.
- El paso es el truco de siempre: hacer aparecer lo de *k*. `Nat.add_succ` dice que *a* + (*b* + 1) = (*a* + *b*) + 1, así que 0 + (*k* + 1) pasa a ser (0 + *k*) + 1, y ahí `ih` cambia 0 + *k* por *k*.

### 2 · El teorema pendiente

Ahora sí: el `sorry` del capítulo 3.

```lean
import Mathlib

def suma : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + suma n

theorem suma_formula (n : ℕ) : 2 * suma n = n * (n + 1) := by
  induction n
  case zero => rfl
  case succ k ih =>
    rw [suma, mul_add, ih]
    ring

#print axioms suma_formula
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"1 + 2 + ⋯ + n, para todo n","etiqueta":"induction · rw [suma] · ring","idea":"El paso abre `suma (k + 1)` con su definición, `(k + 1) + suma k`. Así aparece `suma k`, y la hipótesis de inducción dice cuánto vale.","notas":{"1":"En el paso, la hipótesis es la fórmula para el número anterior.","2":"Base: 2 · 0 = 0 · 1, por cálculo.","3":"Tres reescrituras: `suma` abre la definición, `mul_add` reparte el 2, e `ih` cambia `2 * suma k` por `k * (k + 1)`. Queda álgebra.","4":"`ring` comprueba que 2(*k* + 1) + *k*(*k* + 1) = (*k* + 1)(*k* + 2)."}},"archivo":"datos/trazas/11-induccion-2.json"}
```

- `rw [suma]` usa la definición: `suma (k + 1)` pasa a ser `(k + 1) + suma k`. Es la segunda regla de `suma`, escrita en el capítulo 2.
- `mul_add` reparte el 2: 2 · ((*k* + 1) + `suma k`) = 2(*k* + 1) + 2 · `suma k`. Así aparece `2 * suma k`, que es justo el lado izquierdo de `ih`.
- Tras `rw [ih]`, la meta ya no tiene `suma`: es 2(*k* + 1) + *k*(*k* + 1) = (*k* + 1)(*k* + 2), y `ring` lo comprueba.
- `#print axioms suma_formula` contesta `[propext]`. En el capítulo 3, la misma pregunta daba `sorryAx`. El teorema ya no tiene tapas.

### 3 · Inducción con desigualdades

¿Crece 2*ⁿ* más deprisa que *n*? Por inducción: *n* + 1 ≤ 2*ⁿ* para todo *n*.

```lean
import Mathlib

theorem dos_pot (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n
  case zero => norm_num
  case succ k ih =>
    rw [pow_succ]
    omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una ficha tira la siguiente","etiqueta":"induction · pow_succ · omega","idea":"Si *k* + 1 ≤ 2ᵏ, entonces *k* + 2 ≤ 2ᵏ · 2: basta duplicar la desigualdad. `pow_succ` escribe 2ᵏ⁺¹ como 2ᵏ · 2 para que se vea.","notas":{"2":"Base: 0 + 1 ≤ 2⁰ = 1.","3":"`pow_succ` dice que *a*ⁿ⁺¹ = *a*ⁿ · *a*. La meta queda `k + 1 + 1 ≤ 2 ^ k * 2`.","4":"Con `ih : k + 1 ≤ 2 ^ k`, `omega` ve que *k* + 2 ≤ 2(*k* + 1) ≤ 2 · 2ᵏ. Trata 2ᵏ como un número desconocido."}},"archivo":"datos/trazas/11-induccion-3.json"}
```

- `pow_succ` escribe la potencia siguiente a partir de la anterior: 2*ᵏ*⁺¹ = 2*ᵏ* · 2. Así aparece 2*ᵏ*, que es de lo que habla `ih`.
- `omega` no sabe nada de potencias, pero no le hace falta: trata `2 ^ k` como un número desconocido, digamos *P*. Con *k* + 1 ≤ *P*, ve que *k* + 2 ≤ 2*P*.
- Sin `ih`, `omega` no podría: de la meta sola no se deduce nada. La hipótesis de inducción es la ficha anterior empujando.

### 4 · Sumas con Σ

Mathlib escribe las sumas con Σ: `∑ i ∈ range n, f i` es *f*(0) + *f*(1) + ⋯ + *f*(*n* − 1). Con eso, un clásico: la suma de los *n* primeros impares es *n*².

```lean
import Mathlib

open Finset in
theorem impares (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, ih]
    ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"1 + 3 + 5 + ⋯ = n²","etiqueta":"∑ · sum_range_succ · ring","idea":"`sum_range_succ` separa el último término de la suma: lo que queda es la suma hasta *k*, y de esa habla la hipótesis de inducción.","notas":{"2":"Base: la suma de ningún término es 0, y 0² = 0.","3":"`sum_range_succ` parte la suma hasta *k* + 1 en la suma hasta *k* más el término 2*k* + 1. Con `ih`, queda *k*² + (2*k* + 1).","4":"Y *k*² + 2*k* + 1 = (*k* + 1)²."}},"archivo":"datos/trazas/11-induccion-4.json"}
```

- `range n` es el conjunto {0, 1, …, *n* − 1}, y `∑ i ∈ range n, (2 * i + 1)` suma 2*i* + 1 para esos *i*: 1 + 3 + 5 + ⋯ + (2*n* − 1).
- `sum_range_succ` es el teorema clave de estas inducciones: la suma hasta *k* + 1 es la suma hasta *k* más el último término. Es el «hacer aparecer lo de *k*» para sumas.
- `open Finset in` permite escribir `range` y `sum_range_succ` sin el prefijo `Finset.`.
- En el caso base, `simp` sabe que la suma de cero términos es 0.

::::{div}
:class: afondo
### 5 · Qué es la inducción para Lean

En Lean, la inducción no es un axioma aparte: sale de cómo están definidos los naturales.

```lean
import Mathlib

theorem cero_mas (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

#print Nat
#check @Nat.rec
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Los naturales se construyen desde el cero","etiqueta":"a fondo · with · Nat.rec","idea":"Esta es la forma más habitual de escribir una inducción: con `with` y una rama `|` para cada caso. Debajo, `#print Nat` enseña por qué hay justo dos casos.","notas":{"2":"Rama `zero`.","3":"Rama `succ`, con sus nombres puestos en la propia rama."}},"archivo":"datos/trazas/11-induccion-5.json"}
```

La forma `induction n with` seguida de `| zero => …` y `| succ k ih => …` es la que verás en casi todo el código de Lean y de Mathlib. Hace lo mismo que `induction n` con dos `case`: cada rama trabaja un caso y le pone nombres.

`#print Nat` explica por qué hay justo dos casos. `Nat` es un tipo **inductivo** con dos constructores:

- `Nat.zero : ℕ`, el cero;
- `Nat.succ : ℕ → ℕ`, el siguiente de un natural.

Todo natural es `zero`, o `succ` de otro natural: 3 es `succ (succ (succ zero))`. No hay más formas de fabricar uno.

De ahí sale el principio de inducción, que Lean genera solo al definir `Nat`. `#check @Nat.rec` lo enseña: dada una prueba para `Nat.zero`, y una forma de pasar de `n` a `n.succ`, se tiene una prueba para cualquier `t`. Es el dominó, escrito como tipo. `induction` es una táctica que prepara las dos metas y, al final, usa `Nat.rec`.

Por eso las definiciones por casos del capítulo 2, como `suma` o `fac`, tienen un caso para 0 y otro para *n* + 1: son los dos constructores. Y por eso las inducciones sobre ellas encajan tan bien: cada caso de la inducción abre un caso de la definición.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
2 · (1 + 2 + ⋯ + *n*) = *n*(*n* + 1), por inducción (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
theorem suma_formula (n : ℕ) : 2 * suma n = n * (n + 1) := by
  induction n
  case zero => rfl
  case succ k ih =>
    rw [suma, mul_add, ih]
    ring
```

```coq
(* Rocq (Coq): induction ... as [| k ih] nombra los dos casos *)
Require Import Arith.
Fixpoint suma (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => S m + suma m
  end.
Theorem suma_formula : forall n, 2 * suma n = n * (n + 1).
Proof.
  induction n as [| k ih].
  - reflexivity.
  - cbn [suma].
    rewrite Nat.mul_add_distr_l, ih.
    ring.
Qed.
```

```isabelle
(* Isabelle: induction y auto, que hace el resto *)
fun suma :: "nat => nat" where
  "suma 0 = 0"
| "suma (Suc n) = Suc n + suma n"

lemma suma_formula: "2 * suma n = n * (n + 1)"
  apply (induction n)
  apply auto
  done
```

Los tres hacen la misma inducción sobre la misma definición de los naturales: cero y siguiente (`0` y `S` en Rocq, `0` y `Suc` en Isabelle). En Rocq, `induction n as [| k ih]` da nombre a los dos casos de una vez, y en el paso el panel enseña `ih : 2 * suma k = k * (k + 1)`. Isabelle enseña las dos submetas, `2 * suma 0 = 0 * (0 + 1)` y `⋀n. 2 * suma n = n * (n + 1) ⟹ 2 * suma (Suc n) = …`, y `auto` cierra las dos sin más indicaciones: abre `suma`, usa la hipótesis y hace el álgebra.
:::

## Conexiones

- El `sorry` del capítulo 3 queda cerrado, y `#print axioms` lo confirma.
- Las definiciones por casos del capítulo 2 y la inducción son las dos caras de lo mismo: los naturales se construyen desde el cero con el siguiente.
- `case` y los nombres con cruz son los del capítulo 4.
- `sum_range_succ` volverá en las sucesiones de la parte IV, y la inducción en los capítulos 12 (divisibilidad) y 15 (congruencias).

## La grieta

Con la inducción se demuestran fórmulas para todo *n*. Pero muchas propiedades de los naturales hablan de divisores: «*n*³ − *n* es múltiplo de 6», «hay infinitos primos», «todo número se descompone en primos». ¿Cómo dice Lean «*a* divide a *b*»? ¿Y cómo se trabaja con primos? Lo vemos en **Divisibilidad y primos**.

## Ejercicios

1. **El otro cero.** Demuestra `0 * n = 0` por inducción. Te sirve `Nat.mul_succ`: *a* · (*b* + 1) = *a* · *b* + *a*.

2. **Gauss con Σ.** Demuestra `2 * ∑ i ∈ range (n + 1), i = n * (n + 1)`.

3. **Potencias de dos.** Demuestra `∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n`: 1 + 2 + 4 + ⋯ + 2*ⁿ*⁻¹ + 1 = 2*ⁿ*.

4. **El factorial no se anula.** Con `fac` del capítulo 2 (`fac 0 = 1`, `fac (n + 1) = (n + 1) * fac n`), demuestra `0 < fac n`.

5. **Sin la ficha anterior.** En la prueba de `dos_pot`, escribe `clear ih` antes de `omega`: borra la hipótesis de inducción. ¿Qué pasa?

6. **Leer el paso.** En la prueba de `impares`, ¿qué dice `ih` y cuál es la meta del caso `succ`, antes de reescribir nada?

::::{div}
:class: afondo
7. **Con ramas.** Reescribe la prueba del ejercicio 1 con `induction n with` y dos ramas `|`.

8. **El número 3.** Según `#print Nat`, ¿cómo se escribe el número 3 solo con `Nat.zero` y `Nat.succ`? ¿Qué caso de la inducción le corresponde?
::::

## Solucionario

1. ```lean
   theorem cero_por (n : ℕ) : 0 * n = 0 := by
     induction n
     case zero => rfl
     case succ k ih => rw [Nat.mul_succ, ih]
   ```
   `Nat.mul_succ` pasa 0 · (*k* + 1) a 0 · *k* + 0, `ih` cambia 0 · *k* por 0, y queda 0 + 0 = 0, que `rw` cierra con `rfl`.
2. ```lean
   open Finset in
   theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
     induction n
     case zero => simp
     case succ k ih =>
       rw [sum_range_succ, mul_add, ih]
       ring
   ```
3. ```lean
   open Finset in
   theorem geo (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n := by
     induction n
     case zero => simp
     case succ k ih =>
       rw [sum_range_succ, pow_succ]
       omega
   ```
   Tras las reescrituras, la meta es *S* + 2*ᵏ* + 1 = 2*ᵏ* · 2, con `ih` : *S* + 1 = 2*ᵏ*. `omega` trata *S* y 2*ᵏ* como desconocidas y lo ve.
4. ```lean
   theorem fac_pos (n : ℕ) : 0 < fac n := by
     induction n
     case zero => decide
     case succ k ih =>
       rw [fac]
       positivity
   ```
   `positivity` demuestra que algo es positivo mirando su forma: (*k* + 1) es positivo, y `fac k` también, por `ih`.
5. `omega` falla: *could not prove the goal*. Sin `ih`, la meta *k* + 2 ≤ 2*ᵏ* · 2 no se deduce de nada (para `omega`, 2*ᵏ* podría ser 0). La hipótesis de inducción es imprescindible.
6. `ih : ∑ i ∈ range k, (2 * i + 1) = k ^ 2`, y la meta es `∑ i ∈ range (k + 1), (2 * i + 1) = (k + 1) ^ 2`.

::::{div}
:class: afondo
7. ```lean
   theorem cero_por' (n : ℕ) : 0 * n = 0 := by
     induction n with
     | zero => rfl
     | succ k ih => rw [Nat.mul_succ, ih]
   ```
8. `Nat.succ (Nat.succ (Nat.succ Nat.zero))`. Es `succ` de algo, así que le corresponde el caso `succ`, con *k* = 2. A su vez, 2 es `succ` de 1, y 1 es `succ` de 0: la inducción baja ficha a ficha hasta el caso `zero`.
::::
