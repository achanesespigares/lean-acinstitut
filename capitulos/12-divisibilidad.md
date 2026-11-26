---
title: Divisibilidad y primos
subtitle: «a divide a b» es un «existe», y los primos son infinitos
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

La aritmética de los naturales gira en torno a una pregunta: ¿quién divide a quién? 3 divide a 12, 7 divide a 91, 5 no divide a 12. Con esa pregunta se definen los múltiplos, el máximo común divisor y los **primos**, los números que solo dividen 1 y ellos mismos.

En el instituto, «3 divide a 12» se comprueba haciendo la división. Para demostrar cosas generales, como «si 3 divide a *a* y a *b*, divide a *a* + *b*», hace falta otra forma de verlo: 3 divide a 12 porque **existe** un número, 4, tal que 12 = 3 · 4.

## La pregunta

¿Cómo escribe Lean «*a* divide a *b*»? ¿Cómo se demuestra y cómo se usa? ¿Qué sabe Mathlib de primos? ¿Y se puede escribir en Lean la demostración de Euclides de que hay infinitos primos?

## La idea

`a ∣ b` se lee «*a* divide a *b*», y por dentro es un «existe»: **existe *c* tal que *b* = *a* · *c***. Así que se trata con las herramientas del capítulo 9:

- Para **demostrar** `a ∣ b`, se da el cociente con `use c`, y queda comprobar `b = a * c`.
- Para **usar** `h : a ∣ b`, se saca el cociente con `obtain ⟨c, hc⟩ := h`, y queda `hc : b = a * c`.

:::{important} La barra de dividir no es la del teclado
El símbolo `∣` de «divide» no es la barra vertical `|` del teclado: es otro carácter, que se escribe `\|` o `\mid`. Si escribes `3 | 12` con la barra normal, Lean no lo entiende.
:::

Mathlib tiene, además, los teoremas de siempre con nombre: `dvd_add` (si *a* divide a *b* y a *c*, divide a *b* + *c*), `dvd_mul_right` (*a* divide a *a* · *b*), `dvd_trans`… En los nombres, `dvd` es «divide», de *divides*.

## Construcción

### 1 · Qué es dividir

:::{tip} Predice
Para demostrar `3 ∣ 12` con `use`, ¿qué número hay que dar?
:::

```lean
import Mathlib

example : (3 : ℕ) ∣ 12 := by
  use 4

example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * y
  rw [hy, hx]
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Dividir es que exista un cociente","etiqueta":"∣ · use · obtain","idea":"`a ∣ b` es «existe *c* con *b* = *a* · *c*». Se demuestra dando el cociente, y se usa sacándolo con `obtain`.","notas":{"1":"Con cociente 4 queda `12 = 3 * 4`, que `use` comprueba calculando.","2":"De `a ∣ b` sale un cociente: `hx : b = a * x`.","3":"De `b ∣ c`, otro: `hy : c = b * y`.","4":"El cociente de *c* entre *a* será *x* · *y*.","5":"Cambiamos *c* y luego *b* por lo que valen.","6":"(*a* · *x*) · *y* = *a* · (*x* · *y*): asociativa."}},"archivo":"datos/trazas/12-divisibilidad-1.json"}
```

- `(3 : ℕ) ∣ 12` lleva la anotación de tipo porque `∣` vale para muchos tipos de números, y hay que decir de cuáles se habla.
- Tras `obtain ⟨x, hx⟩ := h1`, el panel enseña `hx : b = a * x`. El orden importa: Mathlib escribe el divisor delante, *a* · *x*.
- La transitividad de la divisibilidad (si *a* ∣ *b* y *b* ∣ *c*, entonces *a* ∣ *c*) sale multiplicando los cocientes: *c* = *b* · *y* = *a* · (*x* · *y*).

### 2 · Propiedades con nombre

Con `obtain`, `use` y `ring` se demuestra cualquier propiedad de la divisibilidad. Pero las más usadas ya están en Mathlib, y se encadenan como piezas.

```lean
import Mathlib

example (a b : ℕ) (ha : 3 ∣ a) (hb : 3 ∣ b) : 3 ∣ a + 2 * b := by
  apply dvd_add ha
  exact dvd_mul_of_dvd_right hb 2
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Si divide a los dos sumandos, divide a la suma","etiqueta":"dvd_add · dvd_mul_of_dvd_right","idea":"`dvd_add` parte «3 divide a una suma» en «3 divide a cada sumando». El primero es `ha`; el segundo, `2 * b`, sale de `hb`.","notas":{"1":"`dvd_add ha` necesita una prueba más, la de que 3 divide a `2 * b`: esa queda como meta.","2":"Si 3 divide a *b*, divide a 2 · *b*: es `dvd_mul_of_dvd_right hb 2`."}},"archivo":"datos/trazas/12-divisibilidad-2.json"}
```

- `dvd_add : a ∣ b → a ∣ c → a ∣ b + c`. Con `apply dvd_add ha`, el primer sumando queda resuelto con `ha`, y la meta pasa a ser el segundo.
- `dvd_mul_of_dvd_right hb 2` dice que, si 3 ∣ *b*, entonces 3 ∣ 2 · *b*. El nombre se lee: «divide al producto, porque divide al factor de la derecha».
- Los nombres de Mathlib son largos pero se pueden adivinar. Y si no, `exact?` busca un teorema que cierre la meta: lo vemos en el capítulo 20.

### 3 · Inducción y divisibilidad

¿Es *n*³ + 2*n* siempre múltiplo de 3? Para *n* = 1, 3; para *n* = 2, 12; para *n* = 3, 33. Por inducción, para todos.

```lean
import Mathlib

theorem tres_divide (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  induction n
  case zero => simp
  case succ k ih =>
    have h : (k + 1) ^ 3 + 2 * (k + 1) = (k ^ 3 + 2 * k) + 3 * (k ^ 2 + k + 1) := by ring
    rw [h]
    exact dvd_add ih (dvd_mul_right 3 _)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"n³ + 2n es múltiplo de 3","etiqueta":"induction · have · dvd_add","idea":"En el paso, se escribe la expresión para *k* + 1 como la de *k* más un múltiplo de 3. La de *k* la cubre `ih`, y el resto es múltiplo de 3 a la vista.","notas":{"2":"Base: 0³ + 2 · 0 = 0, y 3 divide a 0.","3":"La clave: (*k* + 1)³ + 2(*k* + 1) es lo de *k* más 3(*k*² + *k* + 1). `have` lo apunta…","4":"…y `ring` lo comprueba.","5":"Cambiamos la meta por esa forma.","6":"3 divide a lo de *k* (`ih`) y a 3 · (lo que sea) (`dvd_mul_right`): divide a la suma."}},"archivo":"datos/trazas/12-divisibilidad-3.json"}
```

- El caso base sale con `simp`: 0³ + 2 · 0 = 0, y todo número divide a 0.
- El paso es el «hacer aparecer lo de *k*» del capítulo 11, aquí con álgebra: (*k* + 1)³ + 2(*k* + 1) = (*k*³ + 2*k*) + 3(*k*² + *k* + 1). Se apunta con `have` y se comprueba con `ring`.
- Con esa forma, `dvd_add ih (dvd_mul_right 3 _)` cierra: 3 divide al primer sumando por `ih`, y al segundo porque es 3 por algo. El guion bajo deja que Lean rellene ese «algo».

### 4 · Primos

```lean
import Mathlib

example : Nat.Prime 97 := by norm_num
example : ¬ Nat.Prime 91 := by norm_num

#eval Nat.primeFactorsList 360
#eval Nat.gcd 84 120
#check Nat.prime_def
#check Nat.exists_infinite_primes
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que Mathlib sabe de primos","etiqueta":"Nat.Prime · norm_num · factores","idea":"`norm_num` decide si un número concreto es primo. Mathlib sabe descomponer en factores, calcular el máximo común divisor y que hay infinitos primos.","notas":{"1":"97 es primo: `norm_num` prueba los divisores posibles.","2":"91 = 7 · 13 no lo es."}},"archivo":"datos/trazas/12-divisibilidad-4.json"}
```

- `Nat.Prime 97` se demuestra con `norm_num`, que comprueba que no tiene divisores entre 2 y 97. Con `¬ Nat.Prime 91`, encuentra el 7.
- `#eval Nat.primeFactorsList 360` da `[2, 2, 2, 3, 3, 5]`: 360 = 2³ · 3² · 5. `#eval Nat.gcd 84 120` da `12`, el máximo común divisor.
- `Nat.prime_def` es la definición del instituto: *p* es primo si *p* ≥ 2 y sus únicos divisores son 1 y *p*.
- `Nat.exists_infinite_primes` es el teorema de Euclides: para todo *n*, existe un primo *p* ≥ *n*. Dicho de otra forma, no hay un primo que sea el último.

::::{div}
:class: afondo
### 5 · La demostración de Euclides

Euclides demostró hace más de 2300 años que hay infinitos primos. La idea, en versión moderna: dado *n*, el número *n*! + 1 tiene algún factor primo *p*. Si *p* fuera ≤ *n*, dividiría a *n*! (que es 1 · 2 ⋯ *n*) y a *n*! + 1, y por tanto a la diferencia, 1. Imposible. Así que *p* > *n*.

```lean
import Mathlib

theorem infinitos (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  set p := (n.factorial + 1).minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by have := Nat.factorial_pos n; omega)
  refine ⟨p, ?_, hp⟩
  by_contra h
  push Not at h
  have h1 : p ∣ n.factorial := Nat.dvd_factorial hp.pos h.le
  have h2 : p ∣ n.factorial + 1 := Nat.minFac_dvd _
  have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"No hay un primo que sea el último","etiqueta":"a fondo · Euclides · minFac · by_contra","idea":"*p* es el menor factor primo de *n*! + 1. Si fuera *p* < *n*, dividiría a *n*! y a *n*! + 1, y por tanto a 1: absurdo.","notas":{"1":"`set` da nombre a *p*, el menor divisor de *n*! + 1 distinto de 1 (`minFac`).","2":"*p* es primo, porque *n*! + 1 ≠ 1. Esa condición se demuestra dentro del paréntesis…","3":"…con *n*! > 0…","4":"…y `omega`.","5":"Proponemos *p* como el primo buscado; ya sabemos que es primo, falta *n* ≤ *p*.","6":"Reducción al absurdo: supongamos que no.","7":"Es decir, *p* < *n*.","8":"Entonces *p* divide a *n*! = 1 · 2 ⋯ *n*, porque es uno de los factores.","9":"Y *p* divide a *n*! + 1, porque es su menor divisor.","10":"Si divide a *n*! y a *n*! + 1, divide a 1.","11":"Pero un primo es mayor que 1, y solo 1 divide a 1: contradicción."}},"archivo":"datos/trazas/12-divisibilidad-5.json"}
```

Cada línea de la prueba es una frase del razonamiento de Euclides:

- `set p := …` pone nombre al primo candidato: `minFac` es el menor divisor de un número distinto de 1 (*min factor*). El menor divisor de un número mayor que 1 siempre es primo: es `Nat.minFac_prime`.
- `refine ⟨p, ?_, hp⟩` propone *p* como testigo del «existe» y deja como meta lo que falta, `n ≤ p`. Es un `use` que deja huecos (`?_`) a propósito.
- `by_contra` y `push Not` convierten la meta en una reducción al absurdo con `h : p < n`.
- `Nat.dvd_factorial`: un número entre 1 y *n* divide a *n*!. `Nat.dvd_add_right`: si *p* divide a *a*, entonces *p* divide a *a* + *b* exactamente cuando divide a *b*. Con *b* = 1, sale `p ∣ 1`.
- `hp.one_lt` dice que *p* > 1, y `Nat.dvd_one` que solo 1 divide a 1. Juntos dan la contradicción.

Mathlib demuestra `Nat.exists_infinite_primes` justo así. La prueba de 2300 años cabe en diez líneas, y Lean comprueba cada una.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Si *a* divide a *b* y *b* divide a *c*, entonces *a* divide a *c* (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: a ∣ b es ∃ c, b = a * c
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * y
  rw [hy, hx]
  ring
```

```coq
(* Rocq (Coq): Nat.divide a b es exists z, b = z * a *)
Require Import Arith.
Theorem divide_trans : forall a b c : nat,
  Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof.
  intros a b c [x hx] [y hy].
  exists (y * x).
  rewrite hy, hx.
  ring.
Qed.
```

```isabelle
(* Isabelle: dvdE para usar, dvdI para demostrar *)
lemma "(a::nat) dvd b ==> b dvd c ==> a dvd c"
  apply (elim dvdE)
  apply (rule_tac k = "k * ka" in dvdI)
  apply simp
  done
```

Los tres definen «divide» como un «existe», con un detalle distinto: Rocq pone el cociente **delante**, *b* = *z* · *a* (`Print Nat.divide` lo enseña: `fun x y => exists z, y = z * x`), y Lean y Mathlib lo ponen detrás, *b* = *a* · *c*. Isabelle escribe `dvd` con letras, y tras `elim dvdE` la meta es `⋀k ka. ⟦b = a * k; c = b * ka⟧ ⟹ a dvd c`: los cocientes salen como `k` y `ka`, igual que en el capítulo 9.
:::

## Conexiones

- `a ∣ b` es un «existe», y se trata con `use` y `obtain`, como en el capítulo 9. `Even n`, otro «existe», equivale a `2 ∣ n`: Mathlib lo llama `even_iff_two_dvd`.
- La inducción del capítulo 11 sirve igual para divisibilidades: se escribe lo de *k* + 1 como lo de *k* más un múltiplo evidente.
- La prueba de Euclides junta casi todo lo visto: «existe», reducción al absurdo, `push Not`, `have`.
- Los primos vuelven en el capítulo 15, con las congruencias y el pequeño teorema de Fermat, y en el proyecto final del RSA.

## La grieta

Para la inducción y la divisibilidad nos han bastado igualdades. Pero en la prueba de Euclides apareció *p* < *n*, y en el capítulo 11, *n* + 1 ≤ 2*ⁿ*. Las desigualdades tienen sus propias reglas: se pueden sumar, pero no siempre multiplicar; elevar al cuadrado conserva el orden solo si los números son positivos… ¿Cómo las maneja Lean, y qué tácticas hay para ellas? Lo vemos en **Desigualdades**.

## Ejercicios

1. **Un cociente.** Demuestra `(7 : ℕ) ∣ 91`.

2. **Múltiplo de un múltiplo.** Con `h : a ∣ b`, demuestra `a ∣ b * c` con `obtain` y `use`.

3. **Combinar.** Con `ha : 5 ∣ a` y `hb : 5 ∣ b`, demuestra `5 ∣ 3 * a + b` en una sola expresión, sin tácticas.

4. **Siempre par.** Demuestra por inducción que `2 ∣ n ^ 2 + n`.

5. **¿Primo o no?** Demuestra que 101 es primo y que 221 no lo es. ¿Cuáles son los factores de 221?

6. **Factores y divisores.** ¿Qué da `#eval Nat.primeFactorsList 1001`? ¿Y `#eval Nat.gcd 1001 143`?

::::{div}
:class: afondo
7. **El 1 no es primo.** ¿Sabe `norm_num` que 1 no es primo? ¿Y 0? ¿Por qué no lo son, según `Nat.prime_def`?

8. **¿Por qué n! + 1?** En la prueba de Euclides, ¿qué fallaría si se tomara el menor factor primo de *n*! en lugar del de *n*! + 1?
::::

## Solucionario

1. `use 13`: queda `91 = 7 * 13`.
2. ```lean
   example (a b c : ℕ) (h : a ∣ b) : a ∣ b * c := by
     obtain ⟨x, hx⟩ := h
     use x * c
     rw [hx]
     ring
   ```
3. `dvd_add (dvd_mul_of_dvd_right ha 3) hb`.
4. ```lean
   theorem dos_divide (n : ℕ) : 2 ∣ n ^ 2 + n := by
     induction n
     case zero => simp
     case succ k ih =>
       have h : (k + 1) ^ 2 + (k + 1) = (k ^ 2 + k) + 2 * (k + 1) := by ring
       rw [h]
       exact dvd_add ih (dvd_mul_right 2 _)
   ```
   *n*² + *n* = *n*(*n* + 1), el producto de dos consecutivos: el capítulo 7 lo demostró por casos.
5. `example : Nat.Prime 101 := by norm_num` y `example : ¬ Nat.Prime 221 := by norm_num`. 221 = 13 · 17.
6. `[7, 11, 13]`: 1001 = 7 · 11 · 13. Y `143`, porque 143 = 11 · 13 divide a 1001.

::::{div}
:class: afondo
7. Sí: `norm_num` demuestra `¬ Nat.Prime 1` y `¬ Nat.Prime 0`. Según `Nat.prime_def`, un primo tiene que ser al menos 2. El 1 queda fuera a propósito: si contara como primo, la descomposición en factores primos no sería única (6 = 2 · 3 = 1 · 2 · 3 = …).
8. El menor factor primo de *n*! podría ser ≤ *n*: de hecho, para *n* ≥ 2, es 2. La prueba necesita un número que **ningún** primo ≤ *n* divida, y *n*! + 1 lo es: cualquier primo ≤ *n* divide a *n*!, así que deja resto 1 al dividir *n*! + 1.
::::
