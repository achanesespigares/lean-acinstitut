---
title: Congruencias y Fermat
subtitle: Contar con restos, y un teorema de 1640 en una línea
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

¿Qué día de la semana será dentro de 100 días? No hace falta contar los 100: basta con el resto de dividir entre 7. ¿En qué cifra acaba 7¹⁰⁰? Basta con mirar los restos al dividir entre 10. Las horas del reloj, los días de la semana y las cifras finales funcionan igual: solo importa el resto.

Gauss le puso nombre en 1801: *a* y *b* son **congruentes módulo *n*** si dan el mismo resto al dividir entre *n*. Se escribe *a* ≡ *b* (mód *n*). Y lo mejor es que se puede sumar, multiplicar y elevar a potencias trabajando solo con los restos.

## La pregunta

¿Cómo se escriben y se usan las congruencias en Lean? ¿Qué es contar «dentro» de los restos? ¿Y cómo se demuestra el pequeño teorema de Fermat, que cerró la grieta del capítulo anterior?

## La idea

Lean tiene dos maneras de trabajar con restos, y conviene conocer las dos:

| Forma | Qué es | Ejemplo |
|---|---|---|
| `a ≡ b [MOD n]` | Una afirmación sobre naturales: `a % n = b % n` | `17 ≡ 2 [MOD 5]` |
| `a ≡ b [ZMOD n]` | Lo mismo con enteros | `-3 ≡ 4 [ZMOD 7]` |
| `ZMod n` | Un tipo nuevo: los *n* restos, con su suma y su producto | `(3 : ZMod 5) * 2 = 1` |

:::{important} El pequeño teorema de Fermat
Si *p* es primo y *a* no es múltiplo de *p*, entonces *a*ᵖ⁻¹ ≡ 1 (mód *p*). Fermat lo enunció en 1640 sin demostrarlo; la primera prueba publicada es de Euler, en 1736. En Mathlib es un teorema más: `ZMod.pow_card_sub_one_eq_one`.
:::

## Construcción

### 1 · Congruencias

```lean
import Mathlib

example : 17 ≡ 2 [MOD 5] := by
  decide

example (a b c d n : ℕ) (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
    a + c ≡ b + d [MOD n] := by
  exact h1.add h2

example (a b c d n : ℕ) (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
    a * c ≡ b * d [MOD n] := by
  exact h1.mul h2
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Mismo resto","etiqueta":"MOD · decide · add · mul","idea":"`a ≡ b [MOD n]` es, por definición, `a % n = b % n`. Las congruencias se suman y se multiplican como igualdades: es lo que permite calcular solo con restos.","notas":{"1":"17 = 3 · 5 + 2: los dos dan resto 2 al dividir entre 5. `decide` hace la cuenta.","2":"`h1.add h2`: sumar dos congruencias del mismo módulo da otra congruencia.","3":"`h1.mul h2`: y multiplicarlas, también."}},"archivo":"datos/trazas/15-congruencias-1.json"}
```

- `a ≡ b [MOD n]` no es más que `a % n = b % n`: `#print Nat.ModEq` lo enseña tal cual, `fun n a b => a % n = b % n`.
- Con números concretos, `decide` hace la división y compara los restos.
- Las congruencias se pueden **sumar** y **multiplicar** miembro a miembro, como las igualdades. Los teoremas se llaman `Nat.ModEq.add` y `Nat.ModEq.mul`, y con el punto se escriben `h1.add h2` y `h1.mul h2`.
- Multiplicando una congruencia por sí misma *k* veces sale la de las potencias: `h.pow k`. Es la herramienta del apartado siguiente.

### 2 · Calcular solo con restos

:::{tip} Predice
4¹ = 4, 4² = 16, 4³ = 64… ¿Qué resto dan al dividir entre 3? ¿Por qué siempre el mismo?
:::

```lean
import Mathlib

example (n : ℕ) : 4 ^ n ≡ 1 [MOD 3] := by
  have h : 4 ≡ 1 [MOD 3] := by decide
  have h2 := h.pow n
  simpa using h2

example : 2 ^ 100 % 7 = 2 := by
  norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Cambiar un número por su resto","etiqueta":"pow · simpa · norm_num","idea":"Como 4 ≡ 1 (mód 3), cualquier potencia de 4 es congruente con la misma potencia de 1, que es 1. Un número se puede cambiar por su resto antes de elevar.","notas":{"1":"El punto de partida: 4 y 1 dan el mismo resto al dividir entre 3.","2":"`decide` lo comprueba: 4 % 3 = 1 = 1 % 3.","3":"Elevando los dos lados a *n*: `h2 : 4 ^ n ≡ 1 ^ n [MOD 3]`.","4":"`simpa` simplifica 1ⁿ a 1 en `h2`, y ya es la meta.","5":"2¹⁰⁰ tiene 31 cifras, pero `norm_num` calcula el resto sin despeinarse."}},"archivo":"datos/trazas/15-congruencias-2.json"}
```

- La prueba de `4 ^ n ≡ 1 [MOD 3]` es la de la pizarra: 4 ≡ 1, luego 4ⁿ ≡ 1ⁿ = 1. Vale para todo *n* a la vez, sin inducción.
- `simpa using h2` simplifica la hipótesis y la meta con `simp` y comprueba que coinciden. Aquí lo único que hace falta es que 1ⁿ = 1.
- Para un número concreto, como 2¹⁰⁰ mód 7, `norm_num` hace la cuenta. A mano se haría igual que antes: 2³ = 8 ≡ 1 (mód 7), así que 2⁹⁹ = (2³)³³ ≡ 1 y 2¹⁰⁰ ≡ 2.
- `norm_num` solo calcula potencias con exponente hasta 256. Con 2³⁴⁰ avisa (*exponent 340 exceeds the threshold 256*) y deja la meta sin tocar; ahí conviene pasar a `ZMod`.

### 3 · Los restos como números: `ZMod n`

`ZMod n` es un tipo con *n* elementos, los restos 0, 1, …, *n* − 1, con su propia suma y su propio producto. En `ZMod 5`, 3 · 2 = 6 = 1. En `ZMod 7`, 4 + 5 = 9 = 2. Es contar en un reloj de *n* horas.

```lean
import Mathlib

example : (3 : ZMod 5) * 2 = 1 := by
  decide

example : (4 : ZMod 7) + 5 = 2 := by
  decide

example : (3 : ZMod 6) * 2 = 0 := by
  decide
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El reloj de n horas","etiqueta":"ZMod · decide","idea":"En `ZMod n` cada número es su resto. La suma y el producto dan la vuelta al llegar a *n*. Con *n* primo, todo lo que no es 0 tiene inverso; con *n* compuesto, no.","notas":{"1":"3 · 2 = 6, que en el reloj de 5 horas es 1: 2 es el inverso de 3.","2":"4 + 5 = 9, y 9 − 7 = 2.","3":"3 · 2 = 6 = 0 en `ZMod 6`: dos números que no son 0 multiplican 0."}},"archivo":"datos/trazas/15-congruencias-3.json"}
```

- `(3 : ZMod 5)` es el resto 3 en el reloj de 5 horas. `#eval (17 : ZMod 5)` da `2`: Lean reduce el número al escribirlo.
- En `ZMod 5`, 3 · 2 = 1: 2 es el **inverso** de 3, y dividir entre 3 es multiplicar por 2. `#eval (3 : ZMod 7)⁻¹` da `5`, porque 3 · 5 = 15 = 1 en `ZMod 7`.
- En `ZMod 6`, en cambio, 3 · 2 = 0 sin que ninguno sea 0. Ahí no se puede dividir entre 2 ni entre 3. Por eso los teoremas sobre restos piden muchas veces que el módulo sea **primo**: con *p* primo, `ZMod p` es un cuerpo, como ℚ o ℝ.
- Dentro de `ZMod n`, las congruencias se vuelven igualdades, y se puede usar `ring`, `rw` y todo lo de los capítulos anteriores.

### 4 · El pequeño teorema de Fermat

En `ZMod 7`, 3⁶ = 729 = 104 · 7 + 1 = 1. No es casualidad: en `ZMod p`, con *p* primo, *a*ᵖ⁻¹ = 1 para todo *a* ≠ 0.

```lean
import Mathlib

example : (3 : ZMod 7) ^ 6 = 1 := by
  decide

example (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) : a ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one ha

example (a : ℤ) (h : IsCoprime a 7) : a ^ 6 ≡ 1 [ZMOD 7] := by
  exact Int.ModEq.pow_card_sub_one_eq_one (by norm_num) h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"aᵖ⁻¹ = 1","etiqueta":"Fermat · ZMod · ZMOD","idea":"El caso concreto se calcula con `decide`; el general es un teorema de Mathlib. `[Fact p.Prime]` es la forma de decirle a Lean, de una vez para siempre, que *p* es primo.","notas":{"1":"Un caso: 3⁶ = 729, y 729 = 104 · 7 + 1.","2":"El teorema, para todo primo *p* y todo *a* ≠ 0 de `ZMod p`.","3":"La versión con enteros: si *a* y 7 no tienen factores comunes, *a*⁶ ≡ 1 (mód 7).","4":"`norm_num` comprueba que 7 es primo, lo que pide el teorema."}},"archivo":"datos/trazas/15-congruencias-4.json"}
```

- `[Fact p.Prime]` entre corchetes es una hipótesis especial: Lean la busca sola cada vez que un teorema la necesita. Así `ZMod.pow_card_sub_one_eq_one` sabe que *p* es primo sin que se lo pasemos.
- La versión con enteros, `Int.ModEq.pow_card_sub_one_eq_one`, pide dos cosas: que *p* sea primo (`by norm_num` lo comprueba para 7) y que *a* y *p* sean coprimos (`IsCoprime a 7`).
- Hay una versión todavía más fuerte, sin la condición *a* ≠ 0: `ZMod.pow_card` dice que *x*ᵖ = *x* para todo *x* de `ZMod p`. Es la que cierra la grieta del capítulo anterior.
- `#check @ZMod.pow_card` → `∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (x : ZMod p), x ^ p = x`.

::::{div}
:class: afondo
### 5 · Cerrar la grieta: (*a* + *b*)⁵ = *a*⁵ + *b*⁵

En el capítulo 14, `ring` no pudo con (*a* + *b*)⁵ = *a*⁵ + *b*⁵ en `ZMod 5`: dejaba los coeficientes 5 y 10, que ahí valen 0. Con Fermat sale en una línea: los tres términos son de la forma *x*⁵, y *x*⁵ = *x*.

```lean
import Mathlib

example (a b : ZMod 5) : (a + b) ^ 5 = a ^ 5 + b ^ 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El sueño del estudiante, módulo p","etiqueta":"a fondo · Fact · pow_card","idea":"En `ZMod 5`, *x*⁵ = *x* para todo *x*. Aplicado tres veces, la meta queda *a* + *b* = *a* + *b*. Es el «sueño del estudiante» (*a* + *b*)ᵖ = *a*ᵖ + *b*ᵖ, que solo es cierto módulo un primo.","notas":{"1":"Primero, que 5 es primo, en la forma que piden los teoremas de `ZMod`: un `Fact`.","2":"`norm_num` lo comprueba.","3":"Tres veces *x*⁵ = *x*: (*a* + *b*)⁵ pasa a *a* + *b*, *a*⁵ a *a* y *b*⁵ a *b*. Queda *a* + *b* = *a* + *b*, y `rw` la cierra."}},"archivo":"datos/trazas/15-congruencias-5.json"}
```

`have : Fact (Nat.Prime 5) := ⟨by norm_num⟩` mete en el contexto el hecho de que 5 es primo, con el envoltorio `Fact` que buscan los teoremas de `ZMod`. A partir de ahí, `ZMod.pow_card` se puede usar con *p* = 5.

El primer `rw` reescribe la primera quinta potencia que encuentra, (*a* + *b*)⁵, como *a* + *b*; los otros dos, *a*⁵ y *b*⁵. La meta queda *a* + *b* = *a* + *b*, y `rw` la cierra con `rfl`.

Hay otra prueba, a lo bruto: `∀ a b : ZMod 5, (a + b) ^ 5 = a ^ 5 + b ^ 5` sale con `decide`, que prueba las 25 parejas. Funciona para 5, pero no dice por qué es cierto, ni vale para todo primo. La de `pow_card` cambia 5 por 7 y sigue funcionando.

¿Y por qué es cierto en el fondo? En el desarrollo de (*a* + *b*)ᵖ, todos los coeficientes del medio, los números combinatorios C(*p*, *k*) con 0 < *k* < *p*, son múltiplos de *p* cuando *p* es primo. Para *p* = 5: 5, 10, 10, 5. Son justo los que `ring` dejó en el capítulo anterior.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
2¹⁰⁰ mód 7 = 2 (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example : 2 ^ 100 % 7 = 2 := by
  norm_num
```

```coq
(* Rocq (Coq) *)
Require Import ZArith.
Open Scope Z_scope.
Lemma resto : 2 ^ 100 mod 7 = 2.
Proof.
  reflexivity.
Qed.
```

```isabelle
(* Isabelle *)
lemma resto: "(2::nat) ^ 100 mod 7 = 2"
  by simp
```

Los tres hacen la cuenta entera: calculan 2¹⁰⁰ (31 cifras) y lo dividen entre 7. En Rocq basta con `reflexivity`, porque los enteros `Z` están en binario y la cuenta es rápida; en Isabelle, `simp` evalúa la expresión. Lean necesita `norm_num`, que además tiene un límite: con exponentes mayores que 256 no calcula y hay que pasar a `ZMod`.
:::

## Conexiones

- La división con resto viene del capítulo 1 (`7 % 2 = 1`), y la divisibilidad del 12: *a* ≡ *b* (mód *n*) equivale a *n* ∣ *a* − *b*.
- La grieta del capítulo 14 (`ring` en `ZMod 5`) se cierra aquí con `ZMod.pow_card`.
- `ZMod p` con *p* primo es un cuerpo: lo que se hizo en el capítulo 14 con `field_simp` vale también ahí.
- El proyecto del capítulo 27, RSA demostrado, se apoya en Fermat (y en su generalización, el teorema de Euler) para probar que descifrar deshace cifrar.

## La grieta

`ZMod 5` es un conjunto de cinco elementos. Los números pares, los primos, los múltiplos de 3, las soluciones de una ecuación: todo eso son conjuntos. ¿Cómo se escribe en Lean «el conjunto de los pares»? ¿Qué es un elemento, una unión, una intersección? ¿Y cómo se demuestra que dos conjuntos son iguales? Empieza la parte IV con **Conjuntos**.

## Ejercicios

1. **Restos.** Demuestra `23 ≡ 2 [MOD 7]`.

2. **Una potencia.** Demuestra `3 ^ 4 ≡ 1 [MOD 5]`. ¿Es un caso de Fermat?

3. **El inverso.** ¿Qué número *x* de `ZMod 7` cumple 3 · *x* = 1? Compruébalo con `decide`.

4. **La última cifra.** ¿En qué cifra acaba 7¹⁰⁰? Demuéstralo con `norm_num` escribiendo `7 ^ 100 % 10 = …`.

5. **La prueba del nueve.** Demuestra `10 ^ n ≡ 1 [MOD 9]` para todo *n*, como en el apartado 2. ¿Por qué explica esto que un número y la suma de sus cifras den el mismo resto al dividir entre 9?

6. **Sin primo no hay Fermat.** Comprueba con `decide` que `(5 : ZMod 6) ^ 5 ≠ 1`. ¿Qué hipótesis del teorema falla?

::::{div}
:class: afondo
7. **Un falso primo.** Comprueba que `(2 : ZMod 341) ^ 340 = 1` con `decide`, y que `¬ Nat.Prime 341` con `norm_num`. ¿Qué dice esto del recíproco de Fermat?

8. **Con 7.** Demuestra `(a + b) ^ 7 = a ^ 7 + b ^ 7` en `ZMod 7` adaptando la prueba del apartado 5.
::::

## Solucionario

1. `decide`: 23 = 3 · 7 + 2.
2. `decide`: 3⁴ = 81 = 16 · 5 + 1. Sí: es Fermat con *p* = 5 y *a* = 3, porque 3⁵⁻¹ = 3⁴.
3. *x* = 5: `example : (3 : ZMod 7) * 5 = 1 := by decide` (3 · 5 = 15 = 2 · 7 + 1). `#eval (3 : ZMod 7)⁻¹` también da `5`.
4. En 1: `example : 7 ^ 100 % 10 = 1 := by norm_num`. A mano: 7⁴ = 2401 ≡ 1 (mód 10), y 100 = 4 · 25.
5. ```lean
   example (n : ℕ) : 10 ^ n ≡ 1 [MOD 9] := by
     have h : 10 ≡ 1 [MOD 9] := by decide
     simpa using h.pow n
   ```
   Un número es Σ *cₖ* · 10ᵏ, con *cₖ* sus cifras. Como cada 10ᵏ ≡ 1, el número es congruente con Σ *cₖ*, la suma de sus cifras.
6. `example : (5 : ZMod 6) ^ 5 ≠ 1 := by decide`. Falla que el módulo sea primo: 6 = 2 · 3. (En `ZMod 6`, 5 = −1, y (−1)⁵ = −1 = 5.)

::::{div}
:class: afondo
7. Las dos salen. 341 = 11 · 31 no es primo y aun así 2³⁴⁰ ≡ 1 (mód 341): el recíproco de Fermat es falso. Que *a*ⁿ⁻¹ ≡ 1 (mód *n*) no garantiza que *n* sea primo; a estos números se les llama **pseudoprimos** (341 es el menor en base 2).
8. ```lean
   example (a b : ZMod 7) : (a + b) ^ 7 = a ^ 7 + b ^ 7 := by
     have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
     rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card]
   ```
::::
