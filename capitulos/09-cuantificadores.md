---
title: Para todo y existe
subtitle: Hablar de todos los números, o de alguno, y demostrarlo
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

«Para todo número real *x*, *x*² ≥ 0.» «Existe un número natural *n* tal que *n*² = 49.» Casi todas las afirmaciones interesantes de las matemáticas llevan una de estas dos expresiones, o las dos: los **cuantificadores**.

Ya conocemos medio ∀: en el capítulo 3, `intro n` decía «sea *n* un natural cualquiera». Falta la otra mitad, usar una hipótesis que vale para todos, y falta ∃ entero. En la pizarra se hace así:

- Para demostrar que **existe** algo, se da un ejemplo y se comprueba.
- Si **sabes** que existe algo, le pones nombre y trabajas con él: «sea *k* tal que *n* = 2*k*».

## La pregunta

¿Cómo se usa en Lean una hipótesis «para todo *x*»? ¿Cómo se demuestra que existe un número con cierta propiedad? ¿Y cómo se usa una hipótesis que dice que existe?

## La idea

Con los cuantificadores, la tabla de «demostrar / usar» queda completa:

| | Demostrar (en la meta) | Usar (en una hipótesis `h`) |
|---|---|---|
| `∀ x, P x` | `intro x`: «sea *x* cualquiera» | `h a`: el caso concreto `P a`. O `specialize h a` |
| `∃ x, P x` | `use a`: das el ejemplo *a*, y queda demostrar `P a` | `obtain ⟨x, hx⟩ := h`: un *x* con nombre, y `hx : P x` |

- `∀` se escribe `\forall` y `∃` se escribe `\exists`.
- `∀ x, P x` funciona como una implicación: es una máquina que, a cada *a*, le asigna una prueba de `P a`. Por eso se usa aplicándola, `h a`.
- `∃ x, P x` funciona como una «y»: un objeto **y** una prueba de que cumple la propiedad. Por eso se separa con `obtain ⟨x, hx⟩`, con la misma forma que en el capítulo 6.

:::{important} El objeto que da ∃ es cualquiera
Cuando separas `h : ∃ k, n = 2 * k` en `k` y `hk`, no sabes nada de `k` salvo lo que dice `hk`. No puedes elegirlo: es «un *k* que existe». En cambio, en `use a` eres tú quien elige el ejemplo.
:::

## Construcción

### 1 · Usar un «para todo»

:::{tip} Predice
`hf` dice que *f*(*x*) = 2*x* + 1 para todo *x*. ¿Qué es `hf 3`?
:::

```lean
import Mathlib

example (f : ℕ → ℕ) (hf : ∀ x, f x = 2 * x + 1) : f 3 = 7 := by
  rw [hf 3]

example (h : ∀ n : ℕ, n * 0 = 0) : 12345 * 0 = 0 := by
  specialize h 12345
  exact h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que vale para todos vale para este","etiqueta":"∀ · h a · specialize","idea":"Una hipótesis «para todo *x*» se usa dándole un valor concreto: `hf 3` es la igualdad para *x* = 3. `specialize` hace lo mismo y cambia la hipótesis por ese caso.","notas":{"1":"`hf 3` es `f 3 = 2 * 3 + 1`. `rw` cambia `f 3` por `2 * 3 + 1`, y `2 * 3 + 1 = 7` se cierra calculando.","2":"`specialize h 12345` cambia `h`, que hablaba de todos los *n*, por el caso *n* = 12345.","3":"Y es justo la meta."}},"archivo":"datos/trazas/09-cuantificadores-1.json"}
```

- `hf 3` es la prueba de `f 3 = 2 * 3 + 1`: lo que dice `hf` para *x* = 3. Se escribe igual que aplicar una función, porque un «para todo» funciona como una función.
- `rw [hf 3]` usa ese caso concreto para reescribir. También funciona `rw [hf]`: Lean busca en la meta algo de la forma `f _` y rellena el hueco solo.
- `specialize h 12345` sustituye `h` por su caso para *n* = 12345. Es útil cuando ese caso se va a usar varias veces.

### 2 · Demostrar un «existe»: dar un ejemplo

```lean
import Mathlib

example : ∃ n : ℕ, n * n = 49 := by
  use 7

example : Even 10 := by
  use 5
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Basta con un ejemplo","etiqueta":"∃ · use","idea":"Para demostrar que existe un número con una propiedad, se da uno. `use 7` propone *n* = 7, y la meta pasa a ser `7 * 7 = 49`, que `use` comprueba calculando.","notas":{"1":"Con *n* = 7 queda `7 * 7 = 49`. `use` prueba `rfl` al terminar, como `rw`, y la cierra.","2":"`Even 10` quiere decir «existe *r* tal que 10 = *r* + *r*». Con *r* = 5, `10 = 5 + 5` se cierra solo."}},"archivo":"datos/trazas/09-cuantificadores-2.json"}
```

- `use 7` propone el ejemplo. La meta `∃ n, n * n = 49` pasa a ser `7 * 7 = 49`. Como `rw`, `use` prueba `rfl` al terminar, y aquí la cierra.
- Si el ejemplo es malo, la meta queda abierta y no se puede cerrar: con `use 8`, quedaría `8 * 8 = 49`, que es falso.
- `Even 10` es un «existe» disfrazado. En Mathlib, `Even n` está definido como `∃ r, n = r + r`. Por eso se demuestra con `use`.

### 3 · Usar un «existe»: ponerle nombre

:::{tip} Predice
De `ha : Even a`, ¿qué saca `obtain ⟨x, hx⟩ := ha`?
:::

```lean
import Mathlib

example (a b : ℕ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x + y
  rw [hx, hy]
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La suma de dos pares es par","etiqueta":"∃ · obtain · use · ring","idea":"Se sacan los números que dan las hipótesis (*a* = *x* + *x*, *b* = *y* + *y*), se propone el ejemplo para la meta (*x* + *y*) y se comprueba con álgebra.","notas":{"1":"«Como *a* es par, sea *x* tal que *a* = *x* + *x*.» `ha` desaparece y entran `x` y `hx`.","2":"Lo mismo con *b*.","3":"La meta pide un *r* con *a* + *b* = *r* + *r*. Proponemos *r* = *x* + *y*.","4":"Cambiamos *a* y *b* por lo que valen.","5":"Queda una igualdad de álgebra: `ring` la comprueba."}},"archivo":"datos/trazas/09-cuantificadores-3.json"}
```

- `obtain ⟨x, hx⟩ := ha` hace lo de la pizarra: «sea *x* tal que *a* = *x* + *x*». `ha` desaparece del panel y entran `x : ℕ` y `hx : a = x + x`.
- Ahora la meta, `Even (a + b)`, pide su propio ejemplo. Con lo que sabemos, sale *x* + *y*: `use x + y`.
- Queda `a + b = x + y + (x + y)`. Con `rw [hx, hy]` y `ring`, es álgebra.
- El orden importa: primero se sacan los números de las hipótesis, y después se usan para construir el ejemplo de la meta. Al revés no se podría: antes de `obtain`, `x` e `y` no existen.

### 4 · Cuantificadores juntos

Con dos cuantificadores, el orden lo cambia todo. «Para todo *n* existe *m* mayor que *n*» es cierto: cada número tiene uno mayor. «Existe *n* mayor o igual que todos los *m*» es falso: no hay un natural que sea el más grande.

```lean
import Mathlib

example : ∀ n : ℕ, ∃ m, m > n := by
  intro n
  use n + 1
  omega

example : ¬ ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  intro ⟨n, hn⟩
  have h := hn (n + 1)
  omega

example : ¬ ∀ n : ℕ, n ≤ 10 := by
  push Not
  use 11
  norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El orden de los cuantificadores","etiqueta":"∀∃ · ¬∃∀ · push Not","idea":"Cada cuantificador se trata con su regla, de fuera hacia dentro. En el segundo ejemplo, suponer que existe el natural más grande lleva a una contradicción.","notas":{"1":"Primero el ∀: sea *n* cualquiera.","2":"El *m* depende de *n*: proponemos *n* + 1.","4":"Suponemos que existe un *n* mayor o igual que todos. `intro` lo separa: el *n* y la propiedad `hn`.","5":"`hn` vale para todo *m*: lo usamos con *m* = *n* + 1.","6":"*n* + 1 ≤ *n* es imposible.","7":"«No todos son ≤ 10» pasa a ser «alguno es > 10».","8":"Por ejemplo, 11."}},"archivo":"datos/trazas/09-cuantificadores-4.json"}
```

- En `∀ n, ∃ m, m > n`, el *m* se elige **después** de conocer *n*, así que puede depender de él: *m* = *n* + 1.
- En `∃ n, ∀ m, m ≤ n`, el *n* tendría que valer para todos los *m* a la vez. Para ver que no existe, se supone que sí (`intro ⟨n, hn⟩`, que también separa el «existe») y se usa `hn` con *m* = *n* + 1.
- `have h := hn (n + 1)` añade al panel el caso concreto con nombre, sin quitar `hn`.
- `push Not` sabe negar cuantificadores: «no es cierto que todos cumplan *P*» pasa a ser «existe alguno que no cumple *P*». Y al revés: «no existe ninguno» pasa a ser «todos cumplen lo contrario».

::::{div}
:class: afondo
### 5 · Un «existe» es una pareja

`obtain ⟨x, hx⟩` separa igual una «y» que un «existe». ¿Es casualidad?

```lean
import Mathlib

example : ∃ n : ℕ, n * n = 49 := ⟨7, rfl⟩

#check (⟨7, rfl⟩ : ∃ n : ℕ, n * n = 49)
#check @Exists.intro
#check Even
#print Even
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un testigo y su certificado","etiqueta":"a fondo · ⟨ , ⟩ · Exists.intro","idea":"Una prueba de `∃ x, P x` es una pareja: un objeto, el **testigo**, y una prueba de que cumple `P`. Se puede escribir directamente entre ángulos, como una «y».","notas":{}},"archivo":"datos/trazas/09-cuantificadores-5.json"}
```

El primer ejemplo no usa tácticas: la prueba es la pareja `⟨7, rfl⟩`. El 7 es el **testigo**, el número que existe. `rfl` es la prueba de que `7 * 7 = 49`. `#check` confirma que esa pareja es `Exists.intro 7 rfl`, una prueba de `∃ n, n * n = 49`.

`#check @Exists.intro` da su tipo completo: `∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p`. Se lee: dado un testigo `w` y una prueba de `p w`, tienes una prueba de que existe. Es la única forma de construir un «existe», y por eso solo hay una forma de usarlo: sacar el testigo y su prueba.

La diferencia con la «y» es sutil y está en el tipo de la segunda pieza. En `p ∧ q`, la segunda prueba no depende de la primera. En `∃ x, P x`, la segunda pieza es una prueba de `P x`, y su tipo depende del testigo *x*. Es un **par dependiente**, y la parte V cuenta qué significa.

`#print Even` enseña la definición: `fun {α} [Add α] a => ∃ r, a = r + r`. `Even` vale para cualquier tipo con suma, no solo para los naturales, y por dentro es un «existe».
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«La suma de dos pares es par», con par escrito como «existe *k* tal que *a* = 2*k*» (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: obtain para usar ∃, use para demostrarlo
example (a b : ℕ) (ha : ∃ k, a = 2 * k) (hb : ∃ k, b = 2 * k) :
    ∃ k, a + b = 2 * k := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x + y
  rw [hx, hy]
  ring
```

```coq
(* Rocq (Coq): los patrones [x hx] separan al introducir; exists da el testigo *)
Require Import Lia.
Theorem suma_pares : forall a b : nat,
  (exists k, a = 2 * k) -> (exists k, b = 2 * k) -> exists k, a + b = 2 * k.
Proof.
  intros a b [x hx] [y hy].
  exists (x + y).
  lia.
Qed.
```

```isabelle
(* Isabelle: exE para usar ∃, exI para demostrarlo *)
lemma "(EX k. a = 2 * k) ==> (EX k. b = 2 * k) ==> EX k. a + b = 2 * (k::nat)"
  apply (erule exE)
  apply (erule exE)
  apply (rule_tac x = "k + ka" in exI)
  apply simp
  done
```

En Rocq, `intros a b [x hx] [y hy]` separa los dos «existe» mientras introduce, y `exists (x + y)` es el `use` de Lean. Isabelle vuelve a dar nombre a las reglas: `exE` elimina el «existe» y `exI` lo introduce con el testigo que se le da. Tras los dos `exE`, Isabelle llama a los testigos `k` y `ka`, y escribe la meta como `⋀k ka. ⟦a = 2 * k; b = 2 * ka⟧ ⟹ ∃k. a + b = 2 * k`. El `⋀` es su «para todo» interno: los testigos son arbitrarios.
:::

## Conexiones

- La tabla «demostrar / usar» está completa: →, ∧, ∨, ¬, ∀ y ∃. Con ella se puede empezar cualquier demostración: la forma de la meta dice el primer paso.
- La primera prueba del libro, en el capítulo 0, usaba `obtain ⟨k, hk⟩ := h` y `use 2 * k ^ 2` sobre `Even`. Ahora se entiende cada línea.
- El «para todo» como función vuelve en la parte V, en **proposiciones como tipos**. Y el ∃ como par dependiente, en **tipos dependientes y universos**.
- Las definiciones con ∀ y ∃ anidados, como la de límite («para todo ε > 0 existe *N* tal que…»), llegan en la parte IV.

## La grieta

Ya podemos demostrar casi cualquier afirmación lógica. Pero muchas pruebas son, sobre todo, una cadena de igualdades: *a* = *b* = *c* = … = *z*. Con `rw` se hace, pero queda una lista de pasos que no se parece a la cuenta que escribiríamos en la pizarra. ¿Hay forma de escribir la cadena tal cual, con la justificación de cada paso? Lo vemos en **Igualdad y `calc`**.

## Ejercicios

1. **Un ejemplo.** Demuestra `∃ n : ℕ, n + 5 = 12`.

2. **Un caso concreto.** Con `hg : ∀ x, g x = x ^ 2` y `g : ℝ → ℝ`, demuestra `g 3 = 9`.

3. **Impar más uno.** Demuestra que, si *n* es impar, *n* + 1 es par. En Mathlib, `Odd n` es `∃ m, n = 2 * m + 1`.

4. **Dos condiciones.** Demuestra `∃ x : ℝ, x ^ 2 = 4 ∧ x < 0`.

5. **Siempre hay uno mayor.** Demuestra `∀ x : ℝ, ∃ y, y > x`.

6. **El ejemplo equivocado.** ¿Qué pasa si demuestras `∃ n : ℕ, n * n = 50` empezando por `use 7`?

::::{div}
:class: afondo
7. **No todos.** Demuestra `¬ ∀ n : ℕ, Even n` con `push Not`.

8. **Ninguno.** Demuestra `¬ ∃ n : ℕ, n + 1 = 0` con `rintro`.
::::

## Solucionario

1. `use 7`: queda `7 + 5 = 12`, que se cierra solo.
2. ```lean
   example (g : ℝ → ℝ) (hg : ∀ x, g x = x ^ 2) : g 3 = 9 := by
     rw [hg]
     norm_num
   ```
   Tras `rw [hg]`, la meta es `3 ^ 2 = 9`, y `norm_num` hace la cuenta (en ℝ, el `rfl` que prueba `rw` no basta).
3. ```lean
   example (n : ℕ) (hn : Odd n) : Even (n + 1) := by
     obtain ⟨k, hk⟩ := hn
     use k + 1
     rw [hk]
     ring
   ```
   Si *n* = 2*k* + 1, entonces *n* + 1 = (*k* + 1) + (*k* + 1). En lugar de `rw` y `ring`, también vale `omega`.
4. `use -2` y `norm_num`: tras `use`, queda `(-2) ^ 2 = 4 ∧ -2 < 0`, y `norm_num` comprueba las dos partes.
5. ```lean
   example : ∀ x : ℝ, ∃ y, y > x := by
     intro x
     use x + 1
     linarith
   ```
6. Queda la meta `7 * 7 = 50`, que es falsa, y Lean da un error: *unsolved goals*. El 50 no es un cuadrado perfecto: ningún ejemplo sirve, y la afirmación es falsa.

::::{div}
:class: afondo
7. ```lean
   example : ¬ ∀ n : ℕ, Even n := by
     push Not
     use 1
     decide
   ```
   `push Not` cambia la meta por `∃ n, Odd n`: en los naturales, «no par» se reescribe como «impar». Con *n* = 1, `decide` comprueba que 1 es impar.
8. ```lean
   example : ¬ ∃ n : ℕ, n + 1 = 0 := by
     rintro ⟨n, hn⟩
     omega
   ```
   `rintro` supone el «existe» y lo separa: `n` y `hn : n + 1 = 0`. En los naturales, *n* + 1 nunca es 0.
::::
