---
title: Demostrar que el fabricante funciona
subtitle: Un proyecto guiado. Lo que el libro de SageMath comprobó en doce casos, demostrado para todos
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## El proyecto

El último capítulo del libro de SageMath construyó un **fabricante de ejercicios**: elegía la solución al azar y fabricaba el enunciado hacia atrás. Para una ecuación de segundo grado con raíces *r*₁ y *r*₂, escribía *a*(*x* − *r*₁)(*x* − *r*₂) = 0. Para un sistema con solución (2, −1, 3), buscaba una matriz de determinante ±1 y calculaba los términos independientes.

Sage lo comprobaba todo: doce ecuaciones resueltas de doce, siete doctests de siete. Pero aquel capítulo terminaba con una grieta:

> Comprobar muchos casos no es **demostrar** que vale para todos.

En este proyecto cerramos esa grieta. Al final tendremos, demostrado en Lean para **cualquier** elección del fabricante:

- que la ecuación fabricada tiene justo las raíces elegidas, y ninguna más;
- que su discriminante es siempre un cuadrado perfecto;
- que los filtros del fabricante hacen lo que dicen;
- que un sistema con determinante ±1 tiene una única solución entera, y que la inversa es entera;
- y, en el A fondo, la fórmula del área entre la parábola y el eje.

Lo que hace falta ya está en el libro: `ring` (capítulo 14), «o» y casos (capítulo 7), desigualdades (capítulo 13), derivadas (capítulo 19) y `decide` (capítulo 23).

## La idea

- En Sage, cada ejercicio era un **caso**: unos números concretos que se comprobaban. En Lean, cada afirmación es un **teorema** con variables: *a*, *r*₁ y *r*₂ cualesquiera.
- Un teorema con variables vale para todos los ejercicios a la vez, los que el fabricante ya ha hecho y los que hará con cualquier semilla.
- Cada paso del proyecto tiene un **Objetivo** (qué afirmación del fabricante se demuestra) y un **Comprueba** (cómo se ve que lo demostrado encaja con lo que Sage calculó).

## Paso 1 · La ecuación tiene las raíces elegidas

**Objetivo:** demostrar que *a*(*x* − *r*₁)(*x* − *r*₂) es la ecuación *a*·*x*² + *b*·*x* + *c* con *b* = −*a*(*r*₁ + *r*₂) y *c* = *a*·*r*₁·*r*₂, y que *r*₁ y *r*₂ la anulan.

:::{tip} Predice
Para comprobar que *r*₁ es raíz hay que sustituir *x* por *r*₁. ¿Qué factor se anula?
:::

```lean
import Mathlib

theorem desarrolla (a r₁ r₂ x : ℤ) :
    a * (x - r₁) * (x - r₂) = a * x ^ 2 - a * (r₁ + r₂) * x + a * (r₁ * r₂) := by
  ring

theorem raiz_uno (a r₁ r₂ : ℤ) : a * (r₁ - r₁) * (r₁ - r₂) = 0 := by
  simp

theorem raiz_dos (a r₁ r₂ : ℤ) : a * (r₂ - r₁) * (r₂ - r₂) = 0 := by
  simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La ecuación, desde sus raíces","etiqueta":"proyecto · ring · simp","idea":"El fabricante escribe *b* = −*a*(*r*₁ + *r*₂) y *c* = *a*·*r*₁·*r*₂. `ring` demuestra que es lo mismo que desarrollar *a*(*x* − *r*₁)(*x* − *r*₂), para cualquier *a*, *r*₁, *r*₂ y *x*. Y al sustituir *x* por una raíz, un factor es cero.","notas":{"1":"Desarrollar y comparar: `ring`, para todos los valores a la vez.","2":"Con *x* = *r*₁, el factor *r*₁ − *r*₁ es 0, y `simp` lo ve: todo el producto es 0.","3":"Igual con *r*₂: el último factor es *r*₂ − *r*₂ = 0."}},"archivo":"datos/trazas/26-fabricante-1.json"}
```

- `desarrolla` es la fórmula que usaba la función `ecuacion(a, r1, r2)` del libro de Sage, demostrada de una vez para todos los enteros. Es la misma identidad que se ve en clase al «deshacer» la factorización.
- `raiz_uno` y `raiz_dos` dicen que las raíces elegidas **son** raíces. `simp` lo ve porque conoce *r* − *r* = 0 y *a* · 0 = 0.
- Todo está en ℤ, como en el fabricante: *a*, *r*₁ y *r*₂ eran enteros.

**Comprueba:** la primera ecuación de Sage, con la semilla 2026, era (1, −1, −2), de raíces 2 y −1. Con `desarrolla 1 2 (-1) x`, *b* = −1 · (2 + (−1)) = −1 y *c* = 1 · (2 · (−1)) = −2.

## Paso 2 · El discriminante es un cuadrado

**Objetivo:** demostrar que *b*² − 4*ac* = (*a*(*r*₁ − *r*₂))², y por tanto que el discriminante siempre es un cuadrado perfecto.

```lean
import Mathlib

theorem discriminante (a r₁ r₂ : ℤ) :
    (-(a * (r₁ + r₂))) ^ 2 - 4 * a * (a * (r₁ * r₂)) = (a * (r₁ - r₂)) ^ 2 := by
  ring

theorem disc_cuadrado (a r₁ r₂ : ℤ) :
    IsSquare ((-(a * (r₁ + r₂))) ^ 2 - 4 * a * (a * (r₁ * r₂))) := by
  rw [discriminante]
  exact ⟨a * (r₁ - r₂), by ring⟩

example : (3 : ℤ) ^ 2 - 4 * 3 * (-60) = 27 ^ 2 := by
  norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Siempre un cuadrado","etiqueta":"proyecto · discriminante · IsSquare","idea":"En Sage, los discriminantes salían 9, 729, 0 y 324, y se razonó en una línea que siempre es un cuadrado. Aquí ese razonamiento es un teorema: *b*² − 4*ac* = (*a*(*r*₁ − *r*₂))², para cualquier elección.","notas":{"1":"La identidad del discriminante, desarrollando los dos lados.","2":"Se cambia el discriminante por (*a*(*r*₁ − *r*₂))², usando el teorema anterior.","3":"Ser un cuadrado es «existe *r* con *x* = *r* · *r*»: el testigo es *a*(*r*₁ − *r*₂)…","4":"…y `ring` comprueba que su cuadrado es *r* · *r*.","5":"El caso de Sage (3, 3, −60): 9 + 720 = 729 = 27²."}},"archivo":"datos/trazas/26-fabricante-2.json"}
```

- `IsSquare x` es la definición de Mathlib de «*x* es un cuadrado perfecto»: existe un *r* con *x* = *r* · *r*. Se demuestra como cualquier «existe»: dando el testigo (capítulo 9).
- `rw [discriminante]` reutiliza el teorema anterior. Así se construye un proyecto: cada paso apoya en los que ya están demostrados.
- Que el discriminante sea un cuadrado es **por qué** las raíces salen enteras en la fórmula: √(*b*² − 4*ac*) = |*a*(*r*₁ − *r*₂)| es un entero.

**Comprueba:** la segunda ecuación de Sage era (3, 3, −60), de raíces 4 y −5, con discriminante 729. El teorema dice que es (3 · (4 − (−5)))² = 27² = 729, y `norm_num` lo confirma con los números.

## Paso 3 · No hay más raíces

**Objetivo:** demostrar que, si *a* ≠ 0, las únicas soluciones de *a*(*x* − *r*₁)(*x* − *r*₂) = 0 son *r*₁ y *r*₂.

```lean
import Mathlib

theorem solo_esas (a r₁ r₂ x : ℤ) (ha : a ≠ 0) :
    a * (x - r₁) * (x - r₂) = 0 ↔ x = r₁ ∨ x = r₂ := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 ha
      · left
        linarith
    · right
      linarith
  · rintro (h | h) <;> subst h <;> ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Exactamente esas dos","etiqueta":"proyecto · ↔ · mul_eq_zero · casos","idea":"Un producto es cero si y solo si lo es algún factor (`mul_eq_zero`). Como *a* ≠ 0, tiene que ser *x* − *r*₁ = 0 o *x* − *r*₂ = 0. Y al revés, si *x* es *r*₁ o *r*₂, el producto se anula.","notas":{"1":"Un «si y solo si»: dos direcciones.","2":"Primera: suponemos que el producto es 0.","3":"`a * (x - r₁) * (x - r₂)` es (*a*(*x* − *r*₁)) · (*x* − *r*₂): o el primer trozo es 0, o el segundo.","4":"Si el primer trozo es 0: o *a* = 0, o *x* − *r*₁ = 0.","5":"*a* = 0 choca con `ha : a ≠ 0`: caso imposible.","6":"Si *x* − *r*₁ = 0, elegimos el lado izquierdo del «o»…","7":"…y *x* = *r*₁ sale de `h4`.","8":"Si *x* − *r*₂ = 0, el lado derecho…","9":"…y *x* = *r*₂.","10":"Al revés: en los dos casos se sustituye *x* y el producto se anula, con una sola línea para los dos."}},"archivo":"datos/trazas/26-fabricante-3.json"}
```

- `mul_eq_zero` dice que *x* · *y* = 0 ↔ *x* = 0 ∨ *y* = 0. Es la propiedad que se usa en clase para resolver ecuaciones factorizadas, y en ℤ (y en ℝ) es un teorema de Mathlib.
- La hipótesis *a* ≠ 0 es imprescindible: si *a* = 0, todo *x* es solución. El fabricante elegía *a* entre 1, 2 y 3, así que siempre la cumple.
- La vuelta usa el capítulo 25: `rintro (h | h) <;> subst h <;> ring` trata los dos casos con la misma línea.

**Comprueba:** este teorema es lo que el A fondo de Sage comprobaba con `solve` en doce ecuaciones. Aquí vale para **todas** las que el fabricante pueda hacer.

## Paso 4 · Los filtros hacen lo que dicen

**Objetivo:** el fabricante descartaba raíces repetidas, raíces 0 y raíces opuestas. Demostrar que, con esos filtros, el ejercicio tiene dos raíces distintas, *c* ≠ 0 y *b* ≠ 0.

```lean
import Mathlib

theorem filtro_c (a r₁ r₂ : ℤ) (ha : a ≠ 0) (h1 : r₁ ≠ 0) (h2 : r₂ ≠ 0) :
    a * (r₁ * r₂) ≠ 0 := by
  exact mul_ne_zero ha (mul_ne_zero h1 h2)

theorem filtro_b (a r₁ r₂ : ℤ) (ha : a ≠ 0) (h : r₁ + r₂ ≠ 0) :
    -(a * (r₁ + r₂)) ≠ 0 := by
  exact neg_ne_zero.mpr (mul_ne_zero ha h)

theorem disc_pos (a r₁ r₂ : ℤ) (ha : a ≠ 0) (h : r₁ ≠ r₂) :
    0 < (a * (r₁ - r₂)) ^ 2 := by
  have h' : a * (r₁ - r₂) ≠ 0 := mul_ne_zero ha (sub_ne_zero.mpr h)
  positivity
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Filtros con garantía","etiqueta":"proyecto · mul_ne_zero · positivity","idea":"Si ningún factor es cero, el producto no es cero (`mul_ne_zero`). Con eso, cada filtro del fabricante se convierte en una garantía: *c* ≠ 0, *b* ≠ 0, y el discriminante positivo (dos raíces distintas).","notas":{"1":"*c* = *a*·*r*₁·*r*₂, con los tres factores distintos de 0.","2":"*b* = −*a*(*r*₁ + *r*₂): si *a* ≠ 0 y *r*₁ + *r*₂ ≠ 0, el producto no es 0, y su opuesto tampoco.","3":"*a*(*r*₁ − *r*₂) no es 0, porque *r*₁ ≠ *r*₂ significa *r*₁ − *r*₂ ≠ 0.","4":"Y el cuadrado de algo que no es cero es positivo: `positivity` usa `h'`."}},"archivo":"datos/trazas/26-fabricante-4.json"}
```

- `mul_ne_zero ha h` dice: si *a* ≠ 0 y *b* ≠ 0, entonces *a* · *b* ≠ 0. En ℤ es cierto porque no hay divisores de cero.
- `disc_pos` junta el paso 2 con el filtro de raíces distintas: el discriminante es (*a*(*r*₁ − *r*₂))², y es **estrictamente** positivo. Dos raíces distintas, como debe ser.
- `positivity` (capítulo 13) sabe que un cuadrado es positivo si la base no es cero, y busca esa hipótesis entre las que hay.

**Comprueba:** la tercera y la cuarta ecuación de Sage, (1, −6, 9) y (3, −18, 0), eran malas: raíz doble 3 (discriminante 0) y raíz 0 (*c* = 0). Son justo los casos que las hipótesis `h : r₁ ≠ r₂` y `h1 : r₁ ≠ 0` dejan fuera.

## Paso 5 · El sistema concreto

**Objetivo:** comprobar en Lean el sistema que fabricó Sage: *A* = [[1, −2, 3], [2, −3, 2], [−1, 2, −2]], con solución (2, −1, 3) y *b* = (13, 13, −10), y su inversa entera.

```lean
import Mathlib

open Matrix

def A : Matrix (Fin 3) (Fin 3) ℤ := !![1, -2, 3; 2, -3, 2; -1, 2, -2]
def B : Matrix (Fin 3) (Fin 3) ℤ := !![2, 2, 5; 2, 1, 4; 1, 0, 1]

example : A.det = 1 := by
  simp [A, Matrix.det_fin_three]

example : A * B = 1 := by
  decide

example : B * A = 1 := by
  decide

example : A *ᵥ ![2, -1, 3] = ![13, 13, -10] := by
  decide

example : B *ᵥ ![13, 13, -10] = ![2, -1, 3] := by
  decide
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La matriz de Sage, en Lean","etiqueta":"proyecto · Matrix · det · decide","idea":"*A* tiene determinante 1, y su inversa *B* = [[2, 2, 5], [2, 1, 4], [1, 0, 1]] tiene todas las entradas enteras. `decide` multiplica las matrices y lo comprueba entrada a entrada.","notas":{"1":"La fórmula del determinante 3 × 3 (`det_fin_three`), y `simp` hace las cuentas: 1.","2":"*A* · *B* es la identidad…","3":"…y *B* · *A* también: *B* es la inversa de *A*.","4":"*A* · (2, −1, 3) = (13, 13, −10): la solución elegida da los términos independientes.","5":"Y al revés: *B* · (13, 13, −10) devuelve la solución."}},"archivo":"datos/trazas/26-fabricante-5.json"}
```

- `!![…; …; …]` escribe una matriz fila a fila, y `Matrix (Fin 3) (Fin 3) ℤ` es su tipo: matrices 3 × 3 de enteros, con filas y columnas numeradas por `Fin 3` (capítulo 22).
- `*ᵥ` es «matriz por vector». La notación necesita `open Matrix`, y `![…]` escribe un vector.
- `decide` sirve porque una igualdad de matrices de enteros 3 × 3 se puede comprobar haciendo las 9 cuentas: es decidible (capítulo 23).
- En Sage, `A.inverse()` daba la misma *B*, pero en QQ: «la inversa de una matriz de ZZ siempre vive en QQ». Aquí *B* se escribe en ℤ desde el principio, y Lean comprueba que funciona.

**Comprueba:** *B* es exactamente la `A.inverse()` que escribió Sage, `[2 2 5; 2 1 4; 1 0 1]`.

## Paso 6 · Cualquier sistema con determinante ±1

**Objetivo:** demostrar que, para **cualquier** matriz 3 × 3 de enteros con determinante 1 o −1, y cualquier *b* entero, el sistema *A*·*x* = *b* tiene una única solución entera.

```lean
import Mathlib

open Matrix

theorem unica (A : Matrix (Fin 3) (Fin 3) ℤ) (h : A.det = 1 ∨ A.det = -1)
    (b : Fin 3 → ℤ) : ∃! x, A *ᵥ x = b := by
  have hu : IsUnit A.det := by
    rcases h with h | h <;> rw [h] <;> simp
  refine ⟨A⁻¹ *ᵥ b, ?_, ?_⟩
  · show A *ᵥ (A⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · intro y hy
    rw [← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Determinante ±1, solución entera","etiqueta":"proyecto · IsUnit · ∃! · A⁻¹","idea":"En los enteros, 1 y −1 son los únicos números con inverso: son las **unidades**. Si el determinante es una unidad, la inversa de *A* existe dentro de ℤ, y *x* = *A*⁻¹·*b* es la solución, entera y única.","notas":{"1":"Primero, que el determinante es una unidad de ℤ.","2":"En los dos casos: se sustituye el determinante por 1 o por −1, y `simp` sabe que los dos son unidades.","3":"La solución propuesta es *A*⁻¹·*b*. Quedan dos metas: que es solución, y que es la única.","4":"Que es solución: se escribe la meta tal cual…","5":"…y *A*·(*A*⁻¹·*b*) = (*A*·*A*⁻¹)·*b* = I·*b* = *b*.","6":"Que es única: sea *y* otra solución, con `hy : A *ᵥ y = b`.","7":"Entonces *A*⁻¹·*b* = *A*⁻¹·(*A*·*y*) = (*A*⁻¹·*A*)·*y* = *y*."}},"archivo":"datos/trazas/26-fabricante-6.json"}
```

- `∃! x, P x` es «existe un único *x* con *P x*». Se demuestra dando el *x* y probando dos cosas: que cumple *P*, y que cualquier otro que la cumpla es igual a él.
- `IsUnit A.det` dice que el determinante tiene inverso **en ℤ**. Solo 1 y −1 lo tienen; un determinante 2, por ejemplo, daría una inversa con mitades. Esta es la razón de fondo del fabricante: con det ±1, Cramer y Gauss no dan fracciones.
- `A⁻¹` es la inversa de Mathlib. Para matrices cuyo determinante no es una unidad, Mathlib la define como 0, por convenio; por eso los teoremas `mul_nonsing_inv` y `nonsing_inv_mul` piden la hipótesis `hu`.
- La cuenta es la de clase, con la asociatividad del producto de matrices (`mulVec_mulVec`): *A*(*A*⁻¹*b*) = (*AA*⁻¹)*b*.

**Comprueba:** el teorema vale para la *A* del paso 5, y también para la matriz de `random_matrix(ZZ, 3, algorithm='unimodular')` del libro de Sage, `[1 -1 -1; 1 0 -3; -1 3 -2]` (reto 4).

::::{div}
:class: afondo
## A fondo · El área entre la parábola y el eje

El fabricante de Sage también hacía ejercicios de áreas: el área entre *y* = *a*(*x* − *r*₁)(*x* − *r*₂) y el eje, de *r*₁ a *r*₂, es |*a*|·*d*³/6, con *d* = *r*₂ − *r*₁. Lo comprobaba con `integrate` (Maxima) en un caso. Aquí lo demostramos con la regla de Barrow, para cualquier parábola.

```lean
import Mathlib

theorem area (a r s : ℝ) :
    ∫ x in r..s, a * (x - r) * (x - s) = -(a * (s - r) ^ 3 / 6) := by
  have h : ∀ x ∈ Set.uIcc r s,
      HasDerivAt (fun x => a * (x ^ 3 / 3 - (r + s) * x ^ 2 / 2 + r * s * x))
        (a * (x - r) * (x - s)) x := by
    rintro x -
    have h3 := hasDerivAt_pow 3 x
    have h2 := hasDerivAt_pow 2 x
    have h1 := hasDerivAt_id' x
    have := (((h3.div_const 3).sub ((h2.const_mul (r + s)).div_const 2)).add
      (h1.const_mul (r * s))).const_mul a
    convert this using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

example : ∫ x in (1 : ℝ)..4, 2 * (x - 1) * (x - 4) = -9 := by
  rw [area]
  norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Barrow, para cualquier parábola","etiqueta":"a fondo · integral · HasDerivAt · Barrow","idea":"Una primitiva de *a*(*x* − *r*)(*x* − *s*) es *F*(*x*) = *a*(*x*³/3 − (*r* + *s*)*x*²/2 + *rs*·*x*). Por Barrow, la integral es *F*(*s*) − *F*(*r*), y `ring` comprueba que eso es −*a*(*s* − *r*)³/6.","notas":{"1":"Primero, que *F*′ = *f* en todo el intervalo.","2":"Un *x* cualquiera del intervalo (el guion descarta la hipótesis de que está en él, que no hace falta).","3":"La derivada de *x*³…","4":"…la de *x*²…","5":"…y la de *x*.","6":"Se combinan con las reglas de la suma, la resta, el producto por constantes y la división por constantes (capítulo 19).","7":"La derivada que salió y la que queremos son la misma función, escrita distinto…","8":"…(se arreglan las flechas ↑ de los exponentes)…","9":"…y `ring` lo comprueba.","10":"Barrow: la integral es *F*(*s*) − *F*(*r*), si *F*′ = *f* y *f* es integrable.","11":"Para la integrabilidad basta que *f* sea continua…","12":"…y `fun_prop` comprueba que lo es.","13":"Queda *F*(*s*) − *F*(*r*) = −*a*(*s* − *r*)³/6, que es pura álgebra.","14":"El caso de Sage: *a* = 2, raíces 1 y 4.","15":"−2 · 3³/6 = −9."}},"archivo":"datos/trazas/26-fabricante-7.json"}
```

La prueba sigue el camino de clase: buscar una primitiva, comprobar que lo es, y aplicar la regla de Barrow.

- La primitiva *F* se deriva término a término con las reglas del capítulo 19 (`hasDerivAt_pow`, `.div_const`, `.sub`, `.add`, `.const_mul`). `convert … using 1` deja como meta que las dos derivadas, la obtenida y la deseada, son iguales; tras `push_cast`, que arregla los exponentes, es una identidad que cierra `ring`.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` es la regla de Barrow de Mathlib: si *F*′ = *f* en el intervalo y *f* es integrable, ∫ₐᵇ *f* = *F*(*b*) − *F*(*a*). La integrabilidad sale de la continuidad (`fun_prop`).
- El resultado es negativo cuando *a* > 0: entre las raíces, la parábola está por debajo del eje. Por eso Sage escribía `integrate(...)` = −9 y el área era 9. El área es el valor absoluto, |*a*|·*d*³/6.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
La identidad del discriminante del fabricante, *b*² − 4*ac* = (*a*(*r*₁ − *r*₂))², en los tres sistemas (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
theorem discriminante (a r₁ r₂ : ℤ) :
    (-(a * (r₁ + r₂))) ^ 2 - 4 * a * (a * (r₁ * r₂)) = (a * (r₁ - r₂)) ^ 2 := by
  ring
```

```coq
(* Rocq (Coq) *)
Require Import ZArith.
Open Scope Z_scope.
Lemma disc (a r1 r2 : Z) :
  (-(a * (r1 + r2)))^2 - 4 * a * (a * (r1 * r2)) = (a * (r1 - r2))^2.
Proof. ring. Qed.
```

```isabelle
(* Isabelle *)
lemma disc: "(-(a * (r1 + r2)))^2 - 4 * a * (a * (r1 * r2)) = (a * (r1 - r2))^2"
  for a r1 r2 :: int
  by algebra
```

Los tres demuestran la identidad con una sola táctica de álgebra (`ring`, `ring`, `algebra`), porque es una igualdad de polinomios: se desarrollan los dos lados y se comparan. Es el corazón del fabricante, y en los tres sistemas vale para todos los enteros a la vez.
:::

## Conexiones

- El libro de SageMath (capítulo 27) construyó el fabricante; este proyecto demuestra que hace lo que promete.
- `ring` (capítulo 14) para las identidades; «o» y casos (capítulo 7) para «no hay más raíces»; `positivity` (capítulo 13) para el discriminante positivo.
- `Fin 3` como índices de las matrices viene del capítulo 22, y `decide` para comprobarlas, del 23.
- Las derivadas y `fun_prop` del A fondo son las del capítulo 19.
- `<;>` en una línea para varios casos es el capítulo 25 en acción.

## La grieta

El fabricante está demostrado. Queda el otro proyecto del libro de SageMath: **RSA de juguete para el aula**. Allí, con *n* = 61 · 53, *e* = 17 y *d* = 2753, el mensaje 65 se cifraba en 2790 y se descifraba de vuelta en 65. Sage lo comprobó con unos cuantos mensajes. ¿Por qué descifrar devuelve **siempre** el mensaje original? La respuesta es el teorema de Euler, y es el último proyecto: **RSA demostrado**.

## Retos

1. **Otra ecuación.** Demuestra con `ring` que 2(*x* − 3)(*x* + 5) = 2*x*² + 4*x* − 30.

2. **El discriminante de un caso.** Con *a* = 3, *r*₁ = 4 y *r*₂ = −5, calcula *b*² − 4*ac* con `norm_num`. ¿Qué cuadrado sale?

3. **La raíz doble.** Demuestra que, si *r*₁ = *r*₂ = *r*, el discriminante es 0.

4. **La matriz unimodular de Sage.** Demuestra que *U* = [[1, −1, −1], [1, 0, −3], [−1, 3, −2]] tiene determinante 1.

5. **Una columna de la inversa.** Con *B* del paso 5, demuestra que *B*·(1, 0, 0) = (2, 2, 1). ¿Qué sistema resuelve ese vector?

6. **Otra área.** Usa el teorema `area` para calcular ∫₋₁¹ 3(*x* + 1)(*x* − 1) d*x*. ¿Cuál es el área?

::::{div}
:class: afondo
7. **Sistemas 2 × 2.** Adapta `unica` a matrices 2 × 2 de enteros.

8. **Áreas enteras.** El fabricante buscaba *a* y *d* con *a*·*d*³ múltiplo de 6. Demuestra que, en ese caso, *a*·*d*³/6 (en ℝ) es un entero.
::::

## Solucionario

1. `example (x : ℤ) : 2 * (x - 3) * (x + 5) = 2 * x ^ 2 + 4 * x - 30 := by ring`.
2. `example : (-(3 * ((4 : ℤ) + -5))) ^ 2 - 4 * 3 * (3 * (4 * -5)) = 729 := by norm_num`. Sale 729 = 27², y 27 = 3 · (4 − (−5)).
3. `example (a r : ℤ) : (-(a * (r + r))) ^ 2 - 4 * a * (a * (r * r)) = 0 := by ring`. Con raíz doble, *a*(*r*₁ − *r*₂) = 0.
4. Como en el paso 5:
   ```lean
   def U : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, -1; 1, 0, -3; -1, 3, -2]
   example : U.det = 1 := by simp [U, Matrix.det_fin_three]
   ```
5. `example : B *ᵥ ![1, 0, 0] = ![2, 2, 1] := by decide`. Es la solución de *A*·*x* = (1, 0, 0): la primera columna de la inversa.
6. `area 3 (-1) 1` da −(3 · 2³/6) = −4. El área es 4.
7. La misma prueba, cambiando `Fin 3` por `Fin 2`:
   ```lean
   theorem unica2 (A : Matrix (Fin 2) (Fin 2) ℤ) (h : A.det = 1 ∨ A.det = -1)
       (b : Fin 2 → ℤ) : ∃! x, A *ᵥ x = b := by
     have hu : IsUnit A.det := by
       rcases h with h | h <;> rw [h] <;> simp
     refine ⟨A⁻¹ *ᵥ b, ?_, ?_⟩
     · show A *ᵥ (A⁻¹ *ᵥ b) = b
       rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
     · intro y hy
       rw [← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
   ```
   (Con `simp [Matrix.mulVec_mulVec, …]` en lugar del `show` y el `rw`, en 2 × 2 no funciona: `simp` despliega el producto en sus cuatro entradas y se pierde.)

::::{div}
:class: afondo
8. Si 6 ∣ *a*·*d*³, hay un *k* con *a*·*d*³ = 6*k*, y el área es *k*:
   ```lean
   example (a d : ℤ) (h : 6 ∣ a * d ^ 3) : ∃ k : ℤ, (a * d ^ 3 / 6 : ℝ) = k := by
     obtain ⟨k, hk⟩ := h
     refine ⟨k, ?_⟩
     have : (a : ℝ) * d ^ 3 = 6 * k := by exact_mod_cast hk
     rw [this]
     ring
   ```
::::
