---
title: Desigualdades
subtitle: Sumar, multiplicar, elevar al cuadrado… y dejar que Lean busque la combinación
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Las igualdades son cómodas: se puede hacer lo mismo a los dos lados sin pensar. Las desigualdades no. Se pueden **sumar**: si *a* ≤ *b* y *c* ≤ *d*, entonces *a* + *c* ≤ *b* + *d*. Pero al **multiplicar** hay que mirar el signo: por un número positivo se conserva el sentido, y por uno negativo se invierte (de 2 < 3 sale −6 > −9). Y al elevar al cuadrado, depende: −3 < 2, pero 9 > 4.

Media secundaria de errores en desigualdades viene de olvidar una de estas reglas. Lean no las olvida. Y tiene tácticas que buscan solas la combinación de hipótesis que lleva a la conclusión.

## La pregunta

¿Cómo se demuestran desigualdades en Lean? ¿Qué hace `linarith` por dentro, y cuándo no basta? ¿Cómo se demuestra una desigualdad con cuadrados, como 2*xy* ≤ *x*² + *y*²?

## La idea

Lean tiene una táctica para cada tipo de desigualdad:

| Táctica | Para qué | Ejemplo |
|---|---|---|
| `linarith` | Combinaciones lineales de hipótesis: sumar, restar, multiplicar por números positivos | de *x* + *y* ≤ 5 y *x* − *y* ≤ 1, sale *x* ≤ 3 |
| `nlinarith` | Lo mismo, multiplicando además hipótesis entre sí y usando cuadrados | 2*xy* ≤ *x*² + *y*², con una pista |
| `positivity` | Que algo es positivo o no negativo, por su forma | 0 < *x*² + 1 |
| `gcongr` | Comparar dos expresiones con la misma forma pieza a pieza | *a* ≤ *b* ⇒ *a*² + 3*a* ≤ *b*² + 3*b* |

:::{important} Cómo trabaja linarith
`linarith` supone lo **contrario** de la meta y busca una contradicción: una suma de hipótesis, cada una multiplicada por un número positivo, que dé 0 < 0. Si la encuentra, la meta queda demostrada por reducción al absurdo (capítulo 8). Si no existe esa combinación **lineal**, falla, aunque la meta sea verdadera.
:::

## Construcción

### 1 · Las reglas del orden

:::{tip} Predice
Si *a* ≤ *b* y *c* ≤ 0, ¿qué relación hay entre *a* · *c* y *b* · *c*?
:::

```lean
import Mathlib

example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  linarith

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h hc

example (a b c : ℝ) (h : a ≤ b) (hc : c ≤ 0) : b * c ≤ a * c := by
  nlinarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Sumar sí, multiplicar con cuidado","etiqueta":"linarith · mul_le_mul · nlinarith","idea":"Las desigualdades se suman sin condiciones. Para multiplicar hace falta el signo: por un número ≥ 0 se conserva el sentido, por uno ≤ 0 se invierte.","notas":{"1":"Sumar dos desigualdades: `linarith` lo hace sin pistas.","2":"Multiplicar por *c* ≥ 0 conserva el sentido. El teorema lleva la condición en el nombre: *nonneg*, «no negativo».","3":"Con *c* ≤ 0, el sentido se invierte: *b* · *c* ≤ *a* · *c*. `nlinarith` multiplica `h` por `hc` y lo encuentra."}},"archivo":"datos/trazas/13-desigualdades-1.json"}
```

- Sumar desigualdades no tiene condiciones, y `linarith` lo hace solo.
- Multiplicar sí: `mul_le_mul_of_nonneg_right` dice que si *a* ≤ *b* y 0 ≤ *c*, entonces *a* · *c* ≤ *b* · *c*. Sin la hipótesis `hc`, el teorema no se puede usar, y la desigualdad podría ser falsa.
- Con *c* ≤ 0 se invierte el sentido. `nlinarith` lo encuentra multiplicando las hipótesis: (*b* − *a*) ≥ 0 por (−*c*) ≥ 0 da un producto ≥ 0, que es justo *a* · *c* − *b* · *c* ≥ 0… al revés.

### 2 · Qué hace `linarith`, y dónde no llega

```lean
import Mathlib

example (x y : ℝ) (h1 : x + y ≤ 5) (h2 : x - y ≤ 1) : x ≤ 3 := by
  linarith

example (x : ℝ) : x ≤ x ^ 2 + 1 := by
  linarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Combinaciones lineales","etiqueta":"linarith · error","espera_error":true,"idea":"`linarith` encuentra que sumando `h1` y `h2` sale 2*x* ≤ 6. En el segundo ejemplo no hay combinación lineal posible: *x*² es un producto, y para `linarith` es un número más, sin relación con *x*.","notas":{"1":"Sumando `h1` y `h2`: 2*x* ≤ 6, es decir, *x* ≤ 3.","2":"Falla: el panel del error enseña la meta negada, `x ^ 2 + 1 < x`, y que no encontró contradicción."}},"archivo":"datos/trazas/13-desigualdades-2.json"}
```

- En el primer ejemplo, `linarith` suma las dos hipótesis: (*x* + *y*) + (*x* − *y*) ≤ 5 + 1, es decir, 2*x* ≤ 6. Es lo que haríamos a mano, pero sin tener que ver qué sumar.
- En el segundo, la meta es verdadera para todo *x* (*x*² − *x* + 1 = (*x* − ½)² + ¾ > 0), pero `linarith` falla. El mensaje enseña lo que intentó: con la meta negada, `x ^ 2 + 1 < x`, no encontró ninguna contradicción.
- La razón: para `linarith`, `x ^ 2` es un número desconocido más, como si se llamara *z*. Y de *z* + 1 < *x*, sin más datos, no se deduce nada absurdo. Hace falta una táctica que sepa que los cuadrados no son negativos.

### 3 · Cuadrados: la pista que necesita `nlinarith`

La desigualdad estrella: 2*xy* ≤ *x*² + *y*², para cualesquiera *x* e *y*. En la pizarra se demuestra en una línea: (*x* − *y*)² ≥ 0, y desarrollando, *x*² − 2*xy* + *y*² ≥ 0.

```lean
import Mathlib

example (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

example (x : ℝ) : x ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (x - 1)]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El cuadrado que lo explica todo","etiqueta":"nlinarith · sq_nonneg","idea":"`sq_nonneg (x - y)` es el dato 0 ≤ (*x* − *y*)². Con él, la desigualdad es lineal: basta desarrollar el cuadrado. La pista es la idea de la demostración.","notas":{"1":"0 ≤ (*x* − *y*)² = *x*² − 2*xy* + *y*²: justo lo que se pide.","2":"0 ≤ (*x* − 1)² = *x*² − 2*x* + 1, así que *x*² + 1 ≥ 2*x*… y `nlinarith` combina lo que haga falta para llegar a *x*."}},"archivo":"datos/trazas/13-desigualdades-3.json"}
```

- Entre corchetes van las **pistas**: hechos que `nlinarith` añade a las hipótesis. `sq_nonneg (x - y)` es el teorema «un cuadrado no es negativo» aplicado a *x* − *y*: `0 ≤ (x - y) ^ 2`.
- Con esa pista, `nlinarith` desarrolla el cuadrado y la desigualdad pasa a ser lineal en *x*², *xy* e *y*². Ahí ya funciona como `linarith`.
- Sin la pista, `nlinarith` falla en 2*xy* ≤ *x*² + *y*²: prueba productos de hipótesis, pero no se le ocurre (*x* − *y*)². Elegir el cuadrado es la parte creativa de la demostración, y sigue siendo tuya.
- 2*xy* ≤ *x*² + *y*² es la desigualdad entre la media aritmética y la geométrica disfrazada: con *x* = √*a* e *y* = √*b*, dice que √(*ab*) ≤ (*a* + *b*)/2.

### 4 · Monotonía y positividad

Dos tácticas para dos situaciones muy frecuentes: comparar expresiones con la misma forma, y ver que algo es positivo.

```lean
import Mathlib

example (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 + 3 * a ≤ b ^ 2 + 3 * b := by
  gcongr

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  positivity
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Pieza a pieza","etiqueta":"gcongr · positivity","idea":"`gcongr` ve que los dos lados tienen la misma forma y compara pieza con pieza: *a*² con *b*² y 3*a* con 3*b*. `positivity` mira cómo está construida una expresión para ver su signo.","notas":{"1":"Las dos piezas salen de *a* ≤ *b*. Para *a*² ≤ *b*² hace falta además 0 ≤ *a*: `gcongr` lo busca en `ha`.","2":"Un cuadrado es ≥ 0 y 1 es > 0: la suma es > 0."}},"archivo":"datos/trazas/13-desigualdades-4.json"}
```

- `gcongr` (de *generalized congruence*) compara dos expresiones con la misma estructura. Aquí reduce la meta a *a*² ≤ *b*² y 3*a* ≤ 3*b*, y las dos salen de `h`.
- Para elevar al cuadrado hace falta que *a* ≥ 0: con *a* = −3 y *b* = 2 es falso. `gcongr` busca esa condición entre las hipótesis, y si no la encuentra, la deja como meta.
- `positivity` decide el signo de una expresión mirando sus piezas: los cuadrados son ≥ 0, las constantes positivas son > 0, la suma de algo ≥ 0 y algo > 0 es > 0, el producto de positivos es positivo…
- Ni `gcongr` ni `positivity` hacen cuentas: razonan con la **forma** de la expresión. Por eso son rápidas y predecibles.

::::{div}
:class: afondo
### 5 · La desigualdad de Bernoulli

Una desigualdad clásica que junta inducción y `nlinarith`: si *x* ≥ −1, entonces (1 + *x*)*ⁿ* ≥ 1 + *nx* para todo natural *n*. Sirve, por ejemplo, para ver que (1 + 1/*n*)*ⁿ* ≥ 2.

```lean
import Mathlib

theorem desig_bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by
  induction n
  case zero => simp
  case succ k ih =>
    push_cast
    rw [pow_succ]
    nlinarith [sq_nonneg x]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"(1 + x)ⁿ ≥ 1 + nx","etiqueta":"a fondo · inducción · nlinarith · ↑","idea":"En el paso, (1 + *x*)ᵏ⁺¹ = (1 + *x*)ᵏ · (1 + *x*) ≥ (1 + *kx*)(1 + *x*) = 1 + (*k* + 1)*x* + *kx*² ≥ 1 + (*k* + 1)*x*. Hace falta 1 + *x* ≥ 0 para multiplicar la hipótesis, y *kx*² ≥ 0 al final.","notas":{"1":"Fíjate en la flecha ↑: *n* es natural y *x* real, y para multiplicarlos Lean convierte *n* en real.","2":"Base: 1 + 0 · *x* = 1 = (1 + *x*)⁰.","3":"Compara antes y después: la flecha ya no envuelve a *k* + 1, y ahora en la meta aparece ↑*k* · *x*, lo mismo que en `ih`.","4":"(1 + *x*)ᵏ⁺¹ = (1 + *x*)ᵏ · (1 + *x*).","5":"`nlinarith` multiplica `ih` por 1 + *x* ≥ 0 (que sale de `hx`) y usa *x*² ≥ 0 para el término que sobra."}},"archivo":"datos/trazas/13-desigualdades-5.json"}
```

En el enunciado aparece algo nuevo: `1 + n * x` multiplica un natural por un real. Lean no mezcla tipos sin avisar: convierte *n* en real, y lo marca con una flecha, `↑n`. Se llama **coerción** (*cast*). En el paso, `↑(k + 1)` es la conversión de *k* + 1, y `push_cast` la reparte: ↑*k* + 1. Sin ese paso, `nlinarith` no vería la relación con `ih`.

El razonamiento del paso, a mano:

(1 + *x*)*ᵏ*⁺¹ = (1 + *x*)*ᵏ* (1 + *x*) ≥ (1 + *kx*)(1 + *x*) = 1 + (*k* + 1)*x* + *kx*² ≥ 1 + (*k* + 1)*x*.

La primera desigualdad multiplica `ih` por 1 + *x*, que es ≥ 0 gracias a `hx`: aquí se usa la hipótesis *x* ≥ −1. La segunda tira el término *kx*² ≥ 0. `nlinarith` encuentra los dos pasos: el producto de `ih` por `hx` lo prueba solo, y la pista `sq_nonneg x` le da *x*² ≥ 0.

La hipótesis *x* ≥ −1 no es un adorno: con *x* = −4 y *n* = 3, 1 + 3 · (−4) = −11, pero (1 − 4)³ = −27, y −11 ≤ −27 es falso.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
2*xy* ≤ *x*² + *y*² para *x*, *y* reales (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: nlinarith con la pista (x - y)² ≥ 0
example (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]
```

```coq
(* Rocq (Coq): nra, con la misma pista como hipótesis *)
Require Import Reals Lra Psatz.
Open Scope R_scope.
Lemma media : forall x y : R, 2 * x * y <= x ^ 2 + y ^ 2.
Proof.
  intros x y.
  assert (h : 0 <= (x - y) ^ 2) by apply pow2_ge_0.
  nra.
Qed.
```

```isabelle
(* Isabelle: el cuadrado, y simp lo desarrolla *)
lemma media: "2 * x * y <= x^2 + (y::real)^2"
proof -
  have "0 <= (x - y)^2" by simp
  then show ?thesis by (simp add: power2_diff)
qed
```

Los tres necesitan la misma idea: que (*x* − *y*)² ≥ 0. En Rocq, `nra` (*nonlinear real arithmetic*, el `nlinarith` de Rocq) falla sin ella con *No applicable tactic*, igual que `nlinarith` sin pista. En Isabelle se escribe como en la pizarra: se afirma 0 ≤ (*x* − *y*)², y `simp` con la fórmula del cuadrado de una diferencia (`power2_diff`) hace el resto. La parte mecánica la hace la máquina; la idea del cuadrado la pones tú, en los tres.
:::

## Conexiones

- `linarith` es una reducción al absurdo automática: niega la meta y busca la contradicción, como `by_contra` en el capítulo 8.
- `calc` del capítulo 10 encadena desigualdades a mano; `linarith` y `nlinarith` buscan solos la cadena cuando es una combinación de las hipótesis.
- La inducción del capítulo 11 sirve igual para desigualdades, como en Bernoulli o en *n* + 1 ≤ 2*ⁿ*.
- Las desigualdades con ε del capítulo 18 (sucesiones y límites) se demuestran con estas mismas tácticas. Y el capítulo 23 abre `linarith` por dentro.

## La grieta

`nlinarith` necesitó desarrollar (*x* − *y*)² para ver que era *x*² − 2*xy* + *y*². Detrás de esa cuenta está `ring`, que ha aparecido en casi todos los capítulos cerrando igualdades algebraicas. ¿Qué sabe exactamente `ring`? ¿Por qué funciona con los enteros y los reales pero no con la resta de los naturales? ¿Y qué hacer cuando no basta? Lo vemos en **Álgebra con `ring`**.

## Ejercicios

1. **Despejar.** Con `h : 2 * x + 1 ≤ 7` y `x : ℝ`, demuestra `x ≤ 3`.

2. **Estricta y no estricta.** Con `a ≤ b` y `c < d`, demuestra `a + c < b + d`. ¿Qué tipo de desigualdad sale al sumar una ≤ con una <?

3. **Siempre positivo.** Demuestra `0 ≤ a ^ 2 + b ^ 2` y, con `n : ℕ`, `(0 : ℝ) < 2 ^ n`. ¿Qué táctica usas?

4. **El cuadrado de la suma.** Demuestra `(x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2)` para *x*, *y* reales. ¿Qué pista le das a `nlinarith`?

5. **Pieza a pieza.** Con `h : a ≤ b` y `hc : 0 ≤ c`, demuestra `a * c + 1 ≤ b * c + 1` con una sola táctica.

6. **Sin pista.** ¿Qué pasa si escribes `nlinarith` sin corchetes para demostrar `2 * x * y ≤ x ^ 2 + y ^ 2`? ¿Y `linarith`?

::::{div}
:class: afondo
7. **El contraejemplo.** Comprueba en Lean que, con *x* = −4 y *n* = 3, la desigualdad de Bernoulli es falsa: demuestra `¬ ((1 : ℝ) + 3 * (-4) ≤ (1 + -4) ^ 3)`. ¿Qué paso de la demostración falla con *x* < −1?

8. **La desigualdad triangular.** Busca en Mathlib el teorema que dice |*a* + *b*| ≤ |*a*| + |*b*|. Pista: se llama `abs_add_le`. Úsalo para demostrarlo con *a*, *b* reales en una sola expresión.
::::

## Solucionario

1. `linarith`: de 2*x* + 1 ≤ 7 sale 2*x* ≤ 6.
2. `linarith`. Sumar una ≤ con una < da una <: el «estricto» de una basta para que la suma sea estricta.
3. `positivity` en los dos casos. Una suma de cuadrados es ≥ 0, y una potencia de un número positivo es positiva.
4. ```lean
   example (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
     nlinarith [sq_nonneg (x - y)]
   ```
   La misma pista que en la sección 3: 2(*x*² + *y*²) − (*x* + *y*)² = (*x* − *y*)².
5. `gcongr`. Compara las dos piezas que cambian, *a* · *c* con *b* · *c*, y usa `hc` para poder multiplicar.
6. Los dos fallan con *linarith failed to find a contradiction*. Sin la pista, `nlinarith` no encuentra el cuadrado (*x* − *y*)², y para `linarith` los productos son números desconocidos sin relación entre sí.

::::{div}
:class: afondo
7. `example : ¬ ((1 : ℝ) + 3 * (-4) ≤ (1 + -4) ^ 3) := by norm_num`. Con *x* < −1, 1 + *x* es negativo, y al multiplicar `ih` por 1 + *x* la desigualdad se invierte: el primer paso del razonamiento ya no vale.
8. `example (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b`. El nombre se lee: el valor absoluto (`abs`) de una suma (`add`) es menor o igual (`le`, de *less or equal*) que…
::::
