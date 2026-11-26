---
title: Álgebra con ring
subtitle: Desarrollar, simplificar y combinar sin equivocarse en un signo
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

`ring` ha aparecido en casi todos los capítulos: cierra la cuenta algebraica del final y nadie le pregunta nada. Cuando una prueba llega a (*k* + 1)(*k* + 2) = *k*² + 3*k* + 2, escribimos `ring` y Lean da la meta por buena.

En la pizarra, esa cuenta es donde más errores se cometen: un signo que se pierde al desarrollar, un 2 que se olvida en el doble producto, un denominador que se tacha sin mirar si es cero. `ring` no se equivoca en eso. Pero tampoco es magia: sabe hacer una cosa muy concreta, y conviene saber cuál para entender cuándo falla.

## La pregunta

¿Qué igualdades demuestra `ring`, y cuáles no? ¿Por qué falla en los naturales con una resta, o con *x*/*x* = 1? ¿Qué hacer con los denominadores? ¿Y cómo se usan las hipótesis en una cuenta algebraica?

## La idea

`ring` demuestra las igualdades que son ciertas **en cualquier anillo conmutativo**: las que salen solo de las propiedades de la suma y el producto (asociativa, conmutativa, distributiva, neutros, opuestos). Lo hace así: desarrolla los dos lados hasta una **forma normal** (un polinomio con los términos ordenados) y compara.

| Táctica | Para qué |
|---|---|
| `ring` | Identidades de anillos conmutativos: desarrollar y comparar |
| `ring_nf` | Poner los dos lados en forma normal, aunque no coincidan |
| `field_simp` | Quitar denominadores, sabiendo que no son cero |
| `linear_combination` | Igualdades que salen de las hipótesis: tantas veces esta, más tantas aquella |

:::{important} Lo que ring no sabe
`ring` no usa las hipótesis, ni sabe que *x* ≠ 0, ni conoce la resta de los naturales (que se queda en 0: capítulo 1). Si una igualdad depende de algo que no sea «ser un anillo conmutativo», `ring` falla.
:::

## Construcción

### 1 · Desarrollar y comparar

:::{tip} Predice
¿Podrá `ring` demostrar *x*/2 + *x*/2 = *x* en los reales, aunque haya una división?
:::

```lean
import Mathlib

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (x : ℝ) : x / 2 + x / 2 = x := by
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Las identidades notables, en una palabra","etiqueta":"ring","idea":"`ring` desarrolla cada lado hasta un polinomio ordenado y compara. Si salen iguales, la igualdad es cierta en cualquier anillo conmutativo.","notas":{"1":"El cuadrado de una suma: el doble producto, 2*ab*, no se olvida.","2":"Suma por diferencia: los términos cruzados, *ab* y −*ab*, se anulan.","3":"Dividir entre 2 es multiplicar por ½, que es un número: ½*x* + ½*x* = *x*."}},"archivo":"datos/trazas/14-ring-1.json"}
```

- Las tres identidades notables, y cualquier otra que salga desarrollando, se demuestran con `ring`.
- Funciona igual en ℤ, ℚ, ℝ o ℂ: no depende de los números, solo de las reglas de la suma y el producto.
- Dividir entre un número concreto tampoco le molesta: *x*/2 es *x* · ½, y ½ + ½ = 1 es una cuenta con números.
- `ring` no busca: siempre hace lo mismo, desarrollar y comparar. Por eso nunca tarda mucho ni da resultados distintos de un día para otro.

### 2 · Donde `ring` no llega

```lean
import Mathlib

example (a b : ℕ) : a + b - b = a := by
  ring

example (a b : ℕ) : a + b - b = a := by
  omega

example (x : ℝ) : x / x = 1 := by
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Dos igualdades que no son de anillo","etiqueta":"ring · error","espera_error":true,"idea":"La resta de los naturales no es la de un anillo (2 − 5 = 0), y *x*/*x* = 1 es falso si *x* = 0. Ninguna de las dos es cierta «en cualquier anillo», así que `ring` no puede.","notas":{"1":"Falla: en ℕ la resta se queda en 0, y no es la operación inversa de la suma.","2":"`omega` sí conoce la resta de los naturales.","3":"Falla, y deja la meta en forma normal: `x * x⁻¹ = 1`. Para `ring`, *x*⁻¹ es una incógnita más."}},"archivo":"datos/trazas/14-ring-2.json"}
```

- En los naturales, la resta se queda en 0 cuando no llega (capítulo 1). No es la resta de un anillo, y `ring` no la trata como tal. Para la aritmética lineal de ℕ está `omega`.
- *x*/*x* = 1 es falso si *x* = 0: en Lean, 0/0 = 0. Por eso `ring` no puede demostrarlo, y deja la meta en su forma normal, `x * x⁻¹ = 1`, con el inverso *x*⁻¹ como una letra más.
- Cuando `ring` falla, sugiere `ring_nf`: poner los dos lados en forma normal y mirar qué queda. Muchas veces eso basta para ver qué falta.

### 3 · Denominadores: `field_simp`

Para quitar denominadores hay que saber que no son cero, igual que en la pizarra. Con esas hipótesis, `field_simp` multiplica en cruz y deja una igualdad sin fracciones.

```lean
import Mathlib

example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  field_simp

example (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x + 1 / (x + 1) = (2 * x + 1) / (x * (x + 1)) := by
  field_simp
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Quitar denominadores con permiso","etiqueta":"field_simp · ring","idea":"`field_simp` busca en las hipótesis que los denominadores no son cero, multiplica en cruz y deja una igualdad de polinomios. La remata `ring`.","notas":{"1":"Con `hx : x ≠ 0`, *x*/*x* se simplifica a 1 y la meta se cierra sola.","2":"Sin fracciones: `x + 1 + x = x * 2 + 1`. Es la suma de fracciones hecha en común denominador.","3":"Y eso ya es una igualdad de anillo."}},"archivo":"datos/trazas/14-ring-3.json"}
```

- `field_simp` toma de las hipótesis que *x* ≠ 0 y *x* + 1 ≠ 0. Sin ellas no simplifica: no tacha un denominador que podría ser cero.
- Lo que deja es lo que haríamos a mano: pasar todo a común denominador y quedarnos con los numeradores, (*x* + 1) + *x* = 2*x* + 1.
- La pareja `field_simp` + `ring` resuelve casi todas las identidades con fracciones: la primera quita los denominadores y la segunda hace la cuenta.

### 4 · Usar las hipótesis: `linear_combination`

`ring` no mira las hipótesis. Pero muchas cuentas algebraicas dependen de ellas: «si *x* + *y* = 5 y *x* − *y* = 1, entonces *x* = 3». A mano, sumamos las dos ecuaciones y dividimos entre 2. Eso es justo lo que se le dice a `linear_combination`.

```lean
import Mathlib

example (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : x = 3 := by
  linear_combination (h1 + h2) / 2

example (a b : ℝ) (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (a + b) * h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Tantas veces esta ecuación, más tantas aquella","etiqueta":"linear_combination","idea":"Le damos la combinación de hipótesis; `linear_combination` la resta de la meta y comprueba con `ring` que lo que queda es 0 = 0.","notas":{"1":"(*x* + *y*) + (*x* − *y*) = 5 + 1, y entre 2: *x* = 3.","2":"Los coeficientes pueden ser expresiones: (*a* + *b*)(*a* − *b*) = *a*² − *b*²."}},"archivo":"datos/trazas/14-ring-4.json"}
```

- `linear_combination e` comprueba que «meta menos *e*» es una identidad de anillo. La idea (qué ecuaciones combinar y con qué coeficientes) la pones tú; la cuenta, `ring`.
- Los coeficientes no tienen por qué ser números. En el segundo ejemplo, multiplicar *a* = *b* por *a* + *b* da (*a* + *b*)*a* = (*a* + *b*)*b*, que desarrollado es *a*² = *b*².
- Si la combinación no es la buena, el error enseña lo que sobra. Con `linear_combination h1 + h2` (sin dividir entre 2), Lean dice *ring failed* y deja `3 - x = 0`: falta la mitad.
- Es el primo de `linarith` (capítulo 13) para igualdades: allí Lean busca la combinación; aquí se la damos, pero los coeficientes pueden ser expresiones, no solo números.

::::{div}
:class: afondo
### 5 · Qué es «un anillo» para `ring`

`ring` no trabaja con números, sino con cualquier estructura que tenga suma y producto con las propiedades de siempre. En Mathlib, eso es un `CommRing` (anillo conmutativo). Si el producto no conmuta, como con las matrices, ya no vale.

```lean
import Mathlib

example {R : Type*} [CommRing R] (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example {R : Type*} [Ring R] (a b : R) : a * b = b * a := by
  ring

example {R : Type*} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + a * b + b * a + b ^ 2 := by
  noncomm_ring

example (x : ℤ) : (x + 2) * (x - 3) = 0 := by
  ring_nf
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Anillos con y sin conmutativa","etiqueta":"a fondo · CommRing · noncomm_ring · ring_nf","espera_error":true,"idea":"`[CommRing R]` dice «*R* es cualquier anillo conmutativo». La identidad vale para todos a la vez. Sin conmutativa, (*a* + *b*)² tiene cuatro términos: *ab* y *ba* no se juntan.","notas":{"1":"Una prueba para ℤ, ℝ, los polinomios, los enteros módulo *n*… para todo anillo conmutativo.","2":"Falla: en un anillo cualquiera, *ab* y *ba* pueden ser distintos (las matrices, por ejemplo). El mensaje dice que ni siquiera la forma normal cambia la meta.","3":"`noncomm_ring` desarrolla sin conmutar: salen *ab* y *ba* por separado.","4":"`ring_nf` no demuestra nada: escribe la forma normal, `-6 - x + x ^ 2 = 0`, y la meta queda abierta."}},"archivo":"datos/trazas/14-ring-5.json"}
```

`{R : Type*} [CommRing R]` se lee: «sea *R* un tipo cualquiera que sea un anillo conmutativo». La prueba con `ring` no depende de qué *R* sea, así que vale para todos a la vez: enteros, reales, polinomios, enteros módulo *n*…

En un anillo sin conmutativa, como el de las matrices 2 × 2, (*a* + *b*)² = *a*² + *ab* + *ba* + *b*², y *ab* + *ba* no tiene por qué ser 2*ab*. `ring` lo rechaza (el mensaje habla de `ring_nf` porque, cuando `ring` no cierra la meta, intenta al menos normalizarla, y aquí ni eso la cambia); `noncomm_ring` desarrolla sin conmutar y sí lo demuestra.

`ring_nf` enseña la forma normal que usa `ring` por dentro: los términos ordenados por grado, con el número delante. Para (*x* + 2)(*x* − 3) escribe −6 − *x* + *x*². Como no es una prueba, la meta sigue abierta y Lean da el error de meta sin resolver.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
(*a* + *b*)² = *a*² + 2*ab* + *b*² en los enteros (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
```

```coq
(* Rocq (Coq) *)
Require Import ZArith.
Open Scope Z_scope.
Lemma cuadrado : forall a b : Z, (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2.
Proof.
  intros a b.
  ring.
Qed.
```

```isabelle
(* Isabelle *)
lemma cuadrado: "(a + b)^2 = a^2 + 2*a*b + (b::int)^2"
  by algebra
```

Rocq tiene la misma táctica con el mismo nombre, `ring`, y la misma limitación: en los naturales, `a + b - b = a` da *not a valid ring equation*. Isabelle lo resuelve con `algebra`, que trabaja con polinomios; también vale `by (simp add: power2_eq_square algebra_simps)`, que desarrolla el cuadrado y ordena. Los tres hacen lo mismo por dentro: forma normal y comparar.
:::

## Conexiones

- `ring` cerraba las cuentas de la inducción del capítulo 11 (la suma de Gauss) y del 12 (3 ∣ *n*³ + 2*n*).
- La resta truncada de los naturales viene del capítulo 1; `omega`, del 4.
- `linear_combination` es a las igualdades lo que `linarith` (capítulo 13) es a las desigualdades.
- El capítulo 23 abre `ring` y `omega` por dentro, y el 26 usa `ring` para el discriminante del fabricante de ecuaciones.

## La grieta

En los enteros módulo 5 (los restos de dividir entre 5), (*a* + *b*)⁵ = *a*⁵ + *b*⁵ es cierto. Pero `ring` no lo demuestra: deja `a * b ^ 4 * 5 + a ^ 2 * b ^ 3 * 10 + … = a ^ 5 + b ^ 5`, con los coeficientes 5 y 10 que ahí valen 0. No es una identidad de todos los anillos conmutativos: es algo propio de contar módulo 5. ¿Por qué es cierto? ¿Y qué tiene que ver con el pequeño teorema de Fermat? Lo vemos en **Congruencias y Fermat**.

## Ejercicios

1. **El cuadrado de una diferencia.** Demuestra `(a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2` con *a*, *b* enteros.

2. **El cubo.** Demuestra `(x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1` en ℤ.

3. **La resta de los naturales.** ¿Por qué `ring` no demuestra `a + b - b = a` con `a b : ℕ`? ¿Con qué táctica sale? ¿Y si *a* y *b* fueran enteros?

4. **Tercios.** Demuestra `x / 3 + 2 * x / 3 = x` en los reales.

5. **Usar la hipótesis.** Con `h : x = 2 * y` (reales), demuestra `x ^ 2 = 4 * y ^ 2` con `linear_combination`. ¿Qué coeficiente le das a `h`?

6. **Simplificar.** Con `hb : b ≠ 0`, demuestra `a / b * b = a`. ¿Qué pasa si quitas `hb`?

::::{div}
:class: afondo
7. **Sophie Germain.** Demuestra la identidad *a*⁴ + 4*b*⁴ = (*a*² + 2*b*² + 2*ab*)(*a*² + 2*b*² − 2*ab*) en ℤ. Úsala para explicar por qué *n*⁴ + 4 no es primo si *n* > 1.

8. **La forma normal.** ¿Qué escribe `ring_nf` en `(x + 2) * (x - 3) = 0` con `x : ℤ`? ¿En qué orden pone los términos?
::::

## Solucionario

1. `ring`.
2. `ring`.
3. Porque en ℕ la resta se queda en 0 y no es la operación inversa de la suma: no es una identidad de anillo. Sale con `omega`. En ℤ, `ring` la demuestra.
4. `ring`: dividir entre 3 es multiplicar por ⅓, y ⅓ + ⅔ = 1.
5. ```lean
   example (x y : ℝ) (h : x = 2 * y) : x ^ 2 = 4 * y ^ 2 := by
     linear_combination (x + 2 * y) * h
   ```
   Multiplicar *x* = 2*y* por *x* + 2*y* da *x*² + 2*xy* = 2*xy* + 4*y*², que es la meta.
6. `field_simp`. Sin `hb`, la igualdad es falsa para *b* = 0 (*a*/0 · 0 = 0 en Lean), y `field_simp` no puede simplificar.

::::{div}
:class: afondo
7. `ring` la demuestra. Con *a* = *n* y *b* = 1: *n*⁴ + 4 = (*n*² + 2*n* + 2)(*n*² − 2*n* + 2), y si *n* > 1 los dos factores son mayores que 1 (el segundo es (*n* − 1)² + 1 ≥ 2).
8. `-6 - x + x ^ 2 = 0`: primero el término independiente y luego las potencias de *x* de menor a mayor grado, cada una con su coeficiente.
::::
