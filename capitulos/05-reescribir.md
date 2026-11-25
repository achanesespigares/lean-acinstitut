---
title: "Reescribir: rw y simp"
subtitle: Cambiar iguales por iguales, a mano o en automático
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Si *a* = *b* + 1 y *b* = 2*c*, ¿cuánto vale *a*? En la pizarra, nadie lo duda: se sustituye *b* por 2*c* y sale *a* = 2*c* + 1. Cambiar una cosa por otra igual es el paso más corriente de las matemáticas, tanto que casi no se nota.

En el capítulo anterior, `rw` hizo justo eso dos veces. Ahora toca mirar cómo lo hace: qué busca, qué cambia y qué hace cuando no encuentra nada. Y conocer a `simp`, que hace muchas sustituciones seguidas sin que se las pidas una a una.

## La pregunta

Con una igualdad en la mano, ¿cómo se usa para cambiar la meta? ¿Se puede usar al revés, o dentro de una hipótesis? ¿Y qué hace `simp` cuando no le dices qué usar?

## La idea

- `rw [h]`, con `h : A = B`, busca `A` en la meta y lo cambia por `B`. Siempre de izquierda a derecha.
- `rw [← h]` la usa al revés: busca `B` y lo cambia por `A`.
- `rw [h] at h₂` reescribe en la hipótesis `h₂`, no en la meta.
- La igualdad puede ser una hipótesis o un teorema ya demostrado: `mul_comm`, `add_zero`, `two_mul`…
- Al terminar, `rw` prueba `rfl`. Si la meta queda con dos lados iguales al calcular, se cierra sola.
- `simp` reescribe con una lista de igualdades que Mathlib tiene marcadas como simplificaciones, una y otra vez, hasta que no puede más.

:::{important} rw no razona: busca y cambia
`rw` no sabe matemáticas. Busca el lado izquierdo de la igualdad, letra por letra, y lo cambia por el derecho. Si no lo encuentra tal cual, falla, aunque la meta sea obviamente cierta.
:::

## Construcción

### 1 · Sustituir paso a paso

:::{tip} Predice
Con `h1 : a = b + 1`, ¿qué meta deja `rw [h1]` en `a = 2 * c + 1`?
:::

```lean
import Mathlib

example (a b c : ℕ) (h1 : a = b + 1) (h2 : b = 2 * c) : a = 2 * c + 1 := by
  rw [h1]
  rw [h2]

example (a b : ℕ) (h : a = b) (hb : b = 5) : a + a = 10 := by
  rw [← h] at hb
  rw [hb]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Cambiar iguales por iguales","etiqueta":"rw · ← · at","idea":"`rw [h]` cambia el lado izquierdo de `h` por el derecho. Con `←`, al revés. Con `at`, en una hipótesis en lugar de en la meta.","notas":{"1":"`a` pasa a ser `b + 1`. Las hipótesis no cambian.","2":"`b` pasa a ser `2 * c`. Quedaría `2 * c + 1 = 2 * c + 1`, y el `rfl` que prueba `rw` al terminar la cierra.","3":"`← h` usa `a = b` al revés: busca `b` y pone `a`. Y `at hb` lo hace en la hipótesis `hb`, que pasa a ser `a = 5`.","4":"Ahora sí: `a` por `5`, y `5 + 5 = 10` se cierra calculando."}},"archivo":"datos/trazas/05-reescribir-1.json"}
```

- `rw [h1]` cambia **todas** las `a` de la meta por `b + 1`. Aquí solo hay una.
- Tras `rw [h2]`, la meta sería `2 * c + 1 = 2 * c + 1`. `rw` prueba `rfl` y la cierra: por eso no hace falta nada más.
- En el segundo ejemplo, `hb` dice cuánto vale `b`, pero en la meta solo hay `a`. `rw [hb]` no encontraría nada. Por eso primero se cambia `hb`: `rw [← h] at hb` busca `b` en `hb` y pone `a`.
- Hay dos caminos para lo mismo: cambiar la meta hasta que encaje con lo que sabes, o cambiar lo que sabes hasta que encaje con la meta.

### 2 · Reescribir con teoremas

Una hipótesis es una igualdad. Un teorema de Mathlib también, solo que vale para todos los números. `mul_comm` dice que *a* · *b* = *b* · *a*; `two_mul`, que 2 · *a* = *a* + *a*; `add_zero`, que *a* + 0 = *a*.

```lean
import Mathlib

example (x y : ℕ) : x * y + y * x = 2 * (x * y) := by
  rw [mul_comm y x]
  rw [two_mul]

example (a b : ℕ) : a + b + 0 = b + a := by
  rw [add_zero, add_comm]

example (x : ℕ) (h : x + 0 = 7) : x = 7 := by
  rw [add_zero] at h
  exact h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un teorema es una igualdad más","etiqueta":"mul_comm · two_mul · add_zero","idea":"Los teoremas de Mathlib se usan igual que las hipótesis. Entre corchetes se pueden poner varios, y se aplican en orden.","notas":{"1":"`mul_comm y x` es la igualdad `y * x = x * y`: cambia `y * x` por `x * y`.","2":"`two_mul` dice que `2 * a = a + a`. Aquí, con `a = x * y`, la meta queda `x * y + x * y = x * y + x * y`, y se cierra.","3":"Dos reescrituras en una línea: primero `add_zero` quita el `+ 0`, después `add_comm` da la vuelta a `a + b`.","4":"`add_zero` en la hipótesis: `x + 0 = 7` pasa a ser `x = 7`.","5":"`exact h`: la hipótesis es justo la meta."}},"archivo":"datos/trazas/05-reescribir-2.json"}
```

- `mul_comm y x` es el teorema `mul_comm` con los números que tú eliges: `y * x = x * y`. Con los argumentos, sabes qué producto se cambia.
- Con `rw [two_mul]`, Lean busca algo de la forma `2 * _` y lo encuentra en `2 * (x * y)`. El hueco se rellena solo.
- `rw [add_zero, add_comm]` hace dos reescrituras seguidas, en una sola línea. Es lo mismo que escribir dos `rw`.
- Los teoremas tienen nombres que se leen en inglés: `add` es la suma, `mul` el producto, `zero` el cero, `comm` la propiedad conmutativa. `two_mul` es «dos por».

### 3 · Cuando `rw` no encuentra nada

:::{tip} Predice
`h : a = 3` y la meta es `b + 1 = 4`. ¿Qué hará `rw [h]`?
:::

```lean
import Mathlib

example (a b : ℕ) (h : a = 3) : b + 1 = 4 := by
  rw [h]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Buscar lo que no está","etiqueta":"rw · error","espera_error":true,"idea":"`rw [h]` busca el lado izquierdo de `h`, `a`, en la meta. No hay ninguna `a`, así que no puede hacer nada y Lean da un error.","notas":{"1":"Lean dice que no ha encontrado `a` en `b + 1 = 4`, y enseña el panel tal como estaba."}},"archivo":"datos/trazas/05-reescribir-3.json"}
```

- El error dice, en inglés, *did not find an occurrence of the pattern a*: no ha encontrado el patrón `a` en la meta.
- Debajo, Lean copia el panel: así ves qué buscaba y dónde.
- Este error es de los más frecuentes. Casi siempre significa una de tres cosas: la igualdad va al revés (hace falta `←`), lo que buscas está en una hipótesis (hace falta `at`), o la expresión está escrita de otra forma (`x * 2` no es lo mismo que `2 * x`).

### 4 · `simp`: muchas reescrituras de golpe

`rw` hace lo que le dices. `simp` decide solo: tiene una lista de cientos de igualdades sencillas, como `x + 0 = x`, `x * 1 = x` o `0 + x = x`, y las aplica mientras pueda.

```lean
import Mathlib

example (x : ℕ) (h : 0 + x * 1 = 7) : x + 0 = 7 := by
  simp at h
  simp
  exact h

example (x y : ℕ) (h : x = y) : x + 0 = y * 1 := by
  simp [h]

example (x : ℕ) : 0 + x * 1 = x := by
  simp?
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Simplificar sin decir cómo","etiqueta":"simp · simp at · simp [h] · simp?","idea":"`simp` simplifica con todo lo que sabe. `simp at h` lo hace en una hipótesis, `simp [h]` añade `h` a su lista y `simp?` dice qué ha usado.","notas":{"1":"`0 + x * 1` se queda en `x`: la hipótesis pasa a ser `x = 7`.","2":"`x + 0` pasa a ser `x`. La meta no se cierra sola, pero ya coincide con `h`.","3":"Y `exact h` termina.","4":"Con `[h]`, `simp` también cambia `x` por `y`. Queda `y = y`, y se cierra.","5":"`simp?` hace lo mismo que `simp` y además escribe en Mensajes de Lean qué teoremas ha usado."}},"archivo":"datos/trazas/05-reescribir-4.json"}
```

- `simp at h` simplifica la hipótesis: `0 + x * 1 = 7` pasa a ser `x = 7`.
- `simp` simplifica la meta, `x + 0 = 7`, hasta `x = 7`. No la cierra, porque no sabe que `x` vale 7: eso está en `h`, y `simp` no mira las hipótesis si no se las das.
- `simp [h]` añade `h` a su lista de igualdades. En el segundo ejemplo cambia `x` por `y`, quita el `+ 0` y el `* 1`, y queda `y = y`, que cierra.
- `simp?` contesta, en Mensajes de Lean, `simp only [mul_one, zero_add]`: los dos teoremas que ha usado. Puedes copiar esa línea en tu prueba. `simp only […]` usa solo los teoremas de la lista: es más lento de escribir, pero no cambia si Mathlib añade simplificaciones nuevas.

::::{div}
:class: afondo
### 5 · Qué cambia exactamente `rw`

En la sección 2 escribimos `mul_comm y x`. ¿Y si se escribe solo `mul_comm`, sin decir qué producto?

```lean
import Mathlib

example (x y : ℕ) : x * y + y * x = 2 * (x * y) := by
  rw [mul_comm]
  rw [two_mul]

example (x y : ℕ) : x * y + y * x = 2 * (x * y) := by
  nth_rewrite 2 [mul_comm]
  rw [two_mul]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La primera coincidencia manda","etiqueta":"a fondo · rw · nth_rewrite","idea":"Sin argumentos, `rw [mul_comm]` busca el primer producto de la meta, lo fija y cambia todas sus apariciones. `nth_rewrite 2` cambia solo la segunda.","notas":{"1":"El primer producto que encuentra es `x * y`. Lo cambia por `y * x` en los dos sitios donde aparece; el `y * x` que ya estaba no se toca.","2":"Ahora todo está escrito con `y * x`, y `two_mul` cierra igual.","3":"`nth_rewrite 2` cambia solo el segundo producto de la meta, `y * x`.","4":"Y cierra igual."}},"archivo":"datos/trazas/05-reescribir-5.json"}
```

`mul_comm` sin argumentos tiene dos huecos: dice que `?a * ?b = ?b * ?a` para cualesquiera `?a` y `?b`. `rw` recorre la meta, se queda con el **primer** producto que encaja, aquí `x * y`, y fija los huecos: `?a = x` y `?b = y`. Después cambia **todas** las apariciones de `x * y`, pero no las de `y * x`, que es otra expresión.

El resultado, `y * x + y * x = 2 * (y * x)`, no es lo que hicimos en la sección 2, pero también sirve. Con `nth_rewrite 2 [mul_comm]` se elige a mano: cambia solo la segunda coincidencia.

Por eso, en pruebas largas, conviene dar los argumentos (`mul_comm y x`): la prueba dice exactamente qué cambia, y no se rompe si la meta cambia de orden.

`simp` tiene el problema contrario: con `add_comm` podría dar vueltas sin fin (`a + b` → `b + a` → `a + b`…). No las da porque, con las propiedades conmutativas, solo cambia el orden si el resultado queda «más ordenado» según una regla interna. Por eso `simp [add_comm]` demuestra `a + b = b + a` y no se queda colgado.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Si *a* = *b* + 1 y *b* = 2*c*, entonces *a* = 2*c* + 1 (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: rw cierra solo con rfl al terminar
example (a b c : ℕ) (h1 : a = b + 1) (h2 : b = 2 * c) : a = 2 * c + 1 := by
  rw [h1, h2]
```

```coq
(* Rocq (Coq): rewrite no cierra; hace falta reflexivity *)
Goal forall a b c : nat, a = b + 1 -> b = 2 * c -> a = 2 * c + 1.
Proof.
  intros a b c h1 h2.
  rewrite h1. rewrite h2.
  reflexivity.
Qed.
```

```isabelle
(* Isabelle: simp only con las dos igualdades *)
lemma
  assumes h1: "a = b + 1" and h2: "b = 2 * c"
  shows "a = 2 * c + (1::nat)"
  by (simp only: h1 h2)
```

En Rocq, `rewrite` funciona igual que `rw`, también con `<-` para ir al revés y con `in hb` en lugar de `at hb`. Pero no cierra la meta: tras los dos `rewrite` queda `2 * c + 1 = 2 * c + 1`, y hay que escribir `reflexivity`. Isabelle no tiene un `rw` aparte: su `simp` reescribe con las igualdades que le das, de izquierda a derecha, y `simp only` usa solo esas.
:::

## Conexiones

- En el capítulo 3, `simp` demostró `0 + n = n`, que `rfl` no podía. Ahora sabes por qué: `simp` usa el teorema `zero_add`.
- `rw [hk]` apareció en la primera prueba del libro, en el capítulo 0, para cambiar `n` por `k + k`.
- `rw` con `←` y `at` volverá en todos los capítulos de matemáticas. En la parte II, con la igualdad y `calc`, se encadenarán muchas reescrituras en una sola cuenta.
- En la parte V, el capítulo «Qué hacen `simp`, `omega`, `decide`…» abre `simp` por dentro: cómo elige y en qué orden.

## La grieta

Hasta ahora, las metas han sido igualdades y «y». Pero las matemáticas están llenas de «si… entonces…»: si *n* es par, entonces *n*² es par. ¿Qué hace Lean con una implicación? ¿Cómo se supone algo, y cómo se usa una hipótesis que es ella misma un «si… entonces»? Empieza la parte II, con **Implicación y conjunción**.

## Ejercicios

1. **Predice y comprueba.** Con `h : x = 5`, ¿basta `rw [h]` para demostrar `x + x = 10`? ¿Por qué?

2. **Dos sustituciones.** Con `h1 : x = 2` y `h2 : y = x + 1`, demuestra `y * x = 6` con un solo `rw`. ¿Importa el orden de `h2` y `h1` dentro de los corchetes?

3. **En la hipótesis.** Con `h : a + 0 = b`, demuestra `b = a` usando `rw … at h`.

4. **Por los dos lados.** Con `h : p = q` y `hq : q = 4`, demuestra `p * 2 = 8` de dos formas: reescribiendo solo la meta, y reescribiendo primero `hq`.

5. **El error.** ¿Por qué falla `rw [h]` con `h : a = 3` y la meta `b + 1 = 4`? ¿Hay algún cambio en `h` que lo arregle?

6. **¿Qué ha usado?** ¿Qué contesta `simp?` en la meta `(x + 0) * 1 = x`?

::::{div}
:class: afondo
7. **La primera coincidencia.** En la meta `x * y + y * x = 2 * (x * y)`, ¿qué meta deja `rw [mul_comm]`? ¿Y `nth_rewrite 2 [mul_comm]`?

8. **Sin cierre automático.** En Rocq, ¿qué queda tras `rewrite h1. rewrite h2.` en el ejemplo del recuadro? ¿Y en Lean tras `rw [h1, h2]`?
::::

## Solucionario

1. Sí. `rw [h]` cambia las dos `x` por `5`, la meta queda `5 + 5 = 10` y el `rfl` que prueba `rw` al terminar la cierra.
2. `rw [h2, h1]`. El orden importa: primero `h2` cambia `y` por `x + 1` y la meta queda `(x + 1) * x = 6`; después `h1` cambia las dos `x` por `2`, y `(2 + 1) * 2 = 6` se cierra. Con `rw [h1, h2]` no sale: `h1` cambia la `x` de la meta por `2` y queda `y * 2 = 6`; después `h2` cambia `y` por `x + 1` y vuelve a meter una `x`. Lean se queda con `(x + 1) * 2 = 6` y dice *unsolved goals*: falta una meta por cerrar.
3. ```lean
   example (a b : ℕ) (h : a + 0 = b) : b = a := by
     rw [add_zero] at h
     rw [h]
   ```
   Tras el primer paso, `h : a = b`. Tras el segundo, la meta es `b = b`. También vale `simp at h` en lugar de `rw [add_zero] at h`.
4. Solo la meta: `rw [h, hq]`. Primero `hq`: `rw [← h] at hq` deja `hq : p = 4`, y `rw [hq]` termina.
5. `rw [h]` busca `a` en la meta, y la meta no tiene ninguna `a`. Ningún cambio en `h` lo arregla: la meta no dice nada de `a`, y `b + 1 = 4` no se puede demostrar sin saber cuánto vale `b`.
6. `simp only [add_zero, mul_one]`.

::::{div}
:class: afondo
7. `rw [mul_comm]` fija el primer producto, `x * y`, y lo cambia en todos sus sitios: `y * x + y * x = 2 * (y * x)`. `nth_rewrite 2 [mul_comm]` cambia solo el segundo producto, `y * x`: `x * y + x * y = 2 * (x * y)`.
8. En Rocq queda la meta `2 * c + 1 = 2 * c + 1`, y hay que cerrarla con `reflexivity`. En Lean, `rw` prueba `rfl` al terminar, y la meta se cierra sin escribir nada más.
::::
