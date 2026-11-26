---
title: Qué hacen simp, omega y decide
subtitle: Abrir las cajas negras que cierran las metas
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Desde el capítulo 5, tres tácticas han ido cerrando metas sin explicar cómo: `simp`, `omega` y `decide`. Escribes una palabra y la meta desaparece. Funcionan tan bien que es fácil olvidar que hacen algo, y que a veces fallan.

Cuando fallan, entender qué hacen por dentro es lo que permite saber qué hacer. Y la grieta del capítulo 22 dejó una pregunta: en `v[1]`, alguien demostró `1 < 3` sin que se lo pidiéramos. ¿Quién?

## La pregunta

¿Qué hace exactamente cada una de estas tácticas? ¿Por qué `omega` resuelve unas cosas y no otras? ¿Qué queda escrito en la prueba cuando las usamos?

## La idea

Cada una es un **procedimiento** distinto, con un territorio propio:

| Táctica | Qué hace | Sirve para | No sirve para |
|---|---|---|---|
| `decide` | **calcula** si la afirmación es verdadera | afirmaciones que se pueden comprobar haciendo la cuenta: 10 ∣ 1000, ∀ *n* < 10, … | nada con infinitos casos: ∀ *n* : ℕ, … |
| `omega` | **resuelve** la aritmética lineal de enteros y naturales | sumas, restas, multiplicar por números, `/` y `%` por números | productos de variables: *x* · *y* |
| `simp` | **reescribe** con una lista de igualdades (las marcadas `@[simp]`) hasta que no puede más | simplificar: quitar + 0, · 1, `[] ++ l`… | demostrar lo que no se reduce a algo trivial |

:::{important} Una táctica no es magia: es un algoritmo que fabrica una prueba
Las tres hacen lo mismo que harías tú, de forma sistemática. Y las tres acaban igual: construyen un **término**, un objeto de prueba, que el núcleo de Lean comprueba. Si la táctica tiene un error, el núcleo lo detecta. Por eso se puede confiar en ellas sin conocerlas por dentro, y por eso, cuando fallan, no pasa nada grave: solo hay que buscar otro camino.
:::

## Construcción

### 1 · `decide`: hacer la cuenta

:::{tip} Predice
`decide` comprueba `∀ n < 10, n * n ≠ 50` probando los diez casos. ¿Qué crees que pasará con `∀ n : ℕ, n * n ≠ 50`?
:::

```lean
import Mathlib

#eval decide (10 ∣ 1000)

example : 10 ∣ 1000 := by
  decide

example : ∀ n < 10, n * n ≠ 50 := by
  decide

example : ∀ n : ℕ, n * n ≠ 50 := by
  decide
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Decidir es calcular","etiqueta":"decide · Decidable","espera_error":true,"idea":"`decide` funciona con las afirmaciones **decidibles**: las que tienen un procedimiento que contesta sí o no en un número finito de pasos. Lean lo ejecuta, y si sale `true`, la afirmación queda demostrada.","notas":{"1":"La división 1000 : 10 da resto 0, así que 10 divide a 1000. `decide` hace la cuenta y lo demuestra.","2":"Solo hay diez casos, de 0 a 9: `decide` los prueba uno a uno. (*n*² = 50 no tiene solución entera.)","3":"Con infinitos casos no hay cuenta que hacer: Lean no encuentra un procedimiento (`Decidable`) para esa afirmación."}},"archivo":"datos/trazas/23-automaticas-1.json"}
```

- `#eval decide (10 ∣ 1000)` contesta `true`. Detrás de cada afirmación decidible hay una función que devuelve `true` o `false`, y `decide` la ejecuta.
- Lo que hace decidible una afirmación es tener una **instancia** `Decidable`: un procedimiento registrado. Lo tienen las igualdades y desigualdades de naturales, la divisibilidad, los «para todo» acotados (`∀ n < 10`)… y no lo tiene un «para todo» sobre todos los naturales.
- El error lo dice así: `failed to synthesize Decidable (∀ (n : ℕ), n * n ≠ 50)`. No significa que sea falso (es verdadero); significa que no hay cuenta que hacer. Para eso están la inducción del capítulo 11 y el resto de tácticas.

### 2 · `omega`: la aritmética lineal

`omega` trabaja en la **aritmética de Presburger**: la de los naturales y enteros con suma, resta, comparaciones, y multiplicación, división y resto **por números concretos**. En ese territorio resuelve casi todo lo que aparece en la práctica. (La documentación de Lean avisa, con honestidad, de que todavía no es un procedimiento de decisión completo: le faltan dos piezas del algoritmo original, las «sombras oscura y gris». En los problemas de este libro no se nota.)

```lean
import Mathlib

example (x y : ℕ) (h : x + y ≤ 10) : x ≤ 10 := by
  omega

example (n : ℕ) (h : n % 4 = 3) : n % 2 = 1 := by
  omega

example (x : ℤ) : 2 * x ≠ 7 := by
  omega

example (x y : ℕ) (h : x ≤ y) : x * x ≤ y * y := by
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El territorio de omega","etiqueta":"omega · Presburger","espera_error":true,"idea":"`omega` resuelve los problemas de enteros y naturales hechos de sumas, restas, comparaciones y multiplicaciones por números. Fuera de ese territorio, con *x* · *y*, se rinde, y enseña por qué.","notas":{"1":"Una suma de naturales: si *x* + *y* ≤ 10, *x* ≤ 10, porque *y* ≥ 0.","2":"Restos por números concretos: si *n* deja resto 3 al dividir entre 4, es impar.","3":"Un par nunca es 7: `omega` sabe razonar con divisibilidad entre enteros.","4":"*x* · *x* no es lineal. `omega` lo trata como una incógnita más, sin saber que es un cuadrado, y encuentra un «contraejemplo» que no lo es."}},"archivo":"datos/trazas/23-automaticas-2.json"}
```

- `omega` trabaja con naturales y enteros. Convierte todo a enteros (por eso aparece `↑x`, la flecha de conversión), pasa las hipótesis y la negación de la meta a un sistema de desigualdades lineales, y busca una contradicción.
- El mensaje de error es muy informativo. Con *x* · *x* ≤ *y* · *y*, `omega` llama `c` a *x* · *x* y `d` a *y* · *y*, como si fueran números cualesquiera, y encuentra valores que cumplen todo menos la meta. No es un contraejemplo de verdad: es lo mejor que puede hacer sin saber multiplicar variables.
- Para salir de ahí hace falta otra herramienta: `nlinarith` (capítulo 13) o el teorema `Nat.mul_le_mul h h`.

### 3 · `simp`: reescribir hasta no poder más

`simp` tiene una lista enorme de igualdades marcadas con `@[simp]`: *a* + 0 = *a*, *a* · 1 = *a*, *b* · 0 = 0… Las usa como reglas de reescritura, siempre de izquierda a derecha, hasta que ninguna se puede aplicar más. Si al final la meta es `True`, la cierra.

```lean
import Mathlib

set_option trace.Meta.Tactic.simp.rewrite true in
example (a b : ℕ) : (a + 0) * 1 + b * 0 = a := by
  simp

example (a b : ℕ) : (a + 0) * 1 + b * 0 = a := by
  simp only [add_zero]
  simp only [mul_one]
  simp only [mul_zero]
  simp only [add_zero]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Regla a regla","etiqueta":"simp · @[simp] · simp only · traza","idea":"Con la opción de traza, `simp` cuenta cada reescritura que hace: `add_zero`, `mul_one`, `mul_zero`, otra vez `add_zero` y, al final, `eq_self`, que cambia *a* = *a* por `True`. El segundo ejemplo hace lo mismo a mano, una regla cada vez.","notas":{"1":"`simp` aplica sus reglas hasta el final. Los mensajes enseñan las cinco reescrituras, en orden.","2":"*a* + 0 → *a*: queda `a * 1 + b * 0 = a`.","3":"*a* · 1 → *a*: queda `a + b * 0 = a`.","4":"*b* · 0 → 0: queda `a + 0 = a`.","5":"*a* + 0 → *a*, y queda `a = a`, que `simp` cierra él solo."}},"archivo":"datos/trazas/23-automaticas-3.json"}
```

- `set_option trace.Meta.Tactic.simp.rewrite true in` activa un modo en el que `simp` escribe cada reescritura: la regla con su prioridad (`add_zero:1000`; 1000 es la prioridad por defecto), el trozo de antes y el de después (`a + 0 ==> a`). Es la mejor forma de entender por qué `simp` deja una meta como la deja.
- La última regla, `eq_self`, convierte `a = a` en `True`. Así es como `simp` cierra metas: reduciéndolas a `True`.
- `simp only [reglas]` usa solo las reglas que le das. Es lo que propone `simp?` (capítulo 20), y lo que conviene dejar escrito: la prueba no cambia aunque Mathlib añada o quite reglas `@[simp]`.

### 4 · Enseñarle a `simp` una regla nueva

`simp` solo conoce las reglas marcadas `@[simp]`. Si defines algo nuevo, no sabe qué hacer con ello, hasta que le das una regla.

```lean
import Mathlib

def doble (n : ℕ) : ℕ := 2 * n

example : doble 3 + doble 0 = 6 := by
  simp

@[simp] theorem doble_eq (n : ℕ) : doble n = n + n := by
  unfold doble
  omega

example : doble 3 + doble 0 = 6 := by
  simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una regla más para simp","etiqueta":"@[simp] · unfold","espera_error":true,"idea":"`simp` no despliega las definiciones por su cuenta: sin una regla para `doble`, no avanza. Con `@[simp]`, el teorema `doble_eq` pasa a formar parte de su lista, y desde ese momento `simp` sabe reescribir `doble n` como *n* + *n*.","notas":{"1":"`simp` no sabe nada de `doble`: «made no progress».","2":"Para demostrar la regla, se despliega la definición: `2 * n = n + n`.","3":"Y eso es aritmética lineal.","4":"Ahora `simp` usa `doble_eq`: `3 + 3 + (0 + 0) = 6`, y lo termina con sus reglas de números."}},"archivo":"datos/trazas/23-automaticas-4.json"}
```

- `@[simp]` delante de un teorema lo añade a la lista de `simp`. Las reglas tienen que ir de lo complicado a lo simple: `doble n = n + n` está bien orientada; al revés, `simp` podría quedarse dando vueltas.
- `unfold doble` sustituye `doble` por su definición. Es lo que `simp` no hace por defecto.
- Las 184 000 afirmaciones de Mathlib del capítulo 20 no son todas reglas de `simp`: solo las que alguien ha marcado así, porque simplifican.

::::{div}
:class: afondo
### 5 · Quién demostró `1 < 3`, y qué queda escrito

```lean
import Mathlib

example (v : Vector ℕ 3) (i : ℕ) (h : i + 1 < 3) : ℕ := v[i]
example (v : Vector ℕ 3) (i : ℕ) : ℕ := v[i]

theorem div10 : 10 ∣ 1000 := by
  decide

#print div10
#print axioms div10

theorem nd : 10 ∣ 1000 := by
  native_decide

#print axioms nd
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que queda escrito","etiqueta":"a fondo · get_elem_tactic · of_decide_eq_true · native_decide","espera_error":true,"idea":"Cuando escribes `v[i]`, Lean llama a una táctica automática, `get_elem_tactic`, que intenta demostrar `i < 3` (prueba, entre otras, `omega`). Y `decide` deja escrita una prueba diminuta: «la cuenta da `true`».","notas":{"1":"Arriba, en los mensajes: con `h : i + 1 < 3`, `v[i]` funciona sin decir nada (`omega` saca `i < 3`); sin hipótesis, Lean no puede demostrar `⊢ i < 3`. Ahora, `decide` demuestra 10 ∣ 1000.","2":"`#print div10` enseña la prueba: `of_decide_eq_true (id (Eq.refl true))`. `native_decide` hace la misma cuenta, pero compilada, fuera del núcleo, y lo paga con un axioma más."}},"archivo":"datos/trazas/23-automaticas-5.json"}
```

**Quién demostró `1 < 3`.** Al escribir `v[i]`, Lean necesita una prueba de que *i* es una posición válida, y la busca con una táctica, `get_elem_tactic`. Por dentro prueba varias, entre ellas `trivial`, `simp +arith` y `omega`. Con `h : i + 1 < 3`, `omega` deduce `i < 3` y todo funciona en silencio. Sin hipótesis no hay manera, y el error enseña la meta que ha quedado abierta: `⊢ i < 3`. En `v[1]`, la meta era `1 < 3`, y la cerró una de esas tácticas sin que lo viéramos.

**Qué deja escrito `decide`.** `#print div10` contesta `of_decide_eq_true (id (Eq.refl true))`. Es la prueba entera: «la función que decide 10 ∣ 1000 devuelve `true`, y eso es cierto por `rfl`». Lo pesado no está en la prueba, sino en comprobarla: el núcleo tiene que **ejecutar** la cuenta para ver que, efectivamente, da `true`. Por eso `decide` con números enormes es lento.

**`native_decide`.** Hace la misma cuenta, pero compilándola a código máquina y ejecutándola fuera del núcleo, mucho más rápido. El precio aparece en `#print axioms nd`: además de `propext`, la prueba depende de un axioma nuevo, `nd._native.native_decide.ax_1_1`, que dice «confío en lo que ha calculado el compilador». `#print axioms div10`, en cambio, solo enseña `propext`. Qué son esos axiomas y por qué importa cuáles aparecen es el tema del capítulo siguiente.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Los tres sistemas tienen un procedimiento de decisión para la aritmética lineal, y los tres se paran en el mismo sitio: los productos de variables (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: omega
example (x y : ℕ) (h : x + y ≤ 10) : x ≤ 10 := by omega
example (x y : ℕ) (h : x ≤ y) : x * x ≤ y * y := by omega
-- error: omega could not prove the goal
```

```coq
(* Rocq (Coq): lia *)
Require Import Lia.
Lemma l1 (x y : nat) : x + y <= 10 -> x <= 10.
Proof. lia. Qed.
Lemma l3 (x y : nat) : x <= y -> x * x <= y * y.
Proof. lia. Qed.
(* Error: Tactic failure:  Cannot find witness. *)
```

```isabelle
(* Isabelle: arith *)
lemma l1: "(x::nat) + y \<le> 10 \<Longrightarrow> x \<le> 10" by arith
lemma l3: "(x::nat) \<le> y \<Longrightarrow> x * x \<le> y * y" by arith
(* Failed to apply initial proof method *)
```

`omega`, `lia` (de *linear integer arithmetic*) y `arith` resuelven la misma clase de problemas: comparaciones entre sumas de variables multiplicadas por números. Y fallan en el mismo sitio, porque la aritmética con productos de variables ya no es decidible en general. Es un límite matemático, no un defecto de ninguna de las tres.
:::

## Conexiones

- `decide` apareció en los capítulos 3, 7 y 15; aquí se ve que es calcular una función que devuelve `true` o `false`. El capítulo 7 ya habló de proposiciones decidibles.
- `omega` ha cerrado metas desde el capítulo 11; su territorio es la aritmética de Presburger.
- `simp` del capítulo 5 y `simp?` del capítulo 20: reglas `@[simp]` aplicadas de izquierda a derecha.
- `get_elem_tactic` responde a la grieta del capítulo 22.
- Cuando `omega` se rinde con productos, entran `nlinarith` y `positivity` (capítulo 13).

## La grieta

`#print axioms` ha enseñado `propext` en una prueba hecha solo con `decide`, y un axioma raro en la de `native_decide`. En el capítulo 7 apareció `Classical.choice`, y en el 3, `sorryAx`. ¿Qué es un axioma para Lean? ¿Quién comprueba de verdad las pruebas: las tácticas, o alguien más pequeño y más fiable? ¿Y por qué importa qué axiomas aparecen? Es el tema de **El núcleo y los axiomas**.

## Ejercicios

1. **Divisibilidad.** Demuestra `7 ∣ 91` con `decide`.

2. **Restos de cuadrados.** Demuestra con `decide` que, para todo *n* < 20, *n*² no deja resto 2 al dividir entre 4.

3. **Una ecuación.** Demuestra con `omega` que, si 3*x* + 1 = 10 (con *x* natural), entonces *x* = 3.

4. **Restos encadenados.** Demuestra con `omega` que, si *n* deja resto 5 al dividir entre 6, deja resto 2 al dividir entre 3.

5. **Lo que usa `simp`.** Usa `simp?` en `(l ++ []).length = l.length`, con `l : List ℕ`. ¿Qué regla propone?

6. **Ayudar a `omega`.** `omega` no demuestra `y = 3` a partir de `h : x * y = 6` y `hx : x = 2`. ¿Por qué? Arréglalo con una táctica antes de `omega`.

::::{div}
:class: afondo
7. **Los axiomas de una cuenta.** Demuestra `10 ∣ 1000` con `decide` y con `native_decide`, y compara lo que contesta `#print axioms` en cada caso.

8. **Una regla para `triple`.** Define `triple (n : ℕ) : ℕ := 3 * n`, dale una regla `@[simp]` y demuestra `triple 2 = 6` con `simp`.
::::

## Solucionario

1. `example : 7 ∣ 91 := by decide`. 91 = 7 · 13.
2. `example : ∀ n < 20, n ^ 2 % 4 ≠ 2 := by decide`. Son veinte casos, y en ninguno el resto es 2 (los cuadrados solo dejan resto 0 o 1 entre 4).
3. `example (x : ℕ) (h : 3 * x + 1 = 10) : x = 3 := by omega`.
4. `example (n : ℕ) (h : n % 6 = 5) : n % 3 = 2 := by omega`.
5. `simp only [List.append_nil]`: añadir la lista vacía al final no cambia nada.
6. `omega` trata `x * y` como una incógnita más y no sustituye *x* por 2. Con `subst hx`, la hipótesis pasa a ser `2 * y = 6`, que es lineal:
   ```lean
   example (x y : ℕ) (h : x * y = 6) (hx : x = 2) : y = 3 := by
     subst hx
     omega
   ```

::::{div}
:class: afondo
7. Con `decide`: `[propext]`. Con `native_decide`: `[propext, nd._native.native_decide.ax_1_1]` (el nombre del axioma lleva el del teorema). El axioma extra significa «confío en el resultado del código compilado».
8. Las tres líneas:
   ```lean
   def triple (n : ℕ) : ℕ := 3 * n
   @[simp] theorem triple_eq (n : ℕ) : triple n = 3 * n := rfl
   example : triple 2 = 6 := by simp
   ```
   La regla se demuestra con `rfl` porque es justo la definición.
::::
