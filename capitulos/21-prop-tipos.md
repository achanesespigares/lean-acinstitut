---
title: Proposiciones como tipos
subtitle: Una afirmación es un tipo, y su prueba es un objeto de ese tipo
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En el capítulo 3, `#check conmuta 3 5` contestó `conmuta 3 5 : 3 + 5 = 5 + 3`, y allí se dijo una frase que se dejó para más adelante: **una prueba tiene por tipo lo que demuestra**. En el capítulo 20, `exact?` propuso `exact Nat.add_comm a b`, y lo que va detrás de `exact` no era una táctica, sino un objeto.

Este capítulo abre la parte V, la de Lean por dentro, y empieza por esa frase. Es la idea sobre la que está construido todo lo demás: en Lean, demostrar es **construir un objeto**.

## La pregunta

Si una prueba es un objeto, ¿qué clase de objeto es? ¿Qué es una prueba de «si *p*, entonces *q*»? ¿Y de «*p* y *q*», o de «existe un *n* tal que…»? ¿Y qué hacen entonces las tácticas?

## La idea

Cada conectiva lógica corresponde a una forma de construir objetos. Es la **correspondencia de Curry-Howard**, y en Lean no es una analogía: es literal.

| Lógica | Tipos | Una prueba es… | En Lean |
|---|---|---|---|
| proposición *p* | un tipo `p : Prop` | un objeto de ese tipo | `h : p` |
| *p* → *q* | tipo de funciones | una función que convierte pruebas de *p* en pruebas de *q* | `fun hp => …` |
| *p* ∧ *q* | tipo de pares | un par: una prueba de *p* y una de *q* | `⟨hp, hq⟩` |
| *p* ∨ *q* | unión con etiqueta | una prueba de uno de los dos, con la etiqueta del lado | `Or.inl hp`, `Or.inr hq` |
| ∀ *x*, *P x* | funciones que dependen de *x* | una función que, para cada *x*, da una prueba de *P x* | `fun x => …` |
| ∃ *x*, *P x* | pares con testigo | un par: el testigo y la prueba de que cumple *P* | `⟨3, …⟩` |
| False | un tipo vacío | (no hay ninguna) | — |
| ¬*p* | *p* → False | una función que convierte una prueba de *p* en una de False | `fun hp => …` |

:::{important} Las tácticas construyen el objeto por ti
Cuando escribes `intro`, `constructor` o `use`, no estás haciendo algo distinto de construir un objeto: estás construyéndolo **a trozos**. Cada táctica rellena un pedazo y deja huecos, que son las metas del panel. Cuando no quedan huecos, el objeto está completo. `#print` enseña el objeto terminado.
:::

## Construcción

### 1 · Todo tiene un tipo

:::{tip} Predice
Si `3 : ℕ` dice que 3 es un natural, ¿qué crees que contestará `#check Nat.add_comm 2 3`?
:::

```lean
import Mathlib

#check (3 : ℕ)
#check ℕ
#check 2 + 2 = 4
#check Prop
#check Nat.add_comm
#check Nat.add_comm 2 3
#check (rfl : 2 + 2 = 4)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Todo tiene un tipo","etiqueta":"#check · Prop · Type","idea":"Los números tienen tipo, los tipos tienen tipo, las afirmaciones tienen tipo… y las pruebas también: el tipo de una prueba es la afirmación que demuestra.","notas":{"1":"3 es un objeto de tipo ℕ.","2":"ℕ es, a su vez, un objeto: de tipo `Type`, el tipo de los tipos de datos.","3":"Una afirmación es un objeto de tipo `Prop`.","4":"Y `Prop` es un tipo como otro cualquiera.","5":"`Nat.add_comm` es una función: le das *n* y *m*, y devuelve una prueba de *n* + *m* = *m* + *n*.","6":"Aplicada a 2 y 3, es una prueba de 2 + 3 = 3 + 2. Su tipo es esa afirmación.","7":"`rfl` prueba que algo es igual a sí mismo: su tipo es 2 + 2 = 2 + 2. Lean lo acepta como prueba de 2 + 2 = 4 porque, calculando, 2 + 2 y 4 son lo mismo."}},"archivo":"datos/trazas/21-prop-tipos-1.json"}
```

- Los dos puntos se leen «es de tipo»: `3 : ℕ` es «3 es un natural», y `Nat.add_comm 2 3 : 2 + 3 = 3 + 2` es «esto es una prueba de que 2 + 3 = 3 + 2».
- `Nat.add_comm` sin argumentos es una **función**: `(n m : ℕ)` son sus entradas, y lo que devuelve es una prueba. Un teorema con «para todo» es una máquina de fabricar pruebas.
- Lo de `rfl` es un pequeño anticipo del capítulo 24: Lean compara tipos **calculando**. Para él, `2 + 2 = 4` y `2 + 2 = 2 + 2` son el mismo tipo, porque 4 y 2 + 2 dan lo mismo al calcular.

### 2 · Una implicación es una función

Para demostrar «si *p*, entonces *r*», en la pizarra se dice «supongamos *p*» y se llega a *r*. Eso es exactamente una función: recibe una prueba de *p* y devuelve una prueba de *r*.

```lean
import Mathlib

theorem encadena (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  exact hqr (hpq hp)

#print encadena

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Suponer es recibir","etiqueta":"→ · fun · #print","idea":"`intro hp` abre una función que recibe una prueba `hp` de *p*. `exact` entrega lo que la función devuelve. `#print` enseña la función terminada, y el `example` la escribe directamente, sin tácticas.","notas":{"1":"«Supongamos *p*»: la función recibe `hp : p`.","2":"De `hp`, `hpq` da una prueba de *q*, y de ella `hqr` da una de *r*. Aplicar una implicación es **aplicar una función**. Lo que escribe `#print` es el objeto construido: `fun p q r hpq hqr hp => hqr (hpq hp)`."}},"archivo":"datos/trazas/21-prop-tipos-2.json"}
```

- `#print encadena` escribe `fun p q r hpq hqr hp => hqr (hpq hp)`. Es una función con seis entradas: las tres proposiciones, las dos hipótesis y la prueba de *p* que trajo `intro`.
- `hpq hp` es **aplicar** `hpq` a `hp`. La regla del *modus ponens* («si *p* → *q* y *p*, entonces *q*») no es más que aplicar una función a su entrada.
- El `example` escribe el mismo objeto a mano, con `fun`, como en el capítulo 6 (`fun h => ⟨h.2, h.1⟩`). Tácticas o término: el resultado es el mismo objeto.
- El tipo de `encadena` es `∀ (p q r : Prop), (p → q) → (q → r) → p → r`. Las flechas son las de las funciones del capítulo 2: `ℕ → ℕ` era «de naturales a naturales», y `p → q` es «de pruebas de *p* a pruebas de *q*».

### 3 · «Y» es un par; «o» es una etiqueta

```lean
import Mathlib

theorem cambia (p q : Prop) (h : p ∧ q) : q ∧ p := by
  constructor
  · exact h.2
  · exact h.1

#print cambia

theorem izq (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp

#print izq
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Pares y etiquetas","etiqueta":"∧ · ∨ · ⟨ , ⟩ · Or.inl","idea":"Una prueba de *q* ∧ *p* es un par: primero una prueba de *q*, después una de *p*. Una prueba de *p* ∨ *q* es una prueba de uno de los dos lados, con una etiqueta que dice cuál: `Or.inl` (izquierda) u `Or.inr` (derecha).","notas":{"1":"`constructor` empieza a construir el par: deja un hueco para cada componente.","2":"Primera componente: la segunda mitad de `h`.","3":"Segunda componente: la primera mitad. El par está completo.","4":"En los mensajes, `#print cambia` enseña el par terminado: `⟨h.right, h.left⟩`. Ahora, `left` elige la etiqueta de la izquierda, `Or.inl`, y deja un hueco para la prueba de *p*.","5":"El hueco se rellena con `hp`. El objeto es `Or.inl hp`."}},"archivo":"datos/trazas/21-prop-tipos-3.json"}
```

- `#print cambia` escribe `fun p q h => ⟨h.right, h.left⟩`. Los ángulos `⟨ , ⟩` construyen un par; `h.1` y `h.2` son otra forma de escribir `h.left` y `h.right`, las dos mitades.
- `#print izq` escribe `fun p q hp => Or.inl hp`. Una prueba de un «o» **lleva la etiqueta del lado** que se ha demostrado. Por eso, para usar un «o», hay que mirar la etiqueta: es el razonamiento por casos del capítulo 7.
- `constructor` y `left` no son magia: `constructor` usa el único constructor de `∧`, `And.intro`, y `left` usa el primero de los dos de `∨`, `Or.inl`. Las conectivas son tipos definidos con sus constructores, y se pueden ver con `#print And` y `#print Or`.

### 4 · «Para todo» es una función; «existe» es un par

```lean
import Mathlib

theorem todos : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl

#print todos

theorem hay : ∃ n : ℕ, n + n = 6 := by
  use 3

#print hay
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Funciones y testigos","etiqueta":"∀ · ∃ · fun · Exists.intro","idea":"Una prueba de ∀ *n*, *P n* es una función que, para cada *n*, da una prueba de *P n*. Una prueba de ∃ *n*, *P n* es un par: un *n* concreto, el testigo, y una prueba de que lo cumple.","notas":{"1":"«Sea *n* un natural cualquiera»: la función recibe un *n*.","2":"Para ese *n*, la prueba es `rfl`.","3":"`#print todos` enseña la función: `fun n => Eq.refl (n + 0)`. Para el «existe», el testigo es 3, y `use` comprueba él solo que 3 + 3 = 6. El objeto: `Exists.intro 3 (Eq.refl (3 + 3))`."}},"archivo":"datos/trazas/21-prop-tipos-4.json"}
```

- `#print todos` escribe `fun n => Eq.refl (n + 0)`: una función que, a cada *n*, le asigna una prueba de *n* + 0 = *n*. `Eq.refl` es el nombre completo de `rfl`.
- La diferencia con una implicación es que **el tipo del resultado depende de la entrada**: para *n* = 5 la función da una prueba de 5 + 0 = 5, y para *n* = 7, de 7 + 0 = 7. Son las funciones dependientes, y el capítulo 22 las mira de cerca.
- `#print hay` escribe `Exists.intro 3 (Eq.refl (3 + 3))`. Es el par ⟨testigo, prueba⟩, que también se puede escribir directamente: `⟨3, rfl⟩`.
- Por eso una prueba de «existe» siempre lleva **un ejemplo concreto dentro**. No basta con convencer de que hay uno: hay que darlo.

::::{div}
:class: afondo
### 5 · Falso, negación, y por qué todas las pruebas son iguales

```lean
import Mathlib

#print False
#print Not

example (p : Prop) (h : False) : p := by
  exact h.elim

example : ¬ False := by
  intro h
  exact h

example (h1 h2 : 2 + 2 = 4) : h1 = h2 := by
  rfl
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El tipo vacío","etiqueta":"a fondo · False · Not · irrelevancia de las pruebas","idea":"`False` es un tipo sin constructores: no hay manera de fabricar una prueba suya. `Not p` es, por definición, `p → False`. Y dos pruebas de la misma afirmación son, para Lean, el mismo objeto.","notas":{"1":"Si tuviéramos una prueba de False, tendríamos una de cualquier cosa: `h.elim` lo hace (*ex falso quodlibet*).","2":"¬False es False → False: se supone una prueba de False…","3":"…y se devuelve tal cual. Es la función identidad.","4":"Dos pruebas cualesquiera de 2 + 2 = 4 son iguales, y `rfl` lo ve sin más."}},"archivo":"datos/trazas/21-prop-tipos-5.json"}
```

`#print False` contesta `inductive False : Prop` con la lista de constructores **vacía**. Un tipo se define dando las formas de construir sus objetos; `False` no tiene ninguna. Por eso no hay pruebas de False, y por eso una contradicción es tan poderosa: si de verdad tuvieras una prueba `h : False`, `h.elim` la convierte en una prueba de cualquier cosa. No hay que construir nada, porque ese caso no puede darse.

`#print Not` contesta `fun a => a → False`. La negación no es una conectiva aparte: ¬*p* **es** *p* → False. Por eso, en el capítulo 8, demostrar ¬*p* empezaba con `intro`: hay que construir una función que, a partir de una prueba de *p*, llegue a False. Y ¬False es False → False, que se demuestra con la función identidad, `fun h => h`.

El último ejemplo es más extraño: dos pruebas `h1` y `h2` de la misma afirmación son iguales, y `rfl` lo acepta sin mirar cómo están hechas. Es la **irrelevancia de las pruebas**: en `Prop`, lo único que importa de una prueba es que existe, no cuál es. Con datos no pasa: dos naturales `a b : ℕ` no son iguales sin más, y `rfl` fallaría. Esa es la diferencia entre `Prop` y `Type`: en `Type` importa qué objeto tienes (el 3 no es el 5); en `Prop`, solo si tienes alguno.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«Si *p* → *q* y *q* → *r*, entonces *p* → *r*», escrito como una función, y lo que guarda cada sistema después de demostrarlo (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: la prueba es una función
example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)
-- #print tras la prueba con tácticas: fun p q r hpq hqr hp => hqr (hpq hp)
```

```coq
(* Rocq (Coq): también es una función *)
Lemma encadena (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r.
Proof.
  intro hp. apply hqr. apply hpq. exact hp.
Qed.
Print encadena.
(* encadena =
   fun (p q r : Prop) (hpq : p -> q) (hqr : q -> r) (hp : p) => hqr (hpq hp) *)
```

```isabelle
(* Isabelle: una proposición es un término de tipo bool *)
term "p \<longrightarrow> q"
(* "p \<longrightarrow> q" :: "bool" *)
lemma encadena: "(p \<longrightarrow> q) \<Longrightarrow> (q \<longrightarrow> r) \<Longrightarrow> p \<longrightarrow> r"
  by blast
```

Lean y Rocq comparten la idea de este capítulo: las dos están construidas sobre una teoría de tipos, y en las dos la prueba **es** un objeto. En Rocq, `Print encadena` enseña la misma función que en Lean, después de demostrarlo con tácticas. Isabelle/HOL funciona de otra manera: una proposición es un término de tipo `bool`, verdadero o falso, y un teorema no es un objeto de la lógica, sino algo aparte que solo el núcleo puede fabricar (es la arquitectura LCF). Las tres llegan a la misma seguridad, por caminos distintos.
:::

## Conexiones

- El capítulo 3 ya avisó: `#check conmuta 3 5` tenía por tipo la afirmación que demuestra.
- `fun h => ⟨h.2, h.1⟩` del capítulo 6 era una prueba escrita como término; ahora se ve que todas lo son.
- Las funciones del capítulo 2 (`fun n => n * n`) y las implicaciones son la misma cosa: `ℕ → ℕ` y `p → q` se escriben con la misma flecha porque son lo mismo.
- `intro` del capítulo 8 para ¬*p* se explica porque ¬*p* es *p* → False.
- `exact?` del capítulo 20 busca un **objeto** cuyo tipo sea la meta.

## La grieta

`Prop : Type`, decía `#check`. Pero entonces, ¿cuál es el tipo de `Type`? Si fuese `Type`, tendríamos un tipo que se contiene a sí mismo, y eso, como la paradoja del barbero, da problemas. Lean contesta `Type : Type 1`, y `Type 1 : Type 2`, y así sin fin: una escalera de **universos**. Y en el apartado 4 apareció una función cuyo tipo de salida dependía de la entrada. Las dos cosas son el tema de **Tipos dependientes y universos**.

## Ejercicios

1. **La identidad.** Escribe, sin tácticas, una prueba de `p → p`.

2. **Encadenar dos veces.** Escribe, sin tácticas, una prueba de `(p → q) → (q → r) → p → r`. ¿Cuántas entradas tiene la función?

3. **Elegir un lado.** Escribe, sin tácticas, una prueba de `p → q ∨ p`. ¿Qué etiqueta lleva?

4. **Un testigo.** Escribe, sin tácticas, una prueba de `∃ n : ℕ, n + n = 10`.

5. **El tipo de una prueba.** ¿Qué contesta `#check Nat.le_refl 5`? ¿Qué demuestra ese objeto?

6. **La negación de lo falso.** Escribe, sin tácticas, una prueba de `¬ False`.

::::{div}
:class: afondo
7. **Ex falso.** Escribe, sin tácticas, una prueba de `False → p` para una *p* cualquiera.

8. **¿Pruebas iguales?** Demuestra con `rfl` que dos pruebas `h1 h2 : 3 < 5` son iguales. ¿Por qué no se puede demostrar igual que dos naturales `a b : ℕ` son iguales?
::::

## Solucionario

1. `example (p : Prop) : p → p := fun h => h`. Recibe una prueba de *p* y la devuelve tal cual.
2. `example (p q r : Prop) : (p → q) → (q → r) → p → r := fun hpq hqr hp => hqr (hpq hp)`. Tres entradas: las dos implicaciones y la prueba de *p*.
3. `example (p q : Prop) : p → q ∨ p := fun hp => Or.inr hp`. La etiqueta de la derecha, `Or.inr`, porque *p* está a la derecha del «o».
4. `example : ∃ n : ℕ, n + n = 10 := ⟨5, rfl⟩`. El testigo es 5, y `rfl` comprueba 5 + 5 = 10 calculando.
5. `Nat.le_refl 5 : 5 ≤ 5`. Es una prueba de que 5 ≤ 5: `Nat.le_refl` es la propiedad reflexiva, aplicada al 5.
6. `example : ¬ False := fun h => h`. ¬False es False → False, y la identidad sirve.

::::{div}
:class: afondo
7. `example (p : Prop) : False → p := fun h => h.elim`. También vale `False.elim`.
8. `example (h1 h2 : 3 < 5) : h1 = h2 := rfl`. Funciona por la irrelevancia de las pruebas: en `Prop`, dos pruebas de lo mismo son el mismo objeto. Con `a b : ℕ`, `a = b` no es cierto en general (puede ser *a* = 1 y *b* = 2): los naturales son datos, viven en `Type`, y ahí cada objeto es distinto.
::::
