---
title: Implicación y conjunción
subtitle: «Si… entonces…» e «y», las dos piezas más usadas de la lógica
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Casi todos los teoremas tienen la misma forma: **si** se cumple algo, **entonces** se cumple otra cosa. Si un triángulo es rectángulo, entonces *a*² + *b*² = *c*². Si *n* es par, entonces *n*² es par. Y muchas veces las hipótesis vienen de dos en dos: si *x* = 2 **y** *y* = 3…

En la pizarra, para demostrar un «si… entonces…» se empieza con «supongamos que…». Para usar uno que ya sabes, se comprueba la condición y se saca la conclusión. Con «y», hay que demostrar las dos partes, y si lo sabes, sabes cada una por separado.

Lean hace exactamente esto, con una táctica para cada gesto.

## La pregunta

¿Cómo se demuestra un «si *p*, entonces *q*» en Lean? ¿Cómo se usa uno que ya está demostrado? ¿Y cómo se construye o se descompone una «y»?

## La idea

Cada conectiva lógica tiene dos reglas: una para **demostrarla** (cuando está en la meta) y otra para **usarla** (cuando está en una hipótesis).

| Conectiva | Se escribe | Demostrarla (en la meta) | Usarla (en una hipótesis `h`) |
|---|---|---|---|
| si *p*, entonces *q* | `p → q` | `intro hp`: supones *p*, y la meta pasa a ser *q* | `h hp`: con una prueba de *p*, obtienes *q*. O `apply h`: para demostrar *q*, basta *p* |
| *p* y *q* | `p ∧ q` | `constructor`: dos metas, *p* y *q*. O `⟨hp, hq⟩` | `obtain ⟨hp, hq⟩ := h`: separa las dos. O `h.1` y `h.2` |

:::{important} Demostrar y usar
Cuando una prueba se atasca, la pregunta es siempre la misma: ¿qué forma tiene la meta, y qué forma tienen las hipótesis? La forma de la meta dice qué táctica la **demuestra**. La de cada hipótesis, qué táctica la **usa**.
:::

## Construcción

### 1 · Demostrar un «si… entonces…»

:::{tip} Predice
La meta es `∀ n : ℕ, n = 3 → n + 1 = 4`. ¿Qué aparecerá en el panel tras `intro n h`?
:::

```lean
import Mathlib

example : ∀ n : ℕ, n = 3 → n + 1 = 4 := by
  intro n h
  rw [h]

example (x : ℝ) : x > 2 → 2 * x > 4 := by
  intro hx
  linarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Supongamos que…","etiqueta":"→ · intro","idea":"Para demostrar «si *p*, entonces *q*», se supone *p* y se demuestra *q*. `intro` hace las dos cosas: pone *p* entre las hipótesis y deja *q* como meta.","notas":{"1":"`intro n h` hace dos cosas: «sea *n* un natural» y «supongamos que *n* = 3». El ∀ y la flecha desaparecen de la meta.","2":"Con `h`, el resto es una reescritura.","3":"«Supongamos que *x* > 2.» La flecha desaparece y `hx : x > 2` pasa a las hipótesis.","4":"`linarith` combina desigualdades lineales: de *x* > 2 saca 2*x* > 4."}},"archivo":"datos/trazas/06-implicacion-1.json"}
```

- `p → q` se lee «si *p*, entonces *q*», o «*p* implica *q*». La flecha se escribe `\to` o `->`.
- `intro h` quita la primera flecha de la meta y guarda lo que había delante como hipótesis `h`. Es el «supongamos que…» de la pizarra.
- `intro` es la misma táctica que con ∀ en el capítulo 3. Para Lean, «para todo *n*» y «si *p*» se tratan igual: en los dos casos se toma algo y se sigue.
- `intro n h` introduce dos cosas seguidas: el número y la hipótesis.
- `linarith` demuestra desigualdades que salen sumando y multiplicando por números las hipótesis. Funciona en ℝ, en ℚ y en ℤ.

### 2 · Usar un «si… entonces…»

Tienes una implicación entre las hipótesis. ¿Cómo se usa?

```lean
import Mathlib

example (p q : Prop) (h : p → q) (hp : p) : q := by
  exact h hp

example (x : ℝ) (h : x > 2 → x ^ 2 > 4) (hx : x > 2) : x ^ 2 > 4 := by
  apply h
  exact hx
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Si se cumple la condición…","etiqueta":"→ · exact h hp · apply","idea":"Una implicación `h : p → q` se usa de dos formas: hacia delante, `h hp` es una prueba de *q*; hacia atrás, `apply h` cambia la meta *q* por *p*.","notas":{"1":"`h hp`: la implicación aplicada a una prueba de *p* da una prueba de *q*. Como un teorema con su caso concreto.","2":"Hacia atrás: «para demostrar *x*² > 4, basta ver que *x* > 2». La meta cambia por la condición de `h`.","3":"Y la condición está en `hx`."}},"archivo":"datos/trazas/06-implicacion-2.json"}
```

- **Hacia delante.** Si `h : p → q` y `hp : p`, entonces `h hp` es una prueba de `q`. Se escribe como aplicar una función a un número: `h` aplicada a `hp`.
- **Hacia atrás.** `apply h` mira la conclusión de `h`. Si coincide con la meta, cambia la meta por la condición. Es el «basta con ver que…» de la pizarra.
- En matemáticas esta regla se llama ***modus ponens***: de «si *p*, entonces *q*» y de *p*, se deduce *q*.

### 3 · Construir y separar una «y»

```lean
import Mathlib

example (x y : ℕ) (hx : x = 2) (hy : y = 3) : x + y = 5 ∧ x * y = 6 := by
  constructor
  · rw [hx, hy]
  · rw [hx, hy]

example (x y : ℕ) (h : x = 2 ∧ y = 3) : x + y = 5 := by
  obtain ⟨hx, hy⟩ := h
  rw [hx, hy]

example (x y : ℕ) (h : x = 2 ∧ y = 3) : x + y = 5 := by
  rw [h.1, h.2]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una «y» se construye por partes y se usa por partes","etiqueta":"∧ · constructor · obtain · .1 .2","idea":"Para demostrar `p ∧ q`, se demuestran las dos. Si sabes `p ∧ q`, sabes cada una: `obtain` las separa en dos hipótesis.","notas":{"1":"Una meta con «y» se parte en dos, como en el capítulo 4.","4":"`obtain ⟨hx, hy⟩ := h` cambia la hipótesis `h` por sus dos mitades, cada una con su nombre.","6":"Sin separar: `h.1` es la primera mitad de `h` y `h.2`, la segunda."}},"archivo":"datos/trazas/06-implicacion-3.json"}
```

- `∧` se escribe `\and`. `p ∧ q` es verdadera cuando lo son las dos.
- Para demostrarla, `constructor` la parte en dos metas, y cada una se cierra por su lado.
- Para usarla, `obtain ⟨hx, hy⟩ := h` saca las dos mitades como hipótesis con nombre. Los ángulos `⟨ ⟩` se escriben `\<` y `\>`.
- `h.1` y `h.2` son las dos mitades sin sacarlas del contexto. Van bien cuando se usan una sola vez.

### 4 · Juntar las dos piezas

:::{tip} Predice
Para demostrar `p ∧ q → q ∧ p`, ¿qué táctica va primero: la de la flecha o la de la «y»?
:::

```lean
import Mathlib

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

example (p q r : Prop) (h : p → q → r) (hp : p) (hq : q) : r := by
  exact h hp hq

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"De fuera hacia dentro","etiqueta":"intro · obtain · ⟨ , ⟩ · apply","idea":"La forma de la meta manda. Si es una flecha, `intro`. Si es una «y», se construye. Y lo que llega a las hipótesis se usa según su forma.","notas":{"1":"La meta es una flecha: `intro`. Lo de delante, `p ∧ q`, pasa a las hipótesis.","2":"`h` es una «y»: se separa.","3":"`⟨hq, hp⟩` construye `q ∧ p` de golpe, sin `constructor`.","4":"`p → q → r` se lee «si *p*, entonces, si *q*, entonces *r*». Con las dos pruebas, `h hp hq` da *r*.","5":"Tres flechas, tres hipótesis. Queda la meta `r`.","6":"Para tener `r`, basta `q`…","7":"…y para tener `q`, basta `p`…","8":"…que está en `hp`."}},"archivo":"datos/trazas/06-implicacion-4.json"}
```

- La meta `p ∧ q → q ∧ p` es una flecha: lo primero es `intro`. La «y» de las hipótesis se separa después, y la de la meta se construye al final. Se trabaja **de fuera hacia dentro**.
- `⟨hq, hp⟩` construye una «y» en una sola expresión: primero la prueba de la izquierda, después la de la derecha.
- `p → q → r` significa `p → (q → r)`: la flecha agrupa por la derecha. Por eso `h hp hq` funciona: `h hp` es una prueba de `q → r`, y aplicada a `hq` da `r`.
- El último ejemplo es la **transitividad** de la implicación: si *p* implica *q* y *q* implica *r*, *p* implica *r*. Con `apply` se razona hacia atrás, de la meta a lo que la garantiza.

::::{div}
:class: afondo
### 5 · Una implicación es una función

En el capítulo 3 vimos que una prueba tiene por tipo lo que demuestra. ¿Y una prueba de `p → q`?

```lean
import Mathlib

example (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩

theorem intercambia (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

#check intercambia
#check (intercambia)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Pruebas que transforman pruebas","etiqueta":"a fondo · fun · →","idea":"Una prueba de `p → q` es una función: toma una prueba de *p* y devuelve una de *q*. El primer ejemplo no usa tácticas: escribe la función directamente.","notas":{"1":"`intro` también puede separar al entrar: `⟨hp, hq⟩` hace el `obtain` en el mismo paso.","2":"Y se construye la «y» al revés."}},"archivo":"datos/trazas/06-implicacion-5.json"}
```

El primer ejemplo no tiene `by`: es la prueba escrita **directamente**, sin tácticas. `fun h => ⟨h.2, h.1⟩` es una función, como `fun n => n * n` del capítulo 2. Toma una prueba `h` de `p ∧ q` y devuelve una prueba de `q ∧ p`, hecha con sus mitades al revés.

Esto no es una coincidencia: en Lean, **una prueba de `p → q` es una función** que convierte pruebas de *p* en pruebas de *q*. La flecha de la implicación y la flecha de las funciones, `ℕ → ℕ`, son la misma flecha. Por eso `h hp` se escribe como aplicar una función, y por eso `intro` sirve para las dos cosas.

`#check intercambia` da su firma, `intercambia (p q : Prop) : p ∧ q → q ∧ p`. Con paréntesis, `#check (intercambia)` da el tipo completo: `∀ (p q : Prop), p ∧ q → q ∧ p`. El teorema es una función de tres entradas: las dos proposiciones, que van tras el `∀`, y la prueba de `p ∧ q`. Devuelve una prueba de `q ∧ p`. Es la idea de **proposiciones como tipos**, que la parte V desarrolla.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«Si *p* y *q*, entonces *q* y *p*» (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
theorem intercambia (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
```

```coq
(* Rocq (Coq): intros, destruct, split *)
Theorem intercambia : forall p q : Prop, p /\ q -> q /\ p.
Proof.
  intros p q h.
  destruct h as [hp hq].
  split.
  - exact hq.
  - exact hp.
Qed.
```

```isabelle
(* Isabelle: una regla para cada paso *)
lemma "p & q --> q & p"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
  done
```

Los tres dan los mismos pasos con otros nombres: `intro` es `intros` en Rocq y `rule impI` en Isabelle; `obtain` es `destruct` y `erule conjE`; `constructor` es `split` y `rule conjI`. Isabelle nombra cada regla de la lógica: `impI` es la que *introduce* la implicación, `conjE` la que *elimina* la conjunción. Son las mismas dos reglas de la tabla de este capítulo, «demostrar» y «usar», que en lógica se llaman **introducción** y **eliminación**. Tras `erule conjE`, Isabelle enseña la meta como `⟦p; q⟧ ⟹ q ∧ p`: las dos mitades ya separadas, como hipótesis.
:::

## Conexiones

- `intro` ya salió en el capítulo 3 con el ∀, y `constructor` en el capítulo 4. Ahora tienen su sitio: son las reglas para **demostrar** el ∀, la flecha y la «y».
- `obtain` salió en la primera prueba del libro, en el capítulo 0, para separar «existe *k* tal que *n* = *k* + *k*». El capítulo 9 explica por qué funciona igual que con la «y».
- `exact h hp` es lo mismo que `exact conmuta 3 5` del capítulo 3: aplicar un resultado a casos concretos.
- La flecha como función vuelve en la parte V, en **proposiciones como tipos**.

## La grieta

Con «y» se pide todo: las dos partes. ¿Y con «o»? Para demostrar «*n* es par o *n* es impar» basta con una de las dos, pero ¿cuál? Y si sabes que «*x* = 2 o *x* = −2», no sabes cuál de las dos es: hay que razonar en los dos casos. Lo vemos en **Disyunción y casos**.

## Ejercicios

1. **Una hipótesis que sobra.** Con `hp : p`, demuestra `q → p`. ¿Se usa lo que introduces?

2. **Suponer y sustituir.** Demuestra `x = 4 → x * 2 = 8`, con `x : ℕ`.

3. ***Modus ponens*.** Con `h : x > 10 → x > 5` y `hx : x > 10`, demuestra `x > 5` en una sola línea.

4. **Separar.** Con `h : a = 1 ∧ b = 2`, demuestra `b + a = 3`.

5. **Media «y».** Demuestra `p ∧ q → p`.

6. **En una línea.** Demuestra `(p → q) → (q → r) → p → r` con un solo `intro` y un solo `exact`.

::::{div}
:class: afondo
7. **Dos formas de decir lo mismo.** Demuestra `(p → q → r) → (p ∧ q → r)`. ¿Qué dice en castellano?

8. **La función más sencilla.** ¿Qué tipo da `#check fun (hp : p) => hp`, con `p : Prop`? ¿Qué teorema es?
::::

## Solucionario

1. ```lean
   example (p q : Prop) (hp : p) : q → p := by
     intro _
     exact hp
   ```
   No se usa: la hipótesis de *q* sobra, y por eso se le puede dar el nombre `_`. Lo verdadero lo sigue siendo con más hipótesis.
2. ```lean
   example (x : ℕ) : x = 4 → x * 2 = 8 := by
     intro h
     rw [h]
   ```
3. `exact h hx`.
4. ```lean
   example (a b : ℕ) (h : a = 1 ∧ b = 2) : b + a = 3 := by
     obtain ⟨ha, hb⟩ := h
     rw [ha, hb]
   ```
5. `intro h` y `exact h.1`.
6. ```lean
   example (p q r : Prop) : (p → q) → (q → r) → p → r := by
     intro hpq hqr hp
     exact hqr (hpq hp)
   ```
   `hpq hp` es una prueba de *q*, y `hqr` aplicada a ella da *r*.

::::{div}
:class: afondo
7. ```lean
   example (p q r : Prop) : (p → q → r) → (p ∧ q → r) := by
     intro h ⟨hp, hq⟩
     exact h hp hq
   ```
   «Si *p* implica que *q* implica *r*, entonces *p* y *q* juntos implican *r*». Pedir dos condiciones una tras otra es lo mismo que pedirlas a la vez.
8. `fun hp => hp : p → p`. Es la prueba de «si *p*, entonces *p*»: la función que devuelve lo que recibe.
::::
