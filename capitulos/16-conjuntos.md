---
title: Conjuntos
subtitle: Pertenecer, estar contenido, ser iguales: todo se reduce a lógica
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Los conjuntos están en todas partes: los números pares, los primos, el dominio de una función, las soluciones de una ecuación, el intervalo (0, 1). En la pizarra se dibujan como diagramas de Venn y se trabaja con ellos de forma bastante visual: la intersección es la zona común, la unión es todo junto.

Pero un diagrama no es una demostración. Para demostrar que *A* ∩ *B* ⊆ *A*, o que dos conjuntos son iguales, hay que bajar a los elementos: «sea *x* un elemento cualquiera…». Y ahí los conjuntos se convierten en lógica: ∩ es «y», ∪ es «o», ⊆ es «si… entonces», el complementario es «no». Todo lo de la parte II sirve aquí tal cual.

## La pregunta

¿Cómo se escribe un conjunto en Lean? ¿Cómo se demuestra que un elemento pertenece a él, que un conjunto está contenido en otro, o que dos conjuntos son iguales?

## La idea

Cada operación con conjuntos es una conectiva lógica disfrazada. Por eso las tácticas son las mismas de la parte II:

| Conjuntos | Significa | Lógica | Para demostrarlo |
|---|---|---|---|
| *x* ∈ {*x* ∣ *p x*} | *x* cumple *p* | *p x* | lo que pida *p* |
| *A* ⊆ *B* | todo elemento de *A* está en *B* | ∀ *x*, *x* ∈ *A* → *x* ∈ *B* | `intro x hx` |
| *x* ∈ *A* ∩ *B* | *x* está en los dos | *x* ∈ *A* ∧ *x* ∈ *B* | `constructor` / `⟨_, _⟩` |
| *x* ∈ *A* ∪ *B* | *x* está en alguno | *x* ∈ *A* ∨ *x* ∈ *B* | `left` / `right` |
| *x* ∈ *A*ᶜ | *x* no está en *A* | ¬(*x* ∈ *A*) | `intro` |
| *A* = *B* | tienen los mismos elementos | ∀ *x*, *x* ∈ *A* ↔ *x* ∈ *B* | `ext x` |

:::{important} Un conjunto tiene elementos de un solo tipo
En Lean, un conjunto es siempre un `Set α`: un conjunto de naturales, de reales… El tipo va delante. `{x : ℕ | Even x}` es el conjunto de los naturales pares, de tipo `Set ℕ`.
:::

## Construcción

### 1 · Pertenecer

```lean
import Mathlib

example : (4 : ℕ) ∈ {x : ℕ | Even x} := by
  show Even 4
  use 2

example : (3 : ℕ) ∉ {x : ℕ | Even x} := by
  decide
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Ser elemento es cumplir la condición","etiqueta":"∈ · show · use · decide","idea":"*x* ∈ {*x* ∣ *p x*} significa, sin más, que *x* cumple *p*. `show` lo hace visible: la meta pasa de «4 está en los pares» a «4 es par».","notas":{"1":"La meta es la misma, dicha de otra forma: pertenecer a {*x* ∣ *x* es par} es ser par.","2":"Y 4 es par porque 4 = 2 + 2 (capítulo 9: `Even n` es ∃ *r*, *n* = *r* + *r*).","3":"`decide` comprueba que 3 no es par: con números concretos, la condición se calcula."}},"archivo":"datos/trazas/16-conjuntos-1.json"}
```

- `{x : ℕ | Even x}` se lee «el conjunto de los *x* naturales tales que *x* es par». La barra vertical es la de toda la vida: «tales que».
- Pertenecer a ese conjunto es lo mismo que cumplir la condición. `show Even 4` no cambia nada: solo dice la meta con otras palabras, y Lean comprueba que son la misma.
- `∉` es «no pertenece»: `3 ∉ S` es `¬ (3 ∈ S)`. Con números concretos y una condición que se puede calcular, `decide` lo resuelve.

### 2 · Estar contenido

:::{tip} Predice
Si *A* ⊆ *B* significa «todo elemento de *A* está en *B*», ¿qué hará `intro` con esa meta?
:::

```lean
import Mathlib

example : {x : ℕ | x > 5} ⊆ {x : ℕ | x > 3} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at *
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Sea x un elemento cualquiera","etiqueta":"⊆ · intro · simp only","idea":"*A* ⊆ *B* es un «para todo *x*, si *x* ∈ *A*, entonces *x* ∈ *B*». `intro x hx` toma el elemento y la hipótesis; lo que queda es aritmética.","notas":{"1":"Un elemento cualquiera *x* y la hipótesis de que está en el primer conjunto. La meta: que está en el segundo.","2":"Se quita el disfraz de conjunto: `hx : x > 5` y la meta `x > 3`.","3":"De *x* > 5 sale *x* > 3."}},"archivo":"datos/trazas/16-conjuntos-2.json"}
```

- *A* ⊆ *B* es por dentro un ∀ y una →, así que `intro x hx` hace lo de siempre: «sea *x* un elemento cualquiera, y supongamos que *x* ∈ *A*».
- Tras el `intro`, el panel enseña `hx : x ∈ {x | x > 5}` y la meta `x ∈ {x | x > 3}`. El teorema `Set.mem_ofPred_eq` dice que pertenecer a {*y* ∣ *p y*} es cumplir *p*, y `simp only [...] at *` lo aplica en todas partes.
- A partir de ahí no queda nada de conjuntos: `omega` cierra.
- El nombre antiguo de ese teorema, `Set.mem_setOf_eq`, sigue funcionando, pero Lean avisa de que está obsoleto y propone el nuevo.

### 3 · Intersección y unión

```lean
import Mathlib

example (A B : Set ℕ) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

example (A B : Set ℕ) : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"∩ es «y», ∪ es «o»","etiqueta":"∩ · ∪ · .1 · left","idea":"Un elemento de *A* ∩ *B* está en *A* y en *B*: de un «y» se saca cada mitad con `.1` y `.2`. Para estar en *A* ∪ *B* basta estar en uno: se elige con `left` o `right`.","notas":{"1":"`hx : x ∈ A ∩ B`: *x* está en *A* y en *B*.","2":"La primera mitad del «y» es justo lo que se pide.","3":"Ahora `hx : x ∈ A` y la meta `x ∈ A ∪ B`.","4":"Para estar en la unión, basta con estar en *A*: el lado izquierdo del «o».","5":"Y eso es `hx`."}},"archivo":"datos/trazas/16-conjuntos-3.json"}
```

- `x ∈ A ∩ B` es, por definición, `x ∈ A ∧ x ∈ B`. Por eso `hx.1` es la prueba de `x ∈ A` y `hx.2` la de `x ∈ B`, como con cualquier «y» (capítulo 6).
- `x ∈ A ∪ B` es `x ∈ A ∨ x ∈ B`, y para demostrar un «o» se elige un lado (capítulo 7).
- *A* y *B* son conjuntos cualesquiera de naturales: la prueba no mira qué elementos tienen. Vale igual para cualquier tipo.

### 4 · Ser iguales: `ext`

Dos conjuntos son iguales si tienen los mismos elementos. Es el **principio de extensionalidad**, y en Lean se usa con `ext`: toma un elemento cualquiera y pide demostrar que está en uno si y solo si está en el otro.

```lean
import Mathlib

example (A B : Set ℕ) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨hb, ha⟩
  · rintro ⟨hb, ha⟩
    exact ⟨ha, hb⟩
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Mismos elementos, mismo conjunto","etiqueta":"ext · constructor · rintro","idea":"`ext x` cambia la igualdad de conjuntos por un «si y solo si» sobre un elemento *x*. Cada sentido es un «y» que se desmonta y se vuelve a montar al revés.","notas":{"1":"La meta pasa a ser `x ∈ A ∩ B ↔ x ∈ B ∩ A`.","2":"Un ↔ son dos implicaciones: una meta por sentido.","3":"Se supone *x* ∈ *A* ∩ *B* y se desmonta: `ha : x ∈ A`, `hb : x ∈ B`.","4":"Se monta el «y» en el otro orden.","5":"El sentido contrario, igual.","6":"Y la igualdad queda demostrada."}},"archivo":"datos/trazas/16-conjuntos-4.json"}
```

- `ext x` es la táctica de la extensionalidad. Su teorema, `Set.ext`, dice: si para todo *x*, *x* ∈ *A* ↔ *x* ∈ *B*, entonces *A* = *B*.
- Tras `ext x`, la igualdad de conjuntos se ha convertido en un «si y solo si», y `constructor` lo parte en sus dos implicaciones.
- Cada sentido es la conmutativa del «y»: es la misma prueba que `p ∧ q → q ∧ p` del capítulo 6.
- Casi todas las igualdades de conjuntos se demuestran así: `ext x` y lógica.

::::{div}
:class: afondo
### 5 · De Morgan, y qué es un conjunto en Lean

Las leyes de De Morgan de la lógica (capítulo 8) tienen su versión con conjuntos: el complementario de una unión es la intersección de los complementarios.

```lean
import Mathlib

example (A B : Set ℕ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]
  push Not
  rfl

example (A B : Set ℕ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  exact Set.compl_union A B

#print Set
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"De Morgan para conjuntos","etiqueta":"a fondo · ext · simp only · push Not · Set","idea":"Tras `ext x` y quitar el disfraz de conjunto, la meta es De Morgan en lógica: ¬(*p* ∨ *q*) ↔ ¬*p* ∧ ¬*q*. Mathlib lo tiene ya demostrado como `Set.compl_union`.","notas":{"1":"La meta: *x* ∈ (*A* ∪ *B*)ᶜ ↔ *x* ∈ *A*ᶜ ∩ *B*ᶜ.","2":"Se traduce cada símbolo: `¬(x ∈ A ∨ x ∈ B) ↔ x ∉ A ∧ x ∉ B`. Ya es lógica pura.","3":"La negación entra en el «o» y lo convierte en «y»: los dos lados quedan idénticos.","4":"Y lo que es idéntico se cierra con `rfl`.","5":"Lo mismo en una línea, con el teorema de Mathlib (lo encuentra `exact?`)."}},"archivo":"datos/trazas/16-conjuntos-5.json"}
```

`simp only` con tres teoremas traduce los símbolos de conjuntos a lógica: `Set.mem_compl_iff` (estar en el complementario es no estar), `Set.mem_union` (estar en la unión es estar en uno u otro) y `Set.mem_inter_iff` (estar en la intersección es estar en los dos). Después, `push Not` hace el De Morgan lógico.

El teorema de Mathlib se llama `Set.compl_union`, y para encontrarlo no hace falta saber el nombre: `exact?` lo busca y propone `exact Set.compl_union A B`. Lo veremos con calma en el capítulo 20.

¿Y qué es un conjunto por dentro? `#print Set` responde: una estructura con un solo campo, `Set.Mem : α → Prop`. Es decir, un conjunto es una propiedad envuelta: el conjunto de los pares no es más que la propiedad «ser par», guardada en una caja. Por eso pertenecer es cumplir la propiedad, y por eso todas las pruebas de este capítulo acaban siendo lógica. (En versiones anteriores de Mathlib, `Set α` era directamente `α → Prop`, sin caja; la idea es la misma.)
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
*A* ∩ *B* ⊆ *A* (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example (A B : Set ℕ) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1
```

```coq
(* Rocq (Coq) *)
Require Import Ensembles.
Lemma inter_sub : forall (U : Type) (A B : Ensemble U),
  Included U (Intersection U A B) A.
Proof.
  intros U A B x h.
  destruct h as [x ha hb].
  exact ha.
Qed.
```

```isabelle
(* Isabelle *)
lemma inter_sub: "A \<inter> B \<subseteq> A"
  apply (rule subsetI)
  apply (erule IntE)
  apply assumption
  done
```

Los tres hacen lo mismo: tomar un elemento de la intersección, partirlo en sus dos pertenencias y quedarse con la primera. En Rocq, los conjuntos de la biblioteca estándar se llaman `Ensemble` y la intersección es un tipo inductivo, así que se desmonta con `destruct`. En Isabelle, `subsetI` toma el elemento y `IntE` parte la intersección; en el archivo se escribe `\<inter>` y `\<subseteq>`, que el editor enseña como ∩ y ⊆.
:::

## Conexiones

- Cada operación con conjuntos es una conectiva de la parte II: ∩ es ∧ (capítulo 6), ∪ es ∨ (capítulo 7), el complementario es ¬ (capítulo 8), ⊆ es ∀ y → (capítulo 9).
- La extensionalidad (`ext`) vale también para funciones: dos funciones son iguales si dan lo mismo en cada punto. Volverá en el capítulo 17.
- `ZMod 5` del capítulo 15 es un tipo con cinco elementos; los conjuntos son otra cosa: subconjuntos de un tipo. La diferencia entre tipos y conjuntos vuelve en la parte V.

## La grieta

Una función lleva cada elemento de un conjunto a otro. ¿Cuándo no hay dos elementos que vayan al mismo sitio? ¿Cuándo llega a todos los elementos del conjunto de llegada? ¿Y cuándo tiene inversa? Son las funciones inyectivas, sobreyectivas y biyectivas, y se demuestran con todo lo que ya tenemos. Lo vemos en **Funciones: inyectiva y sobreyectiva**.

## Ejercicios

1. **Múltiplos de 3.** Demuestra `(6 : ℕ) ∈ {x : ℕ | 3 ∣ x}`.

2. **Con reales.** Demuestra `{x : ℝ | x > 2} ⊆ {x : ℝ | x > 0}`. ¿Qué táctica cierra al final?

3. **Dentro de la unión.** Demuestra `A ∩ B ⊆ A ∪ B` para *A*, *B* de tipo `Set ℕ`.

4. **La unión conmuta.** Demuestra `A ∪ B = B ∪ A` con `ext x`.

5. **Contenido.** Con `h : A ⊆ B`, demuestra `A ∩ B = A`. Pista: en un sentido, `hx.1`; en el otro, `⟨hx, h hx⟩`.

6. **No pertenece.** Demuestra `(7 : ℕ) ∉ {x : ℕ | Even x}`.

::::{div}
:class: afondo
7. **La distributiva.** Demuestra `A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C` con `ext x`, `simp only [Set.mem_inter_iff, Set.mem_union]` y `tauto`. Busca después el nombre del teorema con `exact?`.

8. **El complementario.** Demuestra `x ∈ Aᶜ ↔ x ∉ A` con `rfl`. ¿Por qué basta `rfl`?
::::

## Solucionario

1. `use 2`: 6 = 3 · 2.
2. ```lean
   example : {x : ℝ | x > 2} ⊆ {x : ℝ | x > 0} := by
     intro x hx
     simp only [Set.mem_ofPred_eq] at *
     linarith
   ```
   `linarith`, porque con reales `omega` no sirve.
3. `intro x hx`, `left`, `exact hx.1`.
4. ```lean
   example (A B : Set ℕ) : A ∪ B = B ∪ A := by
     ext x
     constructor
     · rintro (ha | hb)
       · right; exact ha
       · left; exact hb
     · rintro (hb | ha)
       · right; exact hb
       · left; exact ha
   ```
5. ```lean
   example (A B : Set ℕ) (h : A ⊆ B) : A ∩ B = A := by
     ext x
     constructor
     · intro hx
       exact hx.1
     · intro hx
       exact ⟨hx, h hx⟩
   ```
   `h hx` aplica la inclusión al elemento: de *x* ∈ *A* saca *x* ∈ *B*. (En una línea: `Set.inter_eq_left.mpr h`.)
6. `decide`.

::::{div}
:class: afondo
7. Con `ext x`, `simp only [...]` y `tauto` sale. `exact?` propone `exact Set.inter_union_distrib_left A B C`.
8. Porque es la definición: estar en el complementario es, literalmente, no estar en *A*. Las dos expresiones son la misma por dentro, y `rfl` lo comprueba.
::::
