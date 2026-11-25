---
title: Disyunción y casos
subtitle: «O» se demuestra eligiendo un lado, y se usa razonando por casos
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

«Si *x*² = 4, entonces *x* = 2 o *x* = −2.» Esa «o» es distinta de la «y» del capítulo anterior. Con «y» hay que tener las dos cosas. Con «o» basta una, y a veces no se sabe cuál.

Esto cambia la forma de razonar. Para **demostrar** una «o», hay que elegir un lado y demostrar ese. Para **usarla**, como no sabes cuál de los dos es cierto, hay que razonar en los dos casos: «si *x* = 2, entonces…; si *x* = −2, entonces…». Es la demostración por casos de toda la vida.

## La pregunta

¿Cómo elige Lean un lado de una «o»? ¿Cómo se parte una prueba en casos? ¿Y qué pasa cuando los casos no vienen de ninguna hipótesis, como «*n* es par o *n* es impar»?

## La idea

La disyunción tiene sus dos reglas, como la implicación y la conjunción:

| Conectiva | Se escribe | Demostrarla (en la meta) | Usarla (en una hipótesis `h`) |
|---|---|---|---|
| *p* o *q* | `p ∨ q` | `left`: demuestras *p*. `right`: demuestras *q* | `rcases`: dos metas, una con *p* y otra con *q* |

- `∨` se escribe `\or`. Es la «o» inclusiva de las matemáticas: `p ∨ q` es cierta si lo es al menos una.
- `left` y `right` eligen lado. Si eliges mal, la meta que queda no se puede demostrar.
- `rcases h with hp | hq` parte la prueba en dos: en una, `hp : p`; en la otra, `hq : q`. Las dos metas son la misma, y hay que cerrarlas las dos.

:::{important} Casos que no vienen de una hipótesis
Muchas veces los casos los pones tú: *n* es par o impar, *a* ≤ *b* o *b* ≤ *a*, *x* cumple algo o no lo cumple. Mathlib tiene esas «o» demostradas, como `Nat.even_or_odd n`. Y `by_cases h : p` parte en «*p*» y «no *p*» para cualquier afirmación.
:::

## Construcción

### 1 · Demostrar una «o»: elegir un lado

:::{tip} Predice
Con `h : n = 3`, para demostrar `n = 3 ∨ n = 5`, ¿qué lado eliges? ¿Qué pasaría con el otro?
:::

```lean
import Mathlib

example (n : ℕ) (h : n = 3) : n = 3 ∨ n = 5 := by
  left
  exact h

example : 2 ^ 10 > 1000 ∨ 2 ^ 10 < 1000 := by
  left
  norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Basta con un lado","etiqueta":"∨ · left · right","idea":"Para demostrar una «o», se elige el lado que es cierto. `left` se queda con el de la izquierda y `right` con el de la derecha; el otro desaparece.","notas":{"1":"`left`: de `n = 3 ∨ n = 5` queda solo `n = 3`.","2":"Y eso es justo `h`.","3":"2¹⁰ = 1024: el lado cierto es el de la izquierda.","4":"`norm_num` hace la cuenta."}},"archivo":"datos/trazas/07-disyuncion-1.json"}
```

- `left` cambia la meta `p ∨ q` por `p`, y `right` la cambia por `q`. La otra parte de la «o» se olvida.
- La elección es tuya, y no tiene vuelta atrás: si eliges el lado falso, te quedas con una meta imposible. En el primer ejemplo, `right` dejaría `n = 5`, y con `h : n = 3` no hay forma de demostrarlo.
- Por eso, antes de elegir, conviene saber cuál de los dos lados es cierto. En el segundo ejemplo, hay que hacer la cuenta: 2¹⁰ = 1024.

### 2 · Usar una «o»: razonar por casos

:::{tip} Predice
Con `h : x = 2 ∨ x = -2`, ¿cuántas metas quedarán tras `rcases h with h1 | h2`? ¿Qué hipótesis tendrá cada una?
:::

```lean
import Mathlib

example (x : ℝ) (h : x = 2 ∨ x = -2) : x ^ 2 = 4 := by
  rcases h with h1 | h2
  · rw [h1]
    norm_num
  · rw [h2]
    norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Si es esto…, y si es aquello…","etiqueta":"∨ · rcases · casos","idea":"No sabemos cuál de los dos es cierto, así que se demuestra la meta en los dos casos. `rcases` parte la prueba: en cada caso, una de las dos mitades de la «o» pasa a ser hipótesis.","notas":{"1":"Dos metas iguales, `x ^ 2 = 4`, con hipótesis distintas. Lean las llama `inl` (por la izquierda) e `inr` (por la derecha).","2":"Caso *x* = 2: queda `2 ^ 2 = 4`.","3":"Una cuenta.","4":"Caso *x* = −2: queda `(-2) ^ 2 = 4`. Lean pone los paréntesis.","5":"Otra cuenta. Los dos casos están cerrados."}},"archivo":"datos/trazas/07-disyuncion-2.json"}
```

- `rcases h with h1 | h2` cambia una meta por dos, iguales, y en cada una pone una mitad de la «o» como hipótesis. La barra `|` separa los dos casos.
- Los casos se llaman `inl` e `inr`: de *in left* e *in right*, «por la izquierda» y «por la derecha».
- Cada caso se trabaja en su punto, como en el capítulo 4.
- También vale `obtain h1 | h2 := h`. Es la misma táctica que en el capítulo 6 separaba una «y», ahora con una barra en lugar de una coma.

### 3 · Casos que pones tú

Muchas demostraciones empiezan por «distinguimos dos casos», sin que ninguna hipótesis lo pida. Por ejemplo: el producto de dos naturales consecutivos, *n*(*n* + 1), siempre es par. ¿Por qué? Porque *n* es par o es impar, y en los dos casos sale.

```lean
import Mathlib

example (n : ℕ) : Even (n * (n + 1)) := by
  rcases Nat.even_or_odd n with h | h
  · exact h.mul_right (n + 1)
  · exact h.add_one.mul_left n

example (n : ℕ) : n ≤ 5 ∨ n ≥ 6 := by
  by_cases h : n ≤ 5
  · left
    exact h
  · right
    omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Distinguimos dos casos","etiqueta":"Nat.even_or_odd · by_cases","idea":"Un teorema que dice «*p* o *q*» se usa con `rcases`, como una hipótesis. `by_cases h : p` parte en dos casos cualquier afirmación: *p* es cierta, o no lo es.","notas":{"1":"`Nat.even_or_odd n` es un teorema de Mathlib: `Even n ∨ Odd n`. Dos casos.","2":"Si *n* es par, *n* por cualquier cosa es par: `h.mul_right (n + 1)`.","3":"Si *n* es impar, *n* + 1 es par (`h.add_one`), y *n* por un par es par (`.mul_left n`).","4":"Los casos se llaman `pos` y `neg`. En `neg`, la hipótesis lleva delante `¬`: «no».","5":"Caso `pos`: la izquierda.","6":"Es `h`.","7":"Caso `neg`: la derecha.","8":"`omega` sabe que, si *n* no es ≤ 5, entonces *n* ≥ 6."}},"archivo":"datos/trazas/07-disyuncion-3.json"}
```

- `Nat.even_or_odd n` es un teorema de Mathlib que dice `Even n ∨ Odd n`. Un teorema que es una «o» se parte con `rcases`, igual que una hipótesis.
- `Even` y `Odd` son «par» e «impar». Sus propiedades tienen nombres que se leen: `h.mul_right` («si *n* es par, *n* · *k* también»), `h.add_one` («si *n* es impar, *n* + 1 es par»), `.mul_left` («si *m* es par, *k* · *m* también»).
- `by_cases h : n ≤ 5` parte la prueba en dos casos, `pos` y `neg`. En el primero, `h : n ≤ 5`. En el segundo, `h : ¬n ≤ 5`, que se lee «no es cierto que *n* ≤ 5».
- `¬` es la **negación**. La usaremos a fondo en el capítulo siguiente. De momento, `omega` sabe traducir `¬n ≤ 5` por `n > 5`.

### 4 · Juntar las piezas

```lean
import Mathlib

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  rintro ⟨hp, hq | hr⟩
  · left
    exact ⟨hp, hq⟩
  · right
    exact ⟨hp, hr⟩
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Supongo, separo, elijo","etiqueta":"intro · rcases · rintro · left · right","idea":"Primero la flecha (`intro`), después los casos de la hipótesis (`rcases`), y en cada caso se elige el lado de la meta. `rintro` hace las dos primeras cosas de una vez.","notas":{"1":"La meta es una flecha.","2":"La hipótesis es una «o»: dos casos.","3":"Si tenemos *p*, la meta `q ∨ p` se demuestra por la derecha…","4":"…con `hp`.","5":"Si tenemos *q*, por la izquierda…","6":"…con `hq`.","7":"`rintro ⟨hp, hq | hr⟩` supone, separa la «y» y parte la «o», todo en un paso: dos casos.","8":"En el primer caso tenemos *p* y *q*: la izquierda.","10":"En el segundo, *p* y *r*: la derecha."}},"archivo":"datos/trazas/07-disyuncion-4.json"}
```

- En `p ∨ q → q ∨ p`, la «o» de la hipótesis se **usa** (casos) y la de la meta se **demuestra** (se elige un lado). En cada caso, el lado es distinto.
- `rintro` es `intro` con patrones: `⟨hp, hq | hr⟩` dice «separa la «y» en `hp` y lo otro, y lo otro, que es una «o», pártelo en casos». Escribe en una línea lo que serían tres tácticas.
- El segundo ejemplo es la **propiedad distributiva** de la «y» respecto de la «o». Es la misma que la de los números, *a*(*b* + *c*) = *ab* + *ac*, con ∧ en lugar del producto y ∨ en lugar de la suma.

::::{div}
:class: afondo
### 5 · El tercero excluido

`by_cases h : p` parte en «*p*» y «no *p*», sea *p* lo que sea. Eso supone que toda afirmación es verdadera o falsa, sin una tercera posibilidad. ¿Es una regla de la lógica de Lean, o algo más?

```lean
import Mathlib

theorem tercero (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · left
    exact h
  · right
    exact h

#check Classical.em
#print axioms tercero

theorem cinco (n : ℕ) : n ≤ 5 ∨ n ≥ 6 := by
  by_cases h : n ≤ 5
  · left; exact h
  · right; omega

#print axioms cinco
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"¿Toda afirmación es verdadera o falsa?","etiqueta":"a fondo · by_cases · Classical.em · axiomas","idea":"`p ∨ ¬p` es el principio del tercero excluido. Lean lo demuestra para cualquier *p*, pero `#print axioms` delata que hace falta un axioma: `Classical.choice`. Para `n ≤ 5` no, porque se puede calcular.","notas":{"1":"Dos casos: *p* cierta o *p* falsa.","4":"En el caso `neg`, la meta `¬p` es justo la hipótesis."}},"archivo":"datos/trazas/07-disyuncion-5.json"}
```

`tercero` demuestra `p ∨ ¬p` para cualquier proposición *p*: es el **principio del tercero excluido**. Mathlib ya lo tiene con nombre, `Classical.em` (de *excluded middle*), como dice `#check`.

`#print axioms tercero` contesta `[propext, Classical.choice, Quot.sound]`. Ahí está `Classical.choice`: para partir una afirmación **cualquiera** en «cierta» y «falsa», Lean necesita un axioma de la lógica **clásica**. Sin él, la lógica de Lean es **constructiva**: para demostrar «*p* o *q*», hay que saber cuál de las dos, y con una *p* arbitraria no se sabe.

`#print axioms cinco` contesta `[propext, Quot.sound]`, sin `Classical.choice`. Con `n ≤ 5`, `by_cases` no necesita el axioma: comparar dos naturales es un cálculo que siempre termina, así que Lean puede decidir el caso calculando. Se dice que `n ≤ 5` es una proposición **decidible**.

Las matemáticas de un libro de texto usan la lógica clásica sin pensarlo, y Mathlib también. La diferencia se nota en informática: una prueba constructiva de «existe un *x*…» trae dentro la forma de calcular ese *x*. La parte V vuelve sobre los axiomas.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«Si *p* o *q*, entonces *q* o *p*» (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  rcases h with hp | hq
  · right; exact hp
  · left; exact hq
```

```coq
(* Rocq (Coq): destruct con barra para los casos *)
Theorem conmuta_o : forall p q : Prop, p \/ q -> q \/ p.
Proof.
  intros p q h.
  destruct h as [hp | hq].
  - right. exact hp.
  - left. exact hq.
Qed.
```

```isabelle
(* Isabelle: disjE para usar, disjI1 y disjI2 para demostrar *)
lemma "p | q --> q | p"
  apply (rule impI)
  apply (erule disjE)
  apply (rule disjI2)
  apply assumption
  apply (rule disjI1)
  apply assumption
  done
```

Rocq usa `left` y `right`, como Lean, y escribe los casos con la misma barra: `[hp | hq]`. En Isabelle, las reglas vuelven a llevar el nombre de la lógica: `disjE` *elimina* la disyunción (los casos) y `disjI1`, `disjI2` la *introducen* por un lado o por el otro. Tras `erule disjE`, Isabelle enseña las dos submetas: `p ⟹ q ∨ p` y `q ⟹ q ∨ p`.
:::

## Conexiones

- La tabla «demostrar / usar» del capítulo 6 gana una fila. Con ∀ y ∃, en el capítulo 9, quedará completa.
- `rcases` y `obtain` separan una «y» con coma y una «o» con barra. En el capítulo 0, `obtain ⟨k, hk⟩` separaba un «existe»: el capítulo 9 explica por qué se escribe igual.
- `by_cases` ha traído la negación, `¬`. El capítulo siguiente la estudia a fondo.
- `Classical.choice` vuelve en la parte V, en **el núcleo y los axiomas**.

## La grieta

En el caso `neg` apareció `h : ¬n ≤ 5`, y `omega` supo qué hacer con ella. Pero ¿qué es exactamente «no *p*» para Lean? ¿Cómo se demuestra que algo **no** pasa? ¿Y cómo se usa una contradicción, ese «si fuera así, llegaríamos a un absurdo» de la reducción al absurdo? Lo vemos en **Negación y absurdo**.

## Ejercicios

1. **El otro lado.** Con `h : n = 5`, demuestra `n = 3 ∨ n = 5`.

2. **Por casos.** Con `h : x = 1 ∨ x = 3` y `x : ℝ`, demuestra `x ^ 2 - 4 * x + 3 = 0`.

3. **Debilitar.** Con `hp : p`, demuestra `p ∨ q`. ¿Hace falta saber algo de *q*?

4. **Dos caminos al mismo sitio.** Con `hpr : p → r` y `hqr : q → r`, demuestra `p ∨ q → r` usando `rintro`.

5. **El lado equivocado.** Con `h : n = 3`, ¿qué pasa si demuestras `n = 3 ∨ n = 5` con `right` y `exact h`?

6. **Par o impar en cuentas.** ¿Sabe `omega` demostrar `n % 2 = 0 ∨ n % 2 = 1` para `n : ℕ`?

::::{div}
:class: afondo
7. **El máximo.** Demuestra `max a b ≥ a`, con `a b : ℝ`, partiendo en casos con `le_total a b`, que dice `a ≤ b ∨ b ≤ a`. Te sirven `max_eq_right`, que dice que si `a ≤ b` entonces `max a b = b`, y `max_eq_left`, lo mismo con `b ≤ a`.

8. **Decidible o no.** ¿Por qué `tercero` depende de `Classical.choice` y `cinco` no, si las dos se demuestran con `by_cases`?
::::

## Solucionario

1. `right` y `exact h`.
2. ```lean
   example (x : ℝ) (h : x = 1 ∨ x = 3) : x ^ 2 - 4 * x + 3 = 0 := by
     rcases h with h | h
     · rw [h]; norm_num
     · rw [h]; norm_num
   ```
   Son las dos raíces de *x*² − 4*x* + 3. Se puede usar el mismo nombre, `h`, en los dos casos: cada uno tiene su contexto.
3. `left` y `exact hp`. No hace falta saber nada de *q*: puede ser falsa.
4. ```lean
   example (p q r : Prop) (hpr : p → r) (hqr : q → r) : p ∨ q → r := by
     rintro (hp | hq)
     · exact hpr hp
     · exact hqr hq
   ```
   Con `rintro`, una «o» sola se escribe entre paréntesis: `(hp | hq)`.
5. Tras `right`, la meta es `n = 5`, y `exact h` da un error: `h` es una prueba de `n = 3`, no de `n = 5` (Lean dice *Type mismatch*). La meta queda sin poder demostrarse.
6. Sí: `omega` lo demuestra solo, porque entiende el resto de la división por un número fijo.

::::{div}
:class: afondo
7. ```lean
   example (a b : ℝ) : max a b ≥ a := by
     rcases le_total a b with h | h
     · rw [max_eq_right h]
       exact h
     · rw [max_eq_left h]
   ```
   En el primer caso, `max a b` es `b`, y `b ≥ a` es `h`. En el segundo es `a`, y `a ≥ a` se cierra solo tras `rw`.
8. `cinco` parte en casos sobre `n ≤ 5`, que se puede comprobar calculando: es decidible, y `by_cases` usa ese cálculo. `tercero` parte en casos sobre una *p* cualquiera, de la que no se sabe nada; para eso hace falta el tercero excluido, que en Lean viene del axioma `Classical.choice`.
::::
