---
title: Negación y absurdo
subtitle: «No» quiere decir «llevaría a una contradicción»
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

¿Cómo se demuestra que algo **no** pasa? Que 2 + 2 no es 5, que no hay un natural cuyo cuadrado sea 2, que √2 no es una fracción. No se puede comprobar caso por caso: hay que ver que, si pasara, se llegaría a algo imposible.

Es la **reducción al absurdo**, la más antigua de las técnicas de demostración: «supongamos que sí; entonces… y esto es una contradicción. Luego no». Euclides la usó para ver que hay infinitos primos.

En el capítulo anterior, `by_cases` trajo una hipótesis con `¬` delante, y `omega` supo qué hacer con ella. Ahora toca ver qué es `¬` para Lean.

## La pregunta

¿Qué significa «no *p*» para Lean? ¿Cómo se demuestra, y cómo se usa? ¿Y cómo se escribe en Lean una reducción al absurdo?

## La idea

Para Lean, «no *p*» es una implicación: **`¬p` significa `p → False`**. «No *p*» quiere decir «si *p*, entonces algo imposible».

- `False` es la proposición falsa: la que no tiene ninguna prueba. Si llegas a tener una prueba de `False`, algo en las hipótesis es contradictorio.
- Como `¬p` es una flecha, se demuestra con `intro`: supones *p* y llegas a `False`.
- Y se usa como una flecha: con `hnp : ¬p` y `hp : p`, `hnp hp` es una prueba de `False`.
- `a ≠ b` es `¬(a = b)`: «*a* no es igual a *b*».

| | Demostrar (en la meta) | Usar (en una hipótesis) |
|---|---|---|
| `¬p` | `intro hp`: supones *p*, y la meta pasa a ser `False` | `hnp hp : False`, si tienes también `hp : p` |
| `False` | No se puede: hay que encontrar una contradicción | `exfalso` o `contradiction`: de lo falso sale cualquier cosa |

:::{important} Reducción al absurdo
Para demostrar *p* por reducción al absurdo, se escribe `by_contra h`: Lean pone `h : ¬p` entre las hipótesis y cambia la meta por `False`. Hay que llegar a una contradicción.
:::

## Construcción

### 1 · Demostrar que algo no pasa

:::{tip} Predice
La meta es `¬(2 + 2 = 5)`. ¿Qué meta queda tras `intro h`?
:::

```lean
import Mathlib

example : ¬ (2 + 2 = 5) := by
  intro h
  norm_num at h

example (n : ℕ) (h : n = 3) : n ≠ 4 := by
  intro h4
  rw [h] at h4
  norm_num at h4
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Si fuera así, sería absurdo","etiqueta":"¬ · ≠ · intro · False","idea":"`¬p` es `p → False`. Se demuestra como cualquier flecha: con `intro`, que supone *p* y deja la meta `False`. Después hay que encontrar la contradicción.","notas":{"1":"Suponemos que 2 + 2 = 5. La meta pasa a ser `False`: hay que ver que eso es absurdo.","2":"`norm_num at h` calcula 2 + 2 y ve que `h` es falsa. Una hipótesis falsa cierra la meta.","3":"`n ≠ 4` es `¬(n = 4)`: se supone `n = 4`.","4":"Con `h`, la hipótesis `h4` pasa a decir `3 = 4`.","5":"`3 = 4` es falso: contradicción."}},"archivo":"datos/trazas/08-negacion-1.json"}
```

- Tras `intro h`, el panel tiene `h : 2 + 2 = 5` y la meta es `False`. No se puede demostrar `False` directamente: hay que encontrar algo contradictorio en las hipótesis.
- `norm_num at h` calcula en la hipótesis. `2 + 2 = 5` se queda en algo falso, y cuando una hipótesis es falsa, la meta se cierra sola: de una hipótesis falsa se puede deducir cualquier cosa.
- `≠` se escribe `\ne`. `n ≠ 4` es una negación, así que también empieza con `intro`.

### 2 · Usar una negación: de lo falso, cualquier cosa

Si tienes `hp : p` y `hnp : ¬p` a la vez, tus hipótesis se contradicen. Y con hipótesis contradictorias se demuestra **cualquier** meta, aunque no tenga nada que ver.

```lean
import Mathlib

example (p q : Prop) (hp : p) (hnp : ¬p) : q := by
  exfalso
  exact hnp hp

example (p q : Prop) (hp : p) (hnp : ¬p) : q := by
  contradiction

example (n : ℕ) (h1 : n < 3) (h2 : n > 5) : n = 100 := by
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Hipótesis que se contradicen","etiqueta":"exfalso · contradiction · omega","idea":"Si las hipótesis se contradicen, la meta da igual. `exfalso` la cambia por `False`, y `hnp hp` es una prueba de `False`. `contradiction` busca sola la contradicción.","notas":{"1":"`exfalso`: en lugar de *q*, demostraremos `False`. Si llegamos a algo imposible, cualquier meta queda demostrada.","2":"`hnp : ¬p` es `p → False`. Aplicada a `hp`, da `False`.","3":"`contradiction` encuentra `hp` y `hnp` y cierra la meta en un paso.","4":"*n* < 3 y *n* > 5 no pueden pasar a la vez. `omega` lo ve, y por eso demuestra hasta *n* = 100."}},"archivo":"datos/trazas/08-negacion-2.json"}
```

- `exfalso` cambia cualquier meta por `False`. Es el principio de que **de lo falso se deduce cualquier cosa** (*ex falso quodlibet*, de ahí el nombre).
- `hnp hp` es una prueba de `False`: `hnp` es una flecha `p → False`, aplicada a `hp`. Es lo mismo que `h hp` del capítulo 6.
- `contradiction` busca entre las hipótesis una pareja `p` y `¬p`, o una hipótesis claramente falsa, y cierra la meta.
- `omega` también razona así: con *n* < 3 y *n* > 5, ve que no hay ningún *n* posible, y demuestra lo que sea.

### 3 · Reducción al absurdo

:::{tip} Predice
Para demostrar *n* ≤ 3 sabiendo que *n* · *n* ≤ 9, ¿qué se supone en una reducción al absurdo?
:::

```lean
import Mathlib

example (n : ℕ) (h : n * n ≤ 9) : n ≤ 3 := by
  by_contra hc
  push Not at hc
  nlinarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Supongamos que no","etiqueta":"by_contra · push Not · nlinarith","idea":"`by_contra hc` supone lo contrario de la meta y pide llegar a `False`. `push Not` reescribe la negación de una forma más útil.","notas":{"1":"«Supongamos que *n* no es ≤ 3.» La meta pasa a ser `False`.","2":"`¬n ≤ 3` es lo mismo que `3 < n`: `push Not` lo reescribe.","3":"Si *n* > 3, entonces *n* · *n* > 9, contra `h`. `nlinarith` multiplica las desigualdades y encuentra la contradicción."}},"archivo":"datos/trazas/08-negacion-3.json"}
```

- `by_contra hc` es la reducción al absurdo: pone `hc : ¬n ≤ 3` y cambia la meta por `False`.
- `push Not at hc` empuja la negación hacia dentro hasta que desaparece: `¬n ≤ 3` pasa a ser `3 < n`. Con desigualdades, una negación se puede cambiar por la desigualdad contraria.
- `nlinarith` es `linarith` con productos: multiplica entre sí las hipótesis y busca la contradicción. De 3 < *n*, saca que *n* · *n* > 9, contra `h`.
- En libros y foros de Lean verás `push_neg` en lugar de `push Not`. Es su nombre anterior: en la versión de Mathlib de este libro todavía funciona, pero Lean avisa de que está desaconsejado y propone `push Not`.

### 4 · Negar lo compuesto

¿Qué es «no (*p* o *q*)»? En castellano: ni *p* ni *q*. Son las **leyes de De Morgan**, y en Lean se demuestran con lo que ya sabemos.

```lean
import Mathlib

example (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q := by
  intro h
  constructor
  · intro hp
    exact h (Or.inl hp)
  · intro hq
    exact h (Or.inr hq)

example (x y : ℝ) (h : ¬(x ≤ y)) : y < x := by
  push Not at h
  exact h

example (p q : Prop) (h : ¬(p ∧ q)) : p → ¬q := by
  push Not at h
  exact h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Ni lo uno ni lo otro","etiqueta":"De Morgan · Or.inl · push Not","idea":"De «no (*p* o *q*)» salen «no *p*» y «no *q*»: si tuviéramos *p*, tendríamos *p* o *q*, contra la hipótesis. `push Not` hace estas transformaciones solo.","notas":{"1":"Suponemos `¬(p ∨ q)`.","2":"Hay que demostrar dos negaciones.","3":"Para `¬p`: suponemos *p*…","4":"…y entonces `Or.inl hp` es una prueba de `p ∨ q`, que contradice `h`.","5":"Igual con *q*…","6":"…por la derecha: `Or.inr hq`.","7":"«No es cierto que *x* ≤ *y*» pasa a ser «*y* < *x*».","9":"«No es cierto que *p* y *q*» pasa a ser «si *p*, entonces no *q*»."}},"archivo":"datos/trazas/08-negacion-4.json"}
```

- `Or.inl hp` construye `p ∨ q` a partir de `hp : p`: es el `left` del capítulo 7, escrito como expresión. `Or.inr` es el `right`.
- Para cada `¬`, la misma receta: `intro` y buscar la contradicción. Aquí la contradicción es con `h`.
- `push Not` conoce las leyes de De Morgan y las reglas de las desigualdades. Transforma `¬(x ≤ y)` en `y < x`, y `¬(p ∧ q)` en `p → ¬q`, que se lee «si *p*, entonces no *q*».

::::{div}
:class: afondo
### 5 · Doble negación

«No es cierto que no llueva» quiere decir «llueve». ¿Lean lo ve igual?

```lean
import Mathlib

theorem doble (p : Prop) (hp : p) : ¬¬p := by
  intro hnp
  exact hnp hp

theorem quita_doble (p : Prop) (h : ¬¬p) : p := by
  by_contra hnp
  exact h hnp

#print axioms doble
#print axioms quita_doble
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Dos «no» se anulan… con un axioma","etiqueta":"a fondo · ¬¬ · by_contra · axiomas","idea":"De *p* sale ¬¬*p* sin más. Al revés, de ¬¬*p* a *p*, hace falta la reducción al absurdo, y `#print axioms` delata que usa `Classical.choice`.","notas":{"1":"`¬¬p` es `¬p → False`: se supone `¬p`…","2":"…y con `hp` se llega a `False`.","3":"Para quitar la doble negación hace falta `by_contra`: suponemos `¬p`…","4":"…y `h : ¬¬p` aplicada a eso da `False`."}},"archivo":"datos/trazas/08-negacion-5.json"}
```

Las dos pruebas son casi iguales: dos líneas cada una, y en las dos se aplica una negación a otra. Pero `#print axioms` las separa:

- `'doble' does not depend on any axioms`: pasar de *p* a ¬¬*p* es pura lógica, sin axiomas.
- `'quita_doble' depends on axioms: [propext, Classical.choice, Quot.sound]`: pasar de ¬¬*p* a *p* necesita `Classical.choice`.

El culpable es `by_contra`. Para una *p* cualquiera, suponer ¬*p* y llegar a un absurdo no te da una prueba de *p*: solo te dice que ¬*p* es imposible. Concluir *p* de ahí es justo el tercero excluido del capítulo 7, y en Lean viene de ese axioma.

Con *p* decidible, como `n ≤ 3`, `by_contra` no lo necesita: Lean puede comprobar *p* calculando. La misma prueba con `n ≤ 3` en lugar de *p* no depende de ningún axioma. Lo mismo pasa con la otra ley de De Morgan: `¬p ∨ ¬q → ¬(p ∧ q)` sale sin axiomas, pero `¬(p ∧ q) → ¬p ∨ ¬q` necesita `Classical.choice` (ejercicios 7 y 8).
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
El **contrarrecíproco**: si *p* implica *q* y no *q*, entonces no *p* (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: ¬p es p → False, así que se empieza con intro
example (p q : Prop) (hpq : p → q) (hnq : ¬q) : ¬p := by
  intro hp
  exact hnq (hpq hp)
```

```coq
(* Rocq (Coq): ~p también es p -> False *)
Theorem contrapositivo : forall p q : Prop, (p -> q) -> ~q -> ~p.
Proof.
  intros p q hpq hnq hp.
  apply hnq.
  apply hpq.
  exact hp.
Qed.
```

```isabelle
(* Isabelle: notI para demostrar una negación, notE para usarla *)
lemma "(p --> q) ==> ~q ==> ~p"
  apply (rule notI)
  apply (erule notE)
  apply (erule mp)
  apply assumption
  done
```

En Rocq, `~p` también es `p -> False`, y `intros` llega hasta `hp`: el panel queda con la meta `False`, igual que en Lean. Isabelle trata la negación con sus reglas propias: `notI` la *introduce* (deja la meta `False` con *p* como hipótesis) y `notE` la *elimina*. Tras `rule notI`, la submeta es `⟦p ⟶ q; ¬q; p⟧ ⟹ False`.
:::

## Conexiones

- La tabla «demostrar / usar» gana dos filas, `¬` y `False`. La negación no trae reglas nuevas: es una flecha, y se trata con las del capítulo 6.
- `by_cases` y `by_contra` dependen del tercero excluido cuando la proposición no se puede decidir calculando. Es la misma frontera entre lógica clásica y constructiva del capítulo 7.
- `push Not` vuelve en el capítulo siguiente, donde negará «para todo» y «existe»: «no todos» pasa a ser «alguno no».
- `nlinarith` y `linarith` volverán en el capítulo 13, de desigualdades.

## La grieta

Hemos negado «y», «o» y desigualdades. Pero muchos teoremas hablan de **todos** los números, o de que **existe** alguno. ¿Cómo se demuestra que existe un número con cierta propiedad? ¿Cómo se usa una hipótesis «para todo *n*»? ¿Y qué es «no todos los números son pares»? Lo vemos en **Para todo y existe**.

## Ejercicios

1. **Una desigualdad falsa.** Demuestra `¬(3 < 2)` con `intro`.

2. **Distintos.** Demuestra `(7 : ℕ) ≠ 8` con una sola táctica.

3. **El contrarrecíproco.** Con `hpq : p → q` y `hnq : ¬q`, demuestra `¬p`.

4. **Imposible, luego cualquier cosa.** Con `x : ℝ` y `h : x ^ 2 < 0`, demuestra `x = 17`. Te sirve `sq_nonneg x`, que dice `0 ≤ x ^ 2`.

5. **Sin solución.** Demuestra que `2 * n = 7` es imposible en los naturales: con esa hipótesis, demuestra `False`.

6. **No contradicción.** Demuestra `¬(p ∧ ¬p)`: nada es cierto y falso a la vez.

::::{div}
:class: afondo
7. **De Morgan, la parte fácil.** Demuestra `¬p ∨ ¬q → ¬(p ∧ q)` con `rintro`. ¿Depende de algún axioma?

8. **De Morgan, la parte clásica.** Demuestra `¬(p ∧ q) → ¬p ∨ ¬q`. ¿Por qué hace falta `by_cases`?
::::

## Solucionario

1. ```lean
   example : ¬ (3 < 2) := by
     intro h
     norm_num at h
   ```
2. `decide`: comparar dos números concretos es un cálculo.
3. ```lean
   example (p q : Prop) (hpq : p → q) (hnq : ¬q) : ¬p := by
     intro hp
     exact hnq (hpq hp)
   ```
4. ```lean
   example (x : ℝ) (h : x ^ 2 < 0) : x = 17 := by
     have := sq_nonneg x
     linarith
   ```
   `0 ≤ x ^ 2` y `x ^ 2 < 0` se contradicen, y `linarith` lo ve. La meta `x = 17` da igual: de hipótesis contradictorias sale cualquier cosa.
5. `omega`: sabe que 2*n* es par y 7 no.
6. ```lean
   example (p : Prop) : ¬(p ∧ ¬p) := by
     intro ⟨hp, hnp⟩
     exact hnp hp
   ```

::::{div}
:class: afondo
7. ```lean
   example (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) := by
     rintro (hnp | hnq) ⟨hp, hq⟩
     · exact hnp hp
     · exact hnq hq
   ```
   `rintro` supone la «o» (dos casos) y, como la meta es una negación, supone también `p ∧ q` y la separa. No usa ningún axioma: no hay `by_cases` ni `by_contra`.
8. ```lean
   theorem dm (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
     intro h
     by_cases hp : p
     · right
       intro hq
       exact h ⟨hp, hq⟩
     · left
       exact hp
   ```
   Para elegir lado en `¬p ∨ ¬q` hay que saber si *p* es cierta o no, y de una *p* cualquiera no se sabe. `by_cases` lo decide con el tercero excluido: `#print axioms dm` contesta `[propext, Classical.choice, Quot.sound]`.
::::
