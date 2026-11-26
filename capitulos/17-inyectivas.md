---
title: "Funciones: inyectiva y sobreyectiva"
subtitle: Cuándo una función no repite, cuándo llega a todo, y cuándo se puede deshacer
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En Bachillerato, las funciones son fórmulas con una gráfica: *f*(*x*) = 2*x* + 1 es una recta, *f*(*x*) = *x*² una parábola. Y de algunas se dice que «tienen inversa»: de la recta sí (*y* = 2*x* + 1, despejando, *x* = (*y* − 1)/2), de la parábola no, porque *x*² = 4 tiene dos soluciones.

Detrás de eso hay dos preguntas que no tienen nada que ver con gráficas. ¿Puede haber dos valores distintos de *x* que vayan al mismo *y*? Si no, la función es **inyectiva**. ¿Llega la función a todos los valores posibles de *y*? Si es así, es **sobreyectiva**. Y si cumple las dos cosas, **biyectiva**: entonces, y solo entonces, se puede deshacer.

## La pregunta

¿Cómo se escriben en Lean «inyectiva» y «sobreyectiva»? ¿Cómo se demuestran, y cómo se demuestra que una función *no* lo es? ¿Qué pasa al componer funciones?

## La idea

Las dos definiciones son una frase con cuantificadores, y se demuestran con las herramientas de la parte II:

| Propiedad | Definición en Mathlib | En palabras | Para demostrarla |
|---|---|---|---|
| `Function.Injective f` | ∀ *a*₁ *a*₂, *f a*₁ = *f a*₂ → *a*₁ = *a*₂ | si dan lo mismo, eran iguales | `intro a b h` y despejar |
| `Function.Surjective f` | ∀ *b*, ∃ *a*, *f a* = *b* | todo *b* tiene quien llegue a él | `intro y` y `use` el candidato |
| `Function.Bijective f` | inyectiva ∧ sobreyectiva | las dos cosas | `constructor` |

:::{important} Lo que cambia es el conjunto de partida y el de llegada
La misma fórmula puede ser inyectiva o no según dónde viva. *x*² no es inyectiva en ℤ (1 y −1 van a 1), pero sí lo es en ℕ. 2*n* es sobreyectiva en ℝ, pero no en ℕ (nadie llega al 1). Por eso en Lean siempre se escribe el tipo: `fun x : ℤ => x ^ 2`.
:::

## Construcción

### 1 · Inyectiva: si dan lo mismo, eran iguales

```lean
import Mathlib

#print Function.Injective

example : Function.Injective (fun x : ℤ => 2 * x + 1) := by
  intro a b h
  simp only at h
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Despejar hacia atrás","etiqueta":"Injective · intro · simp only","idea":"Para ver que *f* es inyectiva se toman dos valores con la misma imagen y se demuestra que eran el mismo. Con 2*a* + 1 = 2*b* + 1, basta despejar.","notas":{"1":"Dos valores *a* y *b*, y la hipótesis de que van al mismo sitio. La meta: *a* = *b*.","2":"`h` lleva la función sin aplicar; `simp only` la aplica: `h : 2 * a + 1 = 2 * b + 1`.","3":"Restando 1 y dividiendo entre 2: *a* = *b*."}},"archivo":"datos/trazas/17-inyectivas-1.json"}
```

- `#print Function.Injective` enseña la definición tal cual: `∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂`. Un ∀ y una →, así que `intro a b h`.
- Tras el `intro`, `h` dice `(fun x => 2 * x + 1) a = (fun x => 2 * x + 1) b`: la función todavía sin aplicar. `simp only at h` hace la sustitución y deja `2 * a + 1 = 2 * b + 1`.
- Lo que queda es despejar: lo que haríamos en la pizarra para hallar la inversa, pero hacia atrás.

### 2 · No inyectiva: un contraejemplo

:::{tip} Predice
Para demostrar que *x*² **no** es inyectiva en ℤ, ¿qué dos números elegirías?
:::

```lean
import Mathlib

example : ¬ Function.Injective (fun x : ℤ => x ^ 2) := by
  intro h
  have h1 := @h 1 (-1) (by norm_num)
  norm_num at h1
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Dos que van al mismo sitio","etiqueta":"¬ Injective · contraejemplo","idea":"«No inyectiva» es una negación: se supone que lo es y se llega a un absurdo. El absurdo lo da un contraejemplo: 1² = (−1)², así que la inyectividad obligaría a que 1 = −1.","notas":{"1":"Se supone que *x*² es inyectiva. Hay que llegar a `False`.","2":"Se aplica `h` a 1 y −1. Antes hay que darle la prueba de que van al mismo sitio…","3":"…1² = (−1)², que comprueba `norm_num`. Sale `h1 : 1 = -1`.","4":"Y 1 = −1 es falso."}},"archivo":"datos/trazas/17-inyectivas-2.json"}
```

- «No es inyectiva» es `¬ Function.Injective …`, es decir, «si fuera inyectiva, habría un absurdo» (capítulo 8). Por eso empieza con `intro h`.
- Los valores *a*₁ y *a*₂ de la definición van entre ⦃ ⦄: son implícitos, Lean los deduce. Para dárselos a mano se escribe `@h 1 (-1)`. El tercer argumento es la prueba de que 1² = (−1)².
- Con eso, `h1 : 1 = -1`, y `norm_num` sabe que es falso.
- El mismo esquema sirve para cualquier «no inyectiva»: encontrar dos valores distintos con la misma imagen.

### 3 · Sobreyectiva: dar el candidato

```lean
import Mathlib

example : Function.Surjective (fun x : ℤ => x + 3) := by
  intro y
  use y - 3
  ring

example : ¬ Function.Surjective (fun n : ℕ => 2 * n) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp only at hn
  omega
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"¿Quién llega a y?","etiqueta":"Surjective · use · obtain","idea":"Sobreyectiva es «para todo *y*, existe un *x* con *f x* = *y*»: se toma *y* y se da el *x*. Para ver que no lo es, basta un *y* al que nadie llegue.","notas":{"1":"Un *y* cualquiera. Hay que encontrar quién va a él.","2":"El candidato sale de despejar *x* + 3 = *y*: *x* = *y* − 3.","3":"(*y* − 3) + 3 = *y*.","4":"Si 2*n* fuera sobreyectiva en ℕ, alguien llegaría al 1.","5":"Ese alguien es *n*, con `hn`.","6":"`hn : 2 * n = 1`.","7":"Un número par no puede ser 1."}},"archivo":"datos/trazas/17-inyectivas-3.json"}
```

- Sobreyectiva es un ∀ seguido de un ∃: `intro y` y luego `use` con el candidato (capítulo 9).
- El candidato se encuentra igual que en la pizarra: despejando *x* en *f*(*x*) = *y*. Lean no lo busca; se lo damos nosotros.
- Para ver que 2*n* no es sobreyectiva en ℕ, se elige un valor al que no llega, el 1, y se desmonta el ∃ con `obtain`. `2 * n = 1` es imposible en los naturales, y `omega` lo sabe.

### 4 · Componer funciones

Si *f* va de α a β y *g* de β a γ, la composición *g* ∘ *f* va de α a γ: primero *f*, después *g*. ¿Se conserva la inyectividad?

```lean
import Mathlib

example {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  intro a b h
  apply hf
  apply hg
  exact h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La composición de inyectivas es inyectiva","etiqueta":"∘ · apply","idea":"De *g*(*f a*) = *g*(*f b*), la inyectividad de *g* da *f a* = *f b*, y la de *f* da *a* = *b*. Con `apply` se razona hacia atrás, desde la meta.","notas":{"1":"`h : (g ∘ f) a = (g ∘ f) b`. La meta: *a* = *b*.","2":"Como *f* es inyectiva, basta con *f a* = *f b*.","3":"Como *g* es inyectiva, basta con *g*(*f a*) = *g*(*f b*).","4":"Y eso es `h`: (*g* ∘ *f*) *a* es, por definición, *g*(*f a*)."}},"archivo":"datos/trazas/17-inyectivas-4.json"}
```

- `{α β γ : Type}` dice que la prueba vale para tres tipos cualesquiera: no hace falta saber qué son ni qué hacen *f* y *g*, solo que son inyectivas.
- `apply hf` razona hacia atrás: «para tener *a* = *b*, basta con *f a* = *f b*». Es usar la inyectividad de *f* como una implicación (capítulo 6).
- Al final, `h` sirve tal cual porque (*g* ∘ *f*) *a* es, por definición, *g*(*f a*): Lean lo ve sin que haya que reescribir.
- En Mathlib es `Function.Injective.comp`, con *g* primero: `hg.comp hf`. Para sobreyectivas hay otro igual, `Function.Surjective.comp`.

::::{div}
:class: afondo
### 5 · Biyectiva e inversa

Una función biyectiva es inyectiva y sobreyectiva a la vez. Y es justo la condición para tener inversa: una función que deshace lo que hace la primera.

```lean
import Mathlib

example : Function.Bijective (fun x : ℝ => 2 * x + 1) := by
  constructor
  · intro a b h
    simp only at h
    linarith
  · intro y
    use (y - 1) / 2
    ring

example : (fun y : ℝ => (y - 1) / 2) ∘ (fun x : ℝ => 2 * x + 1) = id := by
  funext x
  simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Ir y volver","etiqueta":"a fondo · Bijective · funext","idea":"Biyectiva es inyectiva ∧ sobreyectiva: `constructor` y cada mitad como antes. La inversa, *g*(*y*) = (*y* − 1)/2, compuesta con *f* da la identidad, y dos funciones son iguales si coinciden en cada punto.","notas":{"1":"Dos metas: inyectiva y sobreyectiva.","2":"Inyectiva: dos valores con la misma imagen…","3":"…`h : 2 * a + 1 = 2 * b + 1`…","4":"…y despejando, *a* = *b*. En los reales, con `linarith`.","5":"Sobreyectiva: un *y* cualquiera.","6":"El candidato es la inversa: *x* = (*y* − 1)/2.","7":"2 · (*y* − 1)/2 + 1 = *y*.","8":"Dos funciones son iguales si dan lo mismo en cada *x*: `funext x`.","9":"(2*x* + 1 − 1)/2 = *x*: `simp` hace la cuenta."}},"archivo":"datos/trazas/17-inyectivas-5.json"}
```

`Function.Bijective f` es, por definición, `Injective f ∧ Surjective f`. `constructor` lo parte en dos, y cada mitad se demuestra como en los apartados 1 y 3.

El candidato de la sobreyectividad, (*y* − 1)/2, es la función inversa. Para comprobar que deshace a *f* se demuestra que *g* ∘ *f* = id, una igualdad entre funciones. Dos funciones son iguales si dan lo mismo en cada punto: es la extensionalidad del capítulo 16, ahora para funciones, y la táctica se llama `funext`. Tras `funext x`, la meta es (*g* ∘ *f*) *x* = id *x*, y `simp` hace la cuenta.

En Mathlib, la relación entre biyectiva e inversa es un teorema: `Function.bijective_iff_has_inverse` dice que *f* es biyectiva si y solo si existe *g* con `LeftInverse g f` (*g*(*f x*) = *x* para todo *x*) y `RightInverse g f` (*f*(*g y*) = *y* para todo *y*).
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
*f*(*x*) = 2*x* + 1 es inyectiva en los enteros (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example : Function.Injective (fun x : ℤ => 2 * x + 1) := by
  intro a b h
  simp only at h
  omega
```

```coq
(* Rocq (Coq) *)
Require Import ZArith Lia FinFun.
Open Scope Z_scope.
Lemma iny : Injective (fun x : Z => 2 * x + 1).
Proof.
  intros a b h.
  lia.
Qed.
```

```isabelle
(* Isabelle *)
lemma iny: "inj (\<lambda>x::int. 2 * x + 1)"
  apply (rule injI)
  apply simp
  done
```

La definición es la misma en los tres: si las imágenes coinciden, los valores también. En Rocq, `Injective` viene de la biblioteca `FinFun`, y `lia` (el `omega` de Rocq) despeja sin necesidad de aplicar la función antes. En Isabelle se llama `inj`; la regla `injI` toma los dos valores y la hipótesis, y `simp` despeja. En el archivo, la λ de la función se escribe `\<lambda>`.
:::

## Conexiones

- Inyectiva es un ∀ con una → (capítulos 6 y 9); sobreyectiva, un ∀ con un ∃ (capítulo 9); «no inyectiva» y «no sobreyectiva» son negaciones (capítulo 8).
- `funext` es la extensionalidad del capítulo 16 para funciones.
- La inversa de una función biyectiva es lo que se usa en el capítulo 27: descifrar en RSA es la inversa de cifrar, y demostrarlo es demostrar que su composición es la identidad.
- El capítulo 18 trabaja con funciones de ℕ en ℝ: las sucesiones.

## La grieta

Una función de ℕ en ℝ es una lista infinita de números: *a*₀, *a*₁, *a*₂… Una sucesión. ¿Qué quiere decir que se acerca a un número? En la pizarra se dice «tiende a», se dibujan puntitos que se aprietan contra una recta. Pero para demostrarlo hacen falta ε, *N* y tres cuantificadores seguidos. Lo vemos en **Sucesiones y límites**.

## Ejercicios

1. **Sumar 5.** Demuestra que `fun n : ℕ => n + 5` es inyectiva.

2. **Restar 1.** Demuestra que `fun x : ℤ => x - 1` es sobreyectiva. ¿Qué candidato das?

3. **La mitad.** Demuestra que `fun n : ℕ => n / 2` no es inyectiva. ¿Qué dos valores van al mismo sitio?

4. **El siguiente.** Demuestra que `fun n : ℕ => n + 1` no es sobreyectiva. ¿A qué número no llega?

5. **Con reales.** Demuestra que `fun x : ℝ => 3 * x - 2` es inyectiva.

6. **Componer sobreyectivas.** Demuestra que si *f* y *g* son sobreyectivas, *g* ∘ *f* también lo es. Pista: `intro z`, dos `obtain` y `use x`.

::::{div}
:class: afondo
7. **Al revés.** Demuestra que si *g* ∘ *f* es inyectiva, entonces *f* es inyectiva. ¿Es necesario que *g* sea inyectiva?

8. **En una línea.** Demuestra el ejercicio 6 en una línea con el teorema de Mathlib para composiciones de sobreyectivas.
::::

## Solucionario

1. `intro a b h`, `simp only at h`, `omega`.
2. ```lean
   example : Function.Surjective (fun x : ℤ => x - 1) := by
     intro y
     use y + 1
     ring
   ```
3. 0 y 1: los dos van a 0 (la división de naturales redondea hacia abajo).
   ```lean
   example : ¬ Function.Injective (fun n : ℕ => n / 2) := by
     intro h
     have h1 := @h 0 1 (by norm_num)
     norm_num at h1
   ```
4. No llega al 0:
   ```lean
   example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
     intro h
     obtain ⟨n, hn⟩ := h 0
     simp only at hn
     omega
   ```
5. `intro a b h`, `simp only at h`, `linarith`.
6. ```lean
   example {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Surjective f)
       (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
     intro z
     obtain ⟨y, hy⟩ := hg z
     obtain ⟨x, hx⟩ := hf y
     use x
     rw [Function.comp_apply, hx, hy]
   ```

::::{div}
:class: afondo
7. ```lean
   example {α β γ : Type} (f : α → β) (g : β → γ) (h : Function.Injective (g ∘ f)) :
       Function.Injective f := by
     intro a b hab
     apply h
     simp only [Function.comp_apply, hab]
   ```
   No hace falta que *g* sea inyectiva: si *f a* = *f b*, entonces *g*(*f a*) = *g*(*f b*) para cualquier *g*.
8. `hg.comp hf` (es decir, `Function.Surjective.comp hg hf`).
::::
