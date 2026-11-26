---
title: Igualdad y calc
subtitle: Cadenas de igualdades y desigualdades, escritas como en la pizarra
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Muchas demostraciones son una sola cuenta larga:

*a* + *b* = 2*b* + *b* = 3*b* = 9.

Cada signo igual es un paso, y cada paso tiene su porqué: el primero, porque *a* = 2*b*; el segundo, por álgebra; el tercero, porque *b* = 3. En la pizarra escribimos la cadena y, si hace falta, la justificación al lado.

Con `rw` se puede hacer lo mismo, pero la prueba queda como una lista de órdenes que no se parece a la cuenta. Lean tiene una forma de escribir la cadena tal cual: `calc`.

## La pregunta

¿Qué propiedades de la igualdad usa Lean, y cómo se invocan? ¿Cómo se escribe una cadena de igualdades, o de desigualdades, con la justificación de cada eslabón? ¿Y qué pasa si un eslabón está mal?

## La idea

La igualdad tiene tres propiedades básicas, y Lean les pone nombre:

- **Reflexiva**: *a* = *a*. Es `rfl`.
- **Simétrica**: si *a* = *b*, entonces *b* = *a*. Con `h : a = b`, es `h.symm`, o la táctica `symm`.
- **Transitiva**: si *a* = *b* y *b* = *c*, entonces *a* = *c*. Es `h1.trans h2`.

`calc` encadena la transitiva tantas veces como haga falta. Cada eslabón lleva su justificación detrás de `:=`, y el guion bajo `_` repite el final del eslabón anterior:

```text
calc a + b = 2 * b + b := by rw [h1]     ← primer eslabón, entero
  _ = 3 * b              := by ring      ← _ es «2 * b + b»
  _ = 9                  := by rw [h2]   ← _ es «3 * b»
```

:::{important} calc admite desigualdades
Una cadena puede mezclar `=`, `≤` y `<`. Lean sabe cuál es la conclusión: si hay al menos un `<`, el resultado es `<`; si hay algún `≤` y ningún `<`, es `≤`.
:::

## Construcción

### 1 · Las propiedades de la igualdad

:::{tip} Predice
Con `h1 : a = b` y `h2 : b = c`, ¿cuál es la meta tras `symm`, si era `c = a`?
:::

```lean
import Mathlib

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : c = a := by
  rw [h1, h2]

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : c = a := by
  symm
  exact h1.trans h2

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : c = a :=
  (h1.trans h2).symm
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Reflexiva, simétrica, transitiva","etiqueta":"symm · trans · rfl","idea":"Tres formas de llegar a `c = a`: reescribiendo, dando la vuelta a la meta con `symm` y encadenando con `trans`, o escribiendo la prueba directamente.","notas":{"1":"`rw` cambia `a` por `b` y después `b` por `c`: queda `c = c`, que se cierra con `rfl`.","2":"`symm` da la vuelta a la meta: de `c = a` pasa a `a = c`.","3":"`h1.trans h2` encadena `a = b` y `b = c` en `a = c`."}},"archivo":"datos/trazas/10-calc-1.json"}
```

- `rw [h1, h2]` funciona, pero no dice qué propiedad se usa: reescribe hasta que los dos lados coinciden.
- `symm` da la vuelta a la meta. `h.symm` da la vuelta a una hipótesis: si `h : a = b`, entonces `h.symm : b = a`.
- `h1.trans h2` encadena dos igualdades cuando el final de la primera es el principio de la segunda.
- El tercer ejemplo no usa tácticas: `(h1.trans h2).symm` es la prueba entera. De `a = b` y `b = c` sale `a = c`, y dándole la vuelta, `c = a`.

### 2 · Una cadena de igualdades

```lean
import Mathlib

example (a b : ℕ) (h1 : a = 2 * b) (h2 : b = 3) : a + b = 9 := by
  calc a + b = 2 * b + b := by rw [h1]
    _ = 3 * b := by ring
    _ = 9 := by rw [h2]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La cuenta, con su porqué","etiqueta":"calc · _ · :=","idea":"Cada eslabón de `calc` es una meta pequeña con su propia prueba. Lean comprueba que la cadena empieza en `a + b`, acaba en `9` y que cada eslabón está demostrado.","notas":{"2":"Primer eslabón: `a + b = 2 * b + b`, porque *a* = 2*b*.","3":"Segundo: `2 * b + b = 3 * b`. El `_` es el final del eslabón anterior. Es álgebra: `ring`.","4":"Tercero: `3 * b = 9`, porque *b* = 3."}},"archivo":"datos/trazas/10-calc-2.json"}
```

- La primera línea del `calc` escribe el eslabón entero: `a + b = 2 * b + b`. Las siguientes empiezan con `_`, que repite el lado derecho del eslabón anterior.
- Lo de detrás de `:=` es la prueba de ese eslabón, y puede ser cualquier cosa: una táctica (`by rw [h1]`), un teorema o una hipótesis.
- Lean comprueba tres cosas: que cada eslabón está demostrado, que la cadena empieza por el lado izquierdo de la meta (`a + b`) y que acaba en el derecho (`9`).
- La prueba se lee como en la pizarra, y en el panel cada eslabón aparece como una meta pequeña, con su contexto.

### 3 · Cadenas de desigualdades

:::{tip} Predice
Una cadena con `=`, `≤`, `≤`, `=`. ¿Qué relación demuestra entre el principio y el final?
:::

```lean
import Mathlib

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  calc a ^ 2 = a * a := by ring
    _ ≤ a * b := by nlinarith
    _ ≤ b * b := by nlinarith
    _ = b ^ 2 := by ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Mezclar = y ≤","etiqueta":"calc · ≤ · nlinarith","idea":"Una cadena puede mezclar igualdades y desigualdades. Con algún `≤` y ningún `<`, la cadena demuestra `≤` entre el principio y el final.","notas":{"2":"*a*² se escribe *a* · *a*: álgebra.","3":"*a* · *a* ≤ *a* · *b*, porque *a* ≤ *b* y *a* ≥ 0: multiplicar por un número no negativo no cambia el sentido.","4":"*a* · *b* ≤ *b* · *b*: ahora se multiplica por *b*, que también es ≥ 0 (porque 0 ≤ *a* ≤ *b*).","5":"Y *b* · *b* es *b*²."}},"archivo":"datos/trazas/10-calc-3.json"}
```

- La cadena demuestra *a*² ≤ *b*², que es la meta. Lean combina los eslabones: `=` con `≤` da `≤`, y `≤` con `≤` da `≤`.
- Cada desigualdad se justifica con `nlinarith`, que sabe multiplicar desigualdades entre sí: de 0 ≤ *a* y *a* ≤ *b* saca *a* · *a* ≤ *a* · *b*.
- Sin la hipótesis `ha`, el resultado es falso: con *a* = −3 y *b* = 1, *a* ≤ *b*, pero *a*² = 9 > 1 = *b*². Por eso la prueba la necesita.

### 4 · Un eslabón mal justificado

¿Qué pasa si la cuenta está bien pero el porqué de un eslabón no?

```lean
import Mathlib

example (x : ℝ) (h : x = 2) : x ^ 2 + 1 = 5 := by
  calc x ^ 2 + 1 = 2 ^ 2 + 1 := by rw [h]
    _ = 4 + 1 := by rw [h]
    _ = 5 := by norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lean señala el eslabón que falla","etiqueta":"calc · error","espera_error":true,"idea":"El segundo eslabón es cierto (2² + 1 = 4 + 1), pero su justificación no sirve: `rw [h]` busca una *x* que ya no está. Lean marca justo ese eslabón; los demás están bien.","notas":{"2":"Bien: *x* pasa a ser 2.","3":"En `2 ^ 2 + 1 = 4 + 1` no hay ninguna *x*: `rw [h]` no tiene nada que cambiar. Aquí habría que poner `norm_num`.","4":"Este eslabón está bien. Lean sigue comprobando aunque otro haya fallado."}},"archivo":"datos/trazas/10-calc-4.json"}
```

- El error sale en el segundo eslabón, y solo ahí: *did not find an occurrence of the pattern x*. Es el error de `rw` del capítulo 5.
- La cuenta es correcta, pero la justificación no. Lean no acepta un eslabón porque sea verdadero: hace falta una prueba que funcione.
- Lean sigue comprobando los demás eslabones, y el tercero está bien. En una cadena larga, el error dice exactamente dónde mirar.
- Para arreglarlo, basta cambiar `by rw [h]` por `by norm_num` en el segundo eslabón.

::::{div}
:class: afondo
### 5 · Qué es `=` para Lean

En Lean, la igualdad no es una primitiva mágica: está definida, como `Even` o `∃`.

```lean
import Mathlib

#print Eq

example (n m : ℕ) (h : n = m) (hn : n > 3) : m > 3 := h ▸ hn

example (n m : ℕ) (h : n = m) (hn : n > 3) : m > 3 := by
  subst h
  exact hn
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una igualdad deja cambiar una cosa por otra en cualquier sitio","etiqueta":"a fondo · Eq · ▸ · subst","idea":"`Eq` es un tipo con una sola forma de construirlo: `Eq.refl a : a = a`. De ahí sale todo lo demás, incluida la regla de que con `n = m` se puede cambiar *n* por *m* en cualquier afirmación.","notas":{"1":"`subst h` hace desaparecer *m*: lo sustituye por *n* en todo el panel, y `h` ya no hace falta.","2":"Y la meta es justo `hn`."}},"archivo":"datos/trazas/10-calc-5.json"}
```

`#print Eq` contesta que `Eq` es un tipo **inductivo** con un único constructor: `Eq.refl : ∀ {α : Sort u_1} (a : α), a = a`. La única forma de fabricar una prueba de igualdad es la reflexiva: *a* = *a*. Y `rfl` es justo eso, `Eq.refl` con el *a* que haga falta.

¿Cómo se demuestra entonces `2 + 2 = 4`? Con `Eq.refl 4`: Lean calcula `2 + 2`, ve que es `4`, y lo acepta como `4 = 4`. Es la igualdad **por definición** del capítulo 3.

De esa definición sale la regla que usa `rw`: si `h : n = m`, en cualquier afirmación sobre *n* se puede poner *m*. Escrita a mano es `h ▸ hn`: el triángulo transporta `hn : n > 3` a lo largo de `h` y da `m > 3`. `subst h` hace lo mismo en el panel: elimina *m* y deja todo en términos de *n*.

`symm` y `trans` no son axiomas: son teoremas que se demuestran a partir de `Eq.refl` y de esta regla de sustitución.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
La cadena *a* + *b* = 2*b* + *b* = 3*b* = 9, con *a* = 2*b* y *b* = 3 (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: calc, con _ para el eslabón anterior
example (a b : ℕ) (h1 : a = 2 * b) (h2 : b = 3) : a + b = 9 := by
  calc a + b = 2 * b + b := by rw [h1]
    _ = 3 * b := by ring
    _ = 9 := by rw [h2]
```

```coq
(* Rocq (Coq): transitivity fija el punto intermedio *)
Require Import Lia.
Goal forall a b : nat, a = 2 * b -> b = 3 -> a + b = 9.
Proof.
  intros a b h1 h2.
  transitivity (2 * b + b). { rewrite h1. reflexivity. }
  transitivity (3 * b). { lia. }
  rewrite h2. reflexivity.
Qed.
```

```isabelle
(* Isabelle: also ... finally, con ... para el eslabón anterior *)
lemma
  assumes h1: "a = 2 * b" and h2: "b = (3::nat)"
  shows "a + b = 9"
proof -
  have "a + b = 2 * b + b" using h1 by simp
  also have "... = 3 * b" by simp
  also have "... = 9" using h2 by simp
  finally show ?thesis .
qed
```

Isabelle tiene casi lo mismo que `calc`: cada eslabón es un `have`, los puntos suspensivos `...` repiten el final del anterior (el `_` de Lean), `also` los encadena y `finally` saca la conclusión. Rocq no trae una cadena así de serie: `transitivity (2 * b + b)` fija un punto intermedio y deja dos metas, una a cada lado, y se repite para cada eslabón.
:::

## Conexiones

- `rw`, del capítulo 5, se apoya en la regla de sustitución de `Eq`: con `h : a = b`, cambia *a* por *b* en la meta. Es `h ▸` aplicado por una táctica.
- `rfl` y la igualdad «por definición» del capítulo 3 son `Eq.refl`.
- `calc` vuelve en el capítulo 13, de desigualdades, y en la parte IV, en las estimaciones de límites y derivadas.
- `Eq` como tipo inductivo vuelve en la parte V, junto con `∧`, `∨` y `∃`, que también lo son.

## La grieta

Con la parte II tenemos todas las piezas de la lógica: las conectivas, los cuantificadores, la igualdad y las cadenas. Pero hay afirmaciones que ninguna de ellas basta para demostrar. ¿Cómo se demuestra que 1 + 2 + ⋯ + *n* = *n*(*n* + 1)/2 **para todo** *n*? Con `intro n`, *n* es un número cualquiera, y no hay cuenta que valga para todos a la vez. Hace falta una herramienta nueva, la que cierra el teorema que el capítulo 3 dejó con `sorry`: la **inducción**. Empieza la parte III.

## Ejercicios

1. **Dar la vuelta.** Con `h : 5 = x`, demuestra `x = 5` de dos formas: con `symm` y sin tácticas.

2. **Encadenar.** Con `h1 : a = b` y `h2 : b = 7`, demuestra `a = 7` sin tácticas.

3. **Un cuadrado.** Con `h : y = x + 1` y `x y : ℝ`, demuestra `y ^ 2 = x ^ 2 + 2 * x + 1` con un `calc` de dos eslabones.

4. **Una desigualdad.** Con `hx : x ≥ 3` y `x : ℝ`, demuestra `x ^ 2 ≥ 9` con un `calc`.

5. **¿Qué eslabón falla?** ¿Dónde da error este `calc`, y por qué?

   ```lean
   example (a : ℕ) (h : a = 4) : a * a = 16 := by
     calc a * a = a + a := by ring
       _ = 16 := by rw [h]
   ```

6. **Sustituir del todo.** Con `h : x = 3` y `hx : x + y = 10`, demuestra `y = 7` empezando con `subst h`.

::::{div}
:class: afondo
7. **El triángulo.** Con `h : a = b` y `ha : a > 0`, demuestra `b > 0` en una sola expresión, sin tácticas.

8. **La reflexiva.** ¿Qué tipo da `#check @rfl`? ¿Por qué `Eq.refl 4` demuestra `2 + 2 = 4`?
::::

## Solucionario

1. `symm` y `exact h`; o, sin tácticas, `h.symm`.
2. `h1.trans h2`.
3. ```lean
   example (x y : ℝ) (h : y = x + 1) : y ^ 2 = x ^ 2 + 2 * x + 1 := by
     calc y ^ 2 = (x + 1) ^ 2 := by rw [h]
       _ = x ^ 2 + 2 * x + 1 := by ring
   ```
4. ```lean
   example (x : ℝ) (hx : x ≥ 3) : x ^ 2 ≥ 9 := by
     calc x ^ 2 = x * x := by ring
       _ ≥ 3 * 3 := by nlinarith
       _ = 9 := by norm_num
   ```
   Una cadena con `≥` se lee de izquierda a derecha igual que con `≤`.
5. Fallan los dos eslabones. El primero, porque *a* · *a* = *a* + *a* no es una identidad: `ring` no puede demostrarla (solo vale para *a* = 0 y *a* = 2). El segundo, porque tras `rw [h]` queda `4 + 4 = 16`, que es falso. La cadena correcta pasa por `4 * 4`.
6. ```lean
   example (x y : ℕ) (h : x = 3) (hx : x + y = 10) : y = 7 := by
     subst h
     omega
   ```
   Tras `subst h`, *x* desaparece y `hx` pasa a ser `3 + y = 10`.

::::{div}
:class: afondo
7. `h ▸ ha`.
8. `@rfl : ∀ {α : Sort u_1} {a : α}, a = a`: para cualquier *a*, una prueba de *a* = *a*. `Eq.refl 4` es una prueba de `4 = 4`, y Lean la acepta para `2 + 2 = 4` porque, al calcular, `2 + 2` es `4`: son iguales por definición.
::::
