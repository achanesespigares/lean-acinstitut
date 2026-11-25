---
title: Proposiciones y pruebas
subtitle: Afirmar no es demostrar, y Lean distingue las dos cosas
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

«2 + 2 = 4» y «2 + 2 = 5» son dos frases con la misma forma. Una es verdadera y la otra es falsa, pero las dos se pueden **decir**. En un examen, escribir la primera no basta: hay que justificarla.

En matemáticas, una afirmación y su demostración son cosas distintas. Lean lo toma al pie de la letra: las afirmaciones tienen su propio tipo, y las demostraciones son objetos que Lean revisa uno a uno.

## La pregunta

¿Qué es una afirmación para Lean? ¿Qué cuenta como demostrarla? ¿Y cómo se afirma algo de **todos** los números, como «*n* + 0 = *n* para cualquier *n*», la grieta del capítulo anterior?

## La idea

- Una **proposición** es una afirmación. Su tipo es `Prop`. `2 + 2 = 4` es una proposición, y `2 + 2 = 5` también: decir algo falso no es un error de escritura.
- Un **teorema** une una proposición con su **prueba**:

```text
theorem dos_mas_dos : 2 + 2 = 4 := by rfl
        ────┬──────   ───┬─────    ──┬───
          nombre    proposición    prueba
```

- Para hablar de todos los números se usa **∀**, que se lee «para todo»: `∀ n : ℕ, n + 0 = n`.
- Para demostrar algo con ∀, se empieza igual que en la pizarra: «sea *n* un natural cualquiera». En Lean eso es la táctica `intro n`.

:::{important} Un teorema demostrado se puede usar
Un teorema con nombre es como un resultado del libro de texto: se puede citar en otra demostración. Y si le das números, sale la prueba de ese caso concreto.
:::

## Construcción

### 1 · Proposiciones

:::{tip} Predice
¿Qué tipo dirá `#check` de `2 + 2 = 5`, que es falsa?
:::

```lean
import Mathlib

#check 2 + 2 = 4
#check 2 + 2 = 5
#check ∀ n : ℕ, n + 0 = n
#eval decide (2 + 2 = 5)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Las afirmaciones tienen tipo","etiqueta":"Prop · ∀ · decide","idea":"Una proposición se puede escribir sea verdadera o falsa. `#check` no dice si es cierta: solo que es una proposición, de tipo `Prop`.","notas":{"1":"Una afirmación es un objeto de tipo `Prop`.","2":"Falsa, pero bien escrita: también es de tipo `Prop`. Afirmar no es demostrar.","3":"`∀ n : ℕ` se lee «para todo natural *n*». Lean escribe los paréntesis: `∀ (n : ℕ)`.","4":"`decide` calcula si la afirmación es verdadera: aquí, `false`."}},"archivo":"datos/trazas/03-proposiciones-1.json"}
```

- `#check 2 + 2 = 4` y `#check 2 + 2 = 5` contestan lo mismo: `… : Prop`. Las dos son proposiciones, aunque solo una sea cierta.
- `#check ∀ n : ℕ, n + 0 = n` contesta `∀ (n : ℕ), n + 0 = n : Prop`. Con ∀, una sola proposición habla de infinitos números.
- `decide (2 + 2 = 5)` da `false`. Para afirmaciones sobre números concretos, Lean puede calcular si son verdaderas. Para afirmaciones con ∀, no: haría falta probar infinitos casos.

### 2 · Teoremas y la táctica `intro`

```lean
import Mathlib

theorem dos_mas_dos : 2 + 2 = 4 := by
  rfl

theorem para_todo : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"De una afirmación concreta a una para todo","etiqueta":"theorem · intro · rfl","idea":"En el segundo teorema, mira cómo cambia el panel con `intro n`: el ∀ desaparece de la meta y aparece `n : ℕ` encima de la raya.","notas":{"1":"2 + 2 y 4 son iguales por definición: basta con calcular.","2":"«Sea *n* un natural cualquiera.» A partir de aquí, `n` es un número fijo pero desconocido, y la meta habla solo de él.","3":"Por cómo está definida la suma en Lean, *n* + 0 se reduce a *n*, sea cual sea *n*."}},"archivo":"datos/trazas/03-proposiciones-2.json"}
```

- `dos_mas_dos` se demuestra con `rfl`: los dos lados son iguales al calcular.
- En `para_todo`, la meta empieza siendo `∀ (n : ℕ), n + 0 = n`. Tras `intro n`, encima de la raya aparece `n : ℕ` y la meta pasa a ser `n + 0 = n`. Es el «sea *n* un natural cualquiera» de la pizarra.
- `rfl` cierra la meta para ese *n* cualquiera, y así queda demostrado para todos. Funciona porque, en Lean, *n* + 0 se reduce a *n* por la propia definición de la suma (el apartado A fondo lo cuenta).

### 3 · Usar un teorema

```lean
import Mathlib

theorem conmuta (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

example : 3 + 5 = 5 + 3 := by
  exact conmuta 3 5

#check conmuta
#check conmuta 3 5
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Citar un teorema","etiqueta":"exact · Nat.add_comm","idea":"`Nat.add_comm` es un teorema que ya trae Lean. `conmuta` lo cita, y después el `example` cita a `conmuta`. Al final, `#check` enseña qué es `conmuta 3 5`: la prueba de un caso concreto.","notas":{"1":"`Nat.add_comm a b` es la prueba de `a + b = b + a` que trae Lean: `exact` la entrega tal cual.","2":"`conmuta 3 5` es la prueba de `3 + 5 = 5 + 3`: justo lo que se pide."}},"archivo":"datos/trazas/03-proposiciones-3.json"}
```

- `Nat.add_comm` es un teorema que ya viene con Lean: la suma de naturales conmuta. `exact Nat.add_comm a b` entrega esa prueba y cierra la meta.
- En el `example`, `exact conmuta 3 5` usa el teorema que acabas de demostrar, con *a* = 3 y *b* = 5.
- `#check conmuta` escribe la firma del teorema: `conmuta (a b : ℕ) : a + b = b + a`.
- `#check conmuta 3 5` contesta `conmuta 3 5 : 3 + 5 = 5 + 3`. Lo de después de los dos puntos es el tipo, y el tipo de esta prueba es la afirmación que demuestra. En Lean, **una prueba tiene por tipo lo que demuestra**. La parte V vuelve sobre esta idea.

### 4 · Dejar un hueco: `sorry`

La grieta del capítulo anterior era 2 · `suma n` = *n* · (*n* + 1) para todo *n*. Todavía no sabemos demostrarlo, pero sí **afirmarlo**, y usarlo mientras tanto.

```lean
import Mathlib

def suma : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + suma n

theorem suma_formula (n : ℕ) : 2 * suma n = n * (n + 1) := by
  sorry

theorem usa (n : ℕ) : 2 * suma n = n * n + n := by
  rw [suma_formula]
  ring

#print axioms usa
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un teorema pendiente","etiqueta":"sorry · rw · #print axioms","idea":"`sorry` tapa la meta sin demostrarla. Lean lo acepta, pero avisa, y deja la marca en todo lo que lo use.","notas":{"2":"`rw [suma_formula]` cambia `2 * suma n` por `n * (n + 1)`, usando el teorema pendiente.","3":"La demostración de `usa` está completa… si `suma_formula` es cierto. `#print axioms` lo dirá."}},"archivo":"datos/trazas/03-proposiciones-4.json"}
```

- `sorry` cierra la meta sin demostrarla. Lean lo acepta y escribe un aviso, en inglés: *declaration uses `sorry`*.
- `usa` cita a `suma_formula` con `rw`, que cambia `2 * suma n` por `n * (n + 1)`, y `ring` termina.
- `#print axioms usa` contesta `'usa' depends on axioms: [propext, sorryAx]`. `sorryAx` delata que, en algún punto de la cadena, hay un `sorry`. Lean no olvida los huecos.
- `sorry` sirve para trabajar de arriba abajo: afirmar los pasos intermedios, comprobar que encajan y rellenarlos después. La parte III, con la inducción, rellenará este.

::::{div}
:class: afondo
### 5 · Por qué *n* + 0 sí y 0 + *n* no

`rfl` demostró `n + 0 = n`. ¿Y `0 + n = n`, que es igual de cierto?

```lean
import Mathlib

example (n : ℕ) : n + 0 = n := by
  rfl

example (n : ℕ) : 0 + n = n := by
  rfl

example (n : ℕ) : 0 + n = n := by
  simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"rfl solo ve lo que dice la definición","etiqueta":"a fondo · rfl · simp","espera_error":true,"idea":"La suma de naturales está definida mirando el segundo sumando. Con *n* + 0, Lean sabe qué hacer; con 0 + *n*, no, porque no sabe si *n* es 0 o el siguiente de otro.","notas":{"1":"*n* + 0 se reduce a *n* por la primera regla de la suma.","2":"0 + *n* no se puede reducir sin saber cómo es *n*.","3":"`simp` usa un teorema ya demostrado, `zero_add`: 0 + *n* = *n*."}},"archivo":"datos/trazas/03-proposiciones-5.json"}
```

La suma de naturales está definida en Lean por recursión **en el segundo sumando**, con dos reglas:

- *n* + 0 = *n*;
- *n* + (*m* + 1) = (*n* + *m*) + 1.

Con `n + 0`, la primera regla se aplica directamente: por eso `rfl` funciona. Con `0 + n`, ninguna regla encaja, porque Lean no sabe si `n` es 0 o el siguiente de otro número. `rfl` falla: Lean dice, en inglés, que `0 + n` *is not definitionally equal* a `n`, que no son iguales por definición.

`simp` sí lo demuestra: no calcula, sino que usa un teorema ya demostrado, `zero_add`. Ese teorema, a su vez, se demuestra por **inducción**.

La diferencia entre «igual por definición» y «igual por un teorema» es de las primeras cosas que se notan al demostrar con un ordenador. En la pizarra, las dos cosas parecen igual de obvias.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«Para todo natural *n*, *n* + 0 = *n*» (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: la suma mira el segundo sumando, y basta con rfl
theorem mas_cero : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl
```

```coq
(* Rocq (Coq): la suma mira el primer sumando; hace falta un teorema *)
Require Import Arith.
Theorem mas_cero : forall n : nat, n + 0 = n.
Proof. intro n. apply Nat.add_0_r. Qed.
```

```isabelle
(* Isabelle: las variables libres valen para todo n *)
lemma mas_cero: "n + 0 = (n::nat)" by simp
```

En Rocq pasa justo al revés que en Lean: su suma está definida mirando el **primer** sumando, así que `0 + n = n` sale con `reflexivity`, y `n + 0 = n` no (Rocq dice *Unable to unify "n" with "n + 0"*). La misma verdad matemática, y en cada demostrador es fácil por un lado distinto. Isabelle lo resuelve con `simp`, y escribe el teorema como `?n + 0 = ?n`: el `?n` indica que vale para cualquier *n*.
:::

## Conexiones

- En el capítulo 1, `decide` comprobaba afirmaciones sobre números concretos calculando. Con ∀, ya no se puede calcular: hay que razonar.
- `intro n` es el «sea *n* un natural cualquiera» de toda demostración. La parte II lo usará con implicaciones: para demostrar «si *p*, entonces *q*», se supone *p*.
- `#check conmuta 3 5` ha enseñado que una prueba tiene por tipo lo que demuestra. Es la idea de **proposiciones como tipos**, en la parte V.
- `sorry` y `#print axioms` vuelven en la parte V, al hablar de qué tiene que aceptar uno para fiarse de una demostración.

## La grieta

En este capítulo, Lean ha escrito el panel de metas, y lo hemos mirado de pasada. Pero ¿qué significa exactamente cada línea: los nombres encima de la raya, el `⊢`, los casos? ¿Y qué pasa cuando hay varias metas a la vez? El capítulo siguiente, **El panel de metas**, lo cuenta con calma.

## Ejercicios

1. **¿Qué tipo?** ¿Qué contesta `#check 3 < 2`?

2. **¿Verdadero?** ¿Y `#eval decide (3 < 2)`?

3. **Un teorema concreto.** Demuestra que 10 − 3 = 7.

4. **Para todo.** Demuestra `∀ n : ℕ, n * 1 = n`. ¿Sirve `rfl` después de `intro n`?

5. **Citar.** Usa el teorema `conmuta` para demostrar que 10 + 20 = 20 + 10.

6. **El tipo de una prueba.** ¿Qué contesta `#check conmuta 10 20`?

::::{div}
:class: afondo
7. **Igual, pero no por definición.** Explica por qué `rfl` demuestra `n + 0 = n` y no `0 + n = n`. ¿En Rocq pasa lo mismo?

8. **El rastro de un hueco.** ¿Qué dice `#print axioms` de un teorema que no tiene ningún `sorry`, como `conmuta`?
::::

## Solucionario

1. `3 < 2 : Prop`. Es una proposición, aunque sea falsa.
2. `false`.
3. `example : 10 - 3 = 7 := by decide`.
4. `intro n` y después `simp`. `rfl` no sirve: Lean dice que `n * 1` no es igual a `n` por definición, porque la multiplicación de naturales está definida a partir de la suma, y *n* · 1 se queda en 0 + *n*, el mismo problema del apartado A fondo.
5. `example : 10 + 20 = 20 + 10 := by exact conmuta 10 20`.
6. `conmuta 10 20 : 10 + 20 = 20 + 10`: la prueba de ese caso concreto.

::::{div}
:class: afondo
7. En Lean, la suma está definida mirando el segundo sumando: *n* + 0 = *n* es una de sus reglas, y `0 + n` no encaja en ninguna mientras no se sepa cómo es *n*. En Rocq es al revés: su suma mira el primer sumando, y `reflexivity` demuestra `0 + n = n` pero no `n + 0 = n`.
8. `'conmuta' does not depend on any axioms`: no usa `sorry` ni ningún axioma.
::::
