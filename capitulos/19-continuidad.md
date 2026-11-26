---
title: Continuidad y derivadas
subtitle: Épsilon y delta, y las reglas de derivar que ya están demostradas
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En Bachillerato, una función es continua si «se dibuja sin levantar el lápiz», y la derivada se calcula con reglas: la de *x*ⁿ es *nx*ⁿ⁻¹, la de una suma es la suma de las derivadas, y así hasta la regla de la cadena. Funciona muy bien para calcular.

Pero «sin levantar el lápiz» no sirve para demostrar nada. La definición precisa es la misma idea que el límite de una sucesión del capítulo 18, cambiando *n* por *x*: para cada margen ε en las imágenes hay un margen δ en los valores, de forma que si *x* está a menos de δ de *a*, entonces *f*(*x*) está a menos de ε de *f*(*a*). Y las reglas de derivar no son un acto de fe: son teoremas, y en Mathlib están todos demostrados.

## La pregunta

¿Cómo se escribe en Lean que una función es continua? ¿Cómo se demuestra con ε y δ? ¿Y cómo se trabaja con derivadas: cómo se calcula una, cómo se usan las reglas?

## La idea

Igual que en el capítulo 18, primero una definición propia, escrita tal cual:

```lean
def Continua (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
```

Y después lo que ya trae Mathlib:

| Concepto | En Mathlib | Táctica o teorema |
|---|---|---|
| *f* continua en todo ℝ | `Continuous f` | `fun_prop` |
| *f* tiene derivada *f′* en *a* | `HasDerivAt f f' a` | `hasDerivAt_pow`, `.fun_add`, `.const_mul`… |
| la derivada de *f* en *x* | `deriv f x` | `simp`, `deriv_fun_add` |
| *f* con forma ∪ en un conjunto | `ConvexOn ℝ s f` | `Even.convexOn_pow`… |

:::{important} Una advertencia sobre los nombres: cóncava y convexa
En este libro, como en el resto de mi material, una función es **cóncava** si tiene forma ∪ (*f*″ > 0) y **convexa** si tiene forma ∩ (*f*″ < 0). Muchos libros lo usan al revés, y **Mathlib también**: lo que aquí llamamos cóncava (forma ∪), Mathlib lo llama `ConvexOn`, y lo que aquí llamamos convexa (forma ∩), `ConcaveOn`. Cuando aparezca uno de esos nombres en Lean, piensa en la forma, no en la palabra.
:::

## Construcción

### 1 · Continuidad con ε y δ

:::{tip} Predice
Para *f*(*x*) = 3*x* + 1, si quieres que *f*(*x*) esté a menos de ε de *f*(*a*), ¿a qué distancia de *a* tiene que estar *x*?
:::

```lean
import Mathlib

def Continua (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

example (a : ℝ) : Continua (fun x => 3 * x + 1) a := by
  intro ε hε
  refine ⟨ε / 3, by positivity, ?_⟩
  intro x hx
  dsimp only
  rw [show 3 * x + 1 - (3 * a + 1) = 3 * (x - a) by ring, abs_mul]
  norm_num
  linarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un δ para cada ε","etiqueta":"ε-δ · refine · δ = ε/3","idea":"La recta 3*x* + 1 multiplica las distancias por 3: si *x* está a menos de δ de *a*, *f*(*x*) está a menos de 3δ de *f*(*a*). Para que 3δ sea ε, basta δ = ε/3.","notas":{"1":"Llega el margen ε en las imágenes.","2":"Se da el δ, ε/3, y se deja un hueco para lo demás…","3":"…después de comprobar que ε/3 > 0.","4":"Un *x* cualquiera, con `hx : |x - a| < ε / 3`.","5":"Se aplica la función: la meta es `|3 * x + 1 - (3 * a + 1)| < ε`.","6":"Se cambia la resta por 3(*x* − *a*) y se separa el valor absoluto del producto…","7":"…después de comprobar con `ring` que la resta es 3(*x* − *a*). Queda `|3| * |x - a| < ε`.","8":"|3| = 3: queda `3 * |x - a| < ε`.","9":"De |*x* − *a*| < ε/3, multiplicando por 3."}},"archivo":"datos/trazas/19-continuidad-1.json"}
```

- La definición tiene la misma forma que la de límite del capítulo 18: ∀ ε, ∃ δ, ∀ *x*. La diferencia es que ahora el segundo cuantificador lleva su propia condición, δ > 0.
- `refine ⟨ε / 3, by positivity, ?_⟩` da a la vez el δ y la prueba de que es positivo, y deja un hueco `?_` para el resto. Es el `use` del capítulo 9 con más control.
- El δ se encuentra hacia atrás, como en la pizarra: se quiere 3|*x* − *a*| < ε, así que basta |*x* − *a*| < ε/3.
- `abs_mul` dice que |*xy*| = |*x*| · |*y*|. Con eso, el 3 sale fuera del valor absoluto.

### 2 · Continuidad con Mathlib: `fun_prop`

Demostrar con ε y δ que cada función es continua sería agotador. En la práctica se hace como en clase: las funciones conocidas son continuas, y sumas, productos y composiciones de continuas también lo son.

```lean
import Mathlib

example : Continuous (fun x : ℝ => x ^ 2 + 3 * x) := by
  fun_prop

example : Continuous (fun x : ℝ => Real.sin (x ^ 2)) := by
  fun_prop

example : Continuous (fun x : ℝ => Real.exp x * Real.cos x) := by
  fun_prop
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Continua por piezas","etiqueta":"Continuous · fun_prop","idea":"`fun_prop` descompone la función en piezas (potencias, senos, exponenciales) y usa que sumas, productos y composiciones de continuas son continuas. Es la forma de razonar de clase, hecha automática.","notas":{"1":"Un polinomio: suma de una potencia y un múltiplo de *x*.","2":"Una composición: el seno de *x*².","3":"Un producto: exponencial por coseno."}},"archivo":"datos/trazas/19-continuidad-2.json"}
```

- `Continuous f` es «*f* es continua en todos los puntos». Es la versión de Mathlib, y equivale a nuestra `Continua f a` para todo *a*.
- `fun_prop` es una táctica que razona como en clase: mira cómo está construida la función, comprueba que cada pieza es continua y aplica las reglas de la suma, el producto y la composición.
- Sirve igual para otras propiedades de funciones, como ser derivable (`Differentiable`). Se verá en el apartado 4.

### 3 · Derivadas

Mathlib tiene dos formas de hablar de derivadas. `HasDerivAt f f' a` dice «*f* tiene derivada *f′* en el punto *a*», y es una afirmación. `deriv f x` es «la derivada de *f* en *x*», un número que se puede calcular.

```lean
import Mathlib

example (a : ℝ) : HasDerivAt (fun x => x ^ 2) (2 * a) a := by
  have h := hasDerivAt_pow 2 a
  simpa using h

example : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 := by
  ext x
  simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La derivada de xⁿ","etiqueta":"HasDerivAt · deriv","idea":"`hasDerivAt_pow` es la regla de *x*ⁿ, ya demostrada: la derivada en *a* es *n*·*a*ⁿ⁻¹. Con *n* = 2 sale ↑2 · *a*²⁻¹, y `simpa` lo deja en 2*a*.","notas":{"1":"La regla de la potencia con *n* = 2: `h : HasDerivAt (fun x => x ^ 2) (↑2 * a ^ (2 - 1)) a`.","2":"`simpa` arregla ↑2 · *a*²⁻¹ hasta dejarlo en 2*a*, y coincide con la meta.","3":"Dos funciones son iguales si coinciden en cada *x*: `⊢ deriv (fun x => x ^ 3) x = 3 * x ^ 2`.","4":"`simp` conoce la derivada de las potencias."}},"archivo":"datos/trazas/19-continuidad-3.json"}
```

- `hasDerivAt_pow n a` es la regla de la potencia: la derivada de *x*ⁿ en *a* es *n* · *a*ⁿ⁻¹. Lean la escribe con una flecha, ↑*n*, porque *n* es natural y la derivada es real.
- `simpa using h` simplifica la hipótesis (↑2 · *a*²⁻¹ = 2*a*) y la usa para cerrar.
- Para `deriv`, que es una función, la igualdad de funciones se demuestra punto a punto con `ext x` (capítulos 16 y 17). Después, `simp` sabe derivar potencias.

### 4 · Las reglas de derivar, y la forma ∪

La derivada de una suma es la suma de las derivadas: en Mathlib, `.fun_add`. La de una constante por una función, la constante por la derivada: `.const_mul`. Con eso se derivan los polinomios pieza a pieza.

```lean
import Mathlib

example (a : ℝ) : HasDerivAt (fun x => x ^ 2 + 3 * x) (2 * a + 3) a := by
  have h := (hasDerivAt_pow 2 a).fun_add ((hasDerivAt_id' a).const_mul 3)
  simpa using h

example (a : ℝ) : deriv (fun x : ℝ => x ^ 2 + 3 * x) a = 2 * a + 3 := by
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  simp

example : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  exact even_two.convexOn_pow
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Pieza a pieza","etiqueta":"fun_add · deriv_fun_add · ConvexOn","idea":"La derivada de *x*² + 3*x* sale sumando la de *x*² (regla de la potencia) y la de 3*x* (3 por la derivada de *x*). Y *x*² tiene forma ∪ en todo ℝ: cóncava en la convención del libro, `ConvexOn` en la de Mathlib.","notas":{"1":"Potencia más 3 por la identidad: `h : HasDerivAt (fun i => i ^ 2 + 3 * i) (↑2 * a ^ (2 - 1) + 3 * 1) a`.","2":"`simpa` deja la derivada en 2*a* + 3.","3":"La derivada de la suma es la suma de las derivadas, si las dos piezas son derivables…","4":"…*x*², derivable…","5":"…y 3*x*, también. Queda `deriv (fun x => x ^ 2) a + deriv (HMul.hMul 3) a = 2 * a + 3`.","6":"`simp` calcula las dos derivadas y suma.","7":"*x*² tiene forma ∪ en todo ℝ. Mathlib lo dice para cualquier potencia par."}},"archivo":"datos/trazas/19-continuidad-4.json"}
```

- `hasDerivAt_id' a` dice que la derivada de *x* es 1, y `.const_mul 3` la multiplica por 3. `.fun_add` suma dos derivadas: es la regla de la suma, ya demostrada.
- Con `deriv`, la regla de la suma es `deriv_fun_add`, que pide antes dos pruebas: que cada sumando es derivable. `fun_prop` las da.
- `ConvexOn ℝ Set.univ f` es la forma ∪ en todo ℝ: el segmento entre dos puntos de la gráfica queda por encima de la gráfica. **En la convención de este libro, eso es cóncava.** Mathlib, como muchos textos, la llama convexa.
- `Even.convexOn_pow` dice que toda potencia par, *x*², *x*⁴…, tiene forma ∪ en todo ℝ. `even_two` es la prueba de que 2 es par.

::::{div}
:class: afondo
### 5 · *x*² es continua, con ε y δ

Para la recta bastaba δ = ε/3, porque las distancias se multiplican siempre por 3. Con *x*² no: cuanto más lejos de 0 está *a*, más se estiran las distancias. El δ tiene que depender de ε y también de *a*.

```lean
import Mathlib

def Continua (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

example (a : ℝ) : Continua (fun x => x ^ 2) a := by
  intro ε hε
  refine ⟨min 1 (ε / (2 * |a| + 1)), by positivity, ?_⟩
  intro x hx
  have h1 : |x - a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - a| < ε / (2 * |a| + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have h3 : |x + a| ≤ 2 * |a| + 1 := by
    calc |x + a| = |(x - a) + 2 * a| := by ring_nf
      _ ≤ |x - a| + |2 * a| := abs_add_le _ _
      _ ≤ 1 + 2 * |a| := by rw [abs_mul]; norm_num; linarith
      _ = 2 * |a| + 1 := by ring
  dsimp only
  rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring, abs_mul]
  calc |x - a| * |x + a| ≤ |x - a| * (2 * |a| + 1) := by gcongr
    _ < ε / (2 * |a| + 1) * (2 * |a| + 1) := by gcongr
    _ = ε := by field_simp
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El δ también depende de a","etiqueta":"a fondo · ε-δ · min","idea":"*x*² − *a*² = (*x* − *a*)(*x* + *a*). El primer factor lo controla δ; el segundo hay que acotarlo. Con |*x* − *a*| < 1, |*x* + *a*| ≤ 2|*a*| + 1, y basta δ = mín(1, ε/(2|*a*| + 1)).","notas":{"1":"Llega ε > 0.","2":"El δ es el menor de dos números: 1 y ε/(2|*a*| + 1)…","3":"…y `positivity` sabe que el mínimo de dos positivos es positivo.","4":"Un *x* con |*x* − *a*| menor que ese mínimo.","5":"Como el mínimo es ≤ 1: |*x* − *a*| < 1.","6":"Como el mínimo es ≤ ε/(2|*a*| + 1): |*x* − *a*| < ε/(2|*a*| + 1).","7":"La cota del segundo factor: |*x* + *a*| ≤ 2|*a*| + 1…","8":"…por una cadena:","9":"*x* + *a* = (*x* − *a*) + 2*a*,","10":"desigualdad triangular y |2*a*| = 2|*a*|…","11":"…(|2| = 2)…","12":"…con |*x* − *a*| < 1,","13":"y se ordenan los sumandos.","14":"Se aplica la función: `|x ^ 2 - a ^ 2| < ε`.","15":"Se factoriza *x*² − *a*² y se separa el valor absoluto…","16":"…(la factorización la comprueba `ring`): `|x - a| * |x + a| < ε`.","17":"La cadena final, eslabón a eslabón.","18":"Se cambia |*x* + *a*| por su cota (`h3`).","19":"Se cambia |*x* − *a*| por la suya (`h2`); el factor 2|*a*| + 1 es positivo.","20":"Y se tacha el denominador: ε."}},"archivo":"datos/trazas/19-continuidad-5.json"}
```

La clave es factorizar: |*x*² − *a*²| = |*x* − *a*| · |*x* + *a*|. El primer factor es pequeño si δ lo es. El segundo no se puede hacer pequeño, pero sí **acotar**: si |*x* − *a*| < 1, entonces |*x* + *a*| = |(*x* − *a*) + 2*a*| ≤ 1 + 2|*a*| (desigualdad triangular, `h3`).

Por eso el δ es un mínimo, `min 1 (ε / (2 * |a| + 1))`. Lo de 1 garantiza la cota de `h3`; lo de ε/(2|*a*| + 1) hace que el producto quede por debajo de ε. `min_le_left` y `min_le_right` sacan las dos consecuencias: |*x* − *a*| < 1 y |*x* − *a*| < ε/(2|*a*| + 1).

El final es una cadena (`calc`): |*x* − *a*| · |*x* + *a*| ≤ |*x* − *a*| · (2|*a*| + 1) < ε/(2|*a*| + 1) · (2|*a*| + 1) = ε. Los dos primeros eslabones los hace `gcongr` (capítulo 13), comparando pieza a pieza; el último, `field_simp`, que tacha el denominador porque es positivo.

Es la prueba que se hace en primero de carrera, y que cuesta: aquí cada paso está a la vista, con su justificación.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
*f*(*x*) = 3*x* + 1 es continua en todo ℝ, con la táctica automática de cada sistema (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example : Continuous (fun x : ℝ => 3 * x + 1) := by
  fun_prop
```

```coq
(* Rocq (Coq) *)
Require Import Reals.
Open Scope R_scope.
Lemma c : continuity (fun x => 3 * x + 1).
Proof.
  reg.
Qed.
```

```isabelle
(* Isabelle *)
lemma c: "continuous_on UNIV (\<lambda>x::real. 3 * x + 1)"
  by (intro continuous_intros)
```

Los tres hacen lo mismo que en clase: la función es una suma de un producto y una constante, y las tres piezas son continuas. En Rocq, `reg` (de *regularity*) aplica las reglas de continuidad y derivabilidad de la biblioteca de reales. En Isabelle, `continuous_intros` es la colección de reglas de continuidad (suma, producto, constantes, identidad), y `intro` las aplica hasta terminar.
:::

## Conexiones

- La definición ε-δ es la de límite del capítulo 18 con *x* real en lugar de *n* natural; las tácticas son las mismas.
- Las desigualdades del capítulo 13 (`abs_add_le`, `gcongr`, `linarith`) hacen el trabajo en las pruebas ε-δ.
- `ext` para igualar funciones viene de los capítulos 16 y 17.
- El capítulo 20 enseña a encontrar teoremas como `hasDerivAt_pow` o `Even.convexOn_pow` sin saberse el nombre.

## La grieta

En este capítulo han aparecido nombres como `hasDerivAt_pow`, `deriv_fun_add`, `Even.convexOn_pow` o `tendsto_one_div_add_atTop_nhds_zero_nat`. Mathlib tiene más de cien mil teoremas. ¿Cómo se encuentra el que hace falta? ¿Hay que sabérselos? No: hay tácticas que buscan (`exact?`, `apply?`), un buscador en lenguaje natural y unas reglas para adivinar los nombres. Lo vemos en **Buscar en Mathlib**.

## Ejercicios

1. **Otra recta.** Demuestra `Continua (fun x => 5 * x - 2) a`. ¿Qué δ eliges?

2. **Un polinomio.** Demuestra `Continuous (fun x : ℝ => x ^ 3 - 2 * x + 1)`.

3. **La derivada de x³.** Demuestra `HasDerivAt (fun x => x ^ 3) (3 * a ^ 2) a` con `hasDerivAt_pow`.

4. **La constante.** Demuestra que la función constante *c* es continua en cualquier *a*, con la definición ε-δ. ¿Qué δ sirve?

5. **El seno.** ¿Cuál es la derivada de `Real.sin`? Busca el teorema `Real.deriv_sin` con `#check` y úsalo.

6. **El doble.** Si *f* es continua en *a*, demuestra que 2*f* también lo es. ¿Qué margen le pides a *f*?

::::{div}
:class: afondo
7. **Forma ∪.** Demuestra `ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4)`. En la convención del libro, ¿*x*⁴ es cóncava o convexa?

8. **¿Por qué el mínimo?** En el apartado 5, ¿qué fallaría si se tomase δ = ε/(2|*a*| + 1) sin el mínimo con 1?
::::

## Solucionario

1. δ = ε/5:
   ```lean
   example (a : ℝ) : Continua (fun x => 5 * x - 2) a := by
     intro ε hε
     refine ⟨ε / 5, by positivity, ?_⟩
     intro x hx
     dsimp only
     rw [show 5 * x - 2 - (5 * a - 2) = 5 * (x - a) by ring, abs_mul]
     norm_num
     linarith
   ```
2. `fun_prop`.
3. `simpa using hasDerivAt_pow 3 a`.
4. Cualquier δ sirve, porque |*c* − *c*| = 0 < ε siempre:
   ```lean
   example (c a : ℝ) : Continua (fun _ => c) a := by
     intro ε hε
     refine ⟨1, by norm_num, ?_⟩
     intro x hx
     simp
     exact hε
   ```
5. `Real.deriv_sin : deriv Real.sin = Real.cos`. Se usa tal cual: `example : deriv Real.sin = Real.cos := Real.deriv_sin`.
6. Se le pide ε/2:
   ```lean
   example (f : ℝ → ℝ) (a : ℝ) (hf : Continua f a) : Continua (fun x => 2 * f x) a := by
     intro ε hε
     obtain ⟨δ, hδ, h⟩ := hf (ε / 2) (by positivity)
     refine ⟨δ, hδ, ?_⟩
     intro x hx
     have := h x hx
     dsimp only
     rw [show 2 * f x - 2 * f a = 2 * (f x - f a) by ring, abs_mul]
     norm_num
     linarith
   ```

::::{div}
:class: afondo
7. `exact (by decide : Even 4).convexOn_pow`. *x*⁴ tiene forma ∪, así que en la convención del libro es **cóncava** (Mathlib la llama convexa: `ConvexOn`).
8. Sin el 1 no se podría acotar |*x* + *a*|: si δ fuese grande, *x* podría estar lejos de *a* y |*x* + *a*| no tendría por qué ser ≤ 2|*a*| + 1. El mínimo con 1 asegura |*x* − *a*| < 1, que es lo que necesita `h3`.
::::
