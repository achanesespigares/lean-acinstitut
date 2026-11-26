---
title: Buscar en Mathlib
subtitle: exact?, apply? y el arte de adivinar cómo se llama un teorema
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En los capítulos anteriores han ido apareciendo nombres como `sq_nonneg`, `abs_mul`, `add_le_add` o `hasDerivAt_pow`. Cada uno es un teorema de Mathlib, y cada vez parecía que había que sabérselo.

No hay que sabérselos. Mathlib es enorme: en la versión que usa este libro, unos 180 000 teoremas escritos a mano, repartidos en más de 8 700 archivos. Nadie se los sabe. Lo que sí se aprende es a **encontrarlos**, igual que en clase nadie se sabe el número de página de cada propiedad, pero sabe dónde buscarla y la reconoce en cuanto la ve.

## La pregunta

Si sé lo que quiero demostrar, pero no cómo se llama el teorema que lo dice, ¿cómo lo encuentro? ¿Puede Lean buscarlo por mí? ¿Y hay alguna forma de adivinar el nombre sin buscar?

## La idea

Hay tres caminos, y se usan los tres:

| Camino | Qué haces | Herramienta |
|---|---|---|
| Que Lean busque | Escribes la meta y le pides que encuentre el teorema | `exact?`, `apply?`, `simp?`, `rw?` |
| Adivinar el nombre | Lees el enunciado como una frase y lo traduces a un nombre | las reglas de nombres de Mathlib, y `#check` para comprobar |
| Buscar fuera | Escribes la forma o una frase en un buscador web | Loogle, LeanSearch |

:::{important} Un teorema se busca por su forma
Lean no entiende «la propiedad conmutativa». Lo que entiende es una forma: `a + b = b + a`. Por eso la búsqueda empieza siempre igual: escribir **la meta exacta** que quieres demostrar, con sus hipótesis. A partir de ahí, Lean (o tú) busca un teorema que tenga esa forma.
:::

## Construcción

### 1 · `exact?`: que Lean busque

:::{tip} Predice
Para demostrar `a + b = b + a` con números naturales, ¿qué teorema crees que encontrará Lean? ¿Y cómo crees que se llamará?
:::

```lean
import Mathlib

example (a b : ℕ) : a + b = b + a := by
  exact?

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact?

example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  exact?
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lean busca el teorema","etiqueta":"exact? · Try this","idea":"`exact?` recorre Mathlib buscando un teorema que, con las hipótesis que hay, dé **exactamente** la meta. Cuando lo encuentra, cierra la meta y escribe en los mensajes la línea `exact …` que puedes copiar en su lugar.","notas":{"1":"Encuentra la conmutativa de la suma de naturales: `exact Nat.add_comm a b`.","2":"Un producto de no negativos es no negativo: `exact Left.mul_nonneg ha hb`. Usa las dos hipótesis.","3":"Se suman dos desigualdades miembro a miembro: `exact add_le_add h1 h2`."}},"archivo":"datos/trazas/20-buscar-1.json"}
```

- `exact?` no adivina: **busca**. Prueba los teoremas de Mathlib cuya conclusión puede encajar con la meta y comprueba si las hipótesis que tienes bastan.
- Cuando lo encuentra, escribe `Try this: exact …`. Lo normal es **copiar esa línea en lugar de `exact?`**: la prueba queda escrita, se entiende al leerla y se comprueba al instante, sin volver a buscar.
- El nombre que propone no siempre es el más conocido. Para el producto ha encontrado `Left.mul_nonneg`, aunque también existe `mul_nonneg`, que dice lo mismo. Cualquiera de los dos sirve.
- Buscar cuesta: cada `exact?` tarda unos segundos, porque recorre medio Mathlib. Otra razón para copiar la sugerencia.

### 2 · `apply?`, `simp?` y `rw?`

`exact?` tiene hermanos. Todos acaban en `?`, y todos hacen lo mismo: el trabajo de la táctica sin interrogación, más un mensaje que cuenta cómo lo han hecho.

```lean
import Mathlib

example (a b : ℝ) (hab : a < b) : a < (a + b) / 2 := by
  apply?

example (a : ℕ) : a + 0 = a := by
  simp?
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Los hermanos de exact?","etiqueta":"apply? · simp?","idea":"`apply?` busca teoremas cuya conclusión encaje con la meta, aunque dejen cosas por demostrar. `simp?` simplifica como `simp` y dice qué reglas ha usado, para que puedas escribir un `simp only` con justo esas.","notas":{"1":"Un número menor que otro es menor que la media de los dos. `apply?` encuentra `exact left_lt_add_div_two.mpr hab`: el teorema es un «si y solo si», y `.mpr` usa la implicación de derecha a izquierda.","2":"`simp?` cierra la meta con una sola regla y lo dice: `simp only [add_zero]`."}},"archivo":"datos/trazas/20-buscar-2.json"}
```

- `apply?` es más generoso que `exact?`: si ningún teorema cierra la meta, propone los que la **reducen** a otras metas más sencillas. Aquí ha encontrado uno que la cierra.
- `left_lt_add_div_two` es un «si y solo si»: *a* < (*a* + *b*)/2 ↔ *a* < *b*. Un «si y solo si» son dos implicaciones: `.mp` va de izquierda a derecha (ya salió en el capítulo 12, con `Nat.dvd_add_right`) y `.mpr` de derecha a izquierda. Aquí, de *a* < *b* sale lo otro.
- `simp?` es muy útil para que una prueba no dependa de todo el conjunto de reglas de `simp`, que cambia de una versión de Mathlib a otra. `simp only [add_zero]` hace lo mismo y es estable.
- `rw?` busca igualdades con las que reescribir la meta. Para `b + a = 7` con `h : a + b = 7`, entre sus primeras propuestas está `rw [Nat.add_comm]`, que deja `a + b = 7`, justo `h`. Pero propone muchas más (una veintena), y elegir es cosa tuya.

### 3 · Los nombres se leen

Un nombre de Mathlib no es una etiqueta arbitraria: **es el enunciado leído en voz alta**, con unas abreviaturas fijas. Si te sabes las abreviaturas, puedes adivinar el nombre antes de buscarlo, y comprobarlo con `#check`.

| Abreviatura | Significa | Abreviatura | Significa |
|---|---|---|---|
| `add`, `mul`, `sub`, `div` | +, ·, −, / | `le`, `lt` | ≤, < |
| `sq`, `pow` | cuadrado, potencia | `pos`, `nonneg` | > 0, ≥ 0 |
| `abs` | valor absoluto | `comm`, `assoc` | conmutativa, asociativa |
| `two`, `one`, `zero` | 2, 1, 0 | `of` | «a partir de» |

```lean
import Mathlib

#check mul_comm
#check add_le_add
#check sq_nonneg
#check abs_mul
#check two_mul
#check le_of_lt
#check lt_of_le_of_lt
#check Nat.Prime.two_le
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El nombre es el enunciado","etiqueta":"#check · nombres de Mathlib","idea":"Cada nombre se lee de izquierda a derecha y dice lo que afirma el teorema. Lo que va antes de `of` es la conclusión; lo que va después, las hipótesis.","notas":{"1":"*mul comm*: el producto conmuta, *a* · *b* = *b* · *a*.","2":"*add le add*: una suma ≤ otra suma, si cada sumando es ≤ el suyo (`h₁`, `h₂`).","3":"*sq nonneg*: el cuadrado es no negativo, 0 ≤ *a*².","4":"*abs mul*: el valor absoluto de un producto, |*a* · *b*| = |*a*| · |*b*|.","5":"*two mul*: dos por algo, 2 · *n* = *n* + *n*. El nombre describe el lado izquierdo.","6":"*le of lt*: ≤ a partir de <. La hipótesis va después de `of`.","7":"*lt of le of lt*: < a partir de un ≤ y un <, encadenados.","8":"El nombre lleva delante `Nat.Prime`: es un teorema sobre primos. Si `hp : p.Prime`, se puede escribir `hp.two_le`."}},"archivo":"datos/trazas/20-buscar-3.json"}
```

- Lo que va entre llaves y corchetes, como `{α : Type u_1}` o `[Preorder α]`, son datos que Lean rellena solo: el tipo de números y sus propiedades. Para leer un teorema, de momento basta lo de después: las hipótesis entre paréntesis y la conclusión al final.
- El nombre describe **la conclusión**, y a veces solo su lado izquierdo: `two_mul` es 2 · *n* = …, y `abs_mul` es |*a* · *b*| = ….
- `of` separa la conclusión de las hipótesis: `le_of_lt` es «≤ a partir de <». Es el orden contrario al de la pizarra, donde se escribe primero la hipótesis.
- `Nat.Prime.two_le` vive en el «apartado» `Nat.Prime`. Por eso, si `hp : p.Prime`, Lean entiende `hp.two_le`: busca `two_le` en el apartado del tipo de `hp`. Es la notación de punto de `h.1` y `h.2` (capítulo 6), y de `hp.one_lt` (capítulo 12).

### 4 · Adivinar y comprobar

Con las reglas de nombres, muchas veces no hace falta buscar: se adivina el nombre, se escribe, y Lean dice si es correcto. Si no lo es, el error avisa al instante, y entonces sí se busca.

```lean
import Mathlib

example (x y : ℝ) : 0 ≤ (x - y) ^ 2 := by
  exact sq_nonneg (x - y)

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

example (p : ℕ) (hp : p.Prime) : 2 ≤ p := by
  exact hp.two_le

example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h hc
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Adivinar el nombre","etiqueta":"sq_nonneg · mul_pos · notación de punto","idea":"Se lee la meta como una frase y se traduce a un nombre: «cuadrado no negativo» es `sq_nonneg`, «producto positivo» es `mul_pos`. Si el nombre existe y encaja, la meta se cierra.","notas":{"1":"*sq nonneg*, aplicado a *x* − *y*: 0 ≤ (*x* − *y*)².","2":"*mul pos*: producto de positivos, con las dos hipótesis.","3":"Notación de punto: `hp.two_le` es `Nat.Prime.two_le hp`.","4":"Un nombre largo, que se lee entero: *mul le mul of nonneg right*. Producto ≤ producto, a partir de un factor no negativo a la derecha (*c*)."}},"archivo":"datos/trazas/20-buscar-4.json"}
```

- `sq_nonneg` sirve para cualquier cuadrado: se le da la expresión, aquí `x - y`, y devuelve 0 ≤ (*x* − *y*)².
- `mul_pos` pide dos pruebas, una por factor. Si das las hipótesis en otro orden, Lean protesta: el orden es el del enunciado, *a* primero.
- `mul_le_mul_of_nonneg_right` parece imposible de recordar, pero se lee solo: *mul le mul* (un producto ≤ otro), *of nonneg* (a partir de algo no negativo), *right* (el factor común va a la derecha). Lo encontró `exact?` al buscarlo, y el nombre ya cuenta lo que hace.

### 5 · Buscar fuera de Lean

A veces no sabes ni escribir la meta, o quieres ver qué hay sobre un tema. Para eso hay dos buscadores web, gratuitos:

- **[Loogle](https://loogle.lean-lang.org/)** busca por forma. Admite nombres de funciones (`Real.sin`), trozos del nombre entre comillas (`"differ"`), formas con huecos (`_ * (_ ^ _)`) y la conclusión que buscas, precedida de `⊢`. Los filtros se combinan separándolos con comas.
- **[LeanSearch](https://leansearch.net/)** busca en lenguaje natural, en inglés: escribes una frase, como «the square of a real number is nonnegative», y te propone teoremas.

Los dos se pueden usar también desde dentro de Lean, con `#loogle` y `#leansearch` (vienen con Mathlib), pero necesitan conexión a internet. Los visualizadores de este libro se calculan sin conexión, así que no los usan.

::::{div}
:class: afondo
### 6 · Cuando `exact?` no encuentra nada

`exact?` solo encuentra teoremas que dan la meta **tal cual**. Si la meta es una combinación que nadie ha escrito como teorema, falla, aunque sea fácil.

```lean
import Mathlib

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + 1 := by
  exact?

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + 1 := by
  have h := mul_pos ha hb
  linarith

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + 1 := by
  positivity
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Cuando la búsqueda falla","etiqueta":"a fondo · exact? · have · positivity","idea":"Ningún teorema de Mathlib dice «0 < *a* · *b* + 1» tal cual. La salida es partir la meta: primero 0 < *a* · *b*, que sí es un teorema, y después dejar que `linarith` sume 1. O usar una táctica que razona por la forma, `positivity`.","espera_error":true,"notas":{"1":"`exact?` no encuentra ningún teorema con esa forma, y lo dice con un error.","2":"Se busca la pieza que sí existe: 0 < *a* · *b*, que es `mul_pos`.","3":"Con `h : 0 < a * b`, sumar 1 es aritmética lineal.","4":"`positivity` mira la forma: un producto de positivos, más 1, es positivo."}},"archivo":"datos/trazas/20-buscar-5.json"}
```

El error de `exact?` no significa que la meta sea difícil. Significa que **no hay un teorema con esa forma exacta**. La estrategia es la de clase: partir el problema en piezas que sí son teoremas conocidos. Aquí, 0 < *a* · *b* es `mul_pos`, y lo que queda es sumar 1, que `linarith` hace solo.

Otra salida es la táctica `hint`, que prueba a la vez varias tácticas automáticas y dice cuáles cierran la meta, marcadas con 🎉. Con esta meta, `hint` contesta que la cierra `finiteness`, y que `field_simp` y `norm_num` la dejan igual. No es la respuesta que uno esperaría, pero es honesta: `hint` no razona, solo prueba.

Al usar un teorema, también se puede leer su versión completa con `#check @`, que enseña todos los argumentos, incluidos los que Lean rellena solo:

```lean
-- #check @mul_le_mul
@mul_le_mul : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α]
  {a b c d : α} [PosMulMono α] [MulPosMono α],
  a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d
```

Se lee en tres partes. Entre llaves, `{α}` y `{a b c d}`: lo que Lean deduce de la meta. Entre corchetes, `[Mul α]`, `[Preorder α]`…: las propiedades que tiene que tener el tipo de números (que se pueda multiplicar, ordenar…), y que en ℝ se cumplen todas. Y después de la coma, el enunciado: cuatro hipótesis separadas por flechas y la conclusión al final. Con cuatro hipótesis, `mul_le_mul` pide cuatro pruebas, en ese orden.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Buscar la propiedad conmutativa de la suma por su forma, `_ + _ = _ + _`, con el buscador de cada sistema (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: busca un teorema que dé la meta tal cual
example (a b : ℕ) : a + b = b + a := by
  exact?   -- Try this: exact Nat.add_comm a b
```

```coq
(* Rocq (Coq): lista los teoremas con esa forma *)
Require Import Arith.
Search (_ + _ = _ + _) inside Nat.
(* Nat.add_comm: forall n m : nat, n + m = m + n
   … y diez más *)
```

```isabelle
(* Isabelle: lista los teoremas con esa forma y «comm» en el nombre *)
find_theorems "_ + _ = _ + _" name: comm
(* found 18 theorem(s): …
   Groups.ab_semigroup_add_class.add.commute: ?a + ?b = ?b + ?a … *)
```

Los tres buscan por la forma, con `_` como hueco. La diferencia está en qué hacen con lo que encuentran. `exact?` de Lean elige uno que cierra la meta y lo propone; `Search` de Rocq y `find_theorems` de Isabelle **listan** todos los que tienen esa forma, y eliges tú. En Rocq, `inside Nat` limita la búsqueda a los teoremas de naturales; en Isabelle, `name: comm` exige que el nombre contenga «comm». Los nombres son parecidos: `Nat.add_comm` en Rocq y en Lean, `add.commute` en Isabelle.
:::

## Conexiones

- Todos los teoremas usados en los capítulos 12 a 19 (`sq_nonneg`, `abs_mul`, `add_le_add`, `hasDerivAt_pow`…) se pueden encontrar con `exact?` o adivinar con las reglas de nombres.
- La notación de punto, `hp.two_le`, es la de `h.1` (capítulo 6) y `hp.one_lt` (capítulo 12): Lean busca el teorema en el apartado del tipo de la hipótesis.
- `.mpr` de `left_lt_add_div_two.mpr` es la mitad de un «si y solo si», como `.mp` en el capítulo 12.
- Cuando `exact?` falla, se vuelve a las tácticas que razonan por la forma: `linarith` y `positivity` (capítulo 13).

## La grieta

`exact?` ha encontrado `Nat.add_comm a b` y lo ha usado como prueba de `a + b = b + a`. Pero, ¿qué es exactamente una prueba para Lean? En `exact`, lo que se escribe después no es una táctica: es un **término**, un objeto, como un número o una función. `Nat.add_comm a b` es un objeto cuyo tipo es `a + b = b + a`. Entonces, ¿una afirmación es un tipo, y su prueba es un objeto de ese tipo? Exactamente. Es la idea central de Lean, y la del capítulo siguiente: **Proposiciones como tipos**.

## Ejercicios

1. **Otro nombre.** Usa `exact?` para demostrar `a * b = b * a` con *a* y *b* reales. ¿Qué nombre propone? ¿Funciona también `mul_comm a b`?

2. **Un cuadrado.** Sin buscar, demuestra `0 ≤ (a + b) ^ 2` con *a* y *b* reales. ¿Cómo se llama el teorema?

3. **Sumar desigualdades.** Sin `exact?`, demuestra `a + c ≤ b + d` a partir de `h1 : a ≤ b` y `h2 : c ≤ d`.

4. **Las reglas de simp.** Usa `simp?` en `a * 1 = a`, con *a* real. ¿Qué regla dice que ha usado?

5. **De < a ≤.** Adivina el nombre del teorema que da `a ≤ b` a partir de `h : a < b`, y úsalo.

6. **El doble.** Adivina el nombre del teorema que dice `2 * n = n + n`, y úsalo con *n* natural.

::::{div}
:class: afondo
7. **Una suma positiva.** `exact?` no encuentra nada para `0 < a ^ 2 + b ^ 2 + 1`, con *a* y *b* reales. Demuéstralo de dos formas: con `positivity`, y partiendo en piezas con `sq_nonneg` y `linarith`.

8. **Leer un teorema.** Con lo que dice `#check @mul_le_mul` (apartado 6), demuestra `a * c ≤ b * d` a partir de `h1 : a ≤ b`, `h2 : c ≤ d`, `hc : 0 ≤ c` y `hb : 0 ≤ b`. ¿En qué orden van las pruebas?
::::

## Solucionario

1. `exact?` propone `exact mul_comm' a b`. También funciona `mul_comm a b`: Mathlib tiene a veces varios teoremas con el mismo enunciado, y `exact?` da el primero que encuentra.
2. *sq nonneg*: `exact sq_nonneg (a + b)`.
3. *add le add*: `exact add_le_add h1 h2`.
4. `simp only [mul_one]`: *mul one*, multiplicar por uno.
5. *le of lt*: `exact le_of_lt h`. Con notación de punto, también `exact h.le`.
6. *two mul*: `exact two_mul n`.

::::{div}
:class: afondo
7. Las dos formas:
   ```lean
   example (a b : ℝ) : 0 < a ^ 2 + b ^ 2 + 1 := by
     positivity

   example (a b : ℝ) : 0 < a ^ 2 + b ^ 2 + 1 := by
     have h1 := sq_nonneg a
     have h2 := sq_nonneg b
     linarith
   ```
8. En el orden del enunciado, después de la coma: primero *a* ≤ *b*, después *c* ≤ *d*, después 0 ≤ *c* y por último 0 ≤ *b*:
   ```lean
   example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b) :
       a * c ≤ b * d := by
     exact mul_le_mul h1 h2 hc hb
   ```
::::
