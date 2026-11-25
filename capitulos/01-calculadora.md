---
title: Lean como calculadora
subtitle: Cada número tiene su tipo, y el tipo decide la cuenta
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

Pregúntale a una calculadora cuánto es 7 entre 2 y contestará 3,5. Pregúntaselo a Lean y contestará 3.

No es un error. Pregúntale cuánto es 2 menos 5 y contestará 0. Tampoco es un error. Y si le pides 10 entre 0, contestará 0, sin quejarse.

Antes de demostrar nada, hay que saber con qué números está trabajando Lean.

## La pregunta

¿Por qué Lean da 7 / 2 = 3? ¿De qué tipo es cada número que escribes, y quién decide cómo se hace la cuenta?

## La idea

En Lean, **cada expresión tiene un tipo**. El tipo dice qué clase de objeto es: un número natural, un entero, una fracción, un texto… Y el tipo decide qué significa cada operación.

- Un número escrito sin más, como `7`, es un **número natural**: 0, 1, 2, 3… Lean lo llama `Nat`, y Mathlib lo escribe `ℕ`.
- En los naturales no hay negativos ni fracciones. Por eso `7 / 2` es la **división entera**, que da 3, y `2 - 5` se queda en 0: la resta no baja de cero.
- Si quieres otro tipo, lo dices con dos puntos: `(2 - 5 : Int)` es una resta de **enteros**, y da −3.

Para trabajar con Lean como calculadora hay dos órdenes:

| Orden | Qué hace | Ejemplo | Lean contesta |
|---|---|---|---|
| `#eval` | calcula la expresión | `#eval 7 / 2` | `3` |
| `#check` | dice el tipo, sin calcular | `#check 7 / 2` | `7 / 2 : Nat` |

:::{important} Lo de después de los dos puntos es el tipo
`7 / 2 : Nat` se lee «7 / 2 es un número natural». En Lean, los dos puntos siempre separan una cosa de su tipo. Lo verás en todas las páginas de este libro.
:::

## Construcción

### 1 · Las cuentas con naturales

:::{tip} Predice
¿Qué contestará Lean a cada línea? Piensa sobre todo en la cuarta y en la quinta.
:::

```lean
#eval 2 + 3
#eval 7 / 2
#eval 7 % 2
#eval 2 - 5
#eval 10 / 0
#eval 2 ^ 100
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Cuentas con números naturales","etiqueta":"#eval · Nat","idea":"Cada `#eval` es una pregunta, y Lean contesta en **Mensajes de Lean**. Todos estos números son naturales: no hay negativos ni fracciones.","notas":{"2":"Es la **división entera**: 7 entre 2 cabe 3 veces.","3":"`%` es el **resto** de la división: 7 = 2 · 3 + 1.","4":"En los naturales no hay negativos: la resta se queda en 0. Se llama **resta truncada**.","5":"Dividir entre 0 da 0. Es una convención, y no rompe nada: los teoremas sobre la división piden que el divisor no sea 0.","6":"Los naturales de Lean no tienen límite de cifras: 2¹⁰⁰ sale entero, con sus 31 cifras."}},"archivo":"datos/trazas/01-calculadora-1.json"}
```

- `2 + 3` da `5`, como en cualquier calculadora.
- `7 / 2` da `3`: es el **cociente** de la división entera. Y `7 % 2` da `1`, el **resto**: 7 = 2 · 3 + 1.
- `2 - 5` da `0`. En los naturales no existe −3, así que la resta se queda en cero.
- `10 / 0` da `0`. Lean necesita que la división dé siempre algún número, y elige 0. Los teoremas sobre la división llevan la condición de que el divisor no sea 0, así que esta convención no estropea ninguno.
- `2 ^ 100` da `1267650600228229401496703205376`, con sus 31 cifras: los naturales de Lean no tienen límite.

### 2 · El tipo manda

Un mismo número puede ser de tipos distintos. Se elige con dos puntos, entre paréntesis.

```lean
#check 7 / 2
#check (7 : Int)
#eval (2 - 5 : Int)
#eval (-7 / 2 : Int)
#eval (-7 % 2 : Int)
#check 3.5
#eval (0.1 + 0.2 : Float)
#eval (0.1 + 0.2 : Float) == 0.3
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El tipo decide la cuenta","etiqueta":"#check · Int · Float","idea":"`#check` dice el tipo sin calcular. Con `Int`, los enteros, sí hay negativos. Con `Float`, los decimales del ordenador, las cuentas son aproximadas.","notas":{"3":"En los enteros, 2 − 5 sí es −3.","4":"−7 = 2 · (−4) + 1: Lean elige el cociente para que el resto nunca sea negativo.","5":"El resto es 1, no −1: siempre está entre 0 y el divisor.","6":"Un número con punto decimal es un `Float`, un decimal del ordenador, como los de una calculadora.","7":"Lean escribe seis decimales: 0.300000. Pero dentro guarda algo más.","8":"`==` pregunta si son iguales, y la respuesta es `false`: 0.1 + 0.2 y 0.3 no son el mismo `Float`."}},"archivo":"datos/trazas/01-calculadora-2.json"}
```

- `#check 7 / 2` contesta `7 / 2 : Nat`, y `#check (7 : Int)` contesta `7 : Int`. El mismo 7, de dos tipos distintos.
- En `Int`, los enteros, `2 - 5` da `-3`.
- `-7 / 2` da `-4` y `-7 % 2` da `1`. Lean elige el cociente de forma que el resto nunca sea negativo: −7 = 2 · (−4) + 1. Python hace lo mismo con `//` y `%`.
- `#check 3.5` contesta `3.5 : Float`. Un número con punto decimal es un `Float`, un decimal del ordenador, con unas 16 cifras de precisión.
- `0.1 + 0.2` en `Float` se escribe `0.300000`, pero `(0.1 + 0.2 : Float) == 0.3` da `false`. Es el mismo problema que en Python, R, Julia y Sage: 0,1 no se puede guardar exacto en binario.

### 3 · Fracciones exactas

Con **Mathlib**, la biblioteca de matemáticas de Lean, hay más tipos de números. El de las fracciones es `ℚ`, los racionales.

```lean
import Mathlib

#eval (7 / 2 : ℚ)
#eval (1 / 3 + 1 / 6 : ℚ)
#eval (0.1 + 0.2 : ℚ)
#eval (0.1 + 0.2 : ℚ) = 0.3
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Fracciones que no se redondean","etiqueta":"ℚ · import Mathlib","idea":"La primera línea, `import Mathlib`, carga la biblioteca de matemáticas. En `ℚ`, las divisiones dan fracciones exactas, y hasta 0.1 es exactamente un décimo.","notas":{"3":"En `ℚ`, 0.1 es la fracción 1/10, exacta. Por eso la suma da 3/10.","4":"Ahora sí: en `ℚ`, 0.1 + 0.2 es exactamente 0.3."}},"archivo":"datos/trazas/01-calculadora-3.json"}
```

- `(7 / 2 : ℚ)` da `7 / 2`: la fracción, sin redondear.
- `1 / 3 + 1 / 6` da `1 / 2`, ya simplificada.
- En `ℚ`, `0.1` no es un decimal del ordenador, sino la fracción 1/10. Por eso `0.1 + 0.2` da `3 / 10`, y la igualdad con `0.3` da `true`.

### 4 · De calcular a demostrar

Hasta aquí Lean ha calculado. Pero Lean sirve sobre todo para **demostrar**. Una afirmación como «7 / 2 = 3» se puede escribir como un `example`, con su demostración después de `:= by`.

```lean
import Mathlib

example : 7 / 2 = 3 := by decide
example : 2 - 5 = 0 := by decide
example : 2 ^ 10 = 1024 := by norm_num
example : (0.1 + 0.2 : ℝ) = 0.3 := by norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Cuatro afirmaciones, cuatro demostraciones","etiqueta":"example · decide · norm_num","idea":"Cada `example` es una afirmación con su demostración. Mira el panel: la meta es la afirmación, y cada táctica la cierra.","notas":{"1":"`decide` hace la cuenta en los naturales y comprueba que los dos lados coinciden.","3":"`norm_num` hace cuentas con números de cualquier tipo.","4":"`ℝ` son los números reales. En los reales, 0.1 + 0.2 = 0.3 es **exactamente** cierto, y `norm_num` lo demuestra."}},"archivo":"datos/trazas/01-calculadora-4.json"}
```

- En cada `example`, lo que va entre `example :` y `:=` es la **afirmación**, y lo que va después de `by`, su **demostración**.
- `decide` calcula: comprueba que 7 / 2 y 3 son el mismo natural.
- `norm_num` es la táctica de las cuentas con números: vale para naturales, enteros, racionales y reales.
- La última línea habla de `ℝ`, los **números reales** de Mathlib. En los reales, 0,1 + 0,2 = 0,3 es una igualdad exacta, y `norm_num` la demuestra. Con `Float` habría sido falsa.

::::{div}
:class: afondo
### 5 · Lo que `#eval` no sabe hacer con los reales

Los racionales se pueden escribir: una fracción son dos enteros. Un real no siempre: √2 tiene infinitas cifras sin repetición. En Mathlib, un número real es, por dentro, una sucesión de racionales que se van acercando a él (una sucesión de Cauchy).

```lean
import Mathlib

#eval (2 : ℝ) + 2
example : (2 : ℝ) + 2 = 4 := by decide
example : (2 : ℝ) + 2 = 4 := by norm_num
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Los reales no se calculan: se demuestran","etiqueta":"a fondo · ℝ","espera_error":true,"idea":"`#eval` escribe un real como la sucesión que lo define. `decide` no sirve con los reales: la igualdad de reales no se puede decidir calculando. `norm_num` sí la demuestra.","notas":{"1":"La igualdad de dos reales no se puede comprobar haciendo una cuenta finita: habría que comparar infinitas cifras."}},"archivo":"datos/trazas/01-calculadora-5.json"}
```

- `#eval (2 : ℝ) + 2` escribe `Real.ofCauchy (sorry /- 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, ... -/)`. Es el real como sucesión de Cauchy: 4, 4, 4… Lean no puede dar «el valor» de un real cualquiera, solo los primeros términos de su sucesión.
- `decide` **falla**. Lean escribe sus mensajes en inglés: dice que `decide` *failed to reduce*, que no ha podido llegar a `true` ni a `false`, y que se ha quedado atascado en `Classical.choice`. La igualdad de reales no es algo que se pueda decidir calculando.
- `norm_num` sí lo demuestra. No calcula el real: razona con las reglas de la aritmética.

Esta es la diferencia que recorre todo el libro: **calcular** y **demostrar** no son lo mismo. Lean puede demostrar cosas que no puede calcular.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Los tres grandes demostradores tienen números naturales con división entera y resta truncada (comprobado con Lean 4.36.0, Coq 8.18 y Isabelle2026):

| | Lean | Rocq (Coq) | Isabelle |
|---|---|---|---|
| Calcular | `#eval (7 / 2, 2 - 5)` | `Compute (7 / 2, 2 - 5).` | `value "((7::nat) div 2, (2::nat) - 5)"` |
| Respuesta | `(3, 0)` | `= (3, 0) : nat * nat` | `"(3, 0)" :: "nat × nat"` |
| Demostrar 7 / 2 = 3 | `example : 7 / 2 = 3 := by decide` | `Example e : 7 / 2 = 3. Proof. reflexivity. Qed.` | `lemma "(7::nat) div 2 = 3" by simp` |

En Rocq hace falta antes `Require Import Arith.` para usar `/`. En Isabelle, la división entera se escribe `div`, y hay que decir el tipo, `nat`, de cada número: si solo se pone en uno, Isabelle no sabe de qué tipo es el otro y da un error. Los tres eligen lo mismo: en los naturales, la resta no baja de cero.
:::

## Conexiones

- En el libro de SageMath, `7/2` daba la fracción 7/2, porque Sage trata un número escrito sin más como un entero de Sage, y dividir enteros da racionales. En Lean, el mismo `7 / 2` da 3, porque es un natural. Cada lenguaje decide qué significa un número sin adornos.
- En Python, la división entera es `7 // 2`, y el resto de −7 entre 2 también es 1.
- `0.1 + 0.2` no da 0.3 con decimales del ordenador en ningún lenguaje de la colección. En Lean, con `ℚ` o `ℝ`, sí.
- El **resto** `%` es la base de la divisibilidad y las congruencias, en la parte III.
- Qué hacen por dentro `decide` y `norm_num` se cuenta en la parte V.

## La grieta

`decide` ha demostrado que 7 / 2 = 3 haciendo la cuenta. Pero ¿y una afirmación sobre **todos** los números, como «n + 0 = n para cualquier n»? No hay forma de hacer infinitas cuentas.

Para eso, antes hay que poder escribir cosas propias: una función que dé el doble de un número, una definición con nombre. Es lo que hace el capítulo siguiente, **Funciones y definiciones**.

## Ejercicios

1. **El cociente y el resto.** ¿Qué contestan `#eval 17 / 5` y `#eval 17 % 5`? Comprueba que 5 · cociente + resto = 17.

2. **El orden importa.** En los naturales, ¿qué dan `#eval 3 - 7 + 7` y `#eval 3 + 7 - 7`?

3. **Con enteros.** ¿Y `#eval (3 - 7 + 7 : Int)`?

4. **¿Qué tipo?** ¿Qué contesta `#check 2 ^ 10`?

5. **Negativos.** ¿Qué dan `#eval (-17 / 5 : Int)` y `#eval (-17 % 5 : Int)`?

6. **Tu primera demostración.** Escribe un `example` que demuestre que 17 % 5 = 2.

::::{div}
:class: afondo
7. **¿Un decimal exacto?** `#eval (1 / 3 : Float) * 3 == 1` da `true`. ¿Quiere decir que los `Float` son exactos?

8. **Decidir o razonar.** ¿Por qué `example : (2 : ℝ) + 2 = 4 := by decide` falla y con `norm_num` funciona?
::::

## Solucionario

1. `3` y `2`. 5 · 3 + 2 = 17.
2. `7` y `3`. En la primera, `3 - 7` se queda en 0, y 0 + 7 = 7. En la segunda, 3 + 7 = 10 y 10 − 7 = 3. En los naturales, el orden de las operaciones cambia el resultado.
3. `3`: en los enteros, 3 − 7 = −4 y −4 + 7 = 3.
4. `2 ^ 10 : Nat`. `#check` no calcula: escribe la expresión tal cual y su tipo.
5. `-4` y `3`: −17 = 5 · (−4) + 3, con el resto entre 0 y 4.
6. `example : 17 % 5 = 2 := by decide`.

::::{div}
:class: afondo
7. No. 1/3 se guarda redondeado, y al multiplicar por 3 el redondeo se compensa justo. Otras veces no se compensa: `(0.1 + 0.2 : Float) == 0.3` da `false`.
8. `decide` necesita una forma de comprobar la igualdad calculando, y para los reales no la hay: Lean se queda atascado en `Classical.choice`. `norm_num` no calcula el real, sino que aplica las reglas de la aritmética a 2 + 2.
::::
