---
title: Funciones y definiciones
subtitle: Ponerle nombre a una idea, y que Lean sepa lo que significa
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

En clase de matemáticas se escribe *f*(*x*) = 2*x*, y a partir de ahí se habla de *f*(7) o de *f*(*f*(3)) sin volver a explicar qué es *f*. Ponerle nombre a una cuenta es lo que permite pensar con ella.

En Python se hacía con `def`. En Sage, con `f(x) = 2*x`. En Lean también hay `def`, pero con una diferencia que lo cambia todo: lo que defines no es solo algo que se puede calcular, también es algo sobre lo que se puede **demostrar**.

## La pregunta

¿Cómo se define una función propia en Lean? ¿Y qué sabe Lean de ella: solo calcularla, o también razonar con lo que dice la definición?

## La idea

Una definición tiene cuatro partes:

```text
def doble (n : ℕ) : ℕ := 2 * n
    ─┬───  ──┬────   ┬    ──┬──
   nombre  entrada  salida  lo que vale
```

- El **nombre**, `doble`.
- Las **entradas**, cada una con su tipo: `(n : ℕ)`.
- El **tipo de la salida**, después de los dos puntos: `ℕ`.
- Lo que **vale**, después de `:=`.

Para usarla no hacen falta paréntesis: `doble 7`. Y la función entera tiene un tipo, `ℕ → ℕ`: «de naturales a naturales».

:::{important} En Lean se escribe `doble 7`, no `doble(7)`
Las funciones se aplican poniendo el argumento detrás, separado por un espacio. Los paréntesis solo agrupan: `doble (doble 3)` es el doble del doble de 3.
:::

## Construcción

### 1 · Una función con nombre

:::{tip} Predice
¿Qué contestará `#check (doble)`, con el nombre entre paréntesis?
:::

```lean
import Mathlib

def doble (n : ℕ) : ℕ := 2 * n

#eval doble 7
#eval doble (doble 3)
#check doble 7
#check (doble)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El doble de un número","etiqueta":"def · #eval · #check","idea":"`def` no escribe nada: solo define. Después, `doble` se usa como cualquier otra función de Lean.","notas":{"2":"Primero se calcula `doble 3`, que da 6, y después `doble 6`.","3":"`doble 7` es un número natural, aunque `#check` no lo calcule.","4":"Entre paréntesis, `doble` es la función entera, y su tipo es `ℕ → ℕ`: de naturales a naturales."}},"archivo":"datos/trazas/02-funciones-1.json"}
```

- `doble 7` da `14`, y `doble (doble 3)` da `12`.
- `#check doble 7` contesta `doble 7 : ℕ`: sin calcular, Lean sabe que es un natural.
- `#check (doble)` contesta `doble : ℕ → ℕ`. La flecha se lee «de… a…»: `doble` convierte un natural en otro natural.

### 2 · Varias entradas y funciones sin nombre

```lean
import Mathlib

def suma3 (a b c : ℕ) : ℕ := a + b + c

#eval suma3 1 2 3
#check suma3 1
#eval (fun n => n * n) 5
#check fun (n : ℕ) => n * n
#eval [1, 2, 3, 4].map (fun n => n * n)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Funciones de varias entradas y funciones anónimas","etiqueta":"aplicación parcial · fun · map","idea":"Si a `suma3` le das solo una entrada, no hay error: sale una función que espera las otras dos. Y con `fun` se escribe una función sin nombre, como una lambda de Python.","notas":{"2":"`suma3 1` es una función que todavía espera dos números: su tipo es `ℕ → ℕ → ℕ`.","3":"`fun n => n * n` es la función «elevar al cuadrado», sin nombre. Se aplica a 5 directamente.","5":"`map` aplica la función a cada elemento de la lista."}},"archivo":"datos/trazas/02-funciones-2.json"}
```

- `suma3 1 2 3` da `6`.
- `#check suma3 1` contesta `suma3 1 : ℕ → ℕ → ℕ`. Con una sola entrada, `suma3 1` es una función que espera las otras dos. Se llama **aplicación parcial**.
- `fun n => n * n` es una función sin nombre: «a cada *n* le hace corresponder *n* · *n*». Aplicada a 5 da `25`, y su tipo es `ℕ → ℕ`.
- `[1, 2, 3, 4].map (fun n => n * n)` aplica la función a cada elemento de la lista y da `[1, 4, 9, 16]`.

### 3 · Funciones que se llaman a sí mismas

El factorial se define en dos casos: 0! = 1 y (*n* + 1)! = (*n* + 1) · *n*!. En Lean se escribe igual, caso a caso.

```lean
import Mathlib

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 5
#eval fac 20

def suma : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + suma n

#eval suma 100
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Recursión caso a caso","etiqueta":"| 0 => … | n + 1 => …","idea":"Cada línea que empieza por `|` es un caso: qué vale la función en 0 y qué vale en el siguiente de un número, usando lo que vale en ese número.","notas":{"1":"5! = 5 · 4 · 3 · 2 · 1 = 120.","2":"20! tiene 19 cifras, y Lean las da todas.","3":"1 + 2 + … + 100 = 5050, la suma que se atribuye a Gauss de niño."}},"archivo":"datos/trazas/02-funciones-3.json"}
```

- `fac` se define por **casos**: `| 0 => 1` dice lo que vale en 0, y `| n + 1 => (n + 1) * fac n` lo que vale en el siguiente de cualquier *n*, usando `fac n`.
- `fac 5` da `120` y `fac 20` da `2432902008176640000`.
- `suma n` suma los números de 1 a *n*: `suma 100` da `5050`.
- Una función que se llama a sí misma se llama **recursiva**. Fíjate en que cada llamada es con un número más pequeño: así la cuenta siempre termina.

### 4 · Demostrar con una definición

Una definición no es una caja negra: Lean sabe lo que dice, y se puede usar en una demostración.

```lean
import Mathlib

def doble (n : ℕ) : ℕ := 2 * n

example : doble 7 = 14 := by rfl

theorem doble_es_suma (n : ℕ) : doble n = n + n := by
  unfold doble
  ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El doble de n es n + n","etiqueta":"rfl · unfold · ring","idea":"La primera afirmación habla de un número concreto, y basta con calcular. La segunda habla de cualquier *n*: hay que abrir la definición y razonar.","notas":{"1":"`doble 7` vale 14 por definición: Lean lo calcula y ve que los dos lados coinciden.","2":"Donde ponía `doble n`, ahora pone lo que dice la definición: `2 * n`.","3":"Queda una identidad de álgebra, 2*n* = *n* + *n*, y `ring` la comprueba para cualquier *n*."}},"archivo":"datos/trazas/02-funciones-4.json"}
```

- `example : doble 7 = 14 := by rfl` se demuestra **calculando**: `rfl` comprueba que los dos lados son iguales por definición.
- `doble_es_suma` habla de **cualquier** *n*, y no se puede calcular para todos. `unfold doble` abre la definición: la meta pasa de `doble n = n + n` a `2 * n = n + n`.
- `ring` termina: 2*n* = *n* + *n* es una identidad de álgebra.
- Ahora `doble_es_suma` es un **teorema con nombre**: se podrá usar en otras demostraciones, como un resultado del libro de texto.

::::{div}
:class: afondo
### 5 · Lean exige que la recursión termine

¿Por qué Lean se fija en que `fac n` llame a `fac` con un número más pequeño? Mira esta definición:

```lean
import Mathlib

def mal (n : ℕ) : ℕ := mal n + 1
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una definición que Lean rechaza","etiqueta":"a fondo · terminación","espera_error":true,"idea":"`mal n` se llama a sí misma con el mismo `n`: la cuenta no terminaría nunca. Lean no la acepta.","notas":{"1":"Lean dice que no consigue demostrar que la recursión termina: el parámetro `n` no cambia en la llamada."}},"archivo":"datos/trazas/02-funciones-5.json"}
```

Lean contesta con un error, en inglés: *fail to show termination for mal*. Explica que el parámetro `n` no cambia en la llamada recursiva, así que no puede asegurar que la cuenta acabe.

No es una manía. Si Lean aceptara `mal`, podría deducir que `mal 0 = mal 0 + 1`, y restando `mal 0` a los dos lados, que 0 = 1. Con una sola definición así, se podría demostrar cualquier cosa, y el demostrador dejaría de servir.

Por eso, para Lean, toda función tiene que **terminar**. Con `fac` y `suma` lo comprueba solo, porque cada llamada es con un número más pequeño. En casos más difíciles, hay que darle la demostración de que termina.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Una definición y una función recursiva (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
def doble (n : ℕ) : ℕ := 2 * n

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 5          -- 120
```

```coq
(* Rocq (Coq) *)
Definition doble (n : nat) : nat := 2 * n.

Fixpoint fac (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * fac m
  end.

Compute fac 5.       (* = 120 : nat *)
```

```isabelle
(* Isabelle *)
definition doble :: "nat => nat" where "doble n = 2 * n"

fun fac :: "nat => nat" where
  "fac 0 = 1"
| "fac (Suc n) = Suc n * fac n"

value "fac 5"        (* "120" :: "nat" *)
```

Los tres separan las definiciones normales de las recursivas: en Rocq son `Definition` y `Fixpoint`, y en Isabelle, `definition` y `fun`. Rocq e Isabelle escriben «el siguiente de *m*» como `S m` y `Suc n`, y Lean como `n + 1`. Y los tres comprueban que la recursión termina: al aceptar `fac`, Isabelle escribe *Found termination order*.
:::

## Conexiones

- En el libro de Python, `def doble(n): return 2 * n` definía algo que solo se podía ejecutar. Aquí, además, se puede razonar con lo que dice.
- `fun n => n * n` es la `lambda n: n * n` de Python y la `x -> x^2` de Julia.
- La recursión caso a caso, `| 0 => … | n + 1 => …`, es la misma idea que la **inducción**: se dice qué pasa en 0 y cómo se pasa de *n* a *n* + 1. En la parte III, la inducción servirá para demostrar, igual que aquí sirve para definir.
- El tipo `ℕ → ℕ` de una función volverá en la parte V, donde las demostraciones también tienen tipo.

## La grieta

`suma 100` da 5050, y `suma 10` da 55. En los dos casos, 2 · `suma n` = *n* · (*n* + 1). ¿Pasa con todos los números? Calcularlo uno a uno no acabaría nunca, y `ring` no sirve, porque `suma` es recursiva.

Para demostrarlo hacen falta dos cosas: saber escribir con precisión una afirmación sobre todos los números, y una forma de razonar que llegue a todos. La primera es el tema del capítulo siguiente, **Proposiciones y pruebas**. La segunda, la inducción, llega en la parte III.

## Ejercicios

1. **Tu primera función.** Define `triple`, que multiplica por 3, y evalúa `triple 7`.

2. **El tipo de una función.** ¿Qué contesta `#check (triple)`?

3. **Sin nombre.** ¿Qué da `#eval (fun x => x * x + 1) 4`?

4. **Aplicación parcial.** Con la `suma3` de la sección 2, ¿de qué tipo es `suma3 1 2`? ¿Y qué da `#eval (suma3 1 2) 10`?

5. **Recursión.** ¿Qué da `#eval suma 10`? Comprueba que 2 · `suma 10` = 10 · 11.

6. **Calcular para demostrar.** Demuestra que `doble 21 = 42`.

::::{div}
:class: afondo
7. **Un 0 = 1 que no llega.** ¿Por qué, si Lean aceptara `def mal (n : ℕ) : ℕ := mal n + 1`, se podría demostrar 0 = 1?

8. **Otra táctica.** En `doble_es_suma`, cambia `ring` por `omega`. ¿Sigue funcionando?
::::

## Solucionario

1. `def triple (n : ℕ) : ℕ := 3 * n`, y `#eval triple 7` da `21`.
2. `triple : ℕ → ℕ`.
3. `17`: 4 · 4 + 1.
4. `suma3 1 2 : ℕ → ℕ`, una función que espera un número más. `#eval (suma3 1 2) 10` da `13`.
5. `55`, y 2 · 55 = 110 = 10 · 11.
6. `example : doble 21 = 42 := by decide`, o con `by rfl`.

::::{div}
:class: afondo
7. Por la definición, `mal 0 = mal 0 + 1`. Un número no puede ser igual a sí mismo más 1, y restando `mal 0` a los dos lados quedaría 0 = 1. Lean no acepta `mal`, y así la contradicción nunca llega a aparecer.
8. Sí. `omega` resuelve igualdades y desigualdades lineales con naturales y enteros, y 2*n* = *n* + *n* lo es.
::::
