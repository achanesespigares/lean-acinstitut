---
title: Tipos dependientes y universos
subtitle: Tipos que dependen de un número, y una escalera de tipos sin final
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

El capítulo 21 dejó dos cabos sueltos. El primero: `#check Prop` contesta `Prop : Type`, así que los tipos también tienen tipo. ¿Y cuál es el tipo de `Type`? El segundo: una prueba de ∀ *n*, *n* + 0 = *n* es una función cuyo **resultado cambia de tipo** según la entrada: para *n* = 5 devuelve una prueba de 5 + 0 = 5, y para *n* = 7, una de 7 + 0 = 7.

En matemáticas esto es tan corriente que ni se nota. «Sea *v* un vector de ℝⁿ» es un objeto cuyo tipo depende de un número, *n*. «Para cada *n*, la matriz identidad de tamaño *n*» es una función que da, en cada caso, un objeto de un tipo distinto. Lean tiene esto dentro, y se llama **tipos dependientes**.

## La pregunta

¿Puede un tipo depender de un número? ¿Qué es una función cuyo tipo de salida depende de la entrada? ¿Y qué hay encima de `Type`?

## La idea

| Concepto | Notación en Lean | Ejemplo |
|---|---|---|
| Función | `A → B` | `ℕ → ℕ`: de naturales a naturales |
| Tipo que depende de un número | `Fin n`, `Vector ℕ n` | `Fin 3`: los naturales menores que 3 |
| Función dependiente | `(x : A) → B x` | `(n : ℕ) → Fin (n + 1)`: para cada *n*, un número menor que *n* + 1 |
| …si el resultado es una proposición | `∀ x : A, P x` | `∀ n : ℕ, n ≤ n`: la misma flecha, escrita con ∀ |
| Par dependiente | `(x : A) × B x` | `(n : ℕ) × Fin n`: un *n* y un número menor que él |
| Subtipo | `{x : A // P x}` | `{n : ℕ // Even n}`: un natural y la prueba de que es par |
| Universos | `Prop`, `Type`, `Type 1`, `Type 2`… | `Prop : Type`, `Type : Type 1`, `Type 1 : Type 2`… |

:::{important} El ∀ es una flecha
El «para todo» de la lógica y la función dependiente son **la misma construcción**. `∀ n : ℕ, n ≤ n` y `(n : ℕ) → n ≤ n` son la misma expresión: Lean escribe ∀ cuando el resultado es una proposición, y la flecha con paréntesis cuando es un dato. Por eso, en el capítulo 21, demostrar un ∀ era construir una función.
:::

## Construcción

### 1 · La escalera de universos

:::{tip} Predice
`ℕ : Type` y `Prop : Type`. ¿Qué crees que contestará `#check Type`? ¿Y `#check Type → Type`?
:::

```lean
import Mathlib

#check ℕ
#check Prop
#check Type
#check Type 1
#check ℕ → ℕ
#check Type → Type
#check List
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Una escalera sin final","etiqueta":"universos · Prop · Type · Type 1","idea":"Cada tipo vive en un **universo**: `ℕ` y `Prop` en `Type`, `Type` en `Type 1`, `Type 1` en `Type 2`… Ningún tipo es de su propio tipo. Y lo que se construye con tipos vive en el universo del más alto.","notas":{"1":"Los naturales son un tipo de datos: viven en `Type`.","2":"Las proposiciones también forman un tipo, y vive en `Type`.","3":"`Type` no es de tipo `Type`: es de tipo `Type 1`, un piso más arriba.","4":"Y `Type 1` vive en `Type 2`. La escalera no se acaba.","5":"Las funciones entre naturales siguen en `Type`.","6":"Pero una función que toma un tipo y devuelve un tipo sube un piso: `Type 1`.","7":"`List` acepta tipos de cualquier piso: `List.{u}` dice que funciona en el universo *u* que haga falta, y la lista queda en ese mismo piso."}},"archivo":"datos/trazas/22-universos-1.json"}
```

- Los pisos de la escalera se llaman **universos**. `Prop` y `Type` están en el primer piso habitable; `Type` mismo está en `Type 1`; y así sin fin. Lean también los numera de otra forma, `Sort 0 = Prop`, `Sort 1 = Type`, `Sort 2 = Type 1`…, pero en la práctica se usan los nombres de la tabla.
- La regla es sencilla: **lo que se construye a partir de tipos vive en el piso del más alto**. `ℕ → ℕ` solo usa `ℕ`, que está en `Type`, y se queda en `Type`. `Type → Type` habla de `Type` mismo, y por eso sube a `Type 1`.
- `List.{u}` lleva un parámetro de universo, *u*. Es una definición que vale **en todos los pisos a la vez**: hay listas de números (en `Type`), listas de tipos (en `Type 1`)… Se llama polimorfismo de universos.

### 2 · Un tipo que depende de un número

`Fin n` es el tipo de los naturales menores que *n*: `Fin 3` tiene exactamente tres elementos, 0, 1 y 2. `Vector ℕ n` es el tipo de las listas de naturales de longitud *n* exactamente. En los dos, **el tipo depende de un número**.

```lean
import Mathlib

#check Fin 3
#eval (2 : Fin 3) + 2

def ceros (n : ℕ) : Vector ℕ n := Vector.replicate n 0

#check ceros
#eval ceros 3

def v : Vector ℕ 3 := #v[10, 20, 30]

#eval v[1]
#eval v[3]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El tipo lleva la longitud","etiqueta":"Fin n · Vector ℕ n · índices seguros","espera_error":true,"idea":"Como la longitud de `v` está en su tipo, `Vector ℕ 3`, Lean sabe antes de ejecutar nada qué posiciones existen. Pedir la posición 3 de un vector de tres elementos no es un fallo al ejecutar: es un error al escribir.","notas":{"1":"`Fin 3` es un tipo: el de los naturales menores que 3.","2":"En `Fin 3` se cuenta como en un reloj de tres horas: 2 + 2 = 4, que es 1 (módulo 3).","3":"El tipo de `ceros` depende de su entrada: `ceros n` es un vector de longitud *n*, sea cual sea *n*.","4":"`ceros 3` es un vector de tres ceros.","5":"Las posiciones de un vector de longitud 3 son 0, 1 y 2. La 1 es el 20.","6":"La posición 3 no existe, y Lean lo dice sin ejecutar: no puede probar `3 < 3`."}},"archivo":"datos/trazas/22-universos-2.json"}
```

- `Fin 3` es un tipo, como `ℕ`, pero con solo tres elementos. Los números de `Fin n` se suman **módulo *n***: es la aritmética del reloj, la de `ZMod` del capítulo 15.
- `ceros` tiene tipo `(n : ℕ) → Vector ℕ n`, aunque `#check` lo escriba como `ceros (n : ℕ) : Vector ℕ n`. Es una función dependiente: su resultado tiene un tipo distinto para cada *n*.
- Lo importante está en el último `#eval`. Para leer `v[3]`, Lean necesita una prueba de que 3 es una posición válida, es decir, de `3 < 3`, y no la hay. El error enseña la meta que no ha podido cerrar: `⊢ 3 < 3`. En otros lenguajes, salirse de una lista es un fallo **al ejecutar**; aquí no se puede ni escribir.

### 3 · La misma flecha para datos y para pruebas

```lean
import Mathlib

def ultimo (n : ℕ) : Fin (n + 1) := Fin.last n

#check ultimo
#eval ultimo 4
#check (n : ℕ) → Fin (n + 1)
#check (n : ℕ) → n ≤ n
#check fun n : ℕ => Nat.le_refl n
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Datos y pruebas, con la misma flecha","etiqueta":"(x : A) → B x · ∀","idea":"Una función dependiente que devuelve datos y una prueba de un «para todo» son la misma construcción. Solo cambia el piso: la primera vive en `Type`, la segunda en `Prop`, y Lean escribe ∀.","notas":{"1":"`ultimo n` es el mayor elemento de `Fin (n + 1)`, que es *n*. Su tipo de salida depende de *n*.","2":"Para *n* = 4, el último de `Fin 5` es 4.","3":"El tipo de `ultimo`, escrito con la flecha dependiente. Es un tipo de datos: vive en `Type`.","4":"La misma flecha, pero el resultado es una proposición: Lean la escribe con ∀ y vive en `Prop`.","5":"Y una función de ese tipo es una prueba: a cada *n* le da una prueba de *n* ≤ *n*."}},"archivo":"datos/trazas/22-universos-3.json"}
```

- `(n : ℕ) → Fin (n + 1)` y `(n : ℕ) → n ≤ n` se escriben igual. La única diferencia es dónde está el resultado: `Fin (n + 1)` es un tipo de datos, y `n ≤ n` es una proposición.
- Cuando el resultado es una proposición, Lean prefiere escribir `∀ (n : ℕ), n ≤ n`. Pero es la misma flecha: el «para todo» de la lógica **es** una función dependiente.
- `fun n => Nat.le_refl n` es, a la vez, una función (le das un *n* y te devuelve algo) y una prueba (de ∀ *n*, *n* ≤ *n*). Es la correspondencia del capítulo 21, en su forma completa.

### 4 · Pares dependientes y subtipos

Si la función dependiente generaliza la flecha, el par dependiente generaliza el par. En `(n : ℕ) × Fin n`, la segunda componente tiene un tipo que depende de la primera. Y un caso muy útil es el **subtipo**: un dato junto con una prueba de que cumple algo.

```lean
import Mathlib

def cuatro : {n : ℕ // Even n} := ⟨4, ⟨2, rfl⟩⟩

#eval cuatro.val
#check cuatro.property
#check cuatro
#check (⟨3, 2⟩ : (n : ℕ) × Fin n)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Un dato con su certificado","etiqueta":"subtipo · {x // P x} · par dependiente","idea":"Un objeto de `{n : ℕ // Even n}` es un par: un natural y una prueba de que es par. El número se puede sacar y usar (`.val`); la prueba viaja con él (`.property`).","notas":{"1":"La primera componente es el número, 4.","2":"La segunda es la prueba de que es par. La flecha ↑ convierte el par en su número.","3":"El tipo de `cuatro`: los naturales pares, cada uno con su prueba.","4":"Un par dependiente: el 3, y un elemento de `Fin 3` (aquí el 2). La segunda componente tiene que ser menor que la primera."}},"archivo":"datos/trazas/22-universos-4.json"}
```

- `{n : ℕ // Even n}` se lee «los naturales *n* tales que *n* es par». Cada elemento es un par ⟨número, prueba⟩. La prueba `⟨2, rfl⟩` dice que 4 = 2 + 2: `Even 4` está definido como «existe *r* con 4 = *r* + *r*».
- Se parece mucho a ∃ *n*, Even *n* del capítulo 21, que también era un par ⟨testigo, prueba⟩. La diferencia está en el universo: ∃ vive en `Prop`, y por la irrelevancia de las pruebas **no se puede sacar el testigo** para calcular con él. El subtipo vive en `Type`, y `.val` devuelve el número.
- En `(n : ℕ) × Fin n` la segunda componente depende de la primera: si la primera es 3, la segunda tiene que estar en `Fin 3`.

::::{div}
:class: afondo
### 5 · Por qué una escalera, y por qué `Prop` es especial

```lean
import Mathlib

#check ∀ p : Prop, p → p
#check (α : Type) → α → α
#check @id
#check id 3
#check id (Nat.le_refl 2)
example : Type := Type
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Ningún tipo se contiene a sí mismo","etiqueta":"a fondo · Girard · impredicatividad · Sort u","espera_error":true,"idea":"Si `Type` fuese de tipo `Type`, se podría demostrar False: es la paradoja de Girard. Por eso la escalera no tiene final. `Prop` es la excepción: una proposición que habla de todas las proposiciones sigue siendo una proposición.","notas":{"1":"Cuantifica sobre todas las proposiciones, y aun así vive en `Prop`. `Prop` es **impredicativo**.","2":"Lo mismo con tipos sube un piso: cuantificar sobre `Type` da algo en `Type 1`.","3":"`id` vale para cualquier piso: `Sort u_1` incluye `Prop` y todos los `Type`.","4":"Aplicada a un número…","5":"…y aplicada a una prueba. La misma función, en dos pisos distintos.","6":"`Type` no es de tipo `Type`, y Lean lo rechaza: `Type` es de tipo `Type 1`."}},"archivo":"datos/trazas/22-universos-5.json"}
```

¿Por qué no un único `Type` que se contenga a sí mismo? Porque sería **contradictorio**. Jean-Yves Girard demostró en 1972 que, en una teoría de tipos con `Type : Type`, se puede construir una prueba de False. Es un primo de la paradoja de Russell (el conjunto de todos los conjuntos que no se contienen a sí mismos), y la solución es la misma de siempre: niveles. Cada piso solo puede hablar de los de abajo. Por eso el último ejemplo da error: `Type` vive en `Type 1`, no en `Type`.

`Prop` es la excepción, y una excepción útil. `∀ p : Prop, p → p` habla de **todas** las proposiciones, incluida ella misma, y aun así es una proposición: vive en `Prop`, no en `Type`. Se dice que `Prop` es **impredicativo**. Con `Type` no pasa: `(α : Type) → α → α` sube a `Type 1`. La impredicatividad de `Prop` no da paradojas gracias a la irrelevancia de las pruebas del capítulo 21: como de una prueba solo importa que existe, no se puede usar para construir datos que se muerdan la cola.

Por último, `#check @id` enseña `{α : Sort u_1} → α → α`. `Sort u` es la escalera completa con `Prop` en el suelo: `Sort 0 = Prop`, `Sort 1 = Type`, `Sort 2 = Type 1`… Una sola definición de `id` sirve para números (`id 3 : ℕ`) y para pruebas (`id (Nat.le_refl 2) : 2 ≤ 2`). Es el polimorfismo de universos de `List.{u}`, llevado hasta `Prop`.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Los números menores que 3 como **tipo**, y el tipo de `Type` (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
#check Fin 3   -- Fin 3 : Type
#check Type    -- Type : Type 1
```

```coq
(* Rocq (Coq) *)
Require Import Coq.Vectors.Fin.
Check Fin.t 3.   (* t 3 : Set *)
Check Type.      (* Type : Type      ← los niveles, ocultos *)
Set Printing Universes.
Check Type.      (* Type@{u.2} : Type@{u.2+1} *)
```

```isabelle
(* Isabelle: no hay tipos dependientes; se usa un conjunto *)
term "{..<(3::nat)}"
(* "{..<3}" :: "nat set" *)
lemma "card {..<(3::nat)} = 3" by simp
```

Lean y Rocq tienen tipos dependientes y una escalera de universos. Rocq la esconde: `Check Type` contesta `Type : Type`, que parece la paradoja de Girard, pero con `Set Printing Universes` aparecen los niveles, `Type@{u.2} : Type@{u.2+1}`. Rocq los pone solo, sin que se vean. En Isabelle/HOL un tipo no puede depender de un número: los tipos y los valores están separados. Los números menores que 3 se escriben como un **conjunto**, `{..<3}`, de tipo `nat set`, y su tamaño es un teorema, no parte del tipo.
:::

## Conexiones

- El capítulo 21 mostró que ∀ se demuestra con una función; aquí se ve que es una **función dependiente**.
- ∃ del capítulo 21 y el subtipo `{x // P x}` son el mismo par en dos universos: `Prop` y `Type`.
- La aritmética de `Fin n` es la de `ZMod n` del capítulo 15.
- Los parámetros de universo, `List.{u}` y `Sort u_1`, aparecían ya en los `#check` del capítulo 20 (`mul_comm.{u_1}`).

## La grieta

`v[3]` daba un error porque Lean no podía demostrar `3 < 3`. Para `v[1]`, en cambio, alguien demostró `1 < 3` sin que lo pidiéramos. ¿Quién? Una táctica automática, la misma clase de máquina que `simp`, `omega` o `decide`. Las hemos usado decenas de veces como cajas negras: escribes `omega` y la meta desaparece. ¿Qué hacen por dentro? ¿Por qué `omega` resuelve unas cosas y no otras? Lo abrimos en **Qué hacen `simp`, `omega` y `decide`**.

## Ejercicios

1. **Más arriba.** ¿Qué contesta `#check Type 2`?

2. **Una familia de tipos.** ¿En qué universo vive `ℕ → Type`? ¿Por qué?

3. **Un vector de unos.** Define `unos (n : ℕ) : Vector ℕ n` con todos sus elementos iguales a 1, y evalúa `unos 4`.

4. **El reloj de cinco horas.** ¿Qué contesta `#eval (7 : Fin 5)`? ¿Por qué?

5. **Un subtipo.** Define `seis : {n : ℕ // n % 3 = 0}` con el número 6, y saca el número con `.val`.

6. **El tipo de una familia de vectores.** ¿Qué contesta `#check (n : ℕ) → Vector ℕ n`? ¿Es un tipo de datos o una proposición?

::::{div}
:class: afondo
7. **¿Qué piso?** ¿En qué universo viven `(α : Type 1) → α` y `∀ p : Prop, p ∨ ¬p`? ¿Por qué no suben igual?

8. **Arreglar el error.** `example : Type := Type` da error. ¿Qué hay que cambiar para que funcione?
::::

## Solucionario

1. `Type 2 : Type 3`. Cada piso vive en el siguiente.
2. `ℕ → Type : Type 1`. El resultado de la función es un tipo, y `Type` vive en `Type 1`: lo construido sube al piso del más alto.
3. `def unos (n : ℕ) : Vector ℕ n := Vector.replicate n 1`, y `#eval unos 4` da `#v[1, 1, 1, 1]`.
4. `2`. En `Fin 5` los números dan la vuelta al llegar a 5, como un reloj: 7 es 2 módulo 5.
5. `def seis : {n : ℕ // n % 3 = 0} := ⟨6, rfl⟩`, y `#eval seis.val` da `6`. `rfl` sirve porque 6 % 3 = 0 se comprueba calculando.
6. `(n : ℕ) → Vector ℕ n : Type`. Es un tipo de datos: el de las funciones que, a cada *n*, le asignan un vector de longitud *n*.

::::{div}
:class: afondo
7. `(α : Type 1) → α : Type 2`, porque cuantificar sobre `Type 1` sube un piso. `∀ p : Prop, p ∨ ¬p : Prop`, porque `Prop` es impredicativo: cuantificar sobre proposiciones da otra proposición.
8. `example : Type 1 := Type`. `Type` vive en `Type 1`.
::::
