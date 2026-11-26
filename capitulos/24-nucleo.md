---
title: El núcleo y los axiomas
subtitle: Quién comprueba de verdad las pruebas, y sobre qué se apoyan
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

A lo largo del libro, `#print axioms` ha ido soltando nombres: `sorryAx` en el capítulo 3, `Classical.choice` en el 7, `propext` y un axioma de `native_decide` en el 23. Y en el 23 quedó dicho que las tácticas fabrican un término que «el núcleo comprueba».

Este capítulo responde a las dos preguntas que quedan. ¿Quién es ese núcleo, y por qué fiarse de él? ¿Y qué son esos axiomas, por qué hay tan pocos, y por qué importa cuáles usa cada prueba?

## La pregunta

Si las tácticas pueden tener errores, ¿por qué fiarse de una prueba de Lean? ¿Sobre qué se apoya, al final, todo lo que Lean demuestra?

## La idea

Lean está construido en dos capas. Arriba, todo lo que ayuda a escribir pruebas: tácticas, `simp`, `omega`, Mathlib, el editor. Abajo, un programa pequeño, el **núcleo** (*kernel*), que solo hace una cosa: comprobar que cada término tiene el tipo que dice tener. Si una táctica se equivoca, el núcleo rechaza el término. Es el **criterio de de Bruijn**: la confianza no está en las tácticas, sino en un comprobador pequeño y revisable.

Y el núcleo parte de unas reglas básicas (las de la teoría de tipos) más **tres axiomas**:

| Axioma | Qué dice | Para qué sirve |
|---|---|---|
| `propext` | dos proposiciones equivalentes son iguales: (*a* ↔ *b*) → *a* = *b* | reescribir con «si y solo si», como hace `simp` |
| `Quot.sound` | en un cociente, elementos relacionados son iguales | cocientes, y de él sale `funext` (dos funciones iguales en cada punto son iguales) |
| `Classical.choice` | de un tipo no vacío se puede sacar un elemento | la lógica clásica: tercero excluido, reducción al absurdo «fuerte» |

:::{important} `#print axioms` es el certificado
Cualquier teorema se puede auditar con `#print axioms`: dice exactamente qué axiomas usa, siguiendo todas las dependencias hasta el fondo. Si aparece algo distinto de los tres de la tabla (un `sorryAx`, un axioma inventado, el de `native_decide`), la prueba depende de algo más que de Lean.
:::

## Construcción

### 1 · Qué axiomas usa cada prueba

:::{tip} Predice
`2 + 2 = 4` se demuestra con `rfl`, calculando. ¿Crees que necesita algún axioma?
:::

```lean
import Mathlib

theorem t1 : 2 + 2 = 4 := rfl
theorem t2 (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem t3 (p : Prop) : p ∨ ¬p := Classical.em p
theorem t4 (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := funext h

#print axioms t1
#print axioms t2
#print axioms t3
#print axioms t4
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Auditar una prueba","etiqueta":"#print axioms","idea":"Cada teorema arrastra los axiomas de todo lo que usa, hasta el fondo. Calcular no necesita ninguno; el «si y solo si» convertido en igualdad necesita `propext`; el tercero excluido, los tres; la extensionalidad de funciones, `Quot.sound`.","notas":{"1":"Calcular 2 + 2 no necesita ningún axioma: el núcleo hace la cuenta.","2":"Convertir *p* ↔ *q* en *p* = *q* es justo el axioma `propext`.","3":"El tercero excluido es un teorema, pero su prueba usa los tres axiomas, `Classical.choice` entre ellos.","4":"`funext` es un teorema de Lean que se apoya en `Quot.sound`."}},"archivo":"datos/trazas/24-nucleo-1.json"}
```

- La mayoría de las pruebas del libro usan alguno de los tres axiomas, y es normal: son los de Lean, y los acepta toda la comunidad. Lo que hay que vigilar es **lo que no está en la lista**.
- `t1` no depende de ningún axioma. Muchas cuentas, y muchas pruebas de lógica, se pueden hacer así: solo con las reglas del núcleo.
- `funext` no es un axioma en Lean, sino un teorema, demostrado a partir de `Quot.sound`. Por eso `t4` enseña `Quot.sound`.

### 2 · Los tres axiomas, de cerca

```lean
import Mathlib

#check @propext
#check @Quot.sound
#check @Classical.choice
#print axioms funext
#print axioms Classical.em
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Tres axiomas, y nada más","etiqueta":"propext · Quot.sound · Classical.choice","idea":"Los tres axiomas de Lean, con su enunciado. El tercero es el más fuerte: convierte una prueba de que un tipo **no está vacío** en un **elemento** concreto, sin decir cuál. De él sale toda la lógica clásica.","notas":{"1":"Si *a* ↔ *b*, entonces *a* = *b*: las proposiciones equivalentes son la misma.","2":"Si *a* y *b* están relacionados por *r*, sus clases en el cociente son iguales.","3":"De `Nonempty α` (hay algún elemento) saca un elemento de α. No dice cuál: lo elige.","4":"`funext` solo necesita `Quot.sound`.","5":"El tercero excluido necesita los tres: es el teorema de Diaconescu, que deduce *p* ∨ ¬*p* de la elección."}},"archivo":"datos/trazas/24-nucleo-2.json"}
```

- `propext` y `Quot.sound` son axiomas «inofensivos»: casi nadie los discute, y hacen que la igualdad se comporte como en matemáticas.
- `Classical.choice` es el que separa la lógica **clásica** de la **constructiva**. Dice: si sabes que hay algún elemento, puedes tener uno. Pero la prueba de `Nonempty α` no dice cuál, así que el elemento que devuelve es una elección que nadie puede calcular.
- `Classical.em`, el tercero excluido (*p* ∨ ¬*p* para cualquier *p*), no es un axioma en Lean: se deduce de los tres. Es el teorema de Diaconescu.

### 3 · Clásico y constructivo

En el capítulo 8, la reducción al absurdo se usaba sin pensar. Pero hay dos direcciones, y no son iguales: de *p* sale ¬¬*p* sin ningún axioma; de ¬¬*p* sale *p* solo con lógica clásica.

```lean
import Mathlib

theorem t6 (p : Prop) (h : p) : ¬¬p := by
  intro hn
  exact hn h

#print axioms t6

theorem t5 (p : Prop) (h : ¬¬p) : p := by
  by_contra hn
  exact h hn

#print axioms t5
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Dos direcciones, dos lógicas","etiqueta":"constructivo · clásico · by_contra","idea":"*p* → ¬¬*p* es constructivo: con una prueba de *p*, se refuta cualquier refutación de *p*. ¬¬*p* → *p* es clásico: saber que *p* no es imposible no da una prueba de *p*, y hace falta `Classical.choice`.","notas":{"1":"¬¬*p* es ¬*p* → False: se supone `hn : ¬p`…","2":"…y choca con `h : p`. Ningún axioma.","3":"En los mensajes, `t6` no depende de nada. Ahora, `by_contra` supone ¬*p*. Para la meta *p*, esto ya es razonamiento clásico.","4":"La contradicción es la misma, pero `#print axioms t5` enseña los tres axiomas: `by_contra` usó el tercero excluido."}},"archivo":"datos/trazas/24-nucleo-3.json"}
```

- Las dos pruebas se parecen mucho, pero `#print axioms` las separa: `t6` no depende de ningún axioma, y `t5` depende de `propext`, `Classical.choice` y `Quot.sound`.
- La diferencia está en `by_contra`. Para demostrar *p* suponiendo ¬*p*, hace falta saber que *p* ∨ ¬*p*, y eso es el tercero excluido. En `t6`, en cambio, la meta ya era una negación, y `intro` basta.
- Mathlib usa lógica clásica sin problemas (`Nat.exists_infinite_primes`, por ejemplo, depende de los tres axiomas). La distinción importa a quien quiere pruebas **constructivas**, de las que se puede extraer un algoritmo.

### 4 · Trampas: `axiom` y `sorry`

`axiom` permite declarar cualquier cosa como axioma. El núcleo lo acepta sin más: un axioma es, precisamente, algo que no se demuestra. Por eso `#print axioms` es tan importante.

```lean
import Mathlib

axiom trampa : False

theorem dos : 1 = 2 := trampa.elim

#print axioms dos

theorem pendiente : 1 = 2 := by
  sorry

#print axioms pendiente
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que delata #print axioms","etiqueta":"axiom · sorry · sorryAx","idea":"Con un axioma falso, se demuestra cualquier cosa, incluso 1 = 2. El núcleo no puede impedirlo: los axiomas no se comprueban. Pero `#print axioms` lo delata siempre, igual que delata un `sorry`.","notas":{"1":"En los mensajes: `dos` depende de `trampa`. Ahora, `sorry` tapa la meta sin demostrarla, y Lean avisa: «declaration uses `sorry`». Y `#print axioms pendiente` enseña `sorryAx`: `sorry` es, por dentro, un axioma más."}},"archivo":"datos/trazas/24-nucleo-4.json"}
```

- `trampa.elim` convierte la «prueba» de False en una prueba de cualquier cosa (capítulo 21). Con un solo axioma falso, todo es demostrable, y el sistema entero deja de servir.
- `sorry` es lo mismo con otro nombre: por dentro usa el axioma `sorryAx`, que dice «acepto esto sin prueba». Lean avisa con una advertencia, y `#print axioms` lo deja a la vista.
- Por eso, para fiarse de un teorema ajeno, se hacen dos cosas: leer bien el enunciado y mirar `#print axioms`. Si solo aparecen `propext`, `Quot.sound` y `Classical.choice`, la prueba se apoya en Lean y en nada más.

::::{div}
:class: afondo
### 5 · El núcleo calcula, y no está solo

```lean
import Mathlib

theorem grande : 123456789 * 987654321 = 121932631112635269 := rfl

#print axioms grande
#reduce (fun x => x + 2) 3
#print propext
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Lo que hace el núcleo","etiqueta":"a fondo · núcleo · rfl · igualdad por definición","idea":"El núcleo comprueba tipos, y para eso a veces tiene que **calcular**: para aceptar `rfl` como prueba de 123456789 · 987654321 = 121932631112635269, multiplica los dos números y compara. Sin ningún axioma.","notas":{"1":"El producto es correcto, y `rfl` basta: el núcleo hace la multiplicación. Ningún axioma.","2":"`#reduce` enseña lo que ve el núcleo al calcular: aplicar la función a 3 da 5.","3":"`propext` es un `axiom`: una constante con tipo y sin prueba. El núcleo la acepta tal cual."}},"archivo":"datos/trazas/24-nucleo-5.json"}
```

**El núcleo calcula.** Para comprobar que `rfl` prueba `123456789 * 987654321 = 121932631112635269`, el núcleo tiene que ver que los dos lados son el mismo número, y para eso multiplica. Lo hace rápido porque tiene una extensión especial para los naturales, con aritmética de números grandes. Es la misma **igualdad por definición** del capítulo 3 (*n* + 0 se reduce a *n*) y la del capítulo 21 (`2 + 2 = 4` y `2 + 2 = 2 + 2` son el mismo tipo): el núcleo acepta dos tipos como iguales si, calculando, llegan a lo mismo.

**Un axioma es una constante sin prueba.** `#print propext` contesta `axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b`. La palabra `axiom` delante es la diferencia con un `theorem`: hay tipo, pero no hay término. El núcleo la añade al entorno sin comprobar nada, y por eso hay que mantener la lista corta y conocida.

**Otros comprobadores.** Si todo descansa en el núcleo, ¿y si el núcleo tiene un error? La respuesta es comprobar la misma prueba con **otro programa, escrito por otras personas**. La instalación de Lean 4.36.0 que usa este libro trae, junto al ejecutable `lean`, un exportador (`leanexport`, que vuelca las declaraciones a un archivo) y `nanoda_bin`, un comprobador de tipos independiente escrito en Rust. Con ellos se puede volver a comprobar `grande`, fuera de Lean:

```text
$ lean -o Prueba.olean Prueba.lean        # teorema cuatro y teorema grande
$ leanexport Prueba -- cuatro grande > prueba.ndjson
$ nanoda_bin cfg.json
Checked 52 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]
```

Las 52 declaraciones son los dos teoremas y todo lo que necesitan (los naturales, la suma, el producto, la igualdad…). `nanoda` las ha comprobado todas sin error de tipos; el aviso final es solo de su impresora, que no ha sabido escribir la lista de axiomas. Si el núcleo de Lean tuviera un fallo que dejara pasar una prueba falsa, un segundo comprobador hecho de forma independiente tendría que tener **el mismo** fallo para no detectarlo. Es la misma idea que pedir que un experimento lo repita otro laboratorio.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
«De ¬¬*p* se deduce *p*», y sobre qué se apoya en cada sistema (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean: la prueba necesita Classical.choice
theorem t5 (p : Prop) (h : ¬¬p) : p := by
  by_contra hn
  exact h hn
#print axioms t5
-- 't5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```coq
(* Rocq (Coq): sin nada, la lógica es constructiva *)
Lemma t6 (p : Prop) : p -> ~~p.
Proof. intros hp hn. exact (hn hp). Qed.
Print Assumptions t6.      (* Closed under the global context *)
Require Import Classical.
Lemma t5 (p : Prop) : ~~p -> p.
Proof. apply NNPP. Qed.
Print Assumptions t5.      (* Axioms: classic : forall P : Prop, P \/ ~ P *)
```

```isabelle
(* Isabelle/HOL: clásica desde el principio *)
thm excluded_middle   (* ¬ ?P ∨ ?P *)
thm someI             (* ?P ?x ⟹ ?P (Eps ?P) *)
lemma t5: "\<not>\<not>p \<Longrightarrow> p" by blast
```

Los tres pueden demostrarlo, pero el precio se ve de forma distinta. Rocq, como Lean, es constructivo de base: `Print Assumptions` dice que `t6` no usa nada, y que `t5` necesita el axioma `classic` (el tercero excluido), que entra al cargar la biblioteca `Classical`. En Isabelle/HOL la lógica clásica viene de serie: el tercero excluido es un teorema más, y el operador de elección de Hilbert, `Eps` (el `someI`), forma parte de las reglas básicas. Lean está a medio camino: constructivo en el núcleo, con `Classical.choice` siempre disponible, y `#print axioms` para ver cuándo se usa.
:::

## Conexiones

- `sorryAx` del capítulo 3, `Classical.choice` del 7 y el axioma de `native_decide` del 23 son los axiomas que delata `#print axioms`.
- La reducción al absurdo del capítulo 8 (`by_contra`) es clásica; la negación como función (`intro` para ¬*p*) es constructiva.
- La igualdad por definición del capítulo 3 y los tipos que se comparan calculando del 21 son trabajo del núcleo.
- `False.elim` del capítulo 21 explica por qué un solo axioma falso lo arruina todo.

## La grieta

Ahora sabemos quién comprueba las pruebas (el núcleo) y quién las fabrica (las tácticas). Las tácticas no son parte del núcleo: son programas escritos en Lean, que construyen términos. Y si son programas en Lean… ¿podemos escribir las nuestras? ¿Una táctica que haga, de una vez, la secuencia que repetimos tantas veces? Sí, y es el tema de **Tus propias tácticas**, el último capítulo antes de los proyectos.

## Ejercicios

1. **Una cuenta.** Demuestra `3 * 4 = 12` con `rfl`. ¿Qué dice `#print axioms`?

2. **Un «y» al revés.** Demuestra, sin tácticas, `p ∧ q → q ∧ p`. ¿Usa algún axioma?

3. **El axioma de `funext`.** ¿Qué axioma usa `funext`, según `#print axioms`?

4. **Una contradicción.** Demuestra, sin tácticas, `¬(p ∧ ¬p)`. ¿Es constructiva la prueba?

5. **El rastro de `sorry`.** ¿Qué axioma enseña `#print axioms` en un teorema que use `sorry`?

6. **Clásico o no.** ¿Cuál de las dos, *p* → ¬¬*p* o ¬¬*p* → *p*, se demuestra sin axiomas? ¿Por qué la otra no?

::::{div}
:class: afondo
7. **Casi el tercero excluido.** Demuestra, sin tácticas y sin axiomas, `¬¬(p ∨ ¬p)`. Comprueba con `#print axioms` que no usa ninguno. ¿Por qué no contradice que *p* ∨ ¬*p* necesite `Classical.choice`?

8. **El peligro de un axioma falso.** Con `axiom trampa : False`, demuestra `2 = 3`. Demuestra también `2 ≠ 3` con `decide`. ¿Qué dice `#print axioms` de cada uno?
::::

## Solucionario

1. `theorem e1 : 3 * 4 = 12 := rfl`. `#print axioms e1` contesta `'e1' does not depend on any axioms`: es una cuenta.
2. `theorem e2 (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩`. No depende de ningún axioma.
3. `Quot.sound`: `'funext' depends on axioms: [Quot.sound]`.
4. `theorem e4 (p : Prop) : ¬(p ∧ ¬p) := fun ⟨hp, hnp⟩ => hnp hp`. Sí: no depende de ningún axioma. Se desmonta el par y se aplica ¬*p* a *p*.
5. `sorryAx`.
6. *p* → ¬¬*p* se demuestra sin axiomas (`t6`). ¬¬*p* → *p* necesita el tercero excluido: saber que *p* no es imposible no da una prueba de *p*.

::::{div}
:class: afondo
7. `theorem e7 (p : Prop) : ¬¬(p ∨ ¬p) := fun h => h (Or.inr (fun hp => h (Or.inl hp)))`, y `#print axioms e7` dice que no depende de ninguno. Se supone `h : ¬(p ∨ ¬p)` y se llega a False: si se tuviera *p*, `h (Or.inl hp)` sería False, así que ¬*p*; pero entonces `h (Or.inr …)` es False. No contradice nada: demuestra que *p* ∨ ¬*p* **no es imposible**, que es ¬¬(*p* ∨ ¬*p*). Pasar de ahí a *p* ∨ ¬*p* es justo eliminar la doble negación, y eso es lo clásico.
8. `theorem a1 : 2 = 3 := trampa.elim` y `theorem a2 : 2 ≠ 3 := by decide`. `#print axioms a1` enseña `[trampa]`; `#print axioms a2`, ninguno. Con el axioma falso se demuestran a la vez una afirmación y su negación: el sistema es inconsistente, y `#print axioms` lo delata.
::::
