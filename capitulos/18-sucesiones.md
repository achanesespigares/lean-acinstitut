---
title: Sucesiones y límites
subtitle: Épsilon, ene y tres cuantificadores seguidos, sin miedo
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## Punto de partida

1, ½, ⅓, ¼, ⅕… Los números se van acercando a 0. En la pizarra decimos que la sucesión *aₙ* = 1/(*n* + 1) «tiende a 0», dibujamos puntitos cada vez más pegados al eje y seguimos adelante. Para calcular límites hay reglas: el límite de una suma es la suma de los límites, 1/*n* se va a 0, y con eso basta casi siempre.

Pero ¿qué significa exactamente «acercarse»? En el siglo XIX, Cauchy y Weierstrass le dieron una respuesta precisa, que es la que se usa hoy: por pequeño que sea el margen ε que se elija, a partir de cierto término *N* todos los términos están a menos de ε del límite. Tres cuantificadores seguidos: para todo ε, existe *N*, para todo *n* ≥ *N*. Es la definición que más cuesta en primero de carrera, y en Lean se vuelve muy concreta, porque cada cuantificador es un paso que se ve en el panel.

## La pregunta

¿Cómo se escribe en Lean que una sucesión tiende a un límite? ¿Cómo se demuestra que 1/(*n* + 1) tiende a 0, o que el límite de una suma es la suma de los límites? ¿Y qué tiene Mathlib ya hecho?

## La idea

Una sucesión de números reales es una función `a : ℕ → ℝ`: a cada *n* le toca un número *aₙ*. Y «*a* tiende a *L*» es esta definición, escrita tal cual:

```lean
def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
```

| Trozo | Se lee | Táctica |
|---|---|---|
| `∀ ε > 0` | sea ε un margen positivo cualquiera | `intro ε hε` |
| `∃ N : ℕ` | hay un término a partir del cual… | `use N` (lo damos nosotros) |
| `∀ n ≥ N` | …todos los términos siguientes… | `intro n hn` |
| `\|a n - L\| < ε` | …están a menos de ε de *L* | la cuenta |

:::{important} El N depende del ε
Primero llega ε, y después hay que encontrar *N*. Cuanto más pequeño es ε, más lejos hay que ir: para 1/(*n* + 1) y ε = 0,01, hace falta *N* = 100. La parte creativa de cada prueba es encontrar *N* en función de ε; el resto es desmontar los cuantificadores.
:::

## Construcción

### 1 · La definición, con la sucesión más sencilla

```lean
import Mathlib

def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example : Tiende (fun _ => 5) 5 := by
  intro ε hε
  use 0
  intro n hn
  simp
  exact hε
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La sucesión constante","etiqueta":"Tiende · intro · use","idea":"La sucesión 5, 5, 5… tiende a 5: todos sus términos están a distancia 0 de 5, que es menos que cualquier ε positivo. Cualquier *N* sirve; tomamos 0.","notas":{"1":"Llega el margen ε, con `hε : ε > 0`.","2":"El término a partir del cual se cumple: aquí vale cualquiera, así que 0.","3":"Un término *n* cualquiera a partir del 0. Queda `|(fun x => 5) n - 5| < ε`.","4":"`simp` aplica la función y hace la cuenta: |5 − 5| = 0. Queda `0 < ε`.","5":"Que es justo `hε`."}},"archivo":"datos/trazas/18-sucesiones-1.json"}
```

- `def Tiende` define una propiedad nueva, una `Prop`, con dos datos: la sucesión y el límite. A partir de aquí, `Tiende a L` es una afirmación como cualquier otra.
- Los tres cuantificadores se desmontan en orden: `intro ε hε` (el ∀), `use 0` (el ∃) e `intro n hn` (el segundo ∀). Es lo del capítulo 9, tres veces seguidas.
- `fun _ => 5` es la sucesión que vale 5 en cada término. El guion bajo dice que el valor de *n* no se usa.
- Lo que queda, |5 − 5| < ε, es 0 < ε, que es la hipótesis.

### 2 · 1/(*n* + 1) tiende a 0

:::{tip} Predice
Dado ε, ¿a partir de qué término es 1/(*n* + 1) < ε? Despeja *n*.
:::

```lean
import Mathlib

def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example : Tiende (fun n => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro n hn
  dsimp only
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / ε < n + 1 := by linarith
  rw [sub_zero, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at h1
  linarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Encontrar N en función de ε","etiqueta":"ε-N · Arquímedes · div_lt_iff₀","idea":"1/(*n* + 1) < ε equivale a *n* + 1 > 1/ε. Así que basta con un *N* mayor que 1/ε, y siempre hay uno: es la propiedad arquimediana. El resto es manejar las desigualdades con cuidado.","notas":{"1":"Llega ε > 0.","2":"Un natural *N* mayor que 1/ε: `hN : 1 / ε < ↑N`. Que exista es la propiedad arquimediana.","3":"Ese es nuestro *N*.","4":"Un término *n* ≥ *N*.","5":"Se aplica la función: la meta queda `|1 / (↑n + 1) - 0| < ε`.","6":"*N* ≤ *n* como naturales, pasado a los reales…","7":"…con `exact_mod_cast`, que arregla las flechas ↑.","8":"Encadenando: 1/ε < *N* ≤ *n* < *n* + 1…","9":"…que comprueba `linarith`.","10":"Se quita el − 0 y el valor absoluto, porque el número es positivo…","11":"…cosa que comprueba `positivity`. Queda `1 / (↑n + 1) < ε`.","12":"Se pasa el denominador multiplicando…","13":"…porque es positivo: 1 < ε · (*n* + 1).","14":"Lo mismo en `h1`: 1 < (*n* + 1) · ε.","15":"Las dos dicen lo mismo, con los factores en otro orden."}},"archivo":"datos/trazas/18-sucesiones-2.json"}
```

- El *N* sale de despejar: 1/(*n* + 1) < ε ⇔ *n* + 1 > 1/ε. Basta con tomar un natural *N* mayor que 1/ε.
- Que ese *N* exista no es obvio: es la **propiedad arquimediana** de los reales (no hay números reales «infinitamente grandes»). En Mathlib se llama `exists_nat_gt`.
- La flecha ↑ aparece porque *N* y *n* son naturales y ε es real (capítulo 13). `exact_mod_cast` pasa *N* ≤ *n* de los naturales a los reales.
- `div_lt_iff₀` es la regla de pasar un denominador positivo multiplicando: *a*/*c* < *b* ⇔ *a* < *b* · *c*. El `₀` del nombre indica que vale en cuerpos ordenados, con la condición *c* > 0.
- Es la prueba más larga hasta ahora, pero cada línea es un paso de la pizarra. Lo difícil es elegir *N*; lo demás, desigualdades.

### 3 · El límite de una suma

La regla «el límite de la suma es la suma de los límites» se usa sin pensar. Su prueba tiene un truco que aparece en todo el análisis: repartir el margen, ε/2 para cada sumando.

```lean
import Mathlib

def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example (a b : ℕ → ℝ) (L M : ℝ) (ha : Tiende a L) (hb : Tiende b M) :
    Tiende (fun n => a n + b n) (L + M) := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := hb (ε / 2) (by linarith)
  use max N₁ N₂
  intro n hn
  have e₁ := h₁ n (le_of_max_le_left hn)
  have e₂ := h₂ n (le_of_max_le_right hn)
  calc |a n + b n - (L + M)| = |(a n - L) + (b n - M)| := by ring_nf
    _ ≤ |a n - L| + |b n - M| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"ε/2 para cada uno","etiqueta":"ε/2 · max · desigualdad triangular","idea":"Se pide a cada sucesión que se acerque a menos de ε/2, se espera a que lo hagan las dos (el mayor de los dos *N*) y la desigualdad triangular suma los márgenes: ε/2 + ε/2 = ε.","notas":{"1":"Llega ε > 0.","2":"Se usa la hipótesis sobre *a* con el margen ε/2: da un *N*₁…","3":"…y antes hay que ver que ε/2 > 0.","4":"Lo mismo con *b*: da un *N*₂…","5":"…con el mismo margen ε/2.","6":"Hay que esperar a las dos: el mayor de *N*₁ y *N*₂.","7":"Un término *n* a partir de ahí.","8":"Como *n* ≥ máx(*N*₁, *N*₂) ≥ *N*₁: `e₁ : |a n - L| < ε / 2`.","9":"Y como *n* ≥ *N*₂: `e₂ : |b n - M| < ε / 2`.","10":"La cadena de la pizarra, eslabón a eslabón.","11":"Reagrupar: (*aₙ* − *L*) + (*bₙ* − *M*).","12":"Sumar los márgenes de `e₁` y `e₂`.","13":"ε/2 + ε/2 = ε."}},"archivo":"datos/trazas/18-sucesiones-3.json"}
```

- `ha (ε / 2) (by linarith)` usa la hipótesis «*a* tiende a *L*» con un margen concreto, ε/2. A cambio, hay que dar la prueba de que ε/2 > 0.
- Cada sucesión da su *N*, y no tienen por qué coincidir. A partir de `max N₁ N₂` se cumplen las dos cosas a la vez. `le_of_max_le_left` dice que si *n* ≥ máx(*N*₁, *N*₂), entonces *n* ≥ *N*₁.
- El paso clave es la **desigualdad triangular**, |*x* + *y*| ≤ |*x*| + |*y*| (`abs_add_le`, ejercicio 8 del capítulo 13). Con ella, el error de la suma es como mucho la suma de los errores.
- `calc` (capítulo 10) deja la cadena tal como se escribe en la pizarra, con la justificación de cada eslabón al lado.

### 4 · La versión de Mathlib

Mathlib no usa `Tiende`. Usa una noción mucho más general, `Filter.Tendsto`, que sirve igual para sucesiones, funciones, límites en el infinito o laterales. Para sucesiones de reales, un teorema la traduce a nuestra definición.

```lean
import Mathlib

open Filter Topology

def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example (a : ℕ → ℝ) (L : ℝ) : Tendsto a atTop (𝓝 L) ↔ Tiende a L := by
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq]
  rfl

example : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

example : Tendsto (fun n : ℕ => 3 + 1 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
  have h := (tendsto_const_nhds (x := (3 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using h
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Tendsto es nuestro Tiende","etiqueta":"Tendsto · atTop · 𝓝","idea":"`Tendsto a atTop (𝓝 L)` se lee «*a* tiende a *L* cuando *n* va al infinito». `Metric.tendsto_atTop` la convierte en ε-*N*, con la distancia en vez del valor absoluto. Y las reglas de los límites ya están demostradas.","notas":{"1":"La definición de Mathlib, traducida: `∀ ε > 0, ∃ N, ∀ n ≥ N, dist (a n) L < ε`.","2":"En los reales, la distancia es el valor absoluto de la resta.","3":"Y ya es, letra a letra, nuestra `Tiende`.","4":"El apartado 2, en una línea: Mathlib ya lo tiene.","5":"Constante más algo que tiende a 0: `.add` suma los límites. Sale 3 + 0…","6":"…y `simpa` lo simplifica a 3."}},"archivo":"datos/trazas/18-sucesiones-4.json"}
```

- `atTop` significa «cuando *n* se hace grande» y `𝓝 L` son «los entornos de *L*». `Tendsto a atTop (𝓝 L)` es «*a* lleva lo que está muy lejos a cerca de *L*». Para escribir `𝓝` hace falta `open Topology`; se teclea `\nhds`.
- `Metric.tendsto_atTop` traduce eso a ε-*N*, con `dist (a n) L`. En los reales, `Real.dist_eq` dice que esa distancia es |*aₙ* − *L*|, y queda exactamente nuestra definición.
- El apartado 2 está en Mathlib con el nombre `tendsto_one_div_add_atTop_nhds_zero_nat`. Y el apartado 3 es `Filter.Tendsto.add`: con `.add` se suman dos límites sin repetir el truco de ε/2.
- `(x := (3 : ℝ))` le dice a Lean que la constante es el real 3. Sin esa anotación, Lean no sabe de qué tipo es y se atasca.

::::{div}
:class: afondo
### 5 · El límite es único

Una sucesión no puede tender a dos números distintos. Parece obvio, pero hay que demostrarlo: si tendiese a *L* y a *M*, a partir de cierto término estaría a la vez cerca de los dos, y eso es imposible si están separados.

```lean
import Mathlib

def Tiende (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

theorem unico (a : ℕ → ℝ) (L M : ℝ) (hL : Tiende a L) (hM : Tiende a M) : L = M := by
  by_contra h
  have hd : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨N₁, h₁⟩ := hL (|L - M| / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := hM (|L - M| / 2) (by linarith)
  have e₁ := h₁ (max N₁ N₂) (le_max_left _ _)
  have e₂ := h₂ (max N₁ N₂) (le_max_right _ _)
  have t := abs_sub_le L (a (max N₁ N₂)) M
  rw [abs_sub_comm] at e₁
  linarith
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"No se puede estar cerca de dos sitios","etiqueta":"a fondo · unicidad · por reducción al absurdo","idea":"Si *L* ≠ *M*, se toma como margen la mitad de la distancia entre ellos. Un término lejano estaría a menos de esa mitad de *L* y de *M*, y por la desigualdad triangular *L* y *M* estarían a menos de su propia distancia. Absurdo.","notas":{"1":"Se supone *L* ≠ *M*. Hay que llegar a `False`.","2":"Entonces su distancia |*L* − *M*| es positiva.","3":"Margen: la mitad de esa distancia. *a* se acerca a *L* a menos de eso a partir de *N*₁…","4":"…(y la mitad de un positivo es positiva)…","5":"…y a *M* a partir de *N*₂.","6":"(Lo mismo para el segundo margen.)","7":"El término número máx(*N*₁, *N*₂) está cerca de *L*…","8":"…y cerca de *M*.","9":"Desigualdad triangular: |*L* − *M*| ≤ |*L* − *aₙ*| + |*aₙ* − *M*|.","10":"Se da la vuelta a `e₁`: |*L* − *aₙ*| < |*L* − *M*|/2.","11":"Sumando: |*L* − *M*| < |*L* − *M*|. Absurdo."}},"archivo":"datos/trazas/18-sucesiones-5.json"}
```

La prueba es por reducción al absurdo (capítulo 8): se supone *L* ≠ *M* y se busca una contradicción. El margen se elige con astucia, *d*/2, siendo *d* = |*L* − *M*| la distancia entre los dos supuestos límites.

El término número máx(*N*₁, *N*₂) está a menos de *d*/2 de *L* y a menos de *d*/2 de *M*. La desigualdad triangular, en la forma `abs_sub_le` (|*x* − *z*| ≤ |*x* − *y*| + |*y* − *z*|), dice entonces que *d* < *d*/2 + *d*/2 = *d*. Y *d* < *d* es imposible: `linarith` encuentra la contradicción.

`abs_sub_comm` da la vuelta a una resta dentro de un valor absoluto, |*x* − *y*| = |*y* − *x*|, para que `e₁` encaje con lo que pide la desigualdad triangular.

En Mathlib, la unicidad es `tendsto_nhds_unique`, y vale mucho más allá de las sucesiones de reales: en cualquier espacio donde dos puntos distintos se puedan separar.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
La sucesión constante 5, 5, 5… tiende a 5, con la definición ε-*N* de cada biblioteca (comprobado con Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean (con la Tiende de este capítulo)
example : Tiende (fun _ => 5) 5 := by
  intro ε hε
  use 0
  intro n hn
  simp
  exact hε
```

```coq
(* Rocq (Coq) *)
Require Import Reals.
Open Scope R_scope.
Lemma cte : Un_cv (fun _ => 5) 5.
Proof.
  intros eps heps.
  exists 0%nat.
  intros n hn.
  unfold R_dist.
  rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0.
  exact heps.
Qed.
```

```isabelle
(* Isabelle *)
lemma cte: "(\<lambda>n. (5::real)) \<longlonglongrightarrow> 5"
  apply (rule LIMSEQ_I)
  apply simp
  done
```

Los tres usan la misma definición de Cauchy y Weierstrass. En Rocq se llama `Un_cv` y mide la distancia con `R_dist`; la prueba es la de Lean, paso a paso: ε, *N* = 0, *n*, y la cuenta 5 − 5 = 0. En Isabelle, `⟶` (en el archivo, `\<longlonglongrightarrow>`) es el límite de una sucesión, y la regla `LIMSEQ_I` lo convierte en ε-*N*; después, `simp` hace la cuenta y encuentra el *N* solo.
:::

## Conexiones

- La definición es una cadena ∀ ∃ ∀ (capítulo 9), y cada prueba la desmonta con `intro`, `use` e `intro`.
- Las desigualdades del capítulo 13 (`linarith`, `positivity`, la desigualdad triangular) hacen casi todo el trabajo, y la flecha ↑ de los naturales a los reales también viene de allí.
- La unicidad es una reducción al absurdo del capítulo 8.
- Una sucesión es una función de ℕ en ℝ (capítulo 17). El capítulo 19 cambia ℕ por ℝ: funciones continuas.

## La grieta

Una función es continua si, al acercarse *x* a *a*, *f*(*x*) se acerca a *f*(*a*). Es la misma idea que el límite de una sucesión, pero con *x* real en lugar de *n* natural: un ε para *f* y un δ para *x*. ¿Cómo se demuestra que *x*² es continua? ¿Y qué es una derivada para Lean? Lo vemos en **Continuidad y derivadas**.

## Ejercicios

1. **Otra constante.** Demuestra `Tiende (fun _ => -2) (-2)`.

2. **Sumar 1.** Si *a* tiende a *L*, demuestra que *aₙ* + 1 tiende a *L* + 1. Pista: el mismo *N* sirve; reescribe *aₙ* + 1 − (*L* + 1) como *aₙ* − *L*.

3. **El doble.** Si *a* tiende a *L*, demuestra que 2*aₙ* tiende a 2*L*. ¿Qué margen le pides a *a*?

4. **Un N concreto.** Para 1/(*n* + 1) y ε = 0,01, ¿sirve *N* = 100? Comprueba con `norm_num` que 1/(100 + 1) < 0,01.

5. **Correr un puesto.** Si *a* tiende a *L*, demuestra que *aₙ*₊₁ también tiende a *L*.

6. **Con Mathlib.** ¿Qué teorema de Mathlib dice que 1/(*n* + 1) tiende a 0? Úsalo con `exact`.

::::{div}
:class: afondo
7. **El opuesto.** Si *a* tiende a *L*, demuestra que −*aₙ* tiende a −*L*.

8. **La unicidad en Mathlib.** Busca con `#check` el teorema `tendsto_nhds_unique`. ¿Qué hipótesis pide sobre el espacio?
::::

## Solucionario

1. `intro ε hε`, `use 0`, `intro n hn`, `simp`, `exact hε`.
2. ```lean
   example (a : ℕ → ℝ) (L : ℝ) (ha : Tiende a L) : Tiende (fun n => a n + 1) (L + 1) := by
     intro ε hε
     obtain ⟨N, hN⟩ := ha ε hε
     use N
     intro n hn
     have h := hN n hn
     rwa [show a n + 1 - (L + 1) = a n - L by ring]
   ```
   `rwa` reescribe y cierra con la hipótesis `h`.
3. Se le pide ε/2:
   ```lean
   example (a : ℕ → ℝ) (L : ℝ) (ha : Tiende a L) : Tiende (fun n => 2 * a n) (2 * L) := by
     intro ε hε
     obtain ⟨N, hN⟩ := ha (ε / 2) (by linarith)
     use N
     intro n hn
     have h := hN n hn
     rw [show 2 * a n - 2 * L = 2 * (a n - L) by ring, abs_mul]
     norm_num
     linarith
   ```
4. Sí: `example : (1 : ℝ) / (100 + 1) < 0.01 := by norm_num`. Y para *n* ≥ 100, 1/(*n* + 1) ≤ 1/101 < 0,01.
5. El mismo *N*: si *n* ≥ *N*, también *n* + 1 ≥ *N*.
   ```lean
   example (a : ℕ → ℝ) (L : ℝ) (ha : Tiende a L) : Tiende (fun n => a (n + 1)) L := by
     intro ε hε
     obtain ⟨N, hN⟩ := ha ε hε
     use N
     intro n hn
     exact hN (n + 1) (by omega)
   ```
6. `exact tendsto_one_div_add_atTop_nhds_zero_nat`.

::::{div}
:class: afondo
7. ```lean
   example (a : ℕ → ℝ) (L : ℝ) (ha : Tiende a L) : Tiende (fun n => -a n) (-L) := by
     intro ε hε
     obtain ⟨N, hN⟩ := ha ε hε
     use N
     intro n hn
     have h := hN n hn
     rwa [show -a n - -L = -(a n - L) by ring, abs_neg]
   ```
8. `tendsto_nhds_unique : Tendsto f l (𝓝 a) → Tendsto f l (𝓝 b) → a = b`, con `[T2Space X]` (espacio de Hausdorff: dos puntos distintos tienen entornos disjuntos) y `[l.NeBot]` (que el filtro no sea trivial). Los reales cumplen las dos cosas.
::::
