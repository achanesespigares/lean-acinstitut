---
title: RSA demostrado
subtitle: Un proyecto guiado. Por qué descifrar devuelve siempre el mensaje, para cualquier mensaje y cualquier par de primos
---

```{anywidget} ../widgets/rutas.mjs
{}
```

## El proyecto

El penúltimo capítulo del libro de SageMath montó un **RSA de juguete para el aula**. Con los primos 61 y 53, la llave pública era *n* = 3233 y *e* = 17, y la privada, *d* = 2753. El mensaje 65 se cifraba en 65¹⁷ mod 3233 = 2790, y al descifrar, 2790²⁷⁵³ mod 3233, volvía el 65.

Sage lo comprobó con unos cuantos mensajes: 65, 7, 3000, HOLA. Y en el paso de Euler encontró algo raro: con el mensaje 61, la cuenta de Euler no daba 1 (daba 1220), y aun así el 61 volvía entero.

En este proyecto demostramos en Lean lo que Sage solo pudo comprobar:

- que las llaves de Sage están bien hechas;
- el teorema de Euler, que es la razón de que RSA funcione;
- que descifrar devuelve el mensaje, primero para los mensajes sin factores comunes con *n*;
- por qué el 61 también vuelve;
- y el teorema completo: **para cualquier mensaje y cualquier par de primos distintos**, descifrar deshace lo que hizo cifrar.

Lo que hace falta ya está en el libro: congruencias y Fermat (capítulo 15), `calc` (capítulo 10), casos (capítulo 7) y `decide` (capítulo 23).

## La idea

| | Sage (libro anterior) | Lean (este proyecto) |
|---|---|---|
| Las llaves | `inverse_mod(17, 3120)` da 2753 | 17 · 2753 = 1 + 15 · 3120, y φ(3233) = 3120 demostrado |
| Cifrar 65 | `power_mod(65, 17, 3233)` da 2790 | `decide +kernel` lo comprueba |
| Descifrar | Se prueba con unos mensajes | Teorema para todo mensaje *m* |
| Euler | 65³¹²⁰ mod 3233 = 1 | `Nat.ModEq.pow_totient`, para todo *m* coprimo con *n* |
| El 61 | Funciona, sin explicación | Fermat primo a primo y restos chinos |

:::{important} Por qué funciona RSA
Las llaves cumplen *e*·*d* = 1 + *k*·(*p* − 1)(*q* − 1). Cifrar y descifrar es elevar a *e* y luego a *d*, es decir, elevar a *e*·*d*. Y por Fermat, elevar a 1 + *k*·(*p* − 1) no cambia nada módulo *p*. Lo mismo módulo *q*. Si no cambia nada módulo *p* ni módulo *q*, tampoco módulo *p*·*q*.
:::

## Paso 1 · Las llaves

**Objetivo:** comprobar las llaves de Sage y demostrar que φ(3233) = 3120.

:::{tip} Predice
φ(*n*) cuenta los números de 1 a *n* sin factores comunes con *n*. Si *n* = *p*·*q* con *p* y *q* primos distintos, ¿cuánto vale φ(*n*)?
:::

```lean
import Mathlib

example : Nat.Prime 61 := by norm_num
example : Nat.Prime 53 := by norm_num
example : 61 * 53 = 3233 := by norm_num
example : Nat.gcd 17 3120 = 1 := by norm_num
example : 17 * 2753 = 1 + 15 * 3120 := by norm_num

theorem phi_n : Nat.totient 3233 = 3120 := by
  rw [show 3233 = 61 * 53 from rfl, Nat.totient_mul (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Las llaves de Sage","etiqueta":"proyecto · Nat.Prime · totient","idea":"Las llaves de Sage, comprobadas: 61 y 53 son primos, *n* = 3233, *e* = 17 no tiene factores comunes con 3120, y *e*·*d* = 1 + 15 · 3120. Y φ(3233) = φ(61)·φ(53) = 60 · 52 = 3120.","notas":{"1":"61 es primo: `norm_num` sabe comprobarlo.","2":"53 también.","3":"*n* = 61 · 53 = 3233.","4":"mcd(17, 3120) = 1: por eso 17 tiene inverso módulo 3120.","5":"Y el inverso es 2753: 17 · 2753 = 46801 = 1 + 15 · 3120.","6":"φ(3233): se escribe 3233 como 61 · 53 y se aplican dos reglas, φ(*a*·*b*) = φ(*a*)·φ(*b*) si *a* y *b* son coprimos, y φ(*p*) = *p* − 1 si *p* es primo.","7":"La primera regla pide que 61 y 53 sean coprimos…","8":"…la segunda, que 61 sea primo…","9":"…y que 53 lo sea. Queda 60 · 52 = 3120, y `rw` lo cierra calculando."}},"archivo":"datos/trazas/27-rsa-1.json"}
```

- `Nat.totient n` es φ(*n*), la función de Euler: cuántos números de 1 a *n* no tienen factores comunes con *n*. En Sage existe como `euler_phi`.
- `Nat.totient_mul` pide que los dos factores sean coprimos, y `Nat.totient_prime`, que el número sea primo. Las tres condiciones las comprueba `norm_num` dentro de cada `(by …)`.
- `show 3233 = 61 * 53 from rfl` cambia el número por su factorización: Lean la acepta porque la cuenta da lo mismo.

**Comprueba:** en Sage, φ = 60 · 52 = 3120, `gcd(17, 3120)` daba 1 e `inverse_mod(17, 3120)` daba 2753, con *k* = 15.

## Paso 2 · Cifrar y descifrar

**Objetivo:** comprobar en Lean las cuentas de Sage: 65 → 2790 → 65.

```lean
import Mathlib

example : 2790 ^ 2753 % 3233 = 65 := by
  norm_num

example : 65 ^ 17 % 3233 = 2790 := by
  decide +kernel

example : 2790 ^ 2753 % 3233 = 65 := by
  decide +kernel

example : 7 ^ 17 % 3233 = 2369 := by
  decide +kernel

example : 2369 ^ 2753 % 3233 = 7 := by
  decide +kernel
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"65 → 2790 → 65","etiqueta":"proyecto · decide +kernel","espera_error":true,"idea":"`norm_num` no eleva a exponentes mayores que 256: avisa y deja la meta. `decide +kernel` le pasa la cuenta al núcleo de Lean, que la hace con números grandes, y la cierra.","notas":{"1":"`norm_num` se niega: el exponente 2753 pasa del límite de 256. Avisa y deja la meta sin cerrar.","2":"Cifrar: 65¹⁷ mod 3233 = 2790. El núcleo hace la cuenta.","3":"Descifrar: 2790²⁷⁵³ mod 3233 = 65. Un número de más de nueve mil cifras, y el núcleo lo calcula.","4":"Otro mensaje de Sage: 7 se cifra en 2369…","5":"…y vuelve a 7."}},"archivo":"datos/trazas/27-rsa-2.json"}
```

- El aviso de `norm_num` es literal: «exponent 2753 exceeds the threshold 256». Es una protección para no colgarse con potencias enormes. Se puede subir con `set_option exponentiation.threshold`, pero aquí hay un camino más directo.
- `decide +kernel` es el `decide` del capítulo 23 con una diferencia: la cuenta no la hace el elaborador, sino el **núcleo**, que tiene aritmética rápida para los naturales (capítulo 24). El `decide` a secas no llega: en la segunda cuenta para con «maximum recursion depth has been reached».
- 2790²⁷⁵³ tiene más de nueve mil cifras. El núcleo la calcula entera y luego divide. Comprobar es posible; lo que no se puede es comprobar **todos** los mensajes uno a uno. Para eso hace falta un teorema.

**Comprueba:** Sage daba `power_mod(65, 17, 3233)` = 2790, la vuelta 65, y 7 → 2369.

## Paso 3 · El teorema de Euler

**Objetivo:** usar el teorema de Euler: si *m* no tiene factores comunes con *n*, entonces *m*^φ(*n*) ≡ 1 (mód *n*).

```lean
import Mathlib

theorem phi_n : Nat.totient 3233 = 3120 := by
  rw [show 3233 = 61 * 53 from rfl, Nat.totient_mul (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

example : 65 ^ 3120 ≡ 1 [MOD 3233] := by
  have h : Nat.Coprime 65 3233 := by norm_num
  have e := Nat.ModEq.pow_totient h
  rw [phi_n] at e
  exact e
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Euler, en un caso","etiqueta":"proyecto · Nat.ModEq.pow_totient","idea":"El teorema de Euler generaliza el de Fermat del capítulo 15: el exponente ya no es *p* − 1, sino φ(*n*). Basta con que *m* y *n* no tengan factores comunes.","notas":{"1":"φ(3233) = 3120, como en el paso 1.","2":"Comprobación de que 61 y 53 son coprimos…","3":"…de que 61 es primo…","4":"…y de que 53 lo es.","5":"65 y 3233 no tienen factores comunes (3233 = 61 · 53, y 65 = 5 · 13).","6":"`norm_num` lo comprueba.","7":"Euler, aplicado a 65 y 3233: da 65^φ(3233) ≡ 1.","8":"Se cambia φ(3233) por 3120…","9":"…y es justo lo que se pedía."}},"archivo":"datos/trazas/27-rsa-3.json"}
```

- `Nat.ModEq.pow_totient` es el teorema de Euler en Mathlib. Su enunciado, tal como lo escribe `#check`: `∀ {x n : ℕ}, x.Coprime n → x ^ n.totient ≡ 1 [MOD n]`.
- `≡ [MOD n]` es la congruencia del capítulo 15: `a ≡ b [MOD n]` significa `a % n = b % n`.
- El de Fermat es el caso *n* primo: φ(*p*) = *p* − 1.
- La hipótesis de ser coprimos es imprescindible. Con 61, que divide a 3233, falla. Lo veremos en el paso 5.

**Comprueba:** Sage calculó `power_mod(65, 3120, 3233)` = 1.

## Paso 4 · Descifrar devuelve el mensaje

**Objetivo:** demostrar que, si *e*·*d* = 1 + *k*·φ(*n*) y *m* no tiene factores comunes con *n*, entonces (*m*^*e*)^*d* ≡ *m* (mód *n*).

```lean
import Mathlib

theorem phi_n : Nat.totient 3233 = 3120 := by
  rw [show 3233 = 61 * 53 from rfl, Nat.totient_mul (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

theorem descifra (m n e d k : ℕ) (hm : Nat.Coprime m n)
    (hed : e * d = 1 + k * Nat.totient n) : (m ^ e) ^ d ≡ m [MOD n] := by
  have h := Nat.ModEq.pow_totient hm
  calc (m ^ e) ^ d = m * (m ^ Nat.totient n) ^ k := by
        rw [← pow_mul, hed, pow_add, pow_one, mul_comm k, pow_mul]
    _ ≡ m * 1 ^ k [MOD n] := (h.pow k).mul_left m
    _ = m := by rw [one_pow, mul_one]

example : (65 ^ 17) ^ 2753 ≡ 65 [MOD 3233] := by
  apply descifra 65 3233 17 2753 15
  · norm_num
  · rw [phi_n]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"Descifrar deshace cifrar","etiqueta":"proyecto · calc · ModEq.pow · mul_left","idea":"(*m*^*e*)^*d* = *m*^(*e*·*d*) = *m*^(1 + *k*·φ) = *m* · (*m*^φ)^*k*. Por Euler, *m*^φ ≡ 1, así que todo es ≡ *m* · 1^*k* = *m*.","notas":{"1":"φ(3233) = 3120, para el ejemplo final…","2":"…con la comprobación de que 61 y 53 son coprimos…","3":"…de que 61 es primo…","4":"…y de que 53 lo es.","5":"Euler, para el *m* y el *n* del teorema.","6":"Una cadena de igualdades y congruencias, con tres eslabones.","7":"Primer eslabón: reescribir la potencia, paso a paso. El segundo, *m*^φ ≡ 1 elevado a *k* y multiplicado por *m*, es un término, sin táctica.","8":"Tercer eslabón: 1^*k* = 1 y *m* · 1 = *m*.","9":"El caso de Sage: se aplica el teorema con *m* = 65, *n* = 3233, *e* = 17, *d* = 2753, *k* = 15. Quedan dos metas.","10":"Que 65 y 3233 son coprimos.","11":"Y que 17 · 2753 = 1 + 15 · φ(3233): con φ(3233) = 3120, es una cuenta, y `rw` la cierra."}},"archivo":"datos/trazas/27-rsa-4.json"}
```

- La cadena del primer eslabón: `← pow_mul` junta (*m*^*e*)^*d* en *m*^(*e*·*d*); `hed` cambia *e*·*d* por 1 + *k*·φ; `pow_add` y `pow_one` separan *m* · *m*^(*k*·φ); y `mul_comm k` con `pow_mul` lo escriben como (*m*^φ)^*k*.
- `h.pow k` eleva la congruencia *m*^φ ≡ 1 a la *k*, y `.mul_left m` multiplica los dos lados por *m*. Son las reglas del capítulo 15 para operar con congruencias como con igualdades.
- Este teorema vale para **cualquier** *n*, no solo para *n* = *p*·*q*. Pero pide que *m* no tenga factores comunes con *n*.

**Comprueba:** el ejemplo final es la vuelta de Sage, 65 → 2790 → 65, demostrada sin hacer la cuenta de nueve mil cifras.

## Paso 5 · El mensaje 61

**Objetivo:** ver que con *m* = 61 Euler falla pero RSA funciona, y demostrar Fermat para **todo** *m* módulo un primo.

```lean
import Mathlib

example : Nat.gcd 61 3233 = 61 := by norm_num

example : 61 ^ 3120 % 3233 = 1220 := by
  decide +kernel

example : (61 ^ 17) ^ 2753 % 3233 = 61 := by
  decide +kernel

theorem fermat (p m t : ℕ) (hp : p.Prime) : m ^ (1 + t * (p - 1)) ≡ m [MOD p] := by
  by_cases h : p ∣ m
  · have h0 : m ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    calc m ^ (1 + t * (p - 1)) ≡ 0 ^ (1 + t * (p - 1)) [MOD p] := h0.pow _
      _ = 0 := by rw [zero_pow (by omega)]
      _ ≡ m [MOD p] := h0.symm
  · have hc : Nat.Coprime m p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
    have hf := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at hf
    calc m ^ (1 + t * (p - 1)) = m * (m ^ (p - 1)) ^ t := by
          rw [pow_add, pow_one, mul_comm t, pow_mul]
      _ ≡ m * 1 ^ t [MOD p] := (hf.pow t).mul_left m
      _ = m := by rw [one_pow, mul_one]
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El 61, y Fermat sin excepciones","etiqueta":"proyecto · by_cases · Fermat","idea":"61 divide a 3233, así que Euler no se aplica: 61³¹²⁰ mod 3233 = 1220. Pero elevar a 1 + *t*·(*p* − 1) no cambia nada módulo un primo *p*, **sea cual sea** el número: si *p* lo divide, los dos lados son 0; si no, es Fermat.","notas":{"1":"61 es un factor común de 61 y 3233.","2":"Euler falla: 61³¹²⁰ mod 3233 = 1220, no 1.","3":"Y sin embargo, cifrar y descifrar devuelve el 61.","4":"Fermat sin excepciones: dos casos, según *p* divida a *m* o no.","5":"Caso *p* ∣ *m*: entonces *m* ≡ 0 (mód *p*).","6":"Una cadena: *m*^(…) ≡ 0^(…), que es 0, que es ≡ *m*.","7":"0^(…) = 0, porque el exponente 1 + … no es 0…","8":"…(lo comprueba `omega`). El último eslabón, 0 ≡ *m*, es `h0` dado la vuelta.","9":"Caso *p* ∤ *m*: entonces *m* y *p* son coprimos.","10":"Euler para *m* y *p*…","11":"…con φ(*p*) = *p* − 1: es el Fermat del capítulo 15.","12":"Y la misma cadena del paso 4, con *p* − 1 en lugar de φ(*n*).","13":"Separar la potencia; el eslabón siguiente usa *m*^(*p* − 1) ≡ 1…","14":"…y al final se simplifica. Fermat vale para todo *m*."}},"archivo":"datos/trazas/27-rsa-5.json"}
```

- `by_cases h : p ∣ m` abre dos casos: o *p* divide a *m*, o no (capítulo 7). En el primero, *m* ≡ 0 y todo es 0; en el segundo, *m* y *p* son coprimos y se aplica Euler.
- `Nat.Prime.coprime_iff_not_dvd` dice que un primo *p* es coprimo con *m* si y solo si no lo divide.
- Euler necesita «coprimos con *n*»; este Fermat, en cambio, no pide nada a *m*. El precio es trabajar con un primo cada vez. El paso 6 junta los dos primos.

**Comprueba:** Sage calculó que 61^φ mod *n* = 1220 y 61^(*e*·*d*) mod *n* = 61, sin poder decir por qué. Ahora se sabe: módulo 61 los dos lados son 0, y módulo 53 es Fermat.

## Paso 6 · RSA, para cualquier mensaje

**Objetivo:** demostrar que, para primos distintos *p* y *q* y *e*·*d* = 1 + *k*·(*p* − 1)(*q* − 1), se cumple (*m*^*e*)^*d* ≡ *m* (mód *p*·*q*) para **todo** *m*.

```lean
import Mathlib

theorem fermat (p m t : ℕ) (hp : p.Prime) : m ^ (1 + t * (p - 1)) ≡ m [MOD p] := by
  by_cases h : p ∣ m
  · have h0 : m ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    calc m ^ (1 + t * (p - 1)) ≡ 0 ^ (1 + t * (p - 1)) [MOD p] := h0.pow _
      _ = 0 := by rw [zero_pow (by omega)]
      _ ≡ m [MOD p] := h0.symm
  · have hc : Nat.Coprime m p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
    have hf := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at hf
    calc m ^ (1 + t * (p - 1)) = m * (m ^ (p - 1)) ^ t := by
          rw [pow_add, pow_one, mul_comm t, pow_mul]
      _ ≡ m * 1 ^ t [MOD p] := (hf.pow t).mul_left m
      _ = m := by rw [one_pow, mul_one]

theorem rsa (p q e d k m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hed : e * d = 1 + k * ((p - 1) * (q - 1))) : (m ^ e) ^ d ≡ m [MOD p * q] := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [← pow_mul, hed]
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
  constructor
  · have := fermat p m (k * (q - 1)) hp
    convert this using 3
    ring
  · have := fermat q m (k * (p - 1)) hq
    convert this using 3
    ring

example : (61 ^ 17) ^ 2753 ≡ 61 [MOD 61 * 53] :=
  rsa 61 53 17 2753 15 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"El teorema de RSA","etiqueta":"proyecto · restos chinos · convert","idea":"Si dos números son congruentes módulo *p* y módulo *q*, con *p* y *q* coprimos, lo son módulo *p*·*q*: es el teorema chino de los restos. Módulo *p*, el exponente 1 + *k*(*p* − 1)(*q* − 1) es 1 + [*k*(*q* − 1)]·(*p* − 1), y Fermat dice que no cambia nada. Igual módulo *q*.","notas":{"1":"Fermat sin excepciones, como en el paso 5: dos casos.","2":"Si *p* ∣ *m*: *m* ≡ 0…","3":"…la cadena…","4":"…0^(…) = 0…","5":"…con el exponente distinto de 0 (`omega`).","6":"Si *p* ∤ *m*: coprimos…","7":"…Euler…","8":"…con φ(*p*) = *p* − 1…","9":"…la cadena…","10":"…separar la potencia…","11":"…y simplificar.","12":"RSA. Primero: dos primos distintos son coprimos.","13":"Se juntan las dos potencias y se cambia *e*·*d* por 1 + *k*(*p* − 1)(*q* − 1).","14":"Restos chinos: basta con demostrarlo módulo *p* y módulo *q*.","15":"Dos metas: módulo *p* y módulo *q*.","16":"Módulo *p*: Fermat con *t* = *k*·(*q* − 1).","17":"El exponente de Fermat, 1 + *k*(*q* − 1)(*p* − 1), y el nuestro, 1 + *k*((*p* − 1)(*q* − 1)), son el mismo escrito distinto: `convert` deja esa igualdad…","18":"…y `ring` la demuestra.","19":"Módulo *q*: Fermat con *t* = *k*·(*p* − 1)…","20":"…el mismo arreglo…","21":"…y `ring`. RSA está demostrado.","22":"El 61 de Sage, como caso particular. Cuatro hipótesis: 61 es primo…","23":"…53 también…","24":"…61 ≠ 53…","25":"…y 17 · 2753 = 1 + 15 · (60 · 52)."}},"archivo":"datos/trazas/27-rsa-6.json"}
```

- `Nat.modEq_and_modEq_iff_modEq_mul` es el teorema chino de los restos en la forma que hace falta: `m.Coprime n → (a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n])`. Con `.mp` se usa de izquierda a derecha.
- `convert this using 3` compara la meta con lo que da Fermat y deja como metas solo las diferencias: aquí, los dos exponentes. `ring` ve que son iguales (trata *p* − 1 y *q* − 1 como bloques).
- `Nat.coprime_primes` dice que dos primos son coprimos si y solo si son distintos.
- El teorema no pide nada a *m*: ni que sea coprimo con *n*, ni siquiera que sea menor que *n*. Lo que dice es que vuelve el **resto** de *m* módulo *n*. Por eso en Sage HOLA (18262211, mayor que 3233) volvía como 2227, el resto de 18262211 entre 3233.

**Comprueba:** el ejemplo final es el 61 de Sage, ahora como caso particular de un teorema.

::::{div}
:class: afondo
## A fondo · Romper la llave

En el A fondo de Sage se rompía una llave pequeña: *n* = 999985999949, *e* = 65537. `factor` la partía en 999983 · 1000003, y con eso se calculaba *d* = 83020476125 y se leía el mensaje SOS (302630), cifrado en 705788091757. Lean puede comprobar todos esos números, y algo más: que descifrar con esa *d* funciona para cualquier mensaje.

```lean
import Mathlib

example : 999983 * 1000003 = 999985999949 := by norm_num
example : Nat.Prime 999983 := by norm_num
example : Nat.Prime 1000003 := by norm_num

example : 65537 * 83020476125 = 1 + 5441 * ((999983 - 1) * (1000003 - 1)) := by
  norm_num

example : 302630 ^ 65537 % 999985999949 = 705788091757 := by
  decide +kernel
```

```{anywidget} ../widgets/metas.mjs
{"config":{"titulo":"La llave rota de Sage","etiqueta":"a fondo · factorizar · decide +kernel","idea":"Quien conoce los dos primos calcula *d* y descifra. Lean comprueba la factorización, que los factores son primos, la relación *e*·*d* = 1 + 5441·(*p* − 1)(*q* − 1) y el cifrado de SOS.","notas":{"1":"La factorización que encontró `factor` (PARI).","2":"999983 es primo…","3":"…y 1000003 también.","4":"La llave privada: 65537 · 83020476125 = 1 + 5441 · (999982 · 1000002).","5":"Y el cifrado de SOS: 302630⁶⁵⁵³⁷ mod 999985999949 = 705788091757. Es un número de unas 360 000 cifras, y el núcleo lo calcula."}},"archivo":"datos/trazas/27-rsa-7.json"}
```

Con esos números, el teorema `rsa` del paso 6 se aplica con *p* = 999983, *q* = 1000003, *e* = 65537, *d* = 83020476125 y *k* = 5441. Da (*m*⁶⁵⁵³⁷)^83020476125 ≡ *m* (mód 999985999949) para todo *m* (reto 8). La cuenta directa de descifrar, en cambio, es imposible: la potencia tendría del orden de 10¹² cifras. La demostración llega donde la cuenta no llega.

Lo que Lean **no** demuestra es que RSA sea seguro. Su seguridad descansa en que factorizar números grandes es difícil en la práctica, y eso no es un teorema: nadie sabe demostrarlo. Ni siquiera se sabe si romper RSA es tan difícil como factorizar; es una pregunta abierta. Lean garantiza que el sistema es **correcto**: el que tiene la llave privada recupera siempre el mensaje.

Rivest, Shamir y Adleman publicaron el método en un informe técnico del MIT en abril de 1977.
::::

:::{admonition} La misma idea en tres lenguajes
:class: seealso
Cifrar y descifrar el 65 de Sage, comprobado haciendo la cuenta en los tres sistemas (Lean 4.36.0, Coq 8.18 e Isabelle2026):

```lean
-- Lean
example : 65 ^ 17 % 3233 = 2790 := by decide +kernel
example : 2790 ^ 2753 % 3233 = 65 := by decide +kernel
```

```coq
(* Rocq (Coq) *)
Require Import NArith.
Open Scope N_scope.
Lemma cifra : 65 ^ 17 mod 3233 = 2790.
Proof. vm_compute. reflexivity. Qed.
Lemma descifra : 2790 ^ 2753 mod 3233 = 65.
Proof. vm_compute. reflexivity. Qed.
```

```isabelle
(* Isabelle *)
lemma cifra: "(65::int) ^ 17 mod 3233 = 2790" by eval
lemma descifra: "(2790::int) ^ 2753 mod 3233 = 65" by eval
```

Los tres le pasan la cuenta a una máquina de calcular de confianza: el núcleo de Lean, la máquina virtual de Coq (`vm_compute`), el código que genera Isabelle (`eval`). En Coq se usan los naturales binarios `N`: los `nat` de Peano escriben cada número como una cadena de sucesores, y un número de nueve mil cifras no cabe así. En Isabelle se usa `int`: con `nat`, incluso 65¹⁷ se quedó varios minutos sin terminar, y con `int` las dos cuentas tardan segundos.
:::

## Conexiones

- El libro de SageMath (capítulo 26) montó el RSA de juguete; este proyecto demuestra por qué funciona.
- Fermat y las congruencias vienen del capítulo 15; aquí se generalizan a Euler.
- Las cadenas de igualdades y congruencias son el `calc` del capítulo 10, y `by_cases` es el razonamiento por casos del capítulo 7.
- `decide +kernel` junta el `decide` del capítulo 23 con el núcleo del capítulo 24.
- `convert` y `ring` (capítulo 14) arreglan las diferencias de escritura entre lo que da un teorema y lo que se pide.

## El final del libro

Con este proyecto termina el libro, y la colección. Los dos proyectos han hecho lo mismo: tomar algo que el libro de SageMath comprobaba con unos cuantos casos y demostrarlo para todos.

Queda una última grieta, y es honesta: hay preguntas que ninguna máquina puede cerrar todavía, porque nadie sabe la respuesta. Que factorizar sea difícil es una de ellas. Lean no adivina teoremas; comprueba los que alguien es capaz de demostrar. Lo que sí garantiza es que lo demostrado está demostrado.

## Retos

1. **Otra llave.** Con *p* = 11 y *q* = 17, demuestra que φ(187) = 160 y que *e* = 7, *d* = 23 cumplen *e*·*d* = 1 + 1 · 160.

2. **Cifrar y descifrar.** Con la llave del reto 1, comprueba que 88 se cifra en 11 y que 11 se descifra en 88.

3. **Sin inverso.** Demuestra que 3 no tiene inverso módulo 3120: no existe *d* con 3·*d* ≡ 1 (mód 3120). ¿Por qué no sirve *e* = 3 con la llave de Sage?

4. **El mensaje 3000.** Comprueba que 3000 se cifra en 1780 y vuelve.

5. **Euler falla con 61.** Demuestra que 61^φ(3233) no es ≡ 1 (mód 3233).

6. **Un mensaje no coprimo.** Usa el teorema `rsa` para demostrar que (11⁷)²³ ≡ 11 (mód 11 · 17).

::::{div}
:class: afondo
7. **Firmar.** Demuestra que también (*m*^*d*)^*e* ≡ *m* (mód *p*·*q*): descifrar y luego cifrar devuelve el mensaje. Es la base de la firma digital.

8. **Descifrar la llave rota.** Aplica `rsa` a la llave del A fondo para demostrar que (*m*⁶⁵⁵³⁷)^83020476125 ≡ *m* (mód 999983 · 1000003) para todo *m*.
::::

## Solucionario

1. Como `phi_n`:
   ```lean
   example : Nat.totient 187 = 160 := by
     rw [show 187 = 11 * 17 from rfl, Nat.totient_mul (by norm_num),
       Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
   example : 7 * 23 = 1 + 1 * 160 := by norm_num
   ```
2. Con exponentes pequeños, `norm_num` sirve: `example : 88 ^ 7 % 187 = 11 := by norm_num` y `example : 11 ^ 23 % 187 = 88 := by norm_num`.
3. Si 3·*d* ≡ 1 (mód 3120), también módulo 3, porque 3120 = 3 · 1040; y módulo 3, 3·*d* es 0:
   ```lean
   example : ¬ ∃ d, 3 * d ≡ 1 [MOD 3120] := by
     rintro ⟨d, h⟩
     have h3 : 3 * d ≡ 1 [MOD 3] := Nat.ModEq.of_mul_right 1040 h
     unfold Nat.ModEq at h3
     omega
   ```
   Con *e* = 3 no hay *d*: mcd(3, 3120) = 3. Sage daba `ZeroDivisionError` en `inverse_mod(3, 3120)`.
4. `example : 3000 ^ 17 % 3233 = 1780 := by decide +kernel` y `example : 1780 ^ 2753 % 3233 = 3000 := by decide +kernel`.
5. Con `phi_n` del paso 1:
   ```lean
   example : ¬ 61 ^ Nat.totient 3233 ≡ 1 [MOD 3233] := by
     rw [phi_n]
     decide +kernel
   ```
6. Con `fermat` y `rsa` del paso 6: `example : (11 ^ 7) ^ 23 ≡ 11 [MOD 11 * 17] := rsa 11 17 7 23 1 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)`.

::::{div}
:class: afondo
7. Es `rsa` con *e* y *d* cambiados; la hipótesis se da la vuelta con `mul_comm`:
   ```lean
   theorem firma (p q e d k m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
       (hed : e * d = 1 + k * ((p - 1) * (q - 1))) : (m ^ d) ^ e ≡ m [MOD p * q] :=
     rsa p q d e k m hp hq hpq (by rw [mul_comm]; exact hed)
   ```
8. Con `rsa` del paso 6:
   ```lean
   example (m : ℕ) : (m ^ 65537) ^ 83020476125 ≡ m [MOD 999983 * 1000003] :=
     rsa 999983 1000003 65537 83020476125 5441 m (by norm_num) (by norm_num)
       (by norm_num) (by norm_num)
   ```
::::
