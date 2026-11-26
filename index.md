---
title: Mirar y ver tu código pensar
subtitle: Entendiendo Lean 4, desde dentro
---

Un libro para aprender a demostrar con Lean 4 viendo cómo piensa cada demostración: táctica a táctica, con lo que sabes y lo que te falta siempre a la vista. Es el quinto de la colección, después de los de Python, R, Julia y SageMath, y está hecho con el mismo método. Cada idea parte de una situación conocida, se construye con código y se comprueba visualizando cada paso.

Lean 4 es un lenguaje de programación y, sobre todo, un **demostrador**: un programa que comprueba, paso a paso y sin fiarse de nadie, que una demostración matemática es correcta. Con su biblioteca **Mathlib**, una enorme colección de matemáticas comprobadas por ordenador que escribe y revisa una comunidad abierta, sirve para demostrar desde que la suma conmuta hasta resultados de investigación.

Los libros anteriores de la colección terminaban con la misma grieta. Un ordenador puede comprobar mil casos, pero eso no es demostrar que algo vale para todos. Este libro empieza justo ahí.

## Un libro, dos rutas

Como los programas del IB con su nivel medio y su nivel superior, este libro tiene **dos rutas** que conviven en las mismas páginas.

- La **ruta base** es la que sigue todo el mundo: la idea con un ejemplo hecho, la demostración visualizada paso a paso y los ejercicios. Sirve para clase y para aprender solo.
- Los apartados **A fondo** llevan una cápsula negra. Cuentan cómo funciona Lean por dentro y cómo se trabaja con él como profesional. Se pueden saltar sin perder el hilo.

Elige aquí tu ruta. La elección se recuerda en todo el libro, y puedes cambiarla cuando quieras desde cualquier capítulo.

```{anywidget} ./widgets/rutas.mjs
{}
```

## Lo que hay ahora

El libro acaba de empezar. Ya puedes leer [Cómo leer este libro](capitulos/00-como-leer.md), con la primera demostración visualizada, y los primeros capítulos, desde [Lean como calculadora](capitulos/01-calculadora.md). El plan completo (en negrita, lo que ya está escrito):

| Parte | Capítulos |
|---|---|
| I · Primeros pasos | **[Lean como calculadora](capitulos/01-calculadora.md)** · **[Funciones y definiciones](capitulos/02-funciones.md)** · **[Proposiciones y pruebas](capitulos/03-proposiciones.md)** · **[El panel de metas](capitulos/04-panel.md)** · **[Reescribir: `rw` y `simp`](capitulos/05-reescribir.md)** |
| II · Lógica | **[Implicación y conjunción](capitulos/06-implicacion.md)** · **[Disyunción y casos](capitulos/07-disyuncion.md)** · **[Negación y absurdo](capitulos/08-negacion.md)** · **[Para todo y existe](capitulos/09-cuantificadores.md)** · **[Igualdad y `calc`](capitulos/10-calc.md)** |
| III · Inducción y números | **[Inducción](capitulos/11-induccion.md)** · **[Divisibilidad y primos](capitulos/12-divisibilidad.md)** · **[Desigualdades](capitulos/13-desigualdades.md)** · **[Álgebra con `ring`](capitulos/14-ring.md)** · **[Congruencias y Fermat](capitulos/15-congruencias.md)** |
| IV · Matemáticas con Mathlib | **[Conjuntos](capitulos/16-conjuntos.md)** · **[Funciones: inyectiva y sobreyectiva](capitulos/17-inyectivas.md)** · **[Sucesiones y límites](capitulos/18-sucesiones.md)** · **[Continuidad y derivadas](capitulos/19-continuidad.md)** · **[Buscar en Mathlib](capitulos/20-buscar.md)** |
| V · Lean por dentro | **[Proposiciones como tipos](capitulos/21-prop-tipos.md)** · **[Tipos dependientes y universos](capitulos/22-universos.md)** · **[Qué hacen `simp`, `omega` y `decide`](capitulos/23-automaticas.md)** · **[El núcleo y los axiomas](capitulos/24-nucleo.md)** · **[Tus propias tácticas](capitulos/25-tacticas.md)** |
| Proyectos | **[Demostrar que el fabricante de ejercicios funciona](capitulos/26-fabricante.md)** · **[RSA demostrado](capitulos/27-rsa.md)** |

Los dos proyectos cierran lo que el libro de SageMath dejó abierto. Allí, un fabricante de ejercicios comprobaba con ejemplos que el discriminante siempre salía un cuadrado, y RSA descifraba bien todos los mensajes que se probaban. Aquí se demuestra que tiene que ser así, siempre.
