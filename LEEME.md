# AMate: un criterio de energía para la hipótesis de Riemann, formalizado en Lean 4

Autor: **Ernesto Álvarez** (investigador independiente, México). English version: [README.md](README.md).

Este repositorio contiene la formalización en Lean 4 del artículo *Un criterio de energía para la hipótesis de Riemann, su calibración y su verificación formal en Lean* ([articulo/](articulo/), en cinco idiomas).

**Lo que no es.** Este trabajo **no** contiene una demostración independiente de la hipótesis de Riemann. Sus resultados propios son teoremas sin hipótesis y equivalencias. Una parte opcional (`AMateConAlpoge`) los compone con una biblioteca de Lean, anunciada en noviembre de 2026, que afirma demostrar RH. Esa biblioteca está verificada por máquina, pero hasta donde sabemos no ha pasado revisión humana.

## Resultados

La tabla completa, con los nombres en Lean, está en [README.md](README.md#main-results). En resumen:
- **Calibración sin hipótesis:** lim log(2 + E_Q)/log Q = 2Θ − 1.
- **Equivalencias:** RH equivale a E_Q ≪ Q^ε y a varias formas aritméticas (ventanas de von Mangoldt, déficit de primos, suma hiperbólica).
- **Un teorema de barrera.**
- **Funciones L de Dirichlet:** una dirección del criterio.
- **La parte algebraica del test de Miller.**

Todo usa solo Mathlib y los axiomas `propext`, `Classical.choice` y `Quot.sound`, sin `sorry`. Los teoremas principales los revisó además el núcleo independiente `nanoda`.

## Compilar

```bash
lake exe cache get
lake build
lake env lean Axiomas.lean
```

## Licencia

- **Código:** Apache 2.0.
- **Artículo:** CC BY 4.0.

## Uso de IA

Las demostraciones formales, las comprobaciones numéricas y las traducciones se desarrollaron con asistencia de modelos de lenguaje (Claude y Codex). La novedad y la corrección matemática deben ser revisadas por especialistas.
