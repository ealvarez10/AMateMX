# AMate: un criterio de energía para la hipótesis de Riemann, formalizado en Lean 4

Autor: **Ernesto Álvarez** (investigador independiente, México). English version: [README.md](README.md).

Este repositorio contiene la formalización en Lean 4 del artículo *Un criterio de energía para la hipótesis de Riemann, su calibración y su verificación formal en Lean* ([articulo/](articulo/), en cinco idiomas).

**Lo que no es.** Este trabajo **no** contiene una demostración independiente de la hipótesis de Riemann. Sus resultados propios son teoremas sin hipótesis y equivalencias. Una parte opcional (`AMateConAlpoge`) los compone con una biblioteca de Lean, anunciada en noviembre de 2026, que afirma demostrar RH. Esa biblioteca está verificada por máquina, pero hasta donde sabemos no ha pasado revisión humana.

## Resultados

La tabla completa, con los nombres en Lean, está en [README.md](README.md#main-results). En resumen:
- **Calibración sin hipótesis:** lim log(2 + E_Q)/log Q = 2Θ − 1.
- **Equivalencias:** RH equivale a E_Q ≪ Q^ε y a varias formas aritméticas (ventanas de von Mangoldt, déficit de primos, suma hiperbólica).
- **Un teorema de barrera.**
- **Funciones L de Dirichlet:** el criterio completo y su calibración: GRH para χ equivale a E_{Q,χ} ≪ Q^ε, y lim log(2 + E_{Q,χ})/log Q = 2Θ_χ − 1.
- **Test de Miller:** la parte algebraica, el puente a caracteres de Dirichlet, un test ejecutable correcto para toda cota de tipo Bach, y las cotas ⌊K(1 + log n)^4⌋ y ⌊K(1 + log n)^2⌋ a partir de GRH, la fórmula explícita y el conteo de ceros.
- **Cota de Bach con constante explícita:** con GRH y enunciados analíticos de la biblioteca de Alpöge como hipótesis, todo carácter no principal módulo n toma un valor ≠ 1 en algún a ≤ 2(log n)² coprimo con n, si log n ≥ 64. De ahí sale un test de Miller ejecutable y certificado, `esPrimoMiller basesExplicitas`, con (⌊log₂ n⌋ + 1)² bases para n ≥ 2^93. En `AMateConAlpoge/`, `HipotesisAlpoge.lean` instancia esas hipótesis con los teoremas de Alpöge (compilado localmente contra su biblioteca) y `MillerAlpoge.lean` quita también GRH.

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

Las demostraciones formales, las comprobaciones numéricas y las traducciones se desarrollaron con asistencia de modelos de lenguaje. La novedad y la corrección matemática deben ser revisadas por especialistas.
