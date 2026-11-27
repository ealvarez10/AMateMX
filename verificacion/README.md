# Verification evidence

## `reproduccion_vm/`: independent rebuild of Alpöge's library (22–23 November 2026)

[amate_alpoge_vm.sh](reproduccion_vm/amate_alpoge_vm.sh) is a self-contained script that ran on an Ubuntu/Debian virtual machine with 64 cores and 255 GB of RAM. It does the following:

1. It sets `vm.max_map_count` to 1,048,576. With the default value of 65,530, Lean fails to load the imports of the heaviest modules.
2. It clones the library at commit `40e56bab026552e089d7afcfeff08d2defb9c005` into the same path MIT used (`/home/ubuntu/grh/src/lean`). This matters because, in Lean 4.33.1, `.olean` files with linter warnings embed the absolute source path.
3. It builds the library as an unprivileged user with no network access.
4. It checks the composition with AMate.
5. It compares every `.olean` with the SHA-256 list published by MIT.

Result ([resultado.txt](reproduccion_vm/resultado.txt), [comparacion_mit.txt](reproduccion_vm/comparacion_mit.txt)):

- 175,187 modules built in 11 hours, with no module failing.
- All 175,187 `.olean` files are byte-identical to the MIT list. This includes `LocModel.olean`, which MIT documents as nondeterministic. `Main.olean` has SHA-256 `9146dfb4148e24d2252e04c50742f3e49dd126dfcc5006d10bf5f873ddf796ad`.
- `AMate.energia_subpolinomial_alpoge`, as well as `riemannHypothesis`, depends only on `propext`, `Classical.choice` and `Quot.sound` ([verificacion.txt](reproduccion_vm/verificacion.txt)).

The full result archive (34 MB, with the hash of every module and the build logs) is not in this repository. Its SHA-256 is in [amate_resultado.tar.gz.sha256](reproduccion_vm/amate_resultado.tar.gz.sha256).

## `nanoda/`: independent kernel recheck (27 November 2026)

The main theorems of `AMateEnergia`, `AMateDirichlet` and `AMateMiller` were exported with `lean4export` and checked by `nanoda`:

- **Export:** the main theorems with all their dependencies, Mathlib included. It was 687,557,410 bytes; its SHA-256 is in [amate.ndjson.sha256](nanoda/amate.ndjson.sha256).
- **Tool versions:** `lean4export` tag v4.33.0 (commit `15f6055`), built with Lean 4.33.1, and `nanoda_lib` commit `0da9f98` (v0.4.32).
- **Result:** "Checked 76387 declarations with no errors" ([nanoda_salida.txt](nanoda/nanoda_salida.txt)). Only `propext`, `Quot.sound` and `Classical.choice` were permitted, and they are the only axioms in the export.
- **Statements:** the statements printed by nanoda match the Lean sources ([enunciados_nanoda.txt](nanoda/enunciados_nanoda.txt)).

To reproduce it, see [../scripts/verificar_con_nanoda.sh](../scripts/verificar_con_nanoda.sh).

## `reproduccion_vm/amate_composiciones_vm.sh`: new compositions (prepared, not yet run)

Run after `amate_alpoge_vm.sh`, on the same machine, it compiles `AMateConAlpoge/ComposicionDirichlet.lean` (E_{Q,χ} ≪_ε Q^ε and Θ_χ = 1/2 for every χ ≠ 1), `AMateConAlpoge/HipotesisAlpoge.lean` and `AMateConAlpoge/MillerAlpoge.lean` (deterministic Miller tests with O((log n)^4) and O((log n)^2) bases, Bach's bound a ≤ 2(log n)² for log n ≥ 64, and the certified executable test `esPrimoMiller basesExplicitas`), and checks that the axioms of ten declarations are only `propext`, `Classical.choice` and `Quot.sound`. Locally, `ComposicionDirichlet.lean` and `MillerAlpoge.lean` were type-checked against literal copies of the statements they use from Alpöge's library, with those statements as placeholders. `HipotesisAlpoge.lean` does not import `Main`, so it was compiled locally against the compiled library (27 November 2026): `hipHadamard_alpoge`, `serieDigamma_alpoge`, `cota_bach_explicita_de_grh` and `esPrimoMiller_explicito_de_grh` depend only on the three standard axioms.
