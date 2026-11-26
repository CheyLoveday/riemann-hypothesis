# Adjacent Frobenius row: local research check

Base: community readable `main` at
[`0d9138b2061a0839b906283edb340291ed9a688d`](https://github.com/leanprover-community/riemann-hypothesis/commit/0d9138b2061a0839b906283edb340291ed9a688d).
Toolchain: `leanprover/lean4:v4.37.0-rc1`, with the base commit's dependency pins.

These research modules are outside the production `src` import graph and Lake
library globs. They test one adjacent pair on one actual scaled Hecke operator.
The original #77 theorem remains recorded separately in
[RH-public v0.1.1](https://github.com/CheyLoveday/RH-public/releases/tag/v0.1.1).

## Statement

For a marked place and a Frobenius cycle satisfying the readable proof's native
matching and size hypotheses, the construction gives an integral linear row
`rowM` and an integral source form `phi0` such that

```text
rowM phi0 = 1
p divides rowM (scaledHeckeOperator phi)
```

for every integral source form `phi`. The theorem also supplies integrality of
the scaled output. The operator is literally
`hΛ.scaledHeckeOperator ⟨l, hlΛ⟩` from the readable proof.

The final declaration is
`New.FrobeniusRowResearch.exists_primitive_row_scaledHeckeOperator_of_adjacentPair`.
Its explicit polynomial input is constructed in
`New.FrobeniusCycle.adjacentPairingRow`; the final statement does not assume a
separating row or its divisibility.

## Construction and conventions

Write `P = p ^ frobExp`. For adjacent letters `s` and `s + 1`, use

$$
H_s=\sum_b X_{b,s}^{P}X_{b,s+1}.
$$

For a fixed coordinate `b0`, multiply by powers of `X_(b0,t)` to bring every
letter to degree `a`: use degree `a-P` at `s`, `a-1` at `s+1`, and `a` elsewhere.
The coefficient of the resulting pure `b0` monomial is exactly one.
The proof derives the capacity condition `P ≤ a` from the existing size
hypothesis; the final theorem has no additional degree premise.

`FrobeniusPairingCore.lean` proves that the adjacent twisted matrices cancel in
characteristic `p`, and that scaling deep variables kills `H_s` modulo the
principal ideal `(p)`. It then identifies polynomial substitution with the
source's `letterRep` and diagonal `p ^ depth` on ordinary coefficient columns.
In particular, every coefficient of `depthPower * letterRep(g) * h` is divisible
by `p`, for every integral change of frame `g`.

`FrobeniusHeckeRow.lean` applies that column as a row to the source's transposed
edge matrix. The divisibility is proved for each incoming edge before summing.
The final transport uses the actual source-form coordinate isomorphism and the
same normalization identity as `Columns.HeckeEdges`.

This is a depth-one statement. The unit-readout seed is integral; ramification
has not been proved here. Products of pairings, the exceptional-prime quotient,
and the old exact-order theorem are outside this check.

## Reproduction

From the repository root, with the pinned toolchain installed, restore the
repository's dependency caches using its documented cache setup. Then run:

```sh
export LEAN_ABORT_ON_PANIC=1
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -o research/FrobeniusPairingCore.olean research/FrobeniusPairingCore.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -o research/FrobeniusHeckeRow.olean research/FrobeniusHeckeRow.lean
```

These use the base package's strict elaboration settings. The production files
and build settings are unchanged. No local resource-limit overrides are added
by these modules.

Audit the main declarations with:

```sh
lake env lean --stdin <<'LEAN'
import research.FrobeniusHeckeRow
#print axioms New.FrobeniusCycle.adjacentPairingRow_unit
#print axioms New.FrobeniusCycle.adjacentPairingRow_deep_dvd
#print axioms New.FrobeniusRowResearch.exists_primitive_row_scaledHeckeOperator_of_adjacentPair
LEAN
```

## Verification recorded on 2026-11-26

- Both research modules compiled with native Lean 4.37.0-rc1, the strict
  elaboration flags above, `LEAN_ABORT_ON_PANIC=1`, and default resource limits.
  Both builds exited successfully with empty output.
- All 34 named definitions, lemmas, and theorems in the two files were audited
  with `#print axioms`. The complete axiom set was
  `{propext, Classical.choice, Quot.sound}`.
- The actual `MarkOperator` dependency target passed `lake build --no-build`
  after restoring the pinned caches. This check compiled the new research
  modules; it did not rebuild the full RH proof from source.
- `Challenge.lean`, `src/Statements.lean`, and `comparator.json` retain their base
  commit hashes. No production source, dependency pin, or build setting changed.
