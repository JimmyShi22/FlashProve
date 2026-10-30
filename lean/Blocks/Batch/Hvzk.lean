-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/Hvzk.lean: a lemma on shared challenges.

One lemma, on lists of rounds with an annotation (`RoundSplits`, Iop/Batch.lean). `Iop.Rho.fst_eq_of_sh`:
annotate s ++ t by `RAnn.ofShared .sh` in every round of s, and by any B in t; two sequences of
challenges with the same shared challenges (`Rho.sh`) have equal parts on s.
It says nothing on t, and nothing on a protocol, a prover or a simulator.

Notation: from Iop/Batch.lean: `RAnn.ofShared k r`: a round in which only the shared part is sent:
the slots send nothing; `RoundSplits.const f s`: the same rule of annotation in every round; `RoundSplits.app`:
the annotation of two shapes one after the other; `Rho.sh A ρ`: the shared verifier messages among
those of a local transcript; `Rho.fst : Rho (s ++ t) → Rho s` (Iop/Shape.lean).
-/
import Blocks.Batch.ProbPi
import Blocks.PfrHVZK_rs
import Iop.BatchUnif
import Blocks.Batch.Kit
import Blocks.Batch.KitHon
import Iop.BatchOne

set_option autoImplicit false

namespace Iop

/-- Where every round of s is annotated by `RAnn.ofShared .sh`, challenges of s ++ t with the same
shared challenges agree on s. -/
theorem Rho.fst_eq_of_sh :
    ∀ {s t : Shape} (B : RoundSplits t) {ρ ρ' : Rho (s ++ t)},
      Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) ρ =
        Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) ρ' →
      Rho.fst ρ = Rho.fst ρ'
  | [], _, _, _, _, _ => rfl
  | r :: s, _, B, (c, ρ), (c', ρ'), h => by
      have h1 : c = c' := congrArg Prod.fst h
      have h2 : Rho.fst ρ = Rho.fst ρ' := Rho.fst_eq_of_sh B (congrArg Prod.snd h)
      show ((c, Rho.fst ρ) : r.Chal × Rho s) = (c', Rho.fst ρ')
      rw [h1, h2]

end Iop
