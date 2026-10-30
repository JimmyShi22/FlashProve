-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ThinOfReads.lean: the congruences of Sim/FirstPubAtHead.lean
from less. There two places are asked to have all seven numbers in common. What the public tests on
a place read is less: the list of stages, whether the first fold sends its own table, and the
declared rounds. Two places that have these in common, and whose blocks pass their tests on the
plan, have the same declared rounds with the same depths and widths (`thinOf`), and the public tests
give the same at both.

  `sent_reads`, `oracles_reads`   the trees that a test sends, and their cut by rounds, read the
                 stages, that flag and the declared rounds alone
  `thin_of_reads`   `thinOf` is the same at both places
  `formPubB_reads`, `tabB_reads`   `formPubB` (FormPubAt.lean) and `tabB` (Sim/FirstPubAtHead.lean)
                 give the same at both places

By what. `thinOf_eq`, `pairs_of_planOk` and the small lemmas on `thinOf` of Sim/FirstPubAtHead.lean.

Limits. On public numbers alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 Parts proximityTestKind)
open H2K.JointK (laidOf laidS)
open Johnson.Prover.Link (asked)

theorem sent_reads {M N : H2U.TestNums} (h1 : M.stages = N.stages) (h2 : M.ownMask = N.ownMask) :
    M.sent = N.sent := by
  unfold H2U.TestNums.sent
  rw [h1, h2]

theorem oracles_reads {M N : H2U.TestNums} (hR : H2U.roundsOfNums M = H2U.roundsOfNums N)
    (hS : M.sent = N.sent) : H2U.testOracles M = H2U.testOracles N := by
  unfold H2U.testOracles
  rw [hR, hS]

theorem thin_of_reads {T Cl : Type} (X : Parts T) {p q : P12}
    (hst : p.nums.stages = q.nums.stages) (hm : p.nums.ownMask = q.nums.ownMask)
    (hR : H2U.roundsOfNums p.nums = H2U.roundsOfNums q.nums)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (hq : (proximityTestKind X q : Block T Cl).planOk = true) :
    thinOf p = thinOf q := by
  have ho : p.oracles.map (·.map pairOf) = q.oracles.map (·.map pairOf) := by
    refine Option.some.inj ?_
    rw [← pairs_of_planOk X p hp, ← pairs_of_planOk X q hq]
    exact oracles_reads hR (sent_reads hst hm)
  rw [thinOf_eq, thinOf_eq, hR, ho]

theorem formPubB_reads {p q : P12} (hst : p.nums.stages = q.nums.stages)
    (hT : thinOf p = thinOf q) : formPubB p = formPubB q := by
  have e1 : (laidOf p).map asked = (laidOf q).map asked := by rw [asked_thin, asked_thin, hT]
  have e2 : ∀ n, (((laidS p).drop n).take 2).map (·.1) = (((laidS q).drop n).take 2).map (·.1) :=
    fun n => by rw [cut_thin, cut_thin, hT]
  unfold formPubB lettersOf
  simp only [e1, e2, hst]

theorem tabB_reads {p q : P12} (hst : p.nums.stages = q.nums.stages) (hT : thinOf p = thinOf q)
    (own : Bool) : tabB p own = tabB q own := by
  unfold tabB
  simp only [at_pairs, pairs_thin, length_congr hT, hT, hst]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sent_reads
#print axioms ProofFile.Honest.K12.Light.oracles_reads
#print axioms ProofFile.Honest.K12.Light.thin_of_reads
#print axioms ProofFile.Honest.K12.Light.formPubB_reads
#print axioms ProofFile.Honest.K12.Light.tabB_reads
