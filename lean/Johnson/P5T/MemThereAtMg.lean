-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/MemThereAtMg.lean: AT THE HEAD `AtMg`, AT THE SECOND HASH FUNCTION: THE CLOSED TEST
`membersThereB` ACCEPTS AT THE CONSTANT's OWN LETTERS, AT EACH OF THE 25 SEGMENTS: the field hmem of
what is left of the core of the kind K9's condition (`CoreLeft`,
Johnson/Desc/First/Link/Law/CoreLeft.lean), at the letters of `AtMgA.K9Left`
(Johnson/P5J/K09Left.lean). One theorem. A joining: the evaluation is
Johnson/P5T/MemThereFull.lean's.
  `AtMg.hmem`: **`membersThereB (At.foldD Zp cF Ld) (At.ms Zp Z.lay) ((At.N Zp cF).group m) ((At.N
  Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1 + 1 + 1]?) = true`** at every Ld that
  `At.laid? Zp` lists and every m below 25.
How each letter is had: Ld is the written `LFull`: `ld_at_laid`
(Johnson/LPFE1R/SeedPublicFull.lean); the shapes and the members: `AtMg.M_full`,
`AtMg.ms_full`
(Johnson/P5J/PlanSixAtMg.lean); the group: `group_at_laid`
(Johnson/Desc/First/Close/Law/AlikeInScope.lean); the count: `LaidAt.msgs`
(Johnson/P5T/NotIxAtMg.lean).
Limits. Over the verifier's list of thirteen entry tests (Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean)
alone. At the second hash function alone. The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.MemThereFull
import Johnson.P5J.PlanSixAtMg
import Johnson.LPFE1R.SeedPublicFull
import Johnson.P5J.LettersAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Close (mlFull group_at_laid)
open VerifiableInference.Desc.Sound (msOf)
open VerifiableInference.Desc.LinkJoin (membersThereB batchAt ld_at_laid)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The closed test accepts, at each of the 25 segments.** -/
theorem AtMg.hmem (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Ld : Desc.K12.Door.Laid}
    (hLd : At.laid? Zp = some Ld) {m : ℕ} (hm : m < 25) :
    membersThereB (At.foldD Zp cF Ld) (At.ms Zp Z.lay) ((At.N Zp cF).group m)
      ((At.N Zp cF).msgsAt At.ps[batchAt fullLinks At.ps m + 1 + 1 + 1]?) = true := by
  obtain rfl : Ld = LFull := Option.some.inj (hLd.symm.trans (ld_at_laid h.scope h.laid))
  rw [P5T.memThere_is, h.M_full LFull, h.ms_full, group_at_laid h.scope h.laid m,
    h.laid.msgs h.scope]
  exact P5T.memThere_at hm

end P5J

#print axioms P5J.AtMg.hmem
