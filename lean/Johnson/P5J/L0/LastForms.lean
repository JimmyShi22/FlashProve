-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastForms.lean: THE SHARED TABLE's CONSTANT's MEANING AND PROMISE (`Sh.mg`, `Sh.pm`,
Johnson/Desc/K14/Law/SharedConst.lean) ARE OF THE TWO FORMS IN WHICH THE LAST TABLE's LAW TAKES THEM
(`meaningSigS … MS`, `promSigS … Pm₀`), at every plan A and every filling O of the open letters: by
unfolding. So `leads3_at` (Johnson/P5J/L0/LastCall.lean) is called at MS := `Sh.mg A O` and Pm₀ :=
`Sh.pm A O` themselves. Over that constant's file alone: no file of the tower's, none of the last
table's.
Limits. Four equations by unfolding. Nothing on soundness, nothing on hiding.
-/
import Johnson.Desc.K14.Law.SharedConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J.L0

open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- The shared table's reader of samples, in the last table's files' words. -/
theorem sh_smp_form : Sh.smp₂ A = smpSt A.Q.codes (Sh.oNo A) stSh := rfl

/-- **The shared table's meaning is its own `meaningSigS …`.** -/
theorem sh_mg_form : Sh.mg A O =
    meaningSigS A.Q.codes A.G O.arr (smpSt A.Q.codes (Sh.oNo A) stSh) (Sh.ms A) (Sh.decT₂ A O)
      (Sh.mg A O) := rfl

/-- **The shared table's promise is its own `promSigS …`.** -/
theorem sh_pm_form : Sh.pm A O =
    promSigS A.Q.codes A.G (smpSt A.Q.codes (Sh.oNo A) stSh) (Sh.ms A) (fun s : St => s.st)
      (fun s : St => shiftBook (Sh.nums A O).lo s.book) (Sh.pm A O) := rfl

/-- The shared table's numbers are the first table's, tied to its own. -/
theorem sh_nums_form : Sh.nums A O =
    tiedNumbers O.N₁
      (_root_.Desc.K14.Law.Fence.numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) (0, 0) (0, 0)) := rfl

end P5J.L0

#print axioms P5J.L0.sh_smp_form
#print axioms P5J.L0.sh_mg_form
#print axioms P5J.L0.sh_pm_form
#print axioms P5J.L0.sh_nums_form
