-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2GoodMProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsm2GoodM.lean (under
the hypotheses of their statements, the assembled lookup is a masked block, as a whole).
`LkAsm2.cut_claim`, `LkAsm2.stab_claim` are auxiliary lemmas.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2GoodM
import Cb.Ld.LdLkpAsm2PullProofs
import Cb.Ld.LdLkpMaskAsm2Proofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpAsm2M_dt : Spec.ldLkpAsm2M_dt E := by
  rintro A Dt h j hj (⟨l, hl, ho⟩ | ⟨l, hl, ho⟩ | ⟨l, hl, ho⟩ | ho | ho)
  · exact h.tie.dt l hl j hj ho
  · exact h.keyT.dt l hl j hj ho
  · exact (h.lev l hl).dt l (Nat.le_refl l) j hj ho
  · exact h.dtE j hj ho
  · exact h.dtB j hj ho

/-- An auxiliary lemma. Under `hRd` and `hC`: if the claim holds of k, it holds of `mjCut Rd k` (k,
with 0 outside Rd). -/
theorem LdLkp.LkAsm2.cut_claim (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop)
    (Dt Rd : A.J → Prop) (hRd : ∀ j, A.srAll Dt j → Rd j) (hC : A.ClaimReads Dt Mu) (st : A.St)
    (k : A.J → E) (h : A.lk.inP Mu st k) : A.lk.inP Mu st (mjCut Rd k) :=
  hC st k _ (fun j hj => (if_pos (hRd j (Or.inl hj))).symm) h

/-- An auxiliary lemma. Under `hM` and `hC`, the claim does not read the own masks. -/
theorem LdLkp.LkAsm2.stab_claim (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop) (Dt : A.J → Prop)
    (hM : A.MaskOK Dt) (hC : A.ClaimReads Dt Mu) : MjStab (A.lk.inP Mu) A.swAll :=
  fun st k k' hk h => hC st k k' (fun j hj => hk j (ldLkpAsm2M_dt E A Dt hM j hj)) h

theorem ldLkpAsm2M_link : Spec.ldLkpAsm2M_link E := by
  intro p _ A N ι Mu Ex _ M Wp Kc msg Dt Rd hA hMu hM hRd hC
  exact mjLift2_baseN E A N ι Ex M Wp Kc msg _ _ _ _ _
    (ldLkpMaskAsm2_link E p A Mu Ex M Wp Kc msg Dt Rd (A.lk.inP Mu) hA hMu hM hRd
      (fun _ _ h => h) (A.stab_claim E Mu Dt hM hC))

theorem ldLkpAsm2M_subN : Spec.ldLkpAsm2M_subN E := by
  intro p _ A N _ ι Mu S E₀ _ Kc Wp R0 msg Dt Rd hι hP hA hMu hM hRd hC
  exact ⟨ldLkpAsm2N_ok E p A N ι Mu S E₀ Kc Wp R0 msg hι hP hA hMu,
    mjLift2_subN E A N ι S E₀ Kc Wp msg _ _ _ _ _
      (ldLkpMaskAsm2_link E p A Mu E₀ S.Msg Wp Kc msg Dt Rd (A.lk.inP Mu) hA hMu hM hRd
        (fun _ _ h => h) (A.stab_claim E Mu Dt hM hC)),
    mjLift2_clN E A N ι Mu S E₀ Kc Wp R0 msg _ _ _ fun st w h =>
      A.cut_claim E Mu Dt Rd hRd hC st _ h⟩

theorem ldLkpAsm2M_subIN : Spec.ldLkpAsm2M_subIN E := by
  intro p _ A N _ ι Mu C _ S rc R0 msg Dt Rd hι hP hA hMu hM hRd hC
  exact ⟨ldLkpAsm2N_idx E p A N ι Mu C S rc R0 msg hι hP hA hMu,
    mjLift2_subIN E A N ι C S msg _ _ _ _ _
      (ldLkpMaskAsm2_link E p A Mu C.E0 (C.Msg × S.Msg) Unit Unit msg Dt Rd (A.lk.inP Mu)
        hA hMu hM hRd (fun _ _ h => h) (A.stab_claim E Mu Dt hM hC)),
    mjLift2_clIN E A N ι Mu C S rc R0 msg _ _ _ fun st w h => A.cut_claim E Mu Dt Rd hRd hC st _ h⟩

end
end Cb
