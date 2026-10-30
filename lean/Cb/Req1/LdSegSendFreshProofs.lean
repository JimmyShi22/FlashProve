-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegSendFreshProofs.lean: the proofs of the statements of Cb/Req1/LdSegSendFresh.lean.
-/
import Cb.Req1.LdSegSendFresh
import Cb.Ld.LdSendFreshVisProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

theorem segSend_hid_but : Spec.segSend_hid_but := by
  classical
  intro E N o Rr r r' ho h
  funext a
  unfold Sig.visAt
  by_cases ha : a = o
  · subst ha
    rw [if_neg ho, if_neg ho]
  · have e : r' a = r a := congrFun h ⟨a, ha⟩
    rw [e]

section
variable (E Kc : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem segSend_fresh : Spec.segSend_fresh E Kc := by
  classical
  intro a d Mb _ _ U RdOld RdNew RrOld RrNew own val hsub hown hoff hpad hhid
  let RdA := a.S.sumP d.N RdOld RdNew
  let rd : d.N.Msg → (∀ o, Option (d.N.om o).Rnd) → a.S.Wit × d.Wp' →
      (a.S.sum d.N).Msg × (∀ o, Option ((a.S.sum d.N).om o).Rnd) × d.Wp' := fun m v w' =>
    ((a.S.sum d.N).cut RdA (a.S.join d.N (T := OMsg.Msg) (a.S.msgs w'.1) m),
      a.S.join d.N (T := fun o => Option o.Rnd)
        (fun o => if RrOld o then some (w'.1 o).2 else none) v,
      w'.2)
  let put : Mb → (a.S.sum d.N).Msg × (∀ o, Option ((a.S.sum d.N).om o).Rnd) × d.Wp' →
      (a.S.sum d.N).Msg × (∀ o, Option ((a.S.sum d.N).om o).Rnd) × d.Wp' := fun M k =>
    ((a.S.sum d.N).ow (a.S.sumP d.N (fun _ => False) own) (a.S.sumV d.N (fun _ => 0) (val M)) k.1,
      k.2)
  have hL : U.LawsV d.Sd (d.N.visAt RrNew) (d.N.budT d.t) rd put := by
    refine ⟨fun M M' k => Prod.ext (funext fun o => funext fun j => ?_) rfl,
      ⟨fun w k₀ v =>
          rd (d.D.upM (d.D.put w (U.mk' (Classical.arbitrary Mb) k₀ (Classical.arbitrary U.Pd)))) v
            (d.D.rest w),
        fun w M k₀ η v => Prod.ext (funext fun o => funext fun j => ?_) rfl⟩,
      hpad, hhid⟩
    · show (if _ then _ else (if _ then _ else _)) = if _ then _ else _
      split_ifs <;> rfl
    · rcases o with o | o
      · exact (if_neg (fun h : False => h)).symm
      · show (if RdNew ⟨o, j⟩ then d.D.upM (d.D.put w (U.mk' M k₀ η)) o j else 0) =
          if own ⟨o, j⟩ then val M ⟨o, j⟩
          else
            (if RdNew ⟨o, j⟩ then
                d.D.upM
                  (d.D.put w (U.mk' (Classical.arbitrary Mb) k₀ (Classical.arbitrary U.Pd))) o j
              else 0)
        by_cases ho : own ⟨o, j⟩
        · rw [if_pos ho, if_pos (hsub _ ho)]
          exact hown w M k₀ η ⟨o, j⟩ ho
        · rw [if_neg ho]
          by_cases hr : RdNew ⟨o, j⟩
          · rw [if_pos hr, if_pos hr]
            exact hoff w M _ k₀ η _ ⟨o, j⟩ hr ho
          · rw [if_neg hr, if_neg hr]
  have h1 := ldSendSig_freshV
    E a.S d.N d.Sd a.St a.Wp d.Wp' a.E₀ d.D d.t a.J.rels.rel Mb U _ _ (d.N.visAt RrNew) rd put hL
  have e : (fun v : (a.S.sum d.N).Wit × d.Wp' =>
        rd (d.N.msgs (a.S.right d.N (T := OMsg.Wit) v.1))
          (d.N.visAt RrNew fun o => (a.S.right d.N (T := OMsg.Wit) v.1 o).2)
          (a.S.left d.N (T := OMsg.Wit) v.1, v.2)) =
      (d.tgt.wideFact (a.S.sumP d.N RdOld RdNew) (a.S.sumO d.N RrOld RrNew)
        (a.S.sumP d.N (fun _ => False) own) Mb fun M => a.S.sumV d.N (fun _ => 0) (val M)).kc := by
    funext v
    refine Prod.ext (congrArg ((a.S.sum d.N).cut RdA) (funext fun o => ?_))
      (Prod.ext (funext fun o => ?_) rfl)
    · rcases o with o | o <;> rfl
    · rcases o with o | o <;> rfl
  exact e ▸ h1

theorem segSend_after :
    Spec.segSend_after E
      Kc := fun a d base Mb _ _ U RdOld RdNew RrOld RrNew own val h1 h2 h3 h4 h5 =>
  segCarry_send_new a d base _
    (segSend_fresh E Kc a d Mb U RdOld RdNew RrOld RrNew own val h1 h2 h3 h4 h5)

end
end Cb
