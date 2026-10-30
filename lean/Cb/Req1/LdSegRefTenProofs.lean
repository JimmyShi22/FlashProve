-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefTenProofs.lean: the statements of Cb/Req1/LdSegRefTen.lean, proved.

The proofs take the block from Cb/Ld/LdBattProofs.lean, the index-lifting rule from
Cb/Ld/LdWfIdxProofs.lean, the steps by the rule for a change of the base joint
(Cb/Ld/LdBatPeelProofs.lean), the sums by Cb/Req1/LdSegProofs.lean; `ldSegRef_tn_own` uses
`ldSegRef_placed0` (Cb/Req1/LdSegRefSupp.lean).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefTen.lean.
-/
import Cb.Req1.LdSegRefTen
import Cb.Ld.LdBattProofs
import Cb.Ld.LdWfIdxProofs
import Cb.Req1.LdSegStep
import Cb.Req1.LdSegRefSupp
import Cb.Req1.LdSegRefKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR IOR.Chain
open scoped ENNReal

theorem ldSegRef_tn_own : Spec.ldSegRef_tn_own := by
  intro E Kc _ _ X h
  refine ⟨fun i j e => h.inj (Sum.inr.inj e), fun i => h.own i, fun _ => trivial, ?_,
    fun i a e => Sum.inr_ne_inl e, ?_⟩
  · rintro q st (a | n) hn
    · rfl
    · exact ldSegRef_placed0 _ _ E X.μAt _ n fun a e => hn (e ▸ h.rdM a)
  · intro q st i
    exact ldSegRef_placed0 _ _ E X.μAt _ (X.wAt i) fun a e => h.wM i a e.symm

theorem ldSegRef_tn_bat : Spec.ldSegRef_tn_bat := fun _ _ _ _ _ _ _ _ _ => rfl

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- the block keeps the state: under `h` (it puts out z from x), `X.stOf z` is x.2 -/
theorem batt_st (x : (X.bt.Q → E) × X.bt.St) (y : X.C.E0.Str) (τ : Tr (X.bt.batt X.C.E0).shape)
    (z : X.bt.par.Mid) (h : (X.bt.batt X.C.E0).out x y τ = some z) : X.stOf z = x.2 := by
  obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 ((seq_out _ _ x y τ).symm.trans h)
  have h1 : some (X.bt.nx x (drawn (Tr.fst τ))) = some x₂ := h1
  have h2 : X.bt.par.outC x₂ (Tr.snd (s := [drawRound X.bt.Z.D]) τ) = some z := h2
  unfold PscPar.outC at h2
  split at h2
  · rw [← Option.some.inj h2, ← Option.some.inj h1]
    rfl
  · exact absurd h2 (by simp)

theorem goodAt (hn : 2 ≤ X.n) (hZ : X.Z.OK) :
    GoodAt (X.bt.batt X.C.E0)
      (idxH X.C (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)) X.m0.A X.m1.A
      (idxExt X.C fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc) :=
  idxLift_goodAt X.C Kc _ _ X.S.Msg X.Wp X.Wp (X.bt.batt X.C.E0) _ _ _ (fun x => X.rc x.2.2)
    (fun z => X.rc (X.stOf z).2) (fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)
    (fun x y τ z hz => congrArg (fun s : X.Xr × X.St => X.rc s.2) (X.batt_st x y τ z hz))
    (fun _ _ => rfl) (batt_goodAt E X.bt X.C.E0 (X.C.Msg × X.S.Msg) X.Wp Kc X.A1 X.msg hn hZ)

theorem stepIn_hyp : X.stepIn.Hyp :=
  ldSeg_step E Kc X.src X.m0 _ _ _ _
    (ldPeel_base E Kc _ _ _ _ X.S X.C.E0 X.C.E0 X.src.A X.m0.A (fun x => (x.2.1, (x.1, x.2.2)))
      (ExtMap.id X.C.E0) (fun _ w => w.2) (fun _ w => w.2) (extMap_isLocal.1 _)
    (fun _ _ _ hw => ⟨hw.2.1, ⟨hw.1, hw.2.2.1⟩, hw.2.2.2⟩) (fun _ _ hh => hh) (fun _ _ => rfl)
    (fun _ _ _ _ hw => by
      obtain ⟨U, hU, ⟨hr, ha⟩, ht⟩ := hw
      exact ⟨hr, U, hU, ha, ht⟩))

theorem stepOut_hyp (St₁ : Type) (fz : X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (hE : X.Ends St₁ fz Az) :
    (X.stepOut St₁ fz Az).Hyp :=
  ldSeg_step E Kc X.m1 (X.tgt St₁ Az) _ _ _ _
    (ldPeel_base E Kc _ _ _ _ X.S X.C.E0 X.C.E0 X.m1.A (X.tgt St₁ Az).A
      (fun z => ((X.stOf z).1, fz z)) (ExtMap.id X.C.E0) (fun _ w => w.2) (fun _ w => w.2)
      (extMap_isLocal.1 _) (fun z y w hw => ⟨hw.2.1.1, hE.fw z y w hw⟩) (fun z y hh => hE.on z y hh)
      (fun _ w => hE.core w) (fun z y w ho hw => hE.bw z y w ho hw.1 hw.2))

end LdTenD

theorem ldSegRef_tn_hyp : Spec.ldSegRef_tn_hyp := by
  intro E Kc _ _ X St₁ fz Az hn hZ hE
  unfold LdTenD.prog
  rw [LdProg.hyp_snoc, LdProg.hyp_snoc, LdProg.hyp_snoc]
  exact ⟨⟨⟨LdProg.hyp_nilK _, X.stepIn_hyp⟩,
      (allB_one X.link).2 (ldSeg_lift E Kc X.m0 _ _ _ X.m1.A _ _ _ _ (X.goodAt hn hZ)).1⟩,
    X.stepOut_hyp St₁ fz Az hE⟩

open Classical in
theorem ldSegRef_tn_goodM : Spec.ldSegRef_tn_goodM := by
  intro E Kc _ _ X hn hZ hO
  have own := ldSegRef_tn_own E Kc X hO
  have gM := idxLift_goodM E X.C X.S Kc _ _ X.Wp X.Wp (X.bt.batt X.C.E0)
    (X.bt.hon X.C.E0 fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1)
    (X.bt.baseIn X.C.E0 X.A1 fun w => X.msg w.1)
    (X.bt.baseOut X.C.E0 X.A1 fun w => X.msg w.1)
    (fun x => X.rc x.2.2) (fun z => X.rc (X.stOf z).2) (fun _ _ _ wp => wp) (X.bt.nums X.C.E0 Kc)
    (X.bt.maskData X.C.E0 (fun w : (X.C.Msg × X.S.Msg) × X.Wp => X.msg w.1) X.RdJ)
    (fun x y τ z hz => congrArg (fun s : X.Xr × X.St => X.rc s.2) (X.batt_st x y τ z hz))
    (fun _ _ => rfl) (batt_goodAt E X.bt X.C.E0 (X.C.Msg × X.S.Msg) X.Wp Kc X.A1 X.msg hn hZ)
    (batt_mm E X.bt X.C.E0 _ _ X.RdJ hn own)
    (fun x _ w hw q => by
      show X.bt.lhs x.2 q (fun j => if X.RdJ j then X.msg w.1 j else 0) = x.1 q
      rw [← hw.2 q]
      exact X.bt.lhs_congr (fun a => if_pos (own.rdM a)) fun j hj =>
        if_pos (by by_contra hr; exact hj (own.rdS q x.2 j hr)))
  exact ldSeg_sub_goodM E Kc X.m0 X.m1 X.link X.mask gM

theorem ldSegRef_tn_zk : Spec.ldSegRef_tn_zk := by
  intro E Kc _ _ X St₁ fz Az base hn hZ hO hf
  unfold LdTenD.prog
  rw [LdProg.zk_snoc, LdProg.zk_snoc, LdProg.zk_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine ⟨⟨⟨(LdProg.zk_nil _ _).2 trivial, ?_⟩, ?_⟩, ?_⟩
  · unfold LdTenD.stepIn
    rw [LdMv.Zk]
    trivial
  · rw [LdMv.Zk]
    exact (okGiven_one X.link _).2 (Or.inr ⟨X.mask, ldSegRef_tn_goodM E Kc X hn hZ hO, hf⟩)
  · unfold LdTenD.stepOut
    rw [LdMv.Zk]
    trivial

theorem ldSegRef_tn_kinds : Spec.ldSegRef_tn_kinds := by
  intro E Kc _ _ X St₁ fz Az
  unfold LdTenD.prog
  rw [LdProg.all_snoc, LdProg.all_snoc, LdProg.all_snoc]
  exact ⟨⟨⟨LdProg.all_nilK _ _, Or.inr (Or.inr rfl)⟩, Or.inr (Or.inl rfl)⟩, Or.inr (Or.inr rfl)⟩

theorem ldSegRef_tn_nums : Spec.ldSegRef_tn_nums := by
  intro E Kc _ _ X St₁ fz Az
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp X.src X.m0 (sideF X.S fun x => (x.2.1, (x.1, x.2.2))) (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun x => (x.2.1, (x.1, x.2.2))) fun _ w => w.2) (sideB X.S fun _ w => w.2)
  have a3 := hp X.m1 (X.tgt St₁ Az) (sideF X.S fun z => ((X.stOf z).1, fz z))
    (sideG X.S (ExtMap.id X.C.E0))
    (sideM X.S (fun z => ((X.stOf z).1, fz z)) fun _ w => w.2) (sideB X.S fun _ w => w.2)
  have c2 : (LdMv.sub X.m0 X.m1 (.one X.link)).chain = .one X.link := by rw [LdMv.chain]
  have l2 : X.link.R.shape.nAll = X.k + 2 := batt_len E X.bt X.C.E0
  unfold LdTenD.prog LdTenD.stepIn LdTenD.stepOut
  refine ⟨?_, ?_, ?_⟩
  · rw [LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_snoc, LdProg.nAll_nil,
      a1.1, a3.1, c2, nAll_one, l2]
    omega
  · rw [LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_snoc, LdProg.pBad_nil,
      a1.2.2.1, a3.2.2.1, c2, pBad_one]
    show (0 : ℝ≥0∞) + 0 + (0 + 0) + 0 = 0
    simp
  · rw [LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_snoc, LdProg.pHid_nil,
      a1.2.2.2, a3.2.2.2, c2, pHid_one]
    show (0 : ℝ≥0∞) + 0 + (0 + 0) + 0 = 0
    simp

end Cb
