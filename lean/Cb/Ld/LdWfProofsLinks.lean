-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfProofsLinks.lean: proofs that, under `P.Laws` and `B.Hyp`, each step of the preamble of
weights-formedness has its bundle (`GoodT` for the sending, `GoodM` for a lookup and for the
batching), between the relations before and after it.
The steps are the three kinds of links (`IOR.Link`) of Cb/Ld/LdWf.lean; the relations are the
preamble's own joints.

By the composition rules alone: each block's own statement (`ldSendFam_goodT`; `Hyp.lkp`,
`Hyp.lkpM`, `Hyp.lkpC`, `Hyp.lkpN`, `Hyp.lkpS`, which are fields of the hypothesis `B.Hyp`;
`batt_goodAt`, `batt_mm`, `batt_row`), consequence (`goodT_conseq`, `goodB_conseq`), steps without
rounds before and after (`goodB_pre`, `goodB_post`, `exact_pre`, `mm_pre`, `mm_post`,
`extMap_isLocal`), `goodB_and`, `goodT_iff`, `goodM_cf`, the index-lifting rule
(Cb/Ld/LdWfIdx.lean), and one lemma of this file on the batching's output (`batt_st`) and one on
numbers (`le_self`), and one of Cb/Ld/LdBattProofs.lean (`lhs_congr`).
The relations fit by Cb/Ld/LdWfProofsRel.lean.

Main names:
  `lSend_goodT`: the sending: the whole bundle, from weights-formedness to the joint after 0
    lookups.
  `lLkp_goodM`: the lookup on forest l, for l ≤ `P.n`, then the filing: a masked block from the
    joint after l lookups to the joint after l + 1.
  `lBatt_goodM`: the batching of tensor rows between its two steps: a masked block from the joint
    after all lookups to the last joint.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfProofsRel
import Cb.Ld.LdWfIdxProofs
import Cb.Ld.LdSendFamProofs
import Cb.Ld.LdBattProofs
import Ior.KnowCollRulesFrameProofs
import Ior.MaskedMap
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

theorem le_self {K Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} (N : Nums K R) : N.Le N :=
  ⟨Err.le_refl _, le_rfl, le_rfl, fun _ _ h => h, fun _ => rfl⟩

/-! ### The sending -/

theorem step0 (hL : P.Laws) :
    StepT (fun rec => some (P.st0 rec)) (ExtMap.id C.E0)
      (fun a : C.Rec × C.PIdx => (P.st0 a.1, (P.bodyOf a.2.1.1, (a.2, ()))))
      (fun _ w => w.2.1) P.jIn.rels P.A0 where
  isLocal := extMap_isLocal.1 _
  acc := fun x y w h => ⟨rfl, wf_rel hL x y w h⟩
  onOut := fun x y x' h e => by
    rw [← Option.some.inj e]
    exact h
  keeps := fun _ _ => rfl
  know := fun x y x' w' h e hw => by
    rw [← Option.some.inj e] at hw
    exact wf_relR hL x y w' h hw

theorem lSend_goodT (hL : P.Laws) {B : P.Blk} (h : B.Hyp) : B.lSend.GoodT := by
  have g0 := ldSendFam_goodT E P.S P.Sd Unit P.WSt (P.Body × P.Wp) P.Wp C.E0 P.A0 P.back B.D B.L B.t
    h.laws h.fair h.list h.evades h.sender h.sBlind h.hides
  have g1 : GoodT (ldSendFam P.S P.Sd P.WSt C.E0) (ldSendFamHon P.Sd P.WSt C.E0 B.D) P.A0
      (P.S.over (P.A 0)).cf (fun _ _ w => P.back (P.S.msgs w.1) w.2)
      (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t) :=
    goodT_conseq _ _ _ _ _ _ _ _ _ P.A0 P.A0 _ (P.S.over (P.A 0)).cf _ _ _ g0 (fun _ _ _ h => h)
      (fun x y w h => ⟨h.1, h.2.1, send_rel x.1 y.1 (P.S.msgs w.1, w.2) h.2.2⟩) (fun _ h => h)
      (fun _ h => h) (fun _ _ _ h => h)
      (fun b w hw =>
        hw.elim (fun hw => Or.inl ⟨hw.1, send_relR (b.1.1, b.2.1) (P.S.msgs w.1, w.2) hw.2⟩) Or.inr)
      (fun _ => rfl) (fun _ => rfl) (le_self _)
  obtain ⟨gB, gx⟩ := (goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 g1
  refine (goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2 ⟨?_, ?_⟩
  · exact goodB_pre _ _ _ _ _ _ _ _ _ _ _ _ P.jIn.rels P.A0 _ _ (fun _ _ w => w.2.1) _ _ _ _ _
      (step0 hL) gB fun _ _ _ _ _ => rfl
  · exact exact_pre _ _ _ _ _ _ _ _ _ _ _ P.A0.rel P.jIn.rels.rel _ _ _ _
      (extMap_isLocal.1 _) (step0 hL).acc gx

/-! ### A lookup -/

/-- the output joint of the lookup on forest l, in the sub-protocol's notation -/
abbrev jOut (P : LdWfP E C) (l : ℕ) : Rels Unit (TX P.WSt E P.N × P.S.Smp) P.Ex P.W :=
  jt P.S C.E0 P.Wp (onFst P.onW)
    (honFst fun st m' wp => P.honAt l st (id m') wp) ((P.lk l).out id P.entM)

/-- the output joint, with the fact on the honest side that what is put out can be filed -/
abbrev jOutN (P : LdWfP E C) (l : ℕ) : Rels Unit (TX P.WSt E P.N × P.S.Smp) P.Ex P.W :=
  (P.jOut l).cf.and (fun x _ _ => P.FileOK l x) (fun _ _ => True) (fun _ => True)

theorem stepFile (hL : P.Laws) (l : ℕ) :
    StepT (P.file l) (ExtMap.id P.Ex)
      (fun a : (TX P.WSt E P.N × P.S.Smp) × P.W => (P.fileD l a.1, a.2)) (fun _ w => w)
      (P.jOutN l) (P.S.over (P.A (l + 1))).cf where
  isLocal := extMap_isLocal.1 _
  acc := fun x y w h => by
    show P.file l x = some (P.fileD l x) ∧ (P.S.over (P.A (l + 1))).rel (P.fileD l x) y w
    rw [fileD_eq l x h.2]
    exact ⟨file_some l x h.2, h.1.1, h.1.2.1,
      out_rel hL l x h.2 y.1 (P.S.msgs w.1, w.2) h.1.2.2.1 h.1.2.2.2⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := fun x y x' w' _ e hw => by
    obtain ⟨h, rfl⟩ := file_eq l x x' e
    exact ⟨hw.elim (fun hw => Or.inl ⟨hw.1, out_relR l x h y.1 (P.S.msgs w'.1, w'.2) hw.2⟩) Or.inr,
      trivial⟩

theorem lLkp_goodM (hL : P.Laws) {B : P.Blk} (h : B.Hyp) {l : ℕ} (hl : l ≤ P.n) :
    (B.lLkp l).GoodM ((B.Dm l).post _ _) := by
  have hrel : ∀ x y w, (P.S.over (P.A l)).cf.rel x y w →
      (jt2 P.S C.E0 P.Wp P.onW (P.honAt l) ((P.lk l).inP (P.multAt l)) (P.lk l).inR).rel x y w :=
    fun x y w hw => ⟨hw.1, hw.2.1, in_rel hL hl x.1 y.1 (P.S.msgs w.1, w.2) hw.2.2⟩
  have g1 : GoodB (B.sub l).R (B.sub l).H (P.S.over (P.A l)).cf (P.jOut l).cf
      (B.sub l).ext (B.sub l).P :=
    goodB_conseq _ _ _ _ _ _ _ _ _ _ (P.S.over (P.A l)).cf _ (P.jOut l).cf _ _ _ (h.lkp l hl) hrel
      (fun _ _ _ h => h) (fun _ h => h) (fun _ h => h)
      (fun a w _ hw =>
        hw.elim (fun hw => Or.inl ⟨hw.1, in_relR hl (a.1.1, a.2.1) (P.S.msgs w.1, w.2) hw.2⟩)
          Or.inr)
      (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl) (le_self _)
  have g2 := goodB_and _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ => True) (fun _ _ => True)
    (fun _ => True) (fun x _ _ => P.FileOK l x) (fun _ _ => True) (fun _ => True) g1
    (fun x y w c ρ hA _ hρ _ =>
      ⟨h.lkpN l hl _ _ _ _ (g1.acc x y w c ρ hA hρ).1,
        h.lkpS l hl _ _ _ _ (g1.acc x y w c ρ hA hρ).1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
  have g3 : GoodB (B.sub l).R (B.sub l).H (P.S.over (P.A l)).cf (P.jOutN l)
      (B.sub l).ext (B.sub l).P :=
    goodB_conseq _ _ _ _ _ _ _ _ _ _ (P.S.over (P.A l)).cf _ (P.jOutN l) _ _ _ g2
      (fun _ _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h) (fun _ h => ⟨h, trivial⟩) (fun _ h => h)
      (fun _ _ _ h => h.1) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl) (le_self _)
  exact
    { base := goodB_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B.sub l).ext _ _ _ _ _ g3
        (stepFile hL l) fun _ _ _ _ _ => rfl
      mm := mm_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.lkpM l hl)
      claim := fun x y w hw => h.lkpC l hl x y w (hrel x y w hw) }

/-! ### The batching -/

/-- the two base joints of the batching, on tuples (message of the index, messages) -/
abbrev bIn (P : LdWfP E C) :
    Rels Unit ((P.bt.Q → E) × P.bt.St) C.E0 ((C.Msg × P.S.Msg) × Unit) :=
  P.bt.baseIn C.E0 P.rows fun w => P.msg w.1
abbrev bOut (P : LdWfP E C) :
    Rels Unit P.bt.par.Mid C.E0 ((C.Msg × P.S.Msg) × Unit) :=
  P.bt.baseOut C.E0 P.rows fun w => P.msg w.1

/-- the record in the two explicit parts of the batching -/
def rcIn (P : LdWfP E C) (x : (P.bt.Q → E) × P.bt.St) : C.Rec := (show P.WSt from x.2).1
def rcOut (P : LdWfP E C) (z : P.bt.par.Mid) : C.Rec := (P.stOf z).1

/-- the batching keeps the state -/
theorem batt_st (x : (P.bt.Q → E) × P.bt.St) (y : C.E0.Str) (τ : Tr (P.bt.batt C.E0).shape)
    (z : P.bt.par.Mid) (h : (P.bt.batt C.E0).out x y τ = some z) : P.stOf z = x.2 := by
  obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1 ((seq_out _ _ x y τ).symm.trans h)
  have h1 : some (P.bt.nx x (drawn (Tr.fst τ))) = some x₂ := h1
  have h2 : P.bt.par.outC x₂ (Tr.snd (s := [drawRound P.bt.Z.D]) τ) = some z := h2
  unfold PscPar.outC at h2
  split at h2
  · rw [← Option.some.inj h2, ← Option.some.inj h1]
    rfl
  · exact absurd h2 (by simp)

theorem stepToBatt (hL : P.Laws) :
    StepT (fun x => some (P.toBatt x)) (ExtMap.id P.Ex) (fun a : P.X × P.W => (P.toBatt a.1, a.2))
      (fun _ w => w) (P.S.over (P.A (P.n + 1))).cf (P.S.over (idxAt C P.rcIn P.bIn)).cf where
  isLocal := extMap_isLocal.1 _
  acc := fun x y w h => ⟨rfl, h.1, h.2.1, h.2.2.1, (done_iff hL x _ _).1 h.2.2.2.1⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := fun x y x' w' _ e hw => by
    rw [← Option.some.inj e] at hw
    rcases hw with ⟨h1, U, hU, h2⟩ | hn
    · exact Or.inl
        ⟨h1, U, hU, (done_iff hL x U _).2 h2, fun f hf hn => absurd hn (Nat.not_le_of_lt hf)⟩
    · exact Or.inr fun hon => hn ⟨hon.1, hon.2, trivial⟩

theorem stepToLast {B : P.Blk} (h : B.Hyp) :
    StepT (fun x => some (P.toLast x)) (ExtMap.id P.Ex)
      (fun a : (P.Cl × P.S.Smp) × P.W => (P.toLast a.1, a.2)) (fun _ w => w)
      (P.S.over (idxAt C P.rcOut P.bOut)).cf (P.S.over P.lastB).cf where
  isLocal := extMap_isLocal.1 _
  acc := fun x y w hw =>
    ⟨rfl, hw.1, hw.2.1, hw.2.2.1,
      (batt_row E P.bt (Nat.le_of_succ_le h.deg) x.1 _).1 hw.2.2.2.2, hw.2.2.2.1⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := fun x y x' w' _ e hw => by
    rw [← Option.some.inj e] at hw
    rcases hw with ⟨h1, U, hU, h2, h3⟩ | hn
    · exact Or.inl ⟨h1, U, hU, h3, (batt_row E P.bt (Nat.le_of_succ_le h.deg) x.1 _).2 h2⟩
    · exact Or.inr fun hon => hn ⟨hon.1, hon.2.1⟩

/-- the parameters of the item of the batching's link -/
def DmL (B : P.Blk) : MaskData P.lBatt.R P.W :=
  (B.DmB.pre (fun x => some (P.toBatt x)) (ExtMap.id _)
      (fun x => B.DmB.pub (P.toBatt x)) B.DmB.kc).post
    (fun x => some (P.toLast x)) (ExtMap.id _)

open Classical in
theorem lBatt_goodM (hL : P.Laws) {B : P.Blk} (h : B.Hyp) : P.lBatt.GoodM (DmL B) := by
  have gM := idxLift_goodM E C P.S Unit _ _ Unit Unit (P.bt.batt C.E0)
    (P.bt.hon C.E0 fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1) P.bIn P.bOut P.rcIn P.rcOut
    (fun _ _ _ wp => wp) (P.bt.nums C.E0 Unit)
    (P.bt.maskData C.E0 (fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1) B.Rd)
    (fun x y τ z hz => congrArg Prod.fst (batt_st x y τ z hz))
    (fun _ _ => rfl) (batt_goodAt E P.bt C.E0 (C.Msg × P.S.Msg) Unit Unit P.rows P.msg h.deg h.zOK)
    (batt_mm E P.bt C.E0 _ _ B.Rd h.deg h.own)
    (fun x _ w hw q => by
      show P.bt.lhs x.2 q (fun j => if B.Rd j then P.msg w.1 j else 0) = x.1 q
      rw [← hw.2 q]
      exact P.bt.lhs_congr (fun a => if_pos (h.own.rdM a)) fun j hj =>
        if_pos (by by_contra hr; exact hj (h.own.rdS q x.2 j hr)))
  have gC := goodM_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _ gM
  have b1 := goodB_pre _ _ _ _ _ _ _ _ _ _ _ _ (P.S.over (P.A (P.n + 1))).cf _ _ _ (fun _ _ w => w)
    _ _ _ _ _ (stepToBatt hL) gC.base fun _ _ _ _ _ => rfl
  exact
    { base := goodB_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ _ _ _ _ b1
        (stepToLast h) fun _ _ _ _ _ => rfl
      mm := mm_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (mm_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) gC.mm)
      claim := fun x y w hw => gC.claim (P.toBatt x) y w ((stepToBatt hL).acc x y w hw).2 }

end LdWfP
end Cb
