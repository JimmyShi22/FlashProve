-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lay/At/Sizes.lean: the numbers of the records of a layers' sub-proof's own rounds at
the value of Cb/Pv/Lay/At/ are the planner's, if the library's sizes are the planner's record's.

Main names:
  `DimIs D x`: fourteen equations between the library's sizes D (Inst/Model/FF/Index.lean,
    Objects.lean) and the planner's record of sizes x (Params.LayerRounds).
  `card_IA`, `card_IB`, `card_ShA`: the numbers of the revealed maps of the batched sumcheck and of
    the shown vectors of the terms.
  `midIs`: MidIs at the value. `sizesV`, `sizesVF`: SizesV and SizesVF at the value, from DimIs and
    the weights' stretch's two numbers.
  `layVO_shape_at`, `layVOF_shape_at`: so the chain's rounds at the value are the rounds of the
    planner's list, with the weights' stretch a letter.
  `nW_eq`: the number of the weight claims is the planner's, from the numbering and DimIs.
  `own_shape`, `own_counts`, `ownF_shape`, `ownF_counts`: with the weights' stretch filled
    (Cb/Pv/Lay/At/OwnW.lean, OwnFirstW.lean): the chain's rounds are the rounds of the planner's
    list, and its bounds on bad draws, round by round, are the numerators of the plan's pairs (at a
    round that draws a point: the count with the same quotient over the number of the field's
    elements). The pairs' denominator c is free there: that it is that number is not said.

The theorems ask, beside DimIs: that the record of sizes has terms, routed experts and both joins
(Full x); that the merge's rounds are the planner's (kW = x.lkW); which group it is (x.firstGroup);
in the first group: ls = x.ls and gB = x.lPd - x.ls.

Limits: that DimIs holds of the sizes that the verifier on bytes makes from its parameter files is
not said here; nor anything on what the records' maps are. The limits of
OnBytes/Tie/Pv/Lay/OwnSizes.lean hold here too.


-/
import OnBytes.Tie.Pv.Lay.OwnSizes
import Cb.Pv.Lay.At.OwnFirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Tie.Pv.Lay.At
open OnBytes OnBytes.Params OnBytes.G4 Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At TWhole
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans lamS lDd lF lFe)
open Cb.Pv.Lay.End.Sig (pans_nodup)

/-- The library's sizes are the planner's. -/
structure DimIs [scl : Scl] (D : Dim) (x : LayerRounds) : Prop where
  lt : D.lT = x.lt
  NI : D.nNu = x.NI
  NS : 9 = x.NS
  lNI : D.lL + 1 = x.lNI
  lPd : lDd D = x.lPd
  NP : 7 = x.NP
  NO : 4 = x.NO
  shown : D.nNu + (D.ne + D.ne * D.nx) = x.shownByTheTerms
  lamS : lamS D = x.lamS
  never : 1 + D.ne = x.neverSent
  claims : ((pans D).map (cntB D)).sum = x.weightClaims
  ll : D.lL = x.ll
  lPf : lF D = x.lPf
  lfe : lFe D = x.lfe

section Cards
variable (D : Dim)

theorem card_sig (c : Pan → ℕ) :
    Fintype.card (Σ p : {p : Pan // p ∈ pans D}, Fin (c p.1)) = ((pans D).map c).sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_subtype (pans D).toFinset (fun _ => List.mem_toFinset) c,
    List.sum_toFinset _ (pans_nodup D)]

theorem sum_cntA : ((pans D).map cntA).sum = 1 + D.ne := by
  simp [pans, cntA, isVirt, List.map_append, List.sum_append, List.map_map, Function.comp_def]

theorem card_IA : Fintype.card (IA D) = 1 + (1 + D.ne) := by
  rw [Fintype.card_sum, Fintype.card_unit, card_sig, sum_cntA]

theorem card_IB : Fintype.card (IB D) = 1 + ((pans D).map (cntB D)).sum := by
  rw [Fintype.card_sum, Fintype.card_unit, card_sig]

theorem card_ShA : Fintype.card (ShA D) = D.nNu + (D.ne + D.ne * D.nx) := by
  simp [Fintype.card_sum, Fintype.card_prod]

end Cards

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

/-- The numbers of the records up to the inner products, at the value. -/
theorem midIs (P : MidPar E M X) {X' : Type} (x0 : X' → X) (pv : X' → Fin P.D.lT → E)
    (Rd0 : X' → M → Prop) (x : LayerRounds) (h : DimIs P.D x) : MidIs (P.mid x0 pv Rd0) x where
  gn := h.NI
  gns := h.NS
  gg := h.lNI
  gk := by
    show lDd P.D + P.D.lT = _
    rw [h.lPd, h.lt]
  rnp := by
    show P.D.nNu * 7 = _
    rw [h.NI, ← h.NP, Nat.mul_comm]
  rk := h.lt
  rA := by
    show Fintype.card (Fin P.D.nNu × Fin 4) = _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, h.NI, ← h.NO, Nat.mul_comm]
  tk := h.lt
  tdy := rfl
  tA := by
    show Fintype.card (ShA P.D) = _
    rw [card_ShA, h.shown]
  ik := by
    show kS P.D = _
    rw [kS_eq, h.lamS]
  iA := by
    show Fintype.card (IA P.D ⊕ IB P.D) = _
    rw [Fintype.card_sum, card_IA, card_IB, h.never, h.claims]
    omega

/-- All records' numbers, for a sub-proof that is not the first. -/
theorem sizesV (P : OwnPar E M X) (W : P.WPart) (x : LayerRounds) (h : DimIs P.D x)
    (wn : W.Wt.n = x.weightClaims) (wk : W.Wt.k = x.lkW) (hf : x.firstGroup = false) :
    SizesV (P.layV W) x where
  mid := midIs P.toMidPar _ _ _ x h
  pk := by
    show P.D.lL + lF P.D + P.D.lT = _
    rw [h.ll, h.lPf, h.lt]
  qg := by
    show P.D.lL - 1 = _
    rw [h.ll]
  qk := by
    show lFe P.D + P.D.lT = _
    rw [h.lfe, h.lt]
  wn := wn
  wk := wk
  hf := hf

/-- All records' numbers, for the first sub-proof. -/
theorem sizesVF (P : OwnFPar E M X) (W : P.WFPart) (x : LayerRounds) (h : DimIs P.D x)
    (wn : W.Wf.n = x.weightClaims) (wk : W.Wf.k = x.lkW) (hf : x.firstGroup = true) :
    SizesVF (P.layVF W) x where
  mid := midIs P.toMidPar _ _ _ x h
  pk := by
    show P.D.lL + lF P.D + P.D.lT = _
    rw [h.ll, h.lPf, h.lt]
  qg := by
    show P.D.lL - 1 = _
    rw [h.ll]
  qk := by
    show lFe P.D + P.D.lT = _
    rw [h.lfe, h.lt]
  wn := wn
  wk := wk
  hf := hf

/-- **The chain's rounds at the value are the rounds of the planner's list.** -/
theorem layVO_shape_at (P : OwnPar E M X) (W : P.WPart) (x : LayerRounds) (hx : Full x)
    (h : DimIs P.D x) (wn : W.Wt.n = x.weightClaims) (wk : W.Wt.k = x.lkW)
    (hf : x.firstGroup = false) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E ((P.layVO W).toOwn.ch.R Ex).shape (ownList w x) :=
  layVO_shape (P.layVO W) x hx h.lt (sizesV P W x h wn wk hf) w Ex

/-- The same for the first sub-proof. -/
theorem layVOF_shape_at (P : OwnFPar E M X) (W : P.WFPart) (x : LayerRounds) (hx : Full x)
    (h : DimIs P.D x) (hls : P.ls = x.ls) (hB : P.gB = x.lPd - x.ls)
    (wn : W.Wf.n = x.weightClaims) (wk : W.Wf.k = x.lkW) (hf : x.firstGroup = true) (w : Nat)
    (Ex : ExtSpec) : ShapeIs E ((P.layVOF W).toOwn.ch.R Ex).shape (ownList w x) :=
  layVOF_shape (P.layVOF W) x hx h.lt
    (by
      show P.ls + P.D.lT = _
      rw [hls, h.lt]) hB (sizesVF P W x h wn wk hf) w Ex

/-! ### With the weights' stretch filled -/

/-- The number of the weight claims is the planner's. -/
theorem nW_eq (P : FullPar E M X) (x : LayerRounds) (h : DimIs P.D x) : P.nW = x.weightClaims := by
  have e : Fintype.card (Fin P.nW) = Fintype.card (Piece P.D) := Fintype.card_congr P.num
  rw [Fintype.card_fin, card_sig] at e
  rw [e, h.claims]

/-- The chain's rounds at the value are the rounds of the planner's list. -/
theorem own_shape (P : FullPar E M X) (x : LayerRounds) (hx : Full x) (h : DimIs P.D x)
    (wk : P.kW = x.lkW) (hf : x.firstGroup = false) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E (P.own.toOwn.ch.R Ex).shape (ownList w x) :=
  layVO_shape_at P.toOwnPar P.wPart x hx h (nW_eq P x h) wk hf w Ex

/-- Its bounds on bad draws, round by round, are the numerators of the plan's pairs (at a drawn
point: the count with the same quotient); c is free. -/
theorem own_counts (P : FullPar E M X) (x : LayerRounds) (hx : Full x) (h : DimIs P.D x)
    (wk : P.kW = x.lkW) (hf : x.firstGroup = false) (c : Nat) (Ex : ExtSpec) :
    List.Forall₂ (CountIs (Fintype.card E)) (TWhole.errList (P.own.toOwn.ch.eps Ex))
      (ownRatios c x) :=
  layVO_counts P.own x hx h.lt (sizesV P.toOwnPar P.wPart x h (nW_eq P x h) wk hf) c Ex

/-- The same for the first sub-proof. -/
theorem ownF_shape (P : FullFPar E M X) (x : LayerRounds) (hx : Full x) (h : DimIs P.D x)
    (hls : P.ls = x.ls) (hB : P.gB = x.lPd - x.ls) (wk : P.kW = x.lkW)
    (hf : x.firstGroup = true) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E (P.ownF.toOwn.ch.R Ex).shape (ownList w x) :=
  layVOF_shape_at P.ofp P.wfPart x hx h hls hB (nW_eq P.toFullPar x h) wk hf w Ex

/-- The same for the first sub-proof. -/
theorem ownF_counts (P : FullFPar E M X) (x : LayerRounds) (hx : Full x) (h : DimIs P.D x)
    (hls : P.ls = x.ls) (hB : P.gB = x.lPd - x.ls) (wk : P.kW = x.lkW)
    (hf : x.firstGroup = true) (c : Nat) (Ex : ExtSpec) :
    List.Forall₂ (CountIs (Fintype.card E)) (TWhole.errList (P.ownF.toOwn.ch.eps Ex))
      (ownRatios c x) :=
  layVOF_counts P.ownF x hx h.lt
    (by
      show P.ls + P.D.lT = _
      rw [hls, h.lt]) hB
    (sizesVF P.ofp P.wfPart x h (nW_eq P.toFullPar x h) wk hf) c Ex

end OnBytes.Tie.Pv.Lay.At

#print axioms OnBytes.Tie.Pv.Lay.At.own_shape
#print axioms OnBytes.Tie.Pv.Lay.At.own_counts
#print axioms OnBytes.Tie.Pv.Lay.At.ownF_shape
#print axioms OnBytes.Tie.Pv.Lay.At.ownF_counts
#print axioms OnBytes.Tie.Pv.Lay.At.midIs
#print axioms OnBytes.Tie.Pv.Lay.At.layVO_shape_at
#print axioms OnBytes.Tie.Pv.Lay.At.layVOF_shape_at
