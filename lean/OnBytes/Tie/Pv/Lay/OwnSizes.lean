-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/OwnSizes.lean: the chain of a layers' sub-proof's own rounds that
Cb/Pv/Lay/OwnAll.lean builds from the blocks' records, against the planner: if the records' numbers
are those of the planner's record of sizes, its rounds are instances of the planner's entries, and
its errors are written out and stand against the plan's pairs.

OnBytes/Tie/Pv/Lay/OwnPlan.lean ties a chain at letters to the planner's list under two conditions
on the letters' numbers (`TailIs`, `TailErrs`). Here these conditions are proved for the chains that
OwnAll.lean builds, from equations between the blocks' own numbers and the numbers of a record of
sizes (Params.LayerRounds).

Main names:
  `MidIs`: the numbers of the squares', the row products', the terms' and the inner products'
    records are the planner's.
  `SizesV`, `SizesVF`: the same of all records, for a sub-proof that is not the first, and for the
    first.
  `tailIs`, `tailErrs`, `tailIsF`, `tailErrsF`: the two conditions of OwnPlan.lean.
  `layVO_shape`, `layVO_planned`: for a sub-proof that is not the first: the chain's rounds are
    instances of the entries of the planner's list; of whatever the planner's routine adds.
  `layVO_errs`: its errors, round by round, as a written list of counts of bad draws.
  `layVO_counts`: these counts against the plan's pairs (numerator, denominator), by the relation
    `CountIs` of OwnPlan.lean. It holds for every c in the place of the denominator: the numerators
    alone are compared, and at the draw of a point the count is the numerator times a power of the
    field's size.
  `layVOF_shape`, `layVOF_planned`, `layVOF_errs`, `layVOF_counts`: the same for the first
    sub-proof.

Limits: those of OwnPlan.lean and OnBytes/G4/RoundIs.lean: three of an entry's eleven numbers are
tied. The record of sizes has terms, routed experts and both joins (`Full`). The chain's laws are
proved in OwnAll.lean from fields that a user pays (link, seam, rides, atPt, atTwo, and the records'
own). No value of the records is built, and the equations of `SizesV` and `SizesVF` are proved of no
value. That the records' maps, forms and claims are the programs' is not said here.
-/
import OnBytes.Tie.Pv.Lay.OwnPlan
import Cb.Pv.Lay.OwnAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Params OnBytes.G4 Iop Cb Cb.Pv.Att Cb.Pv.Lay TWhole

variable {E : Type} [Field E] [Fintype E] {M X : Type}

/-- The numbers of the records up to the inner products are the planner's. -/
structure MidIs (W : Mid E M X) (x : LayerRounds) : Prop where
  gn : W.G.n = x.NI
  gns : W.G.ns = x.NS
  gg : W.G.g = x.lNI
  gk : W.G.k' = x.lPd + x.lt
  rnp : W.Rw.np = x.NP * x.NI
  rk : W.Rw.k = x.lt
  rA : Fintype.card W.Rw.A = x.NO * x.NI
  tk : W.Tm.k = x.lt
  tdy : W.Tm.dy = 1
  tA : Fintype.card W.Tm.A = x.shownByTheTerms
  ik : W.In.k = x.lamS
  iA : Fintype.card W.In.A = 2 + x.neverSent + x.weightClaims

/-- All records' numbers, for a sub-proof that is not the first. -/
structure SizesV (V : LayV E M X) (x : LayerRounds) : Prop where
  mid : MidIs V.toMid x
  pk : V.Ft.Gp.k = x.ll + x.lPf + x.lt
  qg : V.Ft.Rt.g = x.ll - 1
  qk : V.Ft.Rt.k' = x.lfe + x.lt
  wn : V.Ft.Wt.n = x.weightClaims
  wk : V.Ft.Wt.k = x.lkW
  hf : x.firstGroup = false

/-- All records' numbers, for the first sub-proof. -/
structure SizesVF (V : LayVF E M X) (x : LayerRounds) : Prop where
  mid : MidIs V.toMid x
  pk : V.Ft.Gp.k = x.ll + x.lPf + x.lt
  qg : V.Ft.Rt.g = x.ll - 1
  qk : V.Ft.Rt.k' = x.lfe + x.lt
  wn : V.Ft.Wf.n = x.weightClaims
  wk : V.Ft.Wf.k = x.lkW
  hf : x.firstGroup = true

theorem MidIs.nL {W : Mid E M X} {x : LayerRounds} (h : MidIs W x) : W.H.nL = x.NS * x.NI := by
  show W.G.n * W.G.ns = _
  rw [h.gn, h.gns, Nat.mul_comm]

theorem MidIs.s1 {W : Mid E M X} {x : LayerRounds} (h : MidIs W x) :
    StgIs W.H.s1 0 (x.lNI + x.lPd + x.lt) 2 2 :=
  ⟨rfl, by
    show W.G.g + W.G.k' = _
    rw [h.gg, h.gk, Nat.add_assoc], fun _ => rfl, rfl, Fintype.card_bool⟩

theorem MidIs.s2 {W : Mid E M X} {x : LayerRounds} (h : MidIs W x) :
    StgIs W.s2 1 x.lt 2 (x.NO * x.NI) := ⟨rfl, h.rk, fun _ => rfl, rfl, h.rA⟩

theorem MidIs.s3 {W : Mid E M X} {x : LayerRounds} (h : MidIs W x) :
    StgIs W.s3 1 x.lt 1 x.shownByTheTerms := ⟨rfl, h.tk, fun _ => rfl, h.tdy, h.tA⟩

theorem MidIs.s4 {W : Mid E M X} {x : LayerRounds} (h : MidIs W x) :
    StgIs W.s4 0 x.lamS 2 (2 + x.neverSent + x.weightClaims) :=
  ⟨rfl, h.ik, fun _ => rfl, rfl, h.iA⟩

theorem tailIs {V : LayV E M X} {x : LayerRounds} (h : SizesV V x) : TailIs V.toTail x where
  nL := h.mid.nL
  gN := h.mid.gg
  s1 := h.mid.s1
  nP := h.mid.rnp
  s2 := h.mid.s2
  s3 := h.mid.s3
  s4 := h.mid.s4
  s5 := ⟨rfl, h.pk, fun _ => rfl, rfl, Fintype.card_bool⟩
  gR := h.qg
  s6 := ⟨rfl, by
    show V.Ft.Rt.g + V.Ft.Rt.k' = _
    rw [h.qg, h.qk, Nat.add_assoc], fun _ => rfl, rfl, Fintype.card_bool⟩
  nW := by
    rw [h.hf]
    rfl
  s7 := ⟨rfl, h.wk, fun _ => rfl, rfl, Fintype.card_unit⟩

theorem tailErrs {V : LayV E M X} {x : LayerRounds} (h : SizesV V x) :
    TailErrs V.toTail x (Fintype.card E) where
  eL := by
    show V.G.ns - 1 = _
    rw [h.mid.gns]
  eN := by
    show V.G.g * Fintype.card E ^ (V.G.g - 1) = _
    rw [h.mid.gg]
  eP := by
    show V.Rw.np - 1 = _
    rw [h.mid.rnp]
  n4 := rfl
  eR := by
    show V.Ft.Rt.g * Fintype.card E ^ (V.Ft.Rt.g - 1) = _
    rw [h.qg]
  eW := by
    show V.Ft.Wt.n - 1 = _
    rw [h.wn, h.hf]
    rfl

theorem tailIsF {V : LayVF E M X} {x : LayerRounds} (h : SizesVF V x) : TailIs V.toTail x where
  nL := h.mid.nL
  gN := h.mid.gg
  s1 := h.mid.s1
  nP := h.mid.rnp
  s2 := h.mid.s2
  s3 := h.mid.s3
  s4 := h.mid.s4
  s5 := ⟨rfl, h.pk, fun _ => rfl, rfl, Fintype.card_bool⟩
  gR := h.qg
  s6 := ⟨rfl, by
    show V.Ft.Rt.g + V.Ft.Rt.k' = _
    rw [h.qg, h.qk, Nat.add_assoc], fun _ => rfl, rfl, Fintype.card_bool⟩
  nW := by
    rw [h.hf]
    rfl
  s7 := ⟨rfl, h.wk, fun _ => rfl, rfl, Fintype.card_unit⟩

theorem tailErrsF {V : LayVF E M X} {x : LayerRounds} (h : SizesVF V x) :
    TailErrs V.toTail x (Fintype.card E) where
  eL := by
    show V.G.ns - 1 = _
    rw [h.mid.gns]
  eN := by
    show V.G.g * Fintype.card E ^ (V.G.g - 1) = _
    rw [h.mid.gg]
  eP := by
    show V.Rw.np - 1 = _
    rw [h.mid.rnp]
  n4 := rfl
  eR := by
    show V.Ft.Rt.g * Fintype.card E ^ (V.Ft.Rt.g - 1) = _
    rw [h.qg]
  eW := by
    show V.Ft.Wf.n = _
    rw [h.wn, h.hf]
    rfl

/-! ### The whole, for a sub-proof that is not the first -/

theorem layVO_shape (A : LayVO E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (h : SizesV A.V x) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E (A.toOwn.ch.R Ex).shape (ownList w x) :=
  own_shape A.toOwn x hx h.hf hT (tailIs h) w Ex

theorem layVO_planned (A : LayVO E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (h : SizesV A.V x) (Ex : ExtSpec) (s : Setting) (p q : PlanState) (hp : At s 0 p)
    (hq : planLayerOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (A.toOwn.ch.R Ex).shape (l.map (·.entry)) :=
  own_planned A.toOwn x hx h.hf hT (tailIs h) Ex s p q hp hq

/-- The chain's errors, written out. -/
theorem layVO_errs (A : LayVO E M X) (x : LayerRounds) (hT : A.gT = x.lt) (h : SizesV A.V x)
    (Ex : ExtSpec) :
    TWhole.errList (A.toOwn.ch.eps Ex) =
      [x.lt * Fintype.card E ^ (x.lt - 1)] ++ tailCounts (Fintype.card E) x :=
  own_errs A.toOwn x (tailIs h) (Fintype.card E)
    (by
      show A.gT * Fintype.card E ^ (A.gT - 1) = _
      rw [hT]) (tailErrs h) Ex

theorem layVO_counts (A : LayVO E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (h : SizesV A.V x) (c : Nat) (Ex : ExtSpec) :
    List.Forall₂ (CountIs (Fintype.card E)) (TWhole.errList (A.toOwn.ch.eps Ex)) (ownRatios c x) :=
  own_counts A.toOwn x hx h.hf (tailIs h) (Fintype.card E)
    (by
      show A.gT * Fintype.card E ^ (A.gT - 1) = _
      rw [hT]) (tailErrs h) c Ex

/-! ### The whole, for the first sub-proof -/

theorem layVOF_shape (A : LayVOF E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls) (h : SizesVF A.V x) (w : Nat)
    (Ex : ExtSpec) : ShapeIs E (A.toOwn.ch.R Ex).shape (ownList w x) :=
  ownFirst_shape A.toOwn x hx h.hf hT hA hB (tailIsF h) w Ex

theorem layVOF_planned (A : LayVOF E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls) (h : SizesVF A.V x) (Ex : ExtSpec)
    (s : Setting) (p q : PlanState) (hp : At s 0 p) (hq : planLayerOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (A.toOwn.ch.R Ex).shape (l.map (·.entry)) :=
  ownFirst_planned A.toOwn x hx h.hf hT hA hB (tailIsF h) Ex s p q hp hq

/-- The chain's errors, written out. -/
theorem layVOF_errs (A : LayVOF E M X) (x : LayerRounds) (hT : A.gT = x.lt)
    (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls) (h : SizesVF A.V x) (Ex : ExtSpec) :
    TWhole.errList (A.toOwn.ch.eps Ex) = [x.lt * Fintype.card E ^ (x.lt - 1)] ++
      ([(x.ls + x.lt) * Fintype.card E ^ (x.ls + x.lt - 1)] ++
        ([(x.lPd - x.ls) * Fintype.card E ^ (x.lPd - x.ls - 1)] ++
          tailCounts (Fintype.card E) x)) :=
  ownFirst_errs A.toOwn x (tailIsF h) (Fintype.card E)
    (by
      show A.gT * Fintype.card E ^ (A.gT - 1) = _
      rw [hT])
    (by
      show A.gA * Fintype.card E ^ (A.gA - 1) = _
      rw [hA])
    (by
      show A.gB * Fintype.card E ^ (A.gB - 1) = _
      rw [hB]) (tailErrsF h) Ex

theorem layVOF_counts (A : LayVOF E M X) (x : LayerRounds) (hx : Full x) (hT : A.gT = x.lt)
    (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls) (h : SizesVF A.V x) (c : Nat)
    (Ex : ExtSpec) :
    List.Forall₂ (CountIs (Fintype.card E)) (TWhole.errList (A.toOwn.ch.eps Ex)) (ownRatios c x) :=
  ownFirst_counts A.toOwn x hx h.hf (tailIsF h) (Fintype.card E)
    (by
      show A.gT * Fintype.card E ^ (A.gT - 1) = _
      rw [hT])
    (by
      show A.gA * Fintype.card E ^ (A.gA - 1) = _
      rw [hA])
    (by
      show A.gB * Fintype.card E ^ (A.gB - 1) = _
      rw [hB]) (tailErrsF h) c Ex

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.tailIs
#print axioms OnBytes.Tie.Pv.Lay.tailErrs
#print axioms OnBytes.Tie.Pv.Lay.tailIsF
#print axioms OnBytes.Tie.Pv.Lay.tailErrsF
#print axioms OnBytes.Tie.Pv.Lay.layVO_shape
#print axioms OnBytes.Tie.Pv.Lay.layVO_planned
#print axioms OnBytes.Tie.Pv.Lay.layVO_errs
#print axioms OnBytes.Tie.Pv.Lay.layVO_counts
#print axioms OnBytes.Tie.Pv.Lay.layVOF_errs
#print axioms OnBytes.Tie.Pv.Lay.layVOF_shape
#print axioms OnBytes.Tie.Pv.Lay.layVOF_planned
#print axioms OnBytes.Tie.Pv.Lay.layVOF_counts
