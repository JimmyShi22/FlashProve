-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsFormsZero.lean: the norms' stage of the layers' own rounds: the forms'
half: that every form of the per-position bridge's list is worth 0, from K4's own list of claims.

The per-position bridge of a norm (OnBytes/Desc/First/NormBridge/BridgeWorld.lean, `bridge_world`)
speaks of a run in letters (`Run`) and asks five groups of premises. One of them, `Run.FormsZero`,
says that each of 5 + 21 NI forms is worth 0 in the world. Here that group is paid for K4: if every
form of the list that `formsFrontWith` returns is worth 0, and the run's letters are K4's
(`FormsTie`), then `Run.FormsZero` holds.

  `XSof`, `digitsOr`: the caller's forms, as functions of what was heard: the streams' batch through
      its read; digit n of norm i through the read at a named point.
  `FormsTie`: thirteen equations between the letters of a run and K4's record of what was heard.
  `normsForms_shape`: group 2 is a list of three forms, the first two as written.
  `formsZero_of_front`: the law.

Limits. It says of no form that it IS worth 0: that is a premise here (the link's one equation). Two
of the ties (rowS, sR) are facts on the hearing of the squares' product layer, and are premises
here. No draw, no soundness.
-/
import OnBytes.Desc.First.NormBridge.BridgeWorld
import OnBytes.Desc.First.K4.ClaimsLaws
import Johnson.Road.K4.Says2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open Finset
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

/-- The caller's form for the streams' batch at the squares' end point: the slot of the end value
less the third claim of group 2. -/
def XSof (P : Pub) (v : Env) (H : Heard) : Aff :=
  match normsForms P v H with
  | some [_, _, f] => Aff.slot H.wpl.sL - f
  | _ => {}

/-- Digit n of norm i through the read at the point named Pn; the empty form where there is none. -/
def digitsOr (v : Env) (Pn : String) (i n : Nat) : Aff := ((digitsAt v Pn i).getD fun _ => {}) n

/-- The letters of a run are K4's. sh: the 4 NI end values of the row products' sumcheck as
shown. -/
structure FormsTie (R : D6.Bridge.Run) (P : Pub) (o : Own) (sh : Array E) : Prop where
  sW : R.sW = o.H.sW
  sL : R.sL = o.H.wpl.sL
  sR : o.H.wpl.sR = o.H.wpl.sL + 1
  rowS : R.S.p.rowForm R.S.S0 {} = o.H.wpl.row
  XS : R.XS = XSof P o.v o.H
  sPv : R.sPv = o.H.sPv
  sCl : R.sCl = o.H.tV.sCl
  rowP : R.Pr.p.rowForm R.Pr.S0 {} = o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {}
  sE : R.sE = o.H.tV.sEnd
  D : R.D = digitsOr o.v "P_V"
  D' : R.D' = digitsOr o.v "r_tV"
  eps : R.eps = epsOf o.v.y
  two : R.two = twoM o.v

theorem normsForms_shape {P : Pub} {v : Env} {H : Heard} {l : List Aff}
    (h : normsForms P v H = some l) :
    ∃ f, l = [H.wpl.row, Aff.slot H.wpl.sL - Aff.slot H.wpl.sR, f] := by
  unfold normsForms at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨_, (Option.some.inj h).symm⟩

variable {K : Type} [Field K] (ρ : Reading K) (W : World K) (c : D6.Bridge.Data K)

theorem formsZero_of_front (hρ : Road.Numerals ρ) {rows : Bool} {P : Pub} {g : Nat} {o : Own}
    {F G : Fork} {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value ρ W = 0) {sh : Array E}
    (hsh : ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh)
    {R : D6.Bridge.Run} (T : FormsTie R P o sh) (hy : P.y = o.v.y) (hNI : c.NI = o.v.y.NI)
    (hxl : ledNP P.y.h.xl = 7)
    (hom : ∀ m, m < 7 * c.NI → ρ.val (o.H.omV.getD m zeroE) = ρ.val R.om ^ m) :
    R.FormsZero ρ c W := by
  obtain ⟨sh', pp, l, _, _, a1, _, a3, a4, _, _, _⟩ := formsFrontWith_some h
  rw [hsh] at a1
  cases a1
  have hzl : ∀ f ∈ l, f.value ρ W = 0 := fun f hf => hz f (by rw [a4]; simpa using hf)
  obtain ⟨m2, mB, mV, m46, _, _, _, _, _, _⟩ := mem_front a3
  obtain ⟨g2, g46, _, _, _, _, _, b1, b2, _, _, _, _, _, _⟩ := front_some a3
  obtain ⟨f3, e2⟩ := normsForms_shape b1
  subst e2
  have z46 : ∀ f ∈ g46, f.value ρ W = 0 := fun f hf => hzl f (m46 g46 b2 f hf)
  have hXS : R.XS = Aff.slot o.H.wpl.sL - f3 := by
    rw [T.XS]
    unfold XSof
    rw [b1]
  have dP : ∀ i, i < c.NI → ∃ Dr Dp, digitsAt o.v "r_tV" i = some Dr ∧
      digitsAt o.v "P_V" i = some Dp ∧ R.D' i = Dr ∧ R.D i = Dp := by
    intro i hi
    obtain ⟨Dr, Dp, h1, h2, _⟩ := rowsForms_mem b2 (by rw [← hNI]; exact hi)
    refine ⟨Dr, Dp, h1, h2, ?_, ?_⟩
    · rw [T.D']
      funext n
      unfold digitsOr
      rw [h1]
      rfl
    · rw [T.D]
      funext n
      unfold digitsOr
      rw [h2]
      rfl
  have sho : ∀ i, i < c.NI →
      W.slot (o.H.tV.sEnd + 4 * i + 0) = (P6.Row.ofDigits (R.D' i)).a.value ρ W ∧
      W.slot (o.H.tV.sEnd + 4 * i + 1) = (P6.Row.ofDigits (R.D' i)).b.value ρ W ∧
      W.slot (o.H.tV.sEnd + 4 * i + 2) = (P6.Row.ofDigits (R.D' i)).Rlo.value ρ W ∧
      W.slot (o.H.tV.sEnd + 4 * i + 3) = (P6.Row.ofDigits (R.D' i)).Rhi.value ρ W := by
    intro i hi
    obtain ⟨Dr, _, h1, _, e1, _⟩ := dP i hi
    rw [e1]
    exact Road.K4.shown_says b2 z46 (by rw [← hNI]; exact hi) h1
  refine
    { rowS := ?_, endsS := ?_, endS := ?_, batchP := ?_, rowP := ?_, endA := ?_, endB := ?_,
      endLo := ?_, endHi := ?_, carries := ?_, lines := ?_ }
  · rw [T.rowS]
    exact hzl _ (m2 _ b1 _ (by simp))
  · rw [T.sL, ← T.sR]
    exact hzl _ (m2 _ b1 _ (by simp))
  · have z3 := hzl _ (m2 _ b1 f3 (by simp))
    rw [hXS, T.sL, Aff.value_sub, Aff.value_sub, z3]
    ring
  · have e := Road.K4.rowBatch_says hρ P.y o.H (hzl _ mB)
    rw [T.sCl, e, hxl, hy, ← hNI, sub_eq_zero]
    refine sum_congr rfl fun m hm => ?_
    rw [hom m (mem_range.mp hm)]
    unfold D6.Bridge.Run.Pt
    rw [T.sPv]
  · rw [T.rowP]
    exact hzl _ mV
  · intro i hi
    rw [Aff.value_sub, Aff.value_slot, T.sE, ← Nat.add_assoc, (sho i hi).1, sub_self]
  · intro i hi
    rw [Aff.value_sub, Aff.value_slot, T.sE, ← Nat.add_assoc, (sho i hi).2.1, sub_self]
  · intro i hi
    rw [Aff.value_sub, Aff.value_slot, T.sE, ← Nat.add_assoc, (sho i hi).2.2.1, sub_self]
  · intro i hi
    rw [Aff.value_sub, Aff.value_slot, T.sE, ← Nat.add_assoc, (sho i hi).2.2.2, sub_self]
  · intro i hi f hf
    obtain ⟨Dr, Dp, h1, h2, _, mC, _⟩ := rowsForms_mem b2 (i := i) (by rw [← hNI]; exact hi)
    obtain ⟨_, Dp', _, h2', _, e2⟩ := dP i hi
    rw [h2] at h2'
    cases h2'
    rw [e2, T.sW] at hf
    have ef : (fun s => Aff.slot (o.H.sW + (9 * i + s))) = fun s => Aff.slot (o.H.sW + 9 * i + s) :=
      funext fun s => by rw [Nat.add_assoc]
    rw [ef] at hf
    exact z46 f (mC f hf)
  · intro i hi f hf
    obtain ⟨Dr, Dp, h1, h2, _, _, mL⟩ := rowsForms_mem b2 (i := i) (by rw [← hNI]; exact hi)
    obtain ⟨_, Dp', _, h2', _, e2⟩ := dP i hi
    rw [h2] at h2'
    cases h2'
    rw [e2, T.sPv, T.eps, T.two] at hf
    have ef : (fun n => Aff.slot (o.H.sPv + (7 * i + n))) =
        fun n => Aff.slot (o.H.sPv + 7 * i + n) := funext fun n => by rw [Nat.add_assoc]
    rw [ef] at hf
    exact z46 f (mL f hf)

#print axioms formsZero_of_front

end OnBytes.Desc.First.K4
