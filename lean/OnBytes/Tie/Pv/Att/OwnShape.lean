-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/OwnShape.lean: the chain of an attention sub-proof's own rounds
(Cb/Pv/Att/Own.lean) has as many rounds as the port's planAttentionOwn writes, in the same order,
each with the entry's numbers of scalars and of drawn elements; and its errors are the numerators of
the bounds that the planner hands to close, but for one place.

Main names:
  fit_comap: a chain read through a map of statements fits the same entries.
  SumFits S x b: the letters S of one sumcheck have the numbers of the record x : PscSize
    (PlainSc.Fits), and its further scalars fill b bytes.
  OwnFits A x: the letters A have the numbers of the record x : AttentionRounds, stage by stage:
    each score unit is a sumcheck of the size attentionSc3 of its pair of numbers, with 7 further
    scalars, and the first with 3 more for each plane message; then the sizes and further scalars of
    the six other sumchecks; the point has 2 lgk + 2 lt + 4 coordinates; there are x.pairs pairs.
  own_fit: under OwnFits the list attList w x (OnBytes/Tie/Pv/Att/PlanOwn.lean) fits the chain A.ch.
  own_planned: so for every setting, every record and every state of the planner in a request's
    scope without open bytes, roots or answers (At, OnBytes/Tie/Pv/Att/PlanCalc.lean): if
    planAttentionOwn x ends well, the shape of the reduction A.ch.R Ex is an instance of the entries
    of the rounds that it has added (ShapeIs).
  own_nums: the chain's errors, as a list of numbers, are the numerators of the plan's bounds, round
    by round, but for one place: at the draw of the point the chain has its count eZ of bad points
    among all points, where the plan has the numerator 2 lgk + 2 lt + 4 over cardE. numsZ z x is the
    list attNums x with z at that place, and numsZ_att says so.
  zero_ratio: the two numbers at that place are one ratio if eZ is v * q ^ (v - 1), for v
    coordinates, at least one, and q elements: v * q ^ (v - 1) of the q ^ v points are v of q.

Limits: as in OnBytes/Tie/Pv/Att/Shape.lean: ShapeIs counts. OwnFits is a condition on numbers
alone: it does not say that the letters are the programs' maps, weights and claims. That eZ is v * q
^ (v - 1) at a value, and that the setting's cardE is the number q of elements of E, is not said
here. "The plan's bounds" are the bounds that the planner hands to close (attBounds,
OnBytes/Tie/Pv/Att/PlanOwnW.lean); close counts them once for each instance and rounds; nothing here
says that the factor is 1.
-/
import OnBytes.Tie.Pv.Att.ChainShape
import OnBytes.Tie.Pv.Att.ScdJoin
import Cb.Pv.Att.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att Cb.Pv.Lay TWhole Johnson.L5.Layers OnBytes OnBytes.G4 OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan

variable {E : Type} [Field E] [Fintype E] {M : Type}

theorem fit_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X) (ds : List Fmt.Entry),
    Fit c ds → Fit (c.comap f) ds
  | _, .done _, _, _, _, h => h
  | _, .ride _ _ _ _ _ _ _ next, _, _, _, h => by
    obtain ⟨w, k, deg, DY, ds', hf, hd, hn⟩ := h
    exact ⟨w, k, deg, DY, ds', hf, hd, fit_comap next _ ds' hn⟩
  | _, .draw _ _ _ next, _, _, _, h => by
    obtain ⟨e, ds', q, h0, hz, hd, hn⟩ := h
    exact ⟨e, ds', q, h0, hz, hd, fit_comap next _ ds' hn⟩
  | _, .send _ _ _ _ _ next, _, _, _, h => by
    obtain ⟨e, ds', q, h0, hz, hd, hn⟩ := h
    exact ⟨e, ds', q, h0, hz, hd, fit_comap next _ ds' hn⟩

/-- The letters of one sumcheck have the record's numbers; its further scalars fill b bytes. -/
structure SumFits {X : Type} (S : SumL E M X) (x : PscSize) (b : ℕ) : Prop where
  fits : S.T.Fits x
  bytes : b = 24 * S.n

theorem fit_stage {X : Type} (S : SumL E M X) (x : PscSize) (b : ℕ) (h : SumFits S x b) (w : ℕ)
    (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) (ds : List Fmt.Entry) (hn : Fit next ds) :
    Fit (S.stage Ow next) (lPsc w b x ++ ds) := by
  rw [h.bytes]
  exact fit_plain S.T x h.fits w S.n S.T.fix S.cl S.msg S.L Ow next ds hn

/-- The score units have the numbers of the record's list; b bytes are open before the first. -/
def UnitsFit {X : Type} : List (SumL E M X) → List (ℕ × ℕ) → ℕ → Prop
  | [], [], _ => True
  | u :: us, p :: ps, b => SumFits u (attentionSc3 p.1 p.2) (b + 24 * 7) ∧ UnitsFit us ps 0
  | _, _, _ => False

/-- The letters have the numbers of the record. -/
structure OwnFits {X : Type} (A : AttOwn E M X) (x : AttentionRounds) : Prop where
  units : UnitsFit A.units x.score (planeBytes x)
  sE : SumFits A.tail.sE (attentionSc3 x.e x.pairs)
    (leftOpen (planeBytes x) x.score + 24 * (5 + x.lt + 2))
  sVM : SumFits A.tail.sVM (attentionSc3 x.valueM x.pairs) (24 * 2)
  sVD : SumFits A.tail.sVD (attentionSc3 x.valueD x.pairs) 0
  nz : A.tail.nz = 2 * x.lgk + 2 * x.lt + 4
  np : A.tail.np = x.pairs
  sF : SumFits A.tail.sF (attentionSc3 x.attained x.pairs) 0
  sD : SumFits A.tail.sD (attentionScd x.lt x.lgk x.pairs x.Lam) 0
  sH : SumFits A.tail.sH (attentionSc3 x.bits x.pairs) 0

theorem fit_units {X : Type} (w : ℕ) (tail : Ch E M (Seen E X)) (ds : List Fmt.Entry)
    (ht : Fit tail ds) :
    ∀ (us : List (SumL E M (Seen E X))) (ps : List (ℕ × ℕ)) (b : ℕ), UnitsFit us ps b →
      ∀ {X' : Type} (pr : X' → Seen E X), Fit (unitsCh us pr tail) (unitsL w b ps ++ ds)
  | [], [], _, _, _, pr => fit_comap tail pr ds ht
  | u :: us, p :: ps, b, h, _, pr => by
    show Fit (Ch.ride u.T.our.par u.n u.T.fix _ u.msg _ _ (unitsCh us _ tail))
      (lPsc w (b + 24 * 7) (attentionSc3 p.1 p.2) ++ unitsL w 0 ps ++ ds)
    rw [List.append_assoc, h.1.bytes]
    exact fit_plain u.T _ h.1.fits w u.n u.T.fix _ u.msg _ _ _ _
      (fit_units w tail ds ht us ps 0 h.2 _)
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim

/-- The eleven stages behind the score units. -/
theorem fit_tail {X : Type} (A : AttOwn E M X) (x : AttentionRounds) (h : OwnFits A x) (w : ℕ) :
    Fit A.tail.ch (aE w x ++ (batV w x ++ (aVM w x ++ (aVD w x ++ (zeroFH w x ++ (batF w x ++
      (aF w x ++ (batD w x ++ (aD w x ++ (batH w x ++ (aH w x ++ []))))))))))) := by
  have hH : Fit A.tail.chH (batH w x ++ (aH w x ++ [])) :=
    fit_bat w x.pairs _ _ _ _ (fit_stage A.tail.sH _ 0 h.sH w _ _ [] (fit_done _))
  have hD : Fit A.tail.chD (batD w x ++ (aD w x ++ (batH w x ++ (aH w x ++ [])))) :=
    fit_bat w x.pairs _ _ _ _ (fit_stage A.tail.sD _ 0 h.sD w _ _ _ hH)
  have hF : Fit A.tail.chF (batF w x ++ (aF w x ++ (batD w x ++ (aD w x ++ (batH w x ++
      (aH w x ++ [])))))) := by
    show Fit _ (eBat w (24 * x.pairs) x.pairs :: _)
    rw [← h.np]
    exact fit_batSend w A.tail.np A.tail.np _ _ _ _ _ (fit_stage A.tail.sF _ 0 h.sF w _ _ _ hD)
  have hZ : Fit A.tail.chZ (zeroFH w x ++ (batF w x ++ (aF w x ++ (batD w x ++ (aD w x ++
      (batH w x ++ (aH w x ++ []))))))) := by
    show Fit _ (eDraw "ZERO" w 0 (2 * x.lgk + 2 * x.lt + 4) :: _)
    rw [← h.nz]
    exact fit_zero w A.tail.nz _ _ _ _ hF
  exact fit_stage A.tail.sE _ _ h.sE w _ _ _
    (fit_bat w 2 _ _ _ _ (fit_stage A.tail.sVM _ _ h.sVM w _ _ _
      (fit_stage A.tail.sVD _ 0 h.sVD w _ _ _ hZ)))

/-- The plan's list fits the chain. -/
theorem own_fit {X : Type} (A : AttOwn E M X) (x : AttentionRounds) (h : OwnFits A x) (w : ℕ) :
    Fit A.ch (attList w x) := by
  have e : attList w x = unitsL w (planeBytes x) x.score ++ (aE w x ++ (batV w x ++ (aVM w x ++
      (aVD w x ++ (zeroFH w x ++ (batF w x ++ (aF w x ++ (batD w x ++ (aD w x ++ (batH w x ++
        (aH w x ++ []))))))))))) := by
    simp only [attList, scoreL, List.append_assoc, List.append_nil]
  rw [e]
  exact fit_units w A.tail.ch _ (fit_tail A x h w) A.units x.score (planeBytes x) h.units _

/-- The chain's shape has the three numbers of each entry that planAttentionOwn adds. -/
theorem own_planned {X : Type} (A : AttOwn E M X) (x : AttentionRounds) (h : OwnFits A x)
    (Ex : ExtSpec) (s : Setting) (p q : PlanState) (hp : At s 0 p)
    (hq : planAttentionOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (A.ch.R Ex).shape (l.map (·.entry)) :=
  Ch.planned Ex A.ch _ (own_fit A x h _) s 0 0 _ (att_adds s x) p q hp hq

/-! ### The errors -/

/-- The numerators of a sumcheck's bounds. -/
abbrev nP (x : PscSize) : List ℕ := numsOf (qPsc 0 x)

/-- attNums x with z at the place of the draw of the point. -/
def numsZ (z : ℕ) (x : AttentionRounds) : List ℕ :=
  numsOf (x.score.map fun u => qPsc 0 (attentionSc3 u.1 u.2)).flatten ++
    (nP (attentionSc3 x.e x.pairs) ++ ([1] ++ (nP (attentionSc3 x.valueM x.pairs) ++
      (nP (attentionSc3 x.valueD x.pairs) ++ ([z] ++ ([x.pairs - 1] ++
        (nP (attentionSc3 x.attained x.pairs) ++ ([x.pairs - 1] ++
          (nP (attentionScd x.lt x.lgk x.pairs x.Lam) ++ ([x.pairs - 1] ++
            (nP (attentionSc3 x.bits x.pairs) ++ [])))))))))))

theorem numsZ_att (x : AttentionRounds) : numsZ (2 * x.lgk + 2 * x.lt + 4) x = attNums x := by
  simp [numsZ, attNums, attRatios, numsOf]

theorem sum_nums {X : Type} (S : SumL E M X) (x : PscSize) (b : ℕ) (h : SumFits S x b) :
    S.nums = nP x := by
  show 1 :: (List.ofFn S.T.deg ++ [S.T.DY] ++ [0]) = numsOf (qPsc 0 x)
  rw [nums_psc, h.fits.degs, h.fits.degY, h.fits.withY]
  simp

theorem units_nums {X : Type} : ∀ (us : List (SumL E M X)) (ps : List (ℕ × ℕ)) (b : ℕ),
    UnitsFit us ps b → (us.map SumL.nums).flatten =
      numsOf (ps.map fun u => qPsc 0 (attentionSc3 u.1 u.2)).flatten
  | [], [], _, _ => rfl
  | u :: us, p :: ps, b, h => by
    simp only [List.map_cons, List.flatten_cons, numsOf_append]
    rw [units_nums us ps 0 h.2, sum_nums u _ _ h.1]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- The chain's errors are the numerators of the plan's bounds, with eZ at the draw of the point. -/
theorem own_nums {X : Type} (A : AttOwn E M X) (x : AttentionRounds) (h : OwnFits A x)
    (Ex : ExtSpec) : errList (A.ch.eps Ex) = numsZ A.tail.eZ x := by
  rw [attOwn_nums, units_nums A.units x.score _ h.units]
  unfold Tail.nums numsZ
  rw [sum_nums _ _ _ h.sE, sum_nums _ _ _ h.sVM, sum_nums _ _ _ h.sVD, sum_nums _ _ _ h.sF,
    sum_nums _ _ _ h.sD, sum_nums _ _ _ h.sH, h.np]

/-- The count v * q ^ (v - 1) among the q ^ v points is the ratio v over q. -/
theorem zero_ratio (v q : ℕ) (hv : 1 ≤ v) : v * q ^ (v - 1) * q = v * q ^ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
  rw [Nat.succ_sub_one, Nat.mul_assoc, ← pow_succ]

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.numsZ_att
#print axioms OnBytes.Tie.Pv.Att.own_nums
#print axioms OnBytes.Tie.Pv.Att.zero_ratio
#print axioms OnBytes.Tie.Pv.Att.fit_comap
#print axioms OnBytes.Tie.Pv.Att.own_fit
#print axioms OnBytes.Tie.Pv.Att.own_planned
