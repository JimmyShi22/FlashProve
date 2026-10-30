-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RowReturns.lean: the text that makes a sub-proof's pending row on the
committed table RETURNS: from one test with code on the planner's numbers, the sizes of the claims,
and an entry of the index masks' ledger. Definitions with code, and theorems with their proofs.

Why. The table of joints ties the public item `hasRow m` to the open item "wo m": the sub-protocol
that opens "wo" must show that, behind its accepting step, the verifier's state holds a pending row.
The text of that row (`pendingRowO`, Johnson/Desc/First/Pend/Row.lean) can refuse at some twenty
places. Whether it does hangs on sizes and on the units' numbers alone
(OnBytes/Flat/PendingSizes.lean: `wsPending_alike`): so it can be asked ONCE, at claims of zeros.

Main names:
  `skelFac`, `skelClaim`, `skelRec`, `skelOut`: a factor, a claim, what is left of it, and a value
    of the merge, all of zeros, with the sizes that the layout's unit asks for.
  `pendB lay uis claims S`: THE TEST, ON THE PLANNER's NUMBERS ALONE: the routine `wsPending`
    returns at the value of zeros with one claim on each of the units uis. IT CAN FAIL.
  `facSizes_onRows`, `all2_onRows`, `recSizes_rowPart`: what is left of a claim that has passed the
    program's test on its sizes (`wsClaimShape`) has the sizes of what is left of the claim of zeros
    on its unit.
  `isOk_merged`: of the merged part, whether the routine returns hangs on the number of the point's
    coordinates alone.
  `wsPending_returns`: THE ROUTINE RETURNS: general in the list of claims.
  `hasRow_of_returns`: so the verifier's state holds a pending row, where the index masks' ledger
    has an entry to give (by `pend_of`, PendRow.lean).
  `merge_makes_row`: THE MERGE's ACCEPTING STEP MAKES `hasRow` AT THE HEAD, at one claim: where
    `pendB` says yes at the unit of the claim that the state in front holds, and the ledger behind
    has an entry to give.

Limits. `pendB` has been evaluated nowhere. It builds a vector as long as the unit's last row's
number: at the full size some millions of entries a unit. In `merge_makes_row` it is asked at the
unit that the state's claim names: that this is the planner's unit for the head is not shown here;
asked at every unit of the layout it is a closed test. The entry of the ledger is a premise. Nothing
on soundness.

-/
import OnBytes.Flat.PendingSizes
import Johnson.Top.H0.MergeLaw.PendRow
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Top.H0.MergeLaw.ItemsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model OnBytes.Flat

/-- A factor of zeros with the sizes that a group asks for. -/
def skelFac (g : WsGrp) : WsFac :=
  if g.cls == 'E' then { HV := Array.replicate g.o zeroE, pt := Array.replicate g.z zeroE }
  else { AV := Array.replicate g.R zeroE }

/-- A claim of zeros on unit number ui, with the sizes that the unit's groups ask for. -/
def skelClaim (lay : WsLay) (ui : Nat) : WsClaim :=
  { ui := ui, f := ((lay.U[ui]?).map fun u => u.g.map skelFac).getD [] }

/-- What is left of that claim when the columns are bound. -/
def skelRec (lay : WsLay) (ui : Nat) : WsRecClaim := wsRowPart lay (skelClaim lay ui) zeroE

/-- How many members a filtering list has does not hang on what it keeps of each. -/
theorem length_filterMap_if {α β : Type} (c : α → Bool) (f f' : α → β) (l : List α) :
    (l.filterMap fun i => if c i then none else some (f i)).length =
      (l.filterMap fun i => if c i then none else some (f' i)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases c a <;> simp [ih]

/-- **Two factors that fit one group leave factors of the same sizes to the rows.** -/
theorem facSizes_onRows {x x' : WsFac} {g : WsGrp} (h : x.fits g = true) (h' : x'.fits g = true) :
    FacSizes (x.onRows g) (x'.onRows g) := by
  unfold WsFac.fits at h h'
  unfold WsFac.onRows FacSizes
  by_cases hE : (g.cls == 'E') = true
  · simp only [hE, if_true, Bool.and_eq_true, beq_iff_eq] at h h' ⊢
    refine ⟨by rw [h.1.1, h'.1.1], ?_, trivial⟩
    simp only [List.size_toArray]
    exact length_filterMap_if _ _ _ _
  · simp only [hE, Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq] at h h' ⊢
    by_cases hA : g.aTaken = true
    · simp only [hA, if_true]
      exact ⟨trivial, trivial, trivial⟩
    · simp only [hA, Bool.false_eq_true, if_false]
      exact ⟨trivial, trivial, by rw [h.1.1, h'.1.1]⟩

theorem skelFac_fits (g : WsGrp) : (skelFac g).fits g = true := by
  unfold skelFac WsFac.fits
  by_cases hE : (g.cls == 'E') = true
  · simp [hE]
  · simp [hE]

/-- Member by member: two lists of factors that fit one list of groups. -/
theorem all2_onRows : ∀ {f f' : List WsFac} {g : List WsGrp}, f.length = g.length →
    f'.length = g.length → ((f.zip g).all fun y => y.1.fits y.2) = true →
    ((f'.zip g).all fun y => y.1.fits y.2) = true →
    All2 FacSizes ((f.zip g).map fun y => y.1.onRows y.2) ((f'.zip g).map fun y => y.1.onRows y.2)
  | [], [], [], _, _, _, _ => .nil
  | x :: f, x' :: f', g₀ :: g, h1, h2, h3, h4 => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, List.map_cons] at h3 h4 ⊢
    exact .cons (facSizes_onRows h3.1 h4.1)
      (all2_onRows (by simpa using h1) (by simpa using h2) h3.2 h4.2)
  | [], _ :: _, [], _, h2, _, _ => by simp at h2
  | _ :: _, _, [], h1, _, _, _ => by simp at h1
  | [], _, _ :: _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _ :: _, _, h2, _, _ => by simp at h2

/-- **What is left of a claim that has passed the test on its sizes has the sizes of what is left of
the claim of zeros on its unit.** -/
theorem recSizes_rowPart {lay : WsLay} {c : WsClaim} (h : wsClaimShape lay c = .ok ()) (ka : E) :
    RecSizes (wsRowPart lay c ka) (skelRec lay c.ui) := by
  unfold wsClaimShape at h
  unfold skelRec wsRowPart skelClaim
  cases hu : lay.U[c.ui]? with
  | none => simp [hu, throw, throwThe, MonadExceptOf.throw] at h
  | some u =>
    simp only [hu] at h ⊢
    by_cases hc : (c.f.length == u.g.length && ((c.f.zip u.g).all fun y => y.1.fits y.2)) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨rfl, ?_⟩
      simp only [Option.map_some, Option.getD_some]
      refine all2_onRows hc.1 (by simp) hc.2 ?_
      rw [List.all_eq_true]
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
      simp only [List.getElem_zip, List.getElem_map]
      exact skelFac_fits _
    · simp [hc, throw, throwThe, MonadExceptOf.throw] at h

/-- A value of the merge made of zeros: a point of lk coordinates, and what is left of the claims.
-/
def skelOut (lk : Nat) (sk : List WsRecClaim) : WsForkOut :=
  { rm := Array.replicate lk zeroE, recs := sk }

/-- **A TEST WITH CODE ON THE PLANNER's NUMBERS ALONE**: the routine that makes the pending
row returns at the value of zeros with one claim on each of the units uis. -/
def pendB (lay : WsLay) (uis : List Nat) (claims : Nat) (S : Params.LinShape) : Bool :=
  (wsPending lay (skelOut lay.lk (uis.map (skelRec lay))) claims S).isOk

/-- Whether the routine returns hangs, of the merged part, on the number of the point's coordinates
alone. -/
theorem isOk_merged (lay : WsLay) {o o' : WsForkOut} (h1 : o.recs = o'.recs)
    (h2 : o.rm.size = o'.rm.size) (claims : Nat) (S : Params.LinShape) :
    (wsPending lay o claims S).isOk = (wsPending lay o' claims S).isOk := by
  unfold wsPending
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [h1, h2]
  repeat (first | rfl | split)

/-- **THE ROUTINE RETURNS**, where what is left of the claims has the sizes of the claims of zeros
on the units uis, the point has lk coordinates, and the test on the planner's numbers says yes. -/
theorem wsPending_returns (lay : WsLay) {o : WsForkOut} {uis : List Nat}
    (hr : All2 RecSizes o.recs (uis.map (skelRec lay))) (hrm : o.rm.size = lay.lk) (claims : Nat)
    (S : Params.LinShape) (hB : pendB lay uis claims S = true) :
    ∃ w, wsPending lay o claims S = .ok w := by
  have A := wsPending_alike lay (o := o) (o' := { o with recs := uis.map (skelRec lay) }) rfl hr
    claims S
  have B : (wsPending lay { o with recs := uis.map (skelRec lay) } claims S).isOk = true :=
    (isOk_merged lay (o := { o with recs := uis.map (skelRec lay) })
      (o' := skelOut lay.lk (uis.map (skelRec lay))) rfl
      (by show o.rm.size = (Array.replicate lay.lk zeroE).size; rw [hrm, Array.size_replicate])
      claims S).trans hB
  cases h' : wsPending lay { o with recs := uis.map (skelRec lay) } claims S with
  | error e => simp [h', Except.isOk, Except.toBool] at B
  | ok p' =>
    rw [h'] at A
    cases h : wsPending lay o claims S with
    | error e => rw [h] at A; exact A.elim
    | ok p => exact ⟨p, rfl⟩

/-- **So the verifier's state holds a pending row**: where it holds what a merge has left, the
routine returns at that, and the index masks' ledger has an entry to give. -/
theorem hasRow_of_returns {lay : WsLay} {n : Nat} {lin : Params.LinShape} {s : S} {wo : WsForkOut}
    {w : WsPending} (hl : Johnson.Desc.First.Walk.Law.leftOf s = some wo)
    (hw : wsPending lay wo n lin = .ok w) (he : ∃ c, EntryAt s c) :
    Johnson.Desc.First.Walk.Law.hasRow lay n lin s = true := by
  obtain ⟨c, l, l', e1, e2⟩ := he
  unfold Johnson.Desc.First.Walk.Law.hasRow
  rw [Option.isSome_iff_exists]
  exact ⟨_, Johnson.Desc.First.Walk.Law.rowBy_some.2 ⟨wo, _, hl, pend_of hw e1 e2⟩⟩

open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide) in
/-- **THE MERGE's ACCEPTING STEP MAKES THE PENDING ROW's TEXT RETURN**: behind it the verifier's
state holds a pending row, at one claim: where the test on the planner's numbers says yes at the
unit of the claim that the state in front holds, and the index masks' ledger behind has an entry to
give. -/
theorem merge_makes_row (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (lin : Params.LinShape)
    (hB : ∀ a claim, s.here = .head a → a.claim = some claim → pendB P.lay [claim.ui] 1 lin = true)
    (he : ∃ c, EntryAt s' c) : Johnson.Desc.First.Walk.Law.hasRow P.lay 1 lin s' = true := by
  obtain ⟨a, a', tp, F, claim, x, wo, ha, ha', hcl, _, hwo, _, hm, _⟩ := decide_inv h
  obtain ⟨x₁, _, _, _, _, _, _, _, _, _, qs, hq, _, _, _, _, _, _, hrm, _, _, _, _, _, hrecs, _⟩ :=
    mergeHear_inv hm
  have hsz : wo.rm.size = P.lay.lk := by
    have := congrArg List.length hrm
    simpa [hq] using this
  have ez : (#[claim].zip (OnBytes.Model.powers x₁ (#[x.sV] : Array Nat).size)).toList =
      [(claim, oneE)] := by
    simp [OnBytes.Model.powers, OnBytes.Model.powersLoop]
  have hr : All2 RecSizes wo.recs ([claim.ui].map (skelRec P.lay)) := by
    rw [hrecs, ez]
    exact .cons (recSizes_rowPart (shape_of_yes h a claim ha hcl) _) .nil
  obtain ⟨w, hw⟩ := wsPending_returns P.lay hr hsz 1 lin (hB a claim ha hcl)
  refine hasRow_of_returns (wo := wo) (Johnson.Desc.First.Walk.Law.leftOf_of_head ?_) hw he
  unfold VerifiableInference.Desc.First.Close.leftHead
  rw [ha']
  exact hwo

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_makes_row
#print axioms VerifiableInference.Desc.First.MergeLaw.wsPending_returns
#print axioms VerifiableInference.Desc.First.MergeLaw.hasRow_of_returns
#print axioms VerifiableInference.Desc.First.MergeLaw.recSizes_rowPart
#print axioms VerifiableInference.Desc.First.MergeLaw.facSizes_onRows
#print axioms VerifiableInference.Desc.First.MergeLaw.skelFac_fits
