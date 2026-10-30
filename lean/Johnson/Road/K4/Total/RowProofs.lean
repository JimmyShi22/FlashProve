-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RowProofs.lean: TWO SENTENCES OF Johnson/Road/K4/Total/RowReturns.lean,
PROVED: PendSkel (at two leavings of the merge of one skeleton the routine wsPending returns
at both or at neither) and RowReturn (the law: of a leaving w of w₀'s skeleton, where wsPending
returns at w₀ and the statement's ledger has an entry to take, the pending row can be made).
Statements and proofs.

THE ROAD. wsPending_alike (OnBytes/Flat/PendingSizes.lean) says PendSkel's end of two
leavings WITH ONE MERGED PART (point, factor, shown value: drawn and sent elements) whose rests are
alike. Here the merged part is freed in a second step: of it the routine's return reads the point's
length alone (pending_merged). From w to w₀ by way of the leaving with w's merged part and w₀'s
rests.

  `pending_merged`: at two leavings with the same rests and points of one length.
  `isSome_of_alike`: two results that are alike are both there or both not.
  `pend_skel : PendSkel`, `row_return : RowReturn`: the sentences.
New: pending_merged (the text unfolded). The rest: wsPending_alike; pend_of
(Johnson/Top/H0/MergeLaw/PendRow.lean).
**Limits.** row_return HAS THREE PREMISES, as the sentence has them, and pays none: RowSkel w w₀
(payer at K4: the sentence HearRowSkel); THE MEMBER: wsPending returns at w₀: that it returns
anywhere is said by no theorem here, and no run is cited here; roomB: on the state's statement: no
invariant of the chain (see RoomFor.lean). It says that the row can be made, not what it says.
Nothing on soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no
member.


-/
import Johnson.Road.K4.Total.RowReturns
import Johnson.Top.H0.MergeLaw.PendRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Params (LinShape)
open OnBytes.Flat (All2 RecSizes PendAlike wsPending_alike)
open VerifiableInference.Desc.First.Pend (pendingRowO takeEntry)
open VerifiableInference.Desc.First.MergeLaw (pend_of)

/-- Of the merged part the return of the routine wsPending reads the point's length alone. -/
theorem pending_merged (lay : WsLay) {o o' : WsForkOut} (hr : o.recs = o'.recs)
    (hs : o.rm.size = o'.rm.size) (n : Nat) (S : LinShape) :
    (wsPending lay o n S).toOption.isSome = (wsPending lay o' n S).toOption.isSome := by
  unfold wsPending
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [hr, hs]
  split
  · rfl
  · split
    · rfl
    · cases wsSpan lay o'.recs with
      | error _ => rfl
      | ok fl =>
        obtain ⟨first, last⟩ := fl
        simp only []
        split
        · rfl
        · cases List.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate last zeroE)
              o'.recs with
          | error _ => rfl
          | ok Gam =>
            simp only []
            cases memberWeightsOnRows S first (Gam.extract first last) <;> rfl

/-- Two results that are alike are both there or both not. -/
theorem isSome_of_alike {x y : Except String WsPending} (h : PendAlike x y) :
    x.toOption.isSome = y.toOption.isSome := by
  cases x <;> cases y <;> first | rfl | exact h.elim

/-- **The sentence PendSkel.** -/
theorem pend_skel : PendSkel := by
  intro lay n lin w w₀ S
  have h1 := isSome_of_alike (wsPending_alike lay (o := w) (o' := ⟨w.toWsMerged, w₀.recs⟩) rfl
    S.recs n lin)
  exact h1.trans (pending_merged lay (o := ⟨w.toWsMerged, w₀.recs⟩) (o' := w₀) rfl S.rm n lin)

/-- **The sentence RowReturn.** -/
theorem row_return : RowReturn := by
  intro lay im n lin os w w₀ S hm hroom
  have h1 : (wsPending lay w n lin).toOption.isSome = true := (pend_skel lay n lin w w₀ S).trans hm
  cases hw : wsPending lay w n lin with
  | error e =>
    rw [hw] at h1
    cases h1
  | ok p =>
    unfold roomB at hroom
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hroom
    obtain ⟨l, hl, ht⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨c, l'⟩ := x
    exact ⟨_, pend_of hw hl ht⟩

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.pending_merged
#print axioms OnBytes.Desc.First.K4.Total.isSome_of_alike
#print axioms OnBytes.Desc.First.K4.Total.pend_skel
#print axioms OnBytes.Desc.First.K4.Total.row_return
