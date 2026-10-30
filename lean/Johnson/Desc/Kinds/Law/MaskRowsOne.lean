-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/MaskRowsOne.lean: TWO READERS OF THE MASK ROW OF THE OUTPUT HEAD'S SEGMENT,
OFF ONE WITNESS, ARE ONE: the second component of compCut (Johnson/Desc/Kinds/Law/K6Cut.lean)
and maskRowAt (Johnson/Desc/Sound/MaskRowAt.lean, which reads it through
the open segment's part of the verifier's state): WHERE THE STATE HOLDS THE MASK ROW'S SEAT.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  seatAt_wider: a message's seat in one list of seats is its seat in every list that holds it.
  MaskSeatAt arr N n rb s: a segment's part is open at s; its frame names the mask row's message; by
      its book that message sits at a seat of the segment's first sending that is in the segment's
      group; the seat's array has the number n; the message's rows have rb bits. (The fourth clause
      of RecordDue, Johnson/Desc/Kinds/Law/K6OpenedCut.lean, with the open part in front.)
  maskRows_one: under MaskSeatAt, and where the number n names one array of the group: the two
      readers agree below the plan's number of slots.

Every letter under "there is": MaskSeatAt: aK by K9.segAt?; o by K9L.maskOracle; x by K9.seatAt.
What it does not say. THAT ANY STATE MEETS MaskSeatAt. The list of members (msR) is ONE letter on
both sides: that two callers hand in the same list is theirs to show. Without an open part
maskRowAt is 0: then the equation is false in general. Nothing on soundness.
-/
import Johnson.Desc.Sound.MaskRowAt
import Johnson.Desc.Kinds.Law.DataMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)

/-- A seat in one list of seats is the seat in every list that holds it. -/
theorem seatAt_wider (own own' : List (Nat × Nat)) (book : OnBytes.TreeBook) (o : Nat)
    (x : Nat × Nat) (e : K9.seatAt own book o = some x) (hx : x ∈ own') :
    K9.seatAt own' book o = some x := by
  unfold K9.seatAt at e ⊢
  obtain ⟨y, hy, e2⟩ := Option.bind_eq_some_iff.1 e
  rw [hy]
  split at e2
  · obtain rfl := Option.some.inj e2
    show (if own'.contains y then some y else none) = some y
    rw [if_pos (by simpa using hx)]
  · cases e2

/-- **The state holds the mask row's seat.** -/
def MaskSeatAt (arr : Nat → Nat → Nat) (N : Numbers) (n rb : Nat) (s : S) : Prop :=
  ∃ (aK : K9.Part) (o : Nat) (x : Nat × Nat), K9.segAt? s = some aK ∧
    K9L.maskOracle aK.L.check.frame = some o ∧
    K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
    aK.d.st.rowBits o .mask = rb

/-- **THE TWO READERS OF THE MASK ROW ARE ONE.** -/
theorem maskRows_one {rows cols : Nat} {P Tok : Type} (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (sz : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (sz k).NM → Nat → Nat → Nat × Nat × Nat) (W : OnBytes.Model.Verify.Public)
    (n rb : Nat) (h1 : namedOnce arr N 24 n = true) (a : P × S)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hs : MaskSeatAt arr N n rb a.2) :
    ∀ j, j < W.H.ns → rd ((compCut cs arr msR N sz seat W (plAt n rb) w).2 j) =
      Sound.maskRowAt cs arr msR N 24 a w j := by
  obtain ⟨aK, o, x, hseg, ho, hx, hg, hn, hrb⟩ := hs
  intro j hj
  rw [Sound.maskRowAt_of_part cs arr msR N 24 a w j aK hseg,
    Came.mask_of_data cs arr msR N sz seat W (N.group 24) aK w o n x ho
      (seatAt_wider _ _ _ _ _ hx hg) hg hn h1 j hj, hrb]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.seatAt_wider
#print axioms VerifiableInference.Desc.Kinds.Head.Law.maskRows_one
