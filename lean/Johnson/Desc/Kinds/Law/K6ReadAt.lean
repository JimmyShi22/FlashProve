-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6ReadAt.lean: ONE SENTENCE ON THE READER OF A SEGMENT's MESSAGES
OFF THE TABLE's WITNESS (Johnson/Desc/Sound/ReadAt.lean: readAt), FOR K6's HALF OF (pin):
TWO WITNESSES THAT READ ALIKE THROUGH THE ONE ACCESSOR AT EVERY PINNED MEMBER, INSIDE ITS RANGES
(Law/K6Comp.lean: ReadAlike … ms), ARE READ ALIKE BY readAt, WHICH SEARCHES ITS OWN LIST msR, AT
EVERY PLACE THAT LIES INSIDE THE
RANGES OF THE SEGMENT's OWN COPY, WHERE THAT COPY IS A PINNED MEMBER: STATED AND PROVED.

  **TWO LISTS, NOT ONE**: ms: the members that are pinned in front of the piece (their trees were
      sent in front of it) · msR: the list that the reader searches (the table's own: it seats EVERY
      group's tenants, those sent behind the piece too). No one
      letter can hold both offices: no list could pay both at a real plan.
  InCopy cs arr ms msR N k n mask row place a condition on public letters alone: msR HAS a member in
      segment k's group with the number n (so the reader is not silent there: an empty list does not
      pass) · whichever member of msR that is, it is one of ms, and the place lies inside its
      ranges.
  readAt_alike
  maskQ · rd_maskQ · maskQ_alike THE SEGMENT's MASK ROW OFF THE WITNESS: entry j BELOW A PUBLIC nM
      is the program's canonical writing (OnBytes/Slice/KeyOfRec.lean: writeE) of what the
      segment reads at a public place pl j; FROM nM ON IT IS 0 (over all j
      the two conditions would be false from the row's length on at the natural pl). (K6's
      laws' mask row holds the program's
                                   elements; the witness holds field elements.) nM | pl ARE LETTERS:
                                       by the table's word the mask row is a table of the segment's
                                       first oracle message: which rows and places, and how many:
                                       the plan's.
WHAT IT DOES NOT SAY. namedOnce (ReadAt.lean's condition on the plan's numbers: the group has just
one tenant with that number) and InCopy are premises: NEITHER HAS RUN AT A PLAN. InCopy asks all
members of msR with that seat; the reader takes the first: more than is spent. No chance in it.

-/
import Mathlib
import Johnson.Desc.Sound.ReadAt
import OnBytes.Slice.KeyOfRec
import Johnson.Desc.Kinds.Law.K6Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT memTab InMsg namedOnce seatOf numOf seatTab
  readAt_of_named)

/-- Segment k's group has, in the reader's list msR, a member with the number n; and whichever
member of msR sits in that group with that number IS ONE OF THE PINNED MEMBERS ms, and the place
lies inside its ranges. -/
def InCopy (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (ms msR : List Mem) (N : Numbers) (k n :
    Nat)
    (mask : Bool) (row place : Nat) : Prop :=
  (∃ y ∈ msR, seatOf y ∈ N.group k ∧ numOf arr y = n) ∧
    ∀ y ∈ msR, seatOf y ∈ N.group k → numOf arr y = n →
      y ∈ ms ∧ InMsg cs (y.1.l.get y.2).1 mask row place

namespace Came

/-- **ReadAlike witnesses are read alike by readAt inside the segment's own copy's ranges.** -/
theorem readAt_alike {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (ms msR : List Mem) (N : Numbers) (k n : Nat) (w w' : Wit Cells Tok MsgT)
    (hn : namedOnce arr N k n = true) (hA : ReadAlike cs arr ms w w') (mask : Bool)
    (row place : Nat) (hin : InCopy cs arr ms msR N k n mask row place) :
    Sound.readAt cs arr msR N k w n mask row place =
      Sound.readAt cs arr msR N k w' n mask row place := by
  obtain ⟨x, hx, e⟩ := readAt_of_named cs arr msR N k n w hn
  obtain ⟨x', hx', e'⟩ := readAt_of_named cs arr msR N k n w' hn
  have exx : x' = x := by
    have h1 : [x'] = [x] := hx'.symm.trans hx
    exact List.head_eq_of_cons_eq h1
  subst exx
  rw [e, e']
  have hm : x' ∈ (N.group k).filter fun x => arr x.1 x.2 == n := by
    rw [hx]
    exact List.mem_singleton.2 rfl
  have hm' := List.mem_filter.1 hm
  have hxn : arr x'.1 x'.2 = n := eq_of_beq hm'.2
  unfold seatTab
  cases hf : msR.find? fun y => Decidable.decide (seatOf y = x') with
  | none => rfl
  | some y' =>
    have hd' : Decidable.decide (seatOf y' = x') = true :=
      List.find?_some (p := fun y => Decidable.decide (seatOf y = x')) hf
    have hs' : seatOf y' = x' := of_decide_eq_true hd'
    have hn' : numOf arr y' = n := by
      show arr (seatOf y').1 (seatOf y').2 = n
      rw [hs', hxn]
    have hy' : y' ∈ msR := List.mem_of_find?_eq_some hf
    obtain ⟨hpin, hrange⟩ := hin.2 y' hy' (hs' ▸ hm'.1) hn'
    exact hA y' hpin mask row place hrange

end Came

/-- **The segment's mask row, off the witness**: entry j below nM: the program's writing (the
library's writeE: words below the prime) of the entry that segment k reads at the place pl j: the
message's number; mask row or main row; the row; the place. From nM on: 0. nM, pl: public letters.
-/
noncomputable def maskQ {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (k nM : Nat) (pl : Nat → Nat × Bool × Nat × Nat)
    (w : Wit Cells Tok MsgT) : Nat → OnBytes.E := fun j =>
  if j < nM then
    OnBytes.Slice.writeE
      (Sound.readAt cs arr msR N k w (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
  else 0

namespace Came

/-- What is written is read back: the mask row's entry, read, is the witness's entry. -/
theorem rd_maskQ {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (msR : List Mem)
    (N : Numbers) (k nM : Nat) (pl : Nat → Nat × Bool × Nat × Nat) (w : Wit Cells Tok MsgT)
    (j : Nat) (hj : j < nM) : rd (maskQ cs arr msR N k nM pl w j) =
      Sound.readAt cs arr msR N k w (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2 := by
  unfold maskQ
  rw [if_pos hj]
  exact OnBytes.Slice.readE_writeE _

/-- **The mask row reads pinned places alone.** -/
theorem maskQ_alike {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (ms msR : List Mem) (N : Numbers) (k nM : Nat) (pl : Nat → Nat × Bool × Nat × Nat)
    (hn : ∀ j, j < nM → namedOnce arr N k (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N k (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
    (w w' : Wit Cells Tok MsgT) (hA : ReadAlike cs arr ms w w') :
    maskQ cs arr msR N k nM pl w = maskQ cs arr msR N k nM pl w' := by
  funext j
  unfold maskQ
  by_cases hj : j < nM
  · rw [if_pos hj, if_pos hj,
      readAt_alike cs arr ms msR N k (pl j).1 w w' (hn j hj) hA _ _ _ (hin j hj)]
  · rw [if_neg hj, if_neg hj]

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readAt_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rd_maskQ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.maskQ_alike
