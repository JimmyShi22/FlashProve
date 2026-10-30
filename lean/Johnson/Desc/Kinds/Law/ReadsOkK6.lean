-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsOkK6.lean: TOOLS FOR THE WITNESS's SIDE OF THE RIDING: what the
accessors of a witness's messages read. THE TOOLS ALONE: the tops stand in
Law/ReadsSideK6.lean. Statements and proofs.

  OneOn            two witnesses are one on a list of tenants: each tenant's message and pad.
  memTab_same, seatTab_same   the one accessor at a member reads the message of its number and its
                   seat's pad; so does a seat's table.
  readAt_same      so segment k's reading is one at witnesses that are one on its group's tenants.
  alike_of_sent    witnesses that are one on the tenants sent at moment 0 are ReadAlike at ms0.
  oneOn_of_reads   what the table books for an item's tenants, as OneOn.
  ownQ_same, comp_of_cut   segment 24's own integers; the cells' two tables of integers.
  sameQ_symm       "one on a component" turns round.

WHAT IT IS NOT. No top. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers ModelPart Item Comp)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated sameQ memTab seatOf numOf
  seatTab)

section Tools

variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (msR : List Mem)
  (N : Numbers)

/-- Two witnesses are one on a list of tenants: each tenant's message and pad. -/
def OneOn (l : List (Nat × Nat)) (w w' : Wit Cells Tok MsgT) : Prop :=
  ∀ x ∈ l, w.msg (arr x.1 x.2) = w'.msg (arr x.1 x.2) ∧ w.pad x.1 x.2 = w'.pad x.1 x.2

/-- The one accessor at a member reads the message of its number and its seat's pad. -/
theorem memTab_same (w w' : Wit Cells Tok MsgT) (x : Mem)
    (h : w.msg (arr (seatOf x).1 (seatOf x).2) = w'.msg (arr (seatOf x).1 (seatOf x).2) ∧
      w.pad (seatOf x).1 (seatOf x).2 = w'.pad (seatOf x).1 (seatOf x).2) :
    memTab cs arr w x = memTab cs arr w' x := by
  obtain ⟨h1, h2⟩ := h
  unfold memTab Wit.tab numOf
  unfold seatOf at h1 h2
  rw [h1, h2]

/-- A seat's table is one at witnesses that are one on that seat. -/
theorem seatTab_same (w w' : Wit Cells Tok MsgT) (x : Nat × Nat)
    (h : w.msg (arr x.1 x.2) = w'.msg (arr x.1 x.2) ∧ w.pad x.1 x.2 = w'.pad x.1 x.2) :
    seatTab cs arr msR w x = seatTab cs arr msR w' x := by
  unfold seatTab
  cases hf : msR.find? fun y => Decidable.decide (seatOf y = x) with
  | none => rfl
  | some y =>
    have e : seatOf y = x := by simpa using List.find?_some hf
    exact memTab_same cs arr w w' y (by rw [e]; exact h)

/-- Segment k's reading is one at witnesses that are one on its group's tenants. -/
theorem readAt_same (k : Nat) (w w' : Wit Cells Tok MsgT) (h : OneOn arr (N.group k) w w') :
    Sound.readAt cs arr msR N k w = Sound.readAt cs arr msR N k w' := by
  funext n
  unfold Sound.readAt
  cases hf : (N.group k).find? fun x => arr x.1 x.2 == n with
  | none => rfl
  | some x => exact seatTab_same cs arr msR w w' x (h x (List.mem_of_find?_eq_some hf))

/-- Witnesses that are one on the tenants sent at moment 0 read alike at the pinned members. -/
theorem alike_of_sent (w w' : Wit Cells Tok MsgT) (h : OneOn arr (N.sent 24 0) w w') :
    ReadAlike cs arr (ms0 msR N) w w' := by
  intro x hx mask row place _
  have hm : seatOf x ∈ N.sent 24 0 := by
    unfold ms0 at hx
    simpa using (List.mem_filter.mp hx).2
  rw [memTab_same cs arr w w' x (h _ hm)]

/-- What the table books for an item's tenants, as OneOn. -/
theorem oneOn_of_reads (links : List ModelPart) (i : Item) (w w' : Wit Cells Tok MsgT)
    (h : ∀ c ∈ i.reads arr N links, sameQ c w w') : OneOn arr (i.tenants N) w w' := by
  intro x hx
  have hm : ∀ c ∈ [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2], c ∈ i.reads arr N links := by
    intro c hc
    unfold Item.reads
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hx, hc⟩)
  exact ⟨h (Comp.msg (arr x.1 x.2)) (hm _ (by simp)), h (Comp.pad x.1 x.2) (hm _ (by simp))⟩

end Tools

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- Segment 24's own integers are one at witnesses that are one on its group's tenants. -/
theorem ownQ_same (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : OneOn arr (N.group 24) w w') :
    P5J.ownQ cs arr msR N s seat w 24 = P5J.ownQ cs arr msR N s seat w' 24 := by
  rw [P5J.ownQ_at, P5J.ownQ_at, readAt_same cs arr msR N 24 w w' h]

/-- The cells' two tables of integers hang on the cut list alone. -/
theorem comp_of_cut (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : ownCut cs arr msR N s seat Wp w = ownCut cs arr msR N s seat Wp w') :
    (compCut cs arr msR N s seat Wp pl w).1.cell = (compCut cs arr msR N s seat Wp pl w').1.cell ∧
      (compCut cs arr msR N s seat Wp pl w).1.stream =
        (compCut cs arr msR N s seat Wp pl w').1.stream := by
  unfold compCut compOf
  rw [h]
  exact ⟨rfl, rfl⟩

/-- "One on a component" turns round. -/
theorem sameQ_symm {Cells Tk : Type} (c : Comp) (w w' : Wit Cells Tk MsgT) (h : sameQ c w w') :
    sameQ c w' w := by
  cases c <;> exact Eq.symm h

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readAt_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.alike_of_sent
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ownQ_same
