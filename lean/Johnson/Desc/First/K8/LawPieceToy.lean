-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPieceToy.lean: THE LETTERS OF Johnson/Desc/First/K8/LawPiece.lean ARE NOT
EMPTY: A CLOSED MEMBER, WITH TEETH.

`piece_good` is a theorem under letters (`Reads`). A theorem under letters says nothing if there are
none. Here is a member in which nothing is a letter: the proved block's caller is the library's own
written toy (`KObj.TailRow.toyOn`, Johnson/Top/H/TailRngOnToy.lean: one matrix with one cell and one
column, one read, one combination; one plain oracle message with the symbol and the read); the
carried record holds the caller's statement beside the matrix's list; the seat lays the list and
leaves the statement.
  `ToyS`, `toySeatP`, `toyReads`: the record, the seat, the letters. `toyFitsOn`: the toy place's
    numbers are the toy caller's.
  `toy_piece_good`: so the kind's own text, at that seat, is good between the two boundaries, at the
    error `toyErr`: the proved block's count at the toy's sizes times the sampler's own bound.
  `toy_relA_fails`: A TOOTH: what stands in front of the block FAILS at every statement "true" and
    every witness whose message has the symbol 1 and the read 2 (the library's `toyOn_tooth`);
    `toy_relA_not_full`: there is such a witness: so at no statement "true" is the relation full.
    That it holds somewhere is shown here at the base joint alone (the library's `toyOn_joint`:
    symbol 1, read 1), not over the signature.
Limits: a toy. The record CARRIES the typed statement: nothing is read off a frame's oracles. NOT
DONE: the text with a decision that says yes to all, shown NOT to be good between these boundaries.
(A decision that says no to all IS good between any boundaries: knowledge soundness says nothing on
acceptance; what shuts it out is the law's other half, `hear_law_view`, an "if and only if".)


-/
import Johnson.Desc.First.K8.LawReads
import Johnson.Top.H.TailRngOnToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb.Pv.Tail KObj KObj.TailRow VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound
    OnBytes.Tie.Pv.Tail

/-- The toy's carried record: the caller's statement, and the matrix's list. -/
abbrev ToyS : Type := ((KTailRngOn.src toyOn).X × (KTailRngOn.src toyOn).E.Str) × Array Int

/-- The toy's seat: every test holds; the list is laid; the statement is left. -/
def toySeatP : Seat ToyS :=
  ⟨fun _ => true, fun _ => true, fun _ => false, fun _ => 1, fun _ => [1], fun _ => [1],
    fun _ => 1, fun _ => [], fun s m _ => .ok (s.1, m)⟩

def toyFrame : Frame := ⟨0, [], id, 0⟩

theorem toyFitsOn : Fits toyPar toyOn.c.s :=
  ⟨rfl, fun i hi => by
    have h0 : i = 0 := by
      have : i < 1 := hi
      omega
    subst h0
    rfl, rfl⟩

/-- The letters, closed. -/
def toyReads (base e : ℕ) : Reads Unit (KTailRngOn.src toyOn).W toyFrame toySeatP toyPar base e
    toyOn where
  rd := fun a => a.1.1
  wit := fun w => w
  cf := fun s => s.2
  cf_lay := fun st st' mm f h => by
    have e1 : (st.1, mm) = st' := by simpa [toySeatP] using h
    rw [← e1]
  keeps := fun st st' mm f y τ h => by
    have e1 : (st.1, mm) = st' := by simpa [toySeatP] using h
    rw [← e1]

/-- The toy's error: the proved block's count times the sampler's own bound. -/
def toyErr : ℕ :=
  (Fintype.card (Dr toyOn.c.s) / 2 ^ toyOn.c.s.tau) * (Run.bsRound .two (rdt toyPar).entry (rdt
      toyPar).kind).w

/-- **The kind's own text is good between the two boundaries, at a closed member of the letters.**
-/
theorem toy_piece_good (base : ℕ) :
    ((piece (Cl := Unit) (W := (KTailRngOn.src toyOn).W) (F := toyFrame) toySeatP toyPar base
        toyErr).bk
      (toyReads base toyErr).onA (toyReads base toyErr).onB (toyReads base toyErr).relA
      (toyReads base toyErr).relB).Good :=
  piece_good (toyReads base toyErr) toyFitsOn toyOn_mem (Nat.le_refl _)

/-- A tooth: the relation in front of the block is not full. -/
theorem toy_relA_fails (base e : ℕ) (a : ToyS × toyFrame.E.Str) (w : (KTailRngOn.src toyOn).W)
    (hx : a.1.1.1.1 = true) (hm : toySg.msgs w.1 = toyMsg 1 2) : ¬ (toyReads base e).relA a w := fun
        h => by
  have h2 : Cb.Pv.Tail.relIn toyOn.c.letters a.1.1.1.1 (toySg.msgs w.1) := h.2.2
  rw [hx, hm] at h2
  exact toyOn_tooth h2

/-- At every statement "true" there is a witness at which the relation in front of the block fails.
-/
theorem toy_relA_not_full (base e : ℕ) (a : ToyS × toyFrame.E.Str) (hx : a.1.1.1.1 = true) :
    ∃ w : (KTailRngOn.src toyOn).W, ¬ (toyReads base e).relA a w :=
  ⟨(fun i => (toyMsg 1 2 i, fun _ => 0), toyDig), toy_relA_fails base e a _ hx rfl⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.toy_piece_good
#print axioms VerifiableInference.Desc.First.K8.toy_relA_fails
#print axioms VerifiableInference.Desc.First.K8.toy_relA_not_full
