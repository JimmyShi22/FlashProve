-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Leaves.lean: WHAT A YES OF K10's BLOCK LEAVES OF THE FIRST CHAIN's
RECORD AS IT WAS. Statements and proofs.

A table of joints asks of every block's files two facts on the text: a mark stays; what is decoded
rides. K10's block at the record S is `K9.closing P` := the kind's block lifted by `recOf` and
`putRec` (Johnson/Desc/First/Batch/Place.lean). Its yes writes `putRec s` of "nothing owed", a frame
and a statement.
  `putLive_keeps`, `putRec_keeps`: `S.putLive` and `putRec` leave five fields of the record: the
    book of trees, the count of roots, THE MARK (`failed`), the links' result (`out`) and the
    request (`req`).
  `closing_writes`: a yes of `K9.closing P` from s to s': s' is `putRec s ⟨none, f, S'⟩` for the
    frame and the statement that `closeFrame` returned.
  `closing_keeps`: so s' has s's book, roots, mark, out and req; and nothing is owed behind.
  `closing_mark_stays`: A MARK STAYS, at the block's decision: if s bears a mark, s' bears one.
    (More: it is the same mark; and an unmarked s stays unmarked: K10's block marks nothing: it
    refuses.)
  `pieceAt_keeps`, `pieceAt_mark_stays`: THE SAME AT THE PIECE (`pieceAt`, PieceOf.lean): where the
    piece's reduction puts out b from a: by `Piece.out_decide` (Johnson/Desc/Sound/PieceOut.lean)
    and `below_yes`; and the strings of b are those that the stage leaves (`ior.imp`). That is the
    form in which a table of joints asks it of a piece, AT THE RECORD S ITSELF: the table's own
    record is wider (a public part beside S, read by its `get`): the step to the lifted piece is not
    made here.
Limits. ON "WHAT IS DECODED RIDES" NOTHING IS PROVED HERE: that sentence is a letter of the table's
meaning, on the record AND the strings. What this file gives toward it is on the record alone: which
fields stay. The statement `st` does turn (the group is marked as in its test, the members' ledgers
are closed, the fold's mask is marked as spent: the kind's text), and so does the live frame. On the
strings (what the piece's rounds add to the oracles) nothing is said. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PieceOf
import Johnson.Desc.Sound.PieceOut
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open VerifiableInference.Desc VerifiableInference.Desc.K9 VerifiableInference.Desc.Sound
open OnBytes OnBytes.Flat OnBytes.Maker Iop Run

theorem putLive_keeps (s : S) (c : OnBytes.Model.ChainCheck) :
    (s.putLive c).book = s.book ∧ (s.putLive c).roots = s.roots ∧
      (s.putLive c).failed = s.failed ∧ (s.putLive c).out = s.out ∧ (s.putLive c).req = s.req := by
  unfold S.putLive
  cases s.link? with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some L =>
    show (s.putLink _).book = _ ∧ _
    unfold S.putLink
    cases s.here with
    | head a => by_cases h : a.opened <;> simp [h]
    | _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem putRec_keeps (s : S) (r : Rec) :
    (putRec s r).book = s.book ∧ (putRec s r).roots = s.roots ∧ (putRec s r).failed = s.failed ∧
      (putRec s r).out = s.out ∧ (putRec s r).req = s.req ∧ (putRec s r).rowsOwed = r.owed := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := putLive_keeps s { s.live with frame := r.frame }
  exact ⟨h1, h2, h3, h4, h5, rfl⟩

theorem closing_writes {Cl : Type} (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (K9.closing (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ x, closeFrame (recOf s).owed (recOf s).frame (recOf s).st (entries P) rs = .ok x ∧
      s' = putRec s ⟨none, x.1, x.2⟩ :=
  (lift_decide_iff P recOf putRec s s' rs gs).1 h

theorem closing_keeps {Cl : Type} (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (K9.closing (Cl := Cl) P).decide s rs gs = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots ∧ s'.failed = s.failed ∧ s'.out = s.out ∧
      s'.req = s.req ∧ s'.rowsOwed = none := by
  obtain ⟨x, -, rfl⟩ := closing_writes P s s' rs gs h
  exact putRec_keeps s ⟨none, x.1, x.2⟩

/-- **A mark stays.** -/
theorem closing_mark_stays {Cl : Type} (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (K9.closing (Cl := Cl) P).decide s rs gs = .ok s') :
    s.failed ≠ none → s'.failed ≠ none := by
  rw [(closing_keeps P s s' rs gs h).2.2.1]
  exact id

section
variable {Cl W : Type} {F : Frame} (P : Par) (base : ℕ) (dB dE dR : RDT) (k : ℕ)
  (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
  (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR)))

/-- **At the piece**: where the reduction of K10's piece puts out b from a, the record of b has the
five fields of a's, and nothing is owed; the strings of b are those that the stage leaves. -/
theorem pieceAt_keeps (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (pieceAt (Cl := Cl) P recOf putRec base dB dE dR k ext err).ds))
    (h : (pieceAt (Cl := Cl) P recOf putRec base dB dE dR k ext err).ior.red.out a τ = some b) :
    (b.1.book = a.1.book ∧ b.1.roots = a.1.roots ∧ b.1.failed = a.1.failed ∧ b.1.out = a.1.out ∧
      b.1.req = a.1.req ∧ b.1.rowsOwed = none) ∧
    b.2 = (pieceAt (Cl := Cl) P recOf putRec base dB dE dR k ext err).ior.imp a.2 τ := by
  obtain ⟨-, -, ⟨gs, hd⟩, hi⟩ := Piece.out_decide _ a b τ h
  exact ⟨closing_keeps (Cl := Cl) P a.1 b.1 _ gs (below_yes _ _ _ _ _ hd), hi⟩

/-- **A mark stays, at the piece**: the form in which a table of joints asks it of a piece, at the
record S itself. -/
theorem pieceAt_mark_stays (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (pieceAt (Cl := Cl) P recOf putRec base dB dE dR k ext err).ds))
    (h : (pieceAt (Cl := Cl) P recOf putRec base dB dE dR k ext err).ior.red.out a τ = some b) :
    a.1.failed ≠ none → b.1.failed ≠ none := by
  rw [(pieceAt_keeps P base dB dE dR k ext err a b τ h).1.2.2.1]
  exact id

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.putLive_keeps
#print axioms VerifiableInference.Desc.First.Close.putRec_keeps
#print axioms VerifiableInference.Desc.First.Close.closing_writes
#print axioms VerifiableInference.Desc.First.Close.closing_keeps
#print axioms VerifiableInference.Desc.First.Close.closing_mark_stays
#print axioms VerifiableInference.Desc.First.Close.pieceAt_keeps
#print axioms VerifiableInference.Desc.First.Close.pieceAt_mark_stays
