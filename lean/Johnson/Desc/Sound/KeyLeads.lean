-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyLeads.lean: A SEAT'S LAW IN THE PLAIN FORM: no witness, no extractor: outside
the rounds' bad challenges, whatever the block puts out stands to what it was handed as the rows
say.

The setting. A carried seat (`Seat`, Johnson/Desc/Sound/KeyJoints.lean) owes a tie to a proved
typed block (`DecideLaw`, Johnson/Desc/Sound/KeyDecides.lean). A plain form of a kind's law says of
a reduction K, a condition on, a relation Q between a statement and what is put out, and one number
a round ε: for every statement a with on a, round by round (`Iop.Doomed`, Iop/Rbr.lean) at most ε
values of the round's challenge are bad, and on the other transcripts: if K puts out b at a, then Q
a b. It is written out here: this file names no definition of that form.

What is said. For a seat between the rows A and B that meets its law (`Seat.Law`), at the seat's own
piece (the description's block with the test below the prime, at its stretch) and the written counts
`s.M.err s.k.err`:
  `seat_leads`: from A's condition: Q a b := "if B's relation holds of b, or b has left B's
    condition, then A's relation holds of a".
  `seat_leads_false`: THE SAME AS SOUNDNESS: from "a is in A's condition and OUTSIDE A's relation":
    Q a b := "b is in B's condition and outside B's relation": a false statement is handed on as a
    false statement, the promise kept.
  `outright_leads`, `outright_leads_false`: the like for a piece that is good between the two rows.

Limits. Forms. The promise behind is not kept for certain: where it is lost, A's relation holds (it
is paid in the typed block's counts): so "b is in B's condition" is had for false statements alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err Shape IOR ExtSpec Doomed)

variable {S Cl W : Type} {F : Frame}

/-- A piece that is good between two rows, in the plain form. -/
theorem outright_leads [Inhabited W] (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good) (a : S × F.E.Str)
    (ha : A.on a) :
    Doomed (uLT (ckP .two) p.ds) p.err (fun τ => ∀ b, p.ior.red.out a τ = some b →
      (B.rel b ∨ ¬ B.on b) → A.rel a) :=
  Doomed.mono _ _ (fun _ hτ b hb hq => hτ b default hb hq) (h.know a ha)

/-- The same as soundness: a false statement is handed on as a false statement. -/
theorem outright_leads_false [Inhabited W] (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good) (a : S × F.E.Str)
    (ha : A.on a ∧ ¬ A.rel a) :
    Doomed (uLT (ckP .two) p.ds) p.err (fun τ => ∀ b, p.ior.red.out a τ = some b →
      B.on b ∧ ¬ B.rel b) :=
  Doomed.mono _ _ (fun _ hτ b hb =>
    ⟨Classical.byContradiction fun hn => ha.2 (hτ b hb (Or.inr hn)),
      fun hr => ha.2 (hτ b hb (Or.inl hr))⟩) (outright_leads p A B h a ha.1)

/-- A carried seat's piece is good between its two rows. -/
theorem seat_good {A B : JointRow S F} (s : Seat Cl A B) (h : s.Law) :
    ((seatPiece (F := F) W s.b s.base s.ds s.back s.k s.M).bk A.on B.on (fun a _ => A.rel a)
      (fun a _ => B.rel a)).Good := by
  obtain ⟨hk, hB, hM, hb, hd⟩ := h
  exact goodOfSim (seatPiece (F := F) W s.b s.base s.ds s.back s.k s.M) s.k A.rd B.rd A.inv B.inv hk
    hB (simOfDecide W s.b s.base s.ds s.back s.k s.M A.rd B.rd A.inv B.inv hM hb hd)

/-- **A seat's law in the plain form.** -/
theorem seat_leads {A B : JointRow S F} (s : Seat Cl A B) (h : s.Law) (a : S × F.E.Str)
    (ha : A.on a) :
    Doomed (uLT (ckP .two) s.ds) (s.M.err s.k.err) (fun τ => ∀ b,
      (seatPiece (F := F) Unit s.b s.base s.ds s.back s.k s.M).ior.red.out a τ = some b →
      (B.rel b ∨ ¬ B.on b) → A.rel a) :=
  outright_leads _ A B (seat_good s h) a ha

/-- **The same as soundness.** -/
theorem seat_leads_false {A B : JointRow S F} (s : Seat Cl A B) (h : s.Law) (a : S × F.E.Str)
    (ha : A.on a ∧ ¬ A.rel a) :
    Doomed (uLT (ckP .two) s.ds) (s.M.err s.k.err) (fun τ => ∀ b,
      (seatPiece (F := F) Unit s.b s.base s.ds s.back s.k s.M).ior.red.out a τ = some b →
      B.on b ∧ ¬ B.rel b) :=
  outright_leads_false _ A B (seat_good s h) a ha

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seat_leads
#print axioms VerifiableInference.Desc.Sound.seat_leads_false
#print axioms VerifiableInference.Desc.Sound.outright_leads
#print axioms VerifiableInference.Desc.Sound.outright_leads_false
