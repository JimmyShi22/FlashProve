-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RepOfLeaves.lean: the frame fact on the reply at a row of pieces (`EachRep`,
Johnson/Desc/Sound/LeadsQ.lean), from laws on the blocks' decisions in the library's form
(`Block.Leaves`, Johnson/Desc/Sound/FoldHeard.lean).

Why. On the plain road the proof file's first chain owes: the block that hears the reply lays it in
the record, and no other block turns it. Other files type that of a block's DECISION (`Block.Leaves
h b`: where the decision goes on, the reading h of the record is as it was). The rule asks it of
PIECES: wherever a piece puts out. Between the two lies one step: where a piece puts out, its
block's decision has gone on and has returned the record that is put out (`Piece.out_decide`,
Johnson/Desc/Sound/PieceOut.lean).
  `Piece.leaves_out`: that step.
  `Block.Leaves.comp`, `Block.Leaves.below`: a function of a reading that is left is left; a block
  under `below` (the test on the words in front) leaves what the block leaves.
  `EachHears`: at the row that lays the token: the frame fact's first arm, as it stands, wherever
  the piece puts out inside the promise; at every other row: the piece's block leaves the reading.
  `eachRep_of_hears`: then `EachRep` at the reading of the record.
  `Block.Hears h ok`, `Block.YesAt U`, `EachHearsB`, `eachHears_of_blocks`: the row that lays the
  token: BEHIND: on the block's decision: where it goes on, a value is held behind. IN FRONT:
  "nothing is held yet" is asked of the PROMISE at that border (hfront), at the records of which a
  letter U is true alone (meant: the record bears no mark: a table's promise says nothing of a
  marked record), and the block is to go on at such records alone. At the text that rides today the
  piece at that row first enters the head's link and empties its own part, so the block's own test
  "heard once" cannot give "nothing is held yet". And one tie of two letters (htok).
Limits. A carriage: it shows of no block that it leaves a reading or that it hears.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.LeadsQ
import Johnson.Desc.Sound.PieceOut
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- A function of a reading that is left is left. -/
theorem Block.Leaves.comp {S Cl α β : Type} {h : S → α} {b : Block S Cl} (g : α → β)
    (hl : b.Leaves h) : b.Leaves fun s => g (h s) :=
  fun s rs gs s' e => congrArg g (hl s rs gs s' e)

/-- Where the block's decision goes on, the reading h holds, behind it, a value of which ok is true.
-/
def Block.Hears {S Cl α : Type} (h : S → Option α) (ok : α → Prop) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, h s' = some x ∧ ok x

/-- The block's decision goes on only at records of which U is true. -/
def Block.YesAt {S Cl : Type} (U : S → Prop) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → U s

theorem Block.YesAt.below {S Cl : Type} {U : S → Prop} {b : Block S Cl} (hl : b.YesAt U) :
    (Sound.below b).YesAt U := by
  intro s rs gs s' e
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  split at e'
  · exact hl s rs gs s' e'
  · cases e'

theorem Block.YesAt.lift {S T Cl : Type} (get : T → S) (set : T → S → T) {U : S → Prop}
    {b : Block S Cl} (hl : b.YesAt U) : (b.lift get set).YesAt fun t => U (get t) := by
  intro t rs gs t' e
  have e' : (b.decide (get t) rs gs).map (set t) = .ok t' := e
  cases hd : b.decide (get t) rs gs with
  | error m => rw [hd] at e'; cases e'
  | ok s' => exact hl _ _ _ _ hd

theorem Block.Hears.below {S Cl α : Type} {h : S → Option α} {ok : α → Prop} {b : Block S Cl}
    (hl : b.Hears h ok) : (Sound.below b).Hears h ok := by
  intro s rs gs s' e
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  split at e'
  · exact hl s rs gs s' e'
  · cases e'

/-- Under the test on the words in front the block leaves what it leaves. -/
theorem Block.Leaves.below {S Cl α : Type} {h : S → α} {b : Block S Cl} (hl : b.Leaves h) :
    (Sound.below b).Leaves h := by
  intro s rs gs s' e
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  split at e'
  · exact hl s rs gs s' e'
  · cases e'

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers laysSeats laysTok)

/-- **Where a piece puts out, a reading that its block leaves is as it was.** -/
theorem Piece.leaves_out {C : CK} {Fr : Frame} {A Cl W α : Type} (q : Piece C Fr A Cl W)
    (h : A → α) (hl : q.b.Leaves h) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C q.ds))
    (ho : q.ior.red.out a τ = some b) : h b.1 = h a.1 := by
  obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := q.out_decide a b τ ho
  exact hl _ _ _ _ hd

section
variable {P Cells Tok : Type} (tokOf : P × First.S → Tok) {A : Type} {Fr : Frame}
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) {Tok' : Type} (f : Tok → Tok')
  (rep₀ : A → Option Tok') {Cl : Type} {C : CK} (on : ℕ → A × Fr.E.Str → Prop) (U : A → Prop)

/-- At the row that lays the token: the frame fact's first arm; at every other row: the block leaves
the reading. -/
def EachHears : ℕ → List (Piece C Fr A Cl (Wit Cells Tok MsgT)) → Prop
  | _, [] => True
  | k, q :: l =>
    (match ps[k]? with
      | some p =>
        if laysTok links p then
          ∀ a τ b, on k a → q.ior.red.out a τ = some b →
            rep₀ a.1 = none ∧ rep₀ b.1 = some (f (tokOf (get b.1)))
        else q.b.Leaves rep₀
      | none => q.b.Leaves rep₀) ∧
      EachHears (k + 1) l

/-- **The frame fact on the reply, from the blocks' laws.** -/
theorem eachRep_of_hears : ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
    EachHears tokOf links ps get f rep₀ on k l →
    EachRep tokOf links ps get f (fun b => rep₀ b.1) on k l
  | [], _, _ => trivial
  | q :: l, k, h => by
    refine ⟨fun a τ b ha ho => ?_, eachRep_of_hears l (k + 1) h.2⟩
    have h1 := h.1
    unfold RepFact
    revert h1
    cases ps[k]? with
    | none =>
      intro h1
      exact q.leaves_out rep₀ h1 a b τ ho
    | some p =>
      intro h1
      dsimp only at h1 ⊢
      by_cases hl : laysTok links p = true
      · rw [if_pos hl] at h1 ⊢
        exact h1 a τ b ha ho
      · rw [if_neg hl] at h1 ⊢
        exact q.leaves_out rep₀ h1 a b τ ho

/-- The like on the blocks' decisions alone: at the row that lays the token the block hears, and
goes on only at records of which U is true. -/
def EachHearsB : ℕ → List (Piece C Fr A Cl (Wit Cells Tok MsgT)) → Prop
  | _, [] => True
  | k, q :: l =>
    (match ps[k]? with
      | some p =>
        if laysTok links p then q.b.Hears rep₀ (fun _ => True) ∧ q.b.YesAt U else q.b.Leaves rep₀
      | none => q.b.Leaves rep₀) ∧
      EachHearsB (k + 1) l

/-- **From laws on the blocks' decisions**, where the token that the table's extractor reads off a
record is what the reading holds (htok), and the promise in front of the row that lays the token
says, of the records of which U is true, that nothing is held yet (hfront). -/
theorem eachHears_of_blocks (htok : ∀ t x, rep₀ t = some x → f (tokOf (get t)) = x)
    (hfront : ∀ k p, ps[k]? = some p → laysTok links p = true →
      ∀ a, on k a → U a.1 → rep₀ a.1 = none) :
    ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
    EachHearsB (Cells := Cells) (Tok := Tok) links ps rep₀ U k l →
    EachHears tokOf links ps get f rep₀ on k l
  | [], _, _ => trivial
  | q :: l, k, h => by
    refine ⟨?_, eachHears_of_blocks htok hfront l (k + 1) h.2⟩
    have h1 := h.1
    have hf := hfront k
    revert h1 hf
    cases ps[k]? with
    | none => exact fun h1 _ => h1
    | some p =>
      intro h1 hf
      dsimp only at h1 ⊢
      by_cases hl : laysTok links p = true
      · rw [if_pos hl] at h1 ⊢
        intro a τ b ha ho
        obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := q.out_decide a b τ ho
        obtain ⟨x, hx, -⟩ := h1.1 _ _ _ _ hd
        exact ⟨hf p rfl hl a ha (h1.2 _ _ _ _ hd), by rw [hx, htok _ _ hx]⟩
      · rw [if_neg hl] at h1 ⊢
        exact h1

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Block.Leaves.below
#print axioms VerifiableInference.Desc.Sound.Piece.leaves_out
#print axioms VerifiableInference.Desc.Sound.eachRep_of_hears
#print axioms VerifiableInference.Desc.Sound.eachHears_of_blocks
