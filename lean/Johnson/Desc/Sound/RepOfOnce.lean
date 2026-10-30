-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RepOfOnce.lean: the frame fact on the reply at a row of pieces (`EachRep`,
Johnson/Desc/Sound/LeadsQ.lean) from TWO LAWS ON THE BLOCKS' DECISIONS ALONE: the block at the row
that lays the token HEARS ONCE (`Block.HearsOnce`, Johnson/Desc/Sound/HearsOnce.lean); every other
block leaves the reading (`Block.Leaves`).

Why. `eachHears_of_blocks` (Johnson/Desc/Sound/RepOfLeaves.lean) asks "nothing is held yet in front
of the row that lays the token" of the PROMISE at that border (its premise hfront, at the records of
which a letter U is true), since at the record of that day the block's own test could not give it.
Over the record with one seat for the reply the block's own decision gives it: `Block.HearsOnce r
b`: where the decision goes on, r reads nothing in front and something behind. So hfront, U and
`Block.YesAt` fall.
  `EachOnce`: at the row that lays the token the piece's block hears once; at every other row it
  leaves the reading.
  `eachHears_of_once`, `eachRep_of_once`: then `EachHears`, and so `EachRep`, under the one tie of
  two letters htok (the token that the table's extractor reads off a record is what the reading
  holds).
  `eachOnce_of_rows`: `EachOnce` from the form in which the laws of a guarded chain come
  (`Chain.guarded_flat`, Johnson/Desc/Sound/SeatGuardLaws.lean; `Chain.HearsAt.guarded_flat`,
  SeatGuardHears.lean): each piece's block stands at the list's place of its row; AT THAT PLACE
  `but` says what the table's test "lays the token" says; the block stands at a place that `but`
  names or leaves the reading; at a place that `but` names it hears once.
Limits. A carriage over letters: it shows of no block that it hears once or leaves a reading, and of
no row of pieces that its blocks stand at the list's places. That K7's kind hears once is
`Kinds.Reply.kind_hearsOnce` (HearsOnce.lean); it is not called here. htok is owed. No soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RepOfLeaves
import Johnson.Desc.Sound.HearsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers laysSeats laysTok)

section
variable {P Cells Tok : Type} (tokOf : P × First.S → Tok) {A : Type} {Fr : Frame}
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) {Tok' : Type} (f : Tok → Tok')
  (rep₀ : A → Option Tok') {Cl : Type} {C : CK} (on : ℕ → A × Fr.E.Str → Prop)

/-- At the row that lays the token the block hears once; at every other row it leaves the reading.
-/
def EachOnce : ℕ → List (Piece C Fr A Cl (Wit Cells Tok MsgT)) → Prop
  | _, [] => True
  | k, q :: l =>
    (match ps[k]? with
      | some p => if laysTok links p then q.b.HearsOnce rep₀ else q.b.Leaves rep₀
      | none => q.b.Leaves rep₀) ∧
      EachOnce (k + 1) l

/-- **From the two laws on the blocks' decisions**: no premise on the promise. -/
theorem eachHears_of_once (htok : ∀ t x, rep₀ t = some x → f (tokOf (get t)) = x) :
    ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
    EachOnce (Cells := Cells) (Tok := Tok) links ps rep₀ k l →
    EachHears tokOf links ps get f rep₀ on k l
  | [], _, _ => trivial
  | q :: l, k, h => by
    refine ⟨?_, eachHears_of_once htok l (k + 1) h.2⟩
    have h1 := h.1
    revert h1
    cases ps[k]? with
    | none => exact fun h1 => h1
    | some p =>
      intro h1
      dsimp only at h1 ⊢
      by_cases hl : laysTok links p = true
      · rw [if_pos hl] at h1 ⊢
        intro a τ b _ ho
        obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := q.out_decide a b τ ho
        obtain ⟨h0, hs⟩ := h1 _ _ _ _ hd
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
        exact ⟨h0, by rw [hx, htok _ _ hx]⟩
      · rw [if_neg hl] at h1 ⊢
        exact h1

/-- **The frame fact on the reply.** -/
theorem eachRep_of_once (htok : ∀ t x, rep₀ t = some x → f (tokOf (get t)) = x)
    (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ)
    (h : EachOnce (Cells := Cells) (Tok := Tok) links ps rep₀ k l) :
    EachRep tokOf links ps get f (fun b => rep₀ b.1) on k l :=
  eachRep_of_hears tokOf links ps get f rep₀ on l k
    (eachHears_of_once tokOf links ps get f rep₀ on htok l k h)

/-- **From the form in which a guarded chain's laws come.** -/
theorem eachOnce_of_rows (but : Place → Bool) :
    ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
    (∀ i q, l[i]? = some q → ps[k + i]? = some q.b.place ∧ laysTok links q.b.place = but q.b.place ∧
      (but q.b.place = true ∨ q.b.Leaves rep₀) ∧ (but q.b.place = true → q.b.HearsOnce rep₀)) →
    EachOnce (Cells := Cells) (Tok := Tok) links ps rep₀ k l
  | [], _, _ => trivial
  | q :: l, k, h => by
    obtain ⟨hp, hbut, ho, hh⟩ := h 0 q rfl
    refine ⟨?_, eachOnce_of_rows but l (k + 1) fun i q' hq' => ?_⟩
    · have hp' : ps[k]? = some q.b.place := hp
      rw [hp']
      dsimp only
      by_cases hl : laysTok links q.b.place = true
      · rw [if_pos hl]
        exact hh (by rw [← hbut]; exact hl)
      · rw [if_neg hl]
        exact ho.resolve_left (by rw [← hbut]; exact hl)
    · have h2 := h (i + 1) q' hq'
      rwa [show k + (i + 1) = k + 1 + i by omega] at h2

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachHears_of_once
#print axioms VerifiableInference.Desc.Sound.eachRep_of_once
#print axioms VerifiableInference.Desc.Sound.eachOnce_of_rows
