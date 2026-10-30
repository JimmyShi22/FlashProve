-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerJoins.lean: THE JOININGS AT THE LEDGER OF A PROOF FILE's SHARED CHAIN:
what a kind's files owe at block 6 (ClauseAt, LedgerClause.lean). The table's row 6 is
empty: nothing closes, nothing opens, nothing is read: so all that is owed is that the shared
promise goes on and that every open shared item rides back, for certain.

  empty_clause    the clause at any block whose row names nothing in front.
  ins6            the table's row 6 names nothing in front.
  joins_clause    **the clause at block 6**, at any piece and at any errors.
THE PREMISES, AND WHOSE EACH IS. hid: the table's extractor lays nothing at the block (the table's
files) · hprom: the shared promise goes on at a yes (shape 6 to shape 7: the filling, by the
ground's joining) · hride: every open shared item rides back (the rows as they lie: a joining turns
the groups' members, no constraint; the pins: the strings below the piece's base stay).
What is not claimed. NO MEMBER. The block's text is not named: all its content stands in the two
premises. No soundness of a verifier.

-/
import Johnson.Desc.Sound.LedgerClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc.Shared

variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- The clause at a block whose row names nothing in front. -/
theorem empty_clause (k : ℕ) (hin : ∀ i, ¬ insSh split k i) (x : Piece C Fr (P₁ × S₂) Cl Wt)
    (ε : Err (uLT C x.ds)) (hid : ∀ v w, e₀ k v w = w)
    (hprom : ∀ a τ b, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 b))
    (hride : ∀ a τ b w i, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      openSh split k i → muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 b) w →
      muQ N Mg p l i k ((actQ N p l k).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ k x ε := by
  refine clause_of_sure N Mg Pm Oc split p l e₀ k x ε fun a τ b ha hout => ?_
  refine ⟨hprom a τ b ha hout, fun w hw i hi => ?_⟩
  rw [hid]
  exact hride a τ b w i ha hout hi (hw i (Or.inl ⟨hi, hin i⟩))

/-- The table's row 6 names nothing in front. -/
theorem ins6 (i : ItemS) : ¬ insSh split 6 i := by
  have hr : (rowAtS split 6).ins ++ (rowAtS split 6).ctx = [] := by cases split <;> rfl
  unfold insSh
  rw [hr]
  rintro ⟨_, h⟩
  cases h

/-- **The joinings at the ledger.** -/
theorem joins_clause (x : Piece C Fr (P₁ × S₂) Cl Wt) (ε : Err (uLT C x.ds))
    (hid : ∀ v w, e₀ 6 v w = w)
    (hprom : ∀ a τ b, onQ₂ N Pm Oc split p l 6 a → x.ior.red.out a τ = some b →
      promQ N Pm split p l 7 ((actQ N p l 7).2 b))
    (hride : ∀ a τ b w i, onQ₂ N Pm Oc split p l 6 a → x.ior.red.out a τ = some b →
      openSh split 6 i → muQ N Mg p l i 7 ((actQ N p l 7).2 b) w →
      muQ N Mg p l i 6 ((actQ N p l 6).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 6 x ε :=
  empty_clause N Mg Pm Oc split p l e₀ 6 (ins6 split) x ε hid hprom hride

end VerifiableInference.Desc.Sound
