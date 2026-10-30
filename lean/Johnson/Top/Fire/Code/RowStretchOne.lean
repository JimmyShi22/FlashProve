-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowStretchOne.lean: A RIDER TO RowStretchPairs.lean: THE MAKER's STRETCH AT BLOCK n HAS JUST AS MANY ROUNDS' DATA AS BLOCK n DECLARES ROUNDS: so where the block declares one round the cut IS one round's data.
  stretch_len₁ | ₂ | ₃    (cutDs …).length = b.rounds.length
  one_of_len₂ | ₃ | ₁     b.rounds.length = 1 → ∃ d, cutDs … n = [d]
  hpair_len₂ | ₃          THE ASKED FORM WITH hd GONE: from «the block declares one round» (in scope: rounds_in_scope gives every block's number): ∃ d r, the cut is [d] ∧ b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name); _held: at the held blocks
OBJECT · USER · LETTERS: as RowStretchPairs.lean's. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowStretchPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker

section
variable {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
include h

theorem stretch_len₂ (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b) :
    (cutDs D.ds₂ c₂ k₂ n).length = b.rounds.length := (stretch_of_data₂ F file D h c₂ k₂ q₂ n b hb).length_eq

theorem stretch_len₃ (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b) :
    (cutDs D.ds₃ c₃ k₃ n).length = b.rounds.length := (stretch_of_data₃ F file D h c₃ k₃ q₃ n b hb).length_eq

theorem stretch_len₁ (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) (hlast : 1 ≤ lastRounds c₁ k₁) (n : ℕ) (hn : n < k₁.length)
    (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b) : (cutDs D.ds₁ c₁ k₁ n).length = b.rounds.length :=
  (stretch_of_data₁ F file D h c₁ k₁ q₁ hlast n hn b hb).length_eq

theorem one_of_len₂ (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b)
    (hl : b.rounds.length = 1) : ∃ d, cutDs D.ds₂ c₂ k₂ n = [d] :=
  List.length_eq_one_iff.1 ((stretch_len₂ F file D h c₂ k₂ q₂ n b hb).trans hl)

theorem one_of_len₃ (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b)
    (hl : b.rounds.length = 1) : ∃ d, cutDs D.ds₃ c₃ k₃ n = [d] :=
  List.length_eq_one_iff.1 ((stretch_len₃ F file D h c₃ k₃ q₃ n b hb).trans hl)

theorem one_of_len₁ (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) (hlast : 1 ≤ lastRounds c₁ k₁) (n : ℕ) (hn : n < k₁.length)
    (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b) (hl : b.rounds.length = 1) : ∃ d, cutDs D.ds₁ c₁ k₁ n = [d] :=
  List.length_eq_one_iff.1 ((stretch_len₁ F file D h c₁ k₁ q₁ hlast n hn b hb).trans hl)

/-- **The asked form with hd gone.** -/
theorem hpair_len₂ (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b)
    (hl : b.rounds.length = 1) :
    ∃ d r, cutDs D.ds₂ c₂ k₂ n = [d] ∧ b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) := by
  obtain ⟨d, hd⟩ := one_of_len₂ F file D h c₂ k₂ q₂ n b hb hl
  obtain ⟨r, h1, h2⟩ := hpair₂ F file D h c₂ k₂ q₂ n b hb d hd
  exact ⟨d, r, hd, h1, h2⟩

theorem hpair_len₃ (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b)
    (hl : b.rounds.length = 1) :
    ∃ d r, cutDs D.ds₃ c₃ k₃ n = [d] ∧ b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) := by
  obtain ⟨d, hd⟩ := one_of_len₃ F file D h c₃ k₃ q₃ n b hb hl
  obtain ⟨r, h1, h2⟩ := hpair₃ F file D h c₃ k₃ q₃ n b hb d hd
  exact ⟨d, r, hd, h1, h2⟩

theorem hpair_len₂_held {Pb : Type} (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl)
    (hb : (c₂ :: k₂)[n]? = some b) (hl : b.rounds.length = 1) :
    ∃ d r, cutDs D.ds₂ (held c₂ : Block (Pb × F.S₂) F.Cl) (k₂.map held) n = [d] ∧ b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) := by
  obtain ⟨d, r, hd, h1, h2⟩ := hpair_len₂ F file D h c₂ k₂ q₂ n b hb hl
  exact ⟨d, r, (cutDs_held k₂ n _ c₂).trans hd, h1, h2⟩

theorem hpair_len₃_held {Pb : Type} (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl)
    (hb : (c₃ :: k₃)[n]? = some b) (hl : b.rounds.length = 1) :
    ∃ d r, cutDs D.ds₃ (held c₃ : Block (Pb × F.S₃) F.Cl) (k₃.map held) n = [d] ∧ b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) := by
  obtain ⟨d, r, hd, h1, h2⟩ := hpair_len₃ F file D h c₃ k₃ q₃ n b hb hl
  exact ⟨d, r, (cutDs_held k₃ n _ c₃).trans hd, h1, h2⟩

end

end LPFD

#print axioms LPFD.stretch_len₁
#print axioms LPFD.stretch_len₂
#print axioms LPFD.stretch_len₃
#print axioms LPFD.one_of_len₁
#print axioms LPFD.one_of_len₂
#print axioms LPFD.one_of_len₃
#print axioms LPFD.hpair_len₂
#print axioms LPFD.hpair_len₃
#print axioms LPFD.hpair_len₂_held
#print axioms LPFD.hpair_len₃_held
