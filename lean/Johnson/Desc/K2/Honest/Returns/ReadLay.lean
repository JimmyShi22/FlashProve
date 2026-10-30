-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ReadLay.lean: THE LAST STEP OF THE READING OF THE OLD ROWS RETURNS:
the carried single rows' symbols are made of the opened columns (`rowsSymbols`,
Johnson/Desc/Own/Symbols.lean) wherever the columns fit the layout; and they are as many as
positions times rows. Statements and proofs, over the library's `rowsAt_yes` and `rowsAt_inv`
(Johnson/Desc/First/Link/Law/FrontAnswers.lean; LongText.lean, which this file does not import
itself: it comes through the first).

  `ColsFit`         at one position: every member has a column with its number of main symbols that
                    fits the layout's two tables; the fresh mask has a column of 2 ^ h mask symbols
  `rowsAt_behind`   one position's rows are laid behind what is there: as many more as there are
                    rows
  `rowsFrom_returns`, `rowsSymbols_returns`   the positions one after the other; the whole

Limits. Two masks alone. Nothing on the symbols' values. Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.FrontAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.Own (rowsAt rowsFrom rowsSymbols shapeFits layMembers)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount colAt rowsAt_yes rowsAt_inv)

/-- At position number i the opened columns fit the layout. nM: each member's main symbols. -/
structure ColsFit (s : SingleRows) (opened : Array (Array Column)) (nM : Nat → Nat) (i : Nat) :
    Prop where
  members : ∀ w ∈ List.range s.layout.members.size, ∃ c, colAt opened i w = some c ∧
    c.main.size = nM w ∧
    ColFits s.layout w c.main.size c.mask.size (2 ^ s.layout.k) (2 ^ s.layout.h)
  fresh : ∃ c, colAt opened i s.layout.members.size = some c ∧ c.mask.size = 2 ^ s.layout.h

variable {s : SingleRows} {opened : Array (Array Column)}

/-- One position's rows are laid behind what is there. -/
theorem rowsAt_behind (hm : s.masks = 2) (nM : Nat → Nat)
    (hk : keptCount s.layout nM (List.range s.layout.members.size) = s.keptRows) {i : Nat}
    (C : ColsFit s opened nM i) (y : Array E) :
    ∃ y', rowsAt s opened y i = some y' ∧ y'.size = y.size + s.rows := by
  obtain ⟨seg, hs⟩ := rowsAt_yes hm nM C.members hk C.fresh
  obtain ⟨t, fresh, ht, _, _, hkept, hf, hz, _⟩ := rowsAt_inv hm hs
  have ht' : layMembers s.layout opened i (List.range s.layout.members.size)
      ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ =
      some t := ht
  refine ⟨((y.push ((foldLow t.main s.gamma).getD 0 zeroE) ++ t.kept).push
    ((foldLow t.mask (s.gamma.take s.layout.h)).getD 0 zeroE)).push
      ((foldLow fresh.mask (s.gamma.take s.layout.h)).getD 0 zeroE), ?_, ?_⟩
  · unfold rowsAt
    dsimp only
    rw [ht']
    simp [hkept, hm, hf, hz]
  · simp only [Array.size_push, Array.size_append, hkept, SingleRows.rows, hm]
    omega

/-- The positions one after the other. -/
theorem rowsFrom_returns (hm : s.masks = 2) (nM : Nat → Nat)
    (hk : keptCount s.layout nM (List.range s.layout.members.size) = s.keptRows) :
    ∀ (is : List Nat) (y : Array E), (∀ i ∈ is, ColsFit s opened nM i) →
      ∃ y', rowsFrom s opened is y = some y' ∧ y'.size = y.size + is.length * s.rows
  | [], y, _ => ⟨y, rfl, by simp⟩
  | i :: is, y, h => by
    obtain ⟨y1, e1, z1⟩ := rowsAt_behind hm nM hk (h i List.mem_cons_self) y
    obtain ⟨y2, e2, z2⟩ := rowsFrom_returns hm nM hk is y1 fun j hj =>
      h j (List.mem_cons_of_mem _ hj)
    refine ⟨y2, ?_, ?_⟩
    · show (rowsAt s opened y i).bind (rowsFrom s opened is) = some y2
      rw [e1]
      exact e2
    · rw [z2, z1, List.length_cons, Nat.succ_mul]
      omega

/-- **The symbols are made**, and they are as many as positions times rows. -/
theorem rowsSymbols_returns (hm : s.masks = 2) (hs : shapeFits s = true) (nM : Nat → Nat)
    (hk : keptCount s.layout nM (List.range s.layout.members.size) = s.keptRows) (n : Nat)
    (h : ∀ i < n, ColsFit s opened nM i) :
    ∃ y, rowsSymbols s opened n = some y ∧ y.size = n * s.rows := by
  obtain ⟨y, e, z⟩ := rowsFrom_returns (opened := opened) hm nM hk (List.range n) #[] fun i hi =>
    h i (List.mem_range.1 hi)
  refine ⟨y, ?_, ?_⟩
  · unfold rowsSymbols
    rw [if_pos hs]
    exact e
  · rw [z, List.length_range]
    simp

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.rowsSymbols_returns
