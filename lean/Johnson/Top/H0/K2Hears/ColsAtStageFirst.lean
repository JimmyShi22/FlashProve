-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/ColsAtStageFirst.lean: the code switch: every column that the kind's text is
shown at a stretch of a chain is the oracles' own, at its key and position: the statement of
ColsAtStage.lean (`colsOf_stage`), at the same reading of the oracles (`orcS`), UNDER TWO OTHER
PREMISES on the plan's numbers. Statements and proofs; no definition.

Why. `colsOf_stage` asks that the keys of ALL trees at hand are apart, and that NO tree numbered at
or beyond the stretch's base has a key that the switch reads. At the frame of a file's first chain
the trees at hand are those of all three chains (`allOf`, Johnson/Desc/Sound/Tiles.lean), and a
tree's key is the number in its label (`Three.Whole.key`, OnBytes/Three/Data.lean), which begins at
0 again in the second chain. So both premises fail there. What the proof spends is other: the two
premises here do not follow from those two, nor those from these.

  `opened_want`   a column of a stretch's view is a stored table's, or a tree's THAT THE STRETCH's
                  DATA OPEN, at a want
  `wants_opens`   a tree in a want is opened by one of the rounds' data
  `orcS_first`    the column of a tree at hand is orcS's, if that tree is THE FIRST at hand with its
                  key
  `colsOf_first`  THE STATEMENT
Premises of `colsOf_first`: Fits (Block.step's own tests) · h16: the numbers in "read" are below
2 ^ 16 · hFirst: each tree below the base is the first tree at hand with its key · hOld: the
stretch's data open trees below the base alone. The last three are facts on public numbers: NOT
SHOWN HERE AT ANY PLAN. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.ColsAtStage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open VerifiableInference.Desc (Block groupsOf regroup roundsFit roundsFit_length)
open OnBytes.Maker _root_.Run _root_.Run.PQ

/-- A tree in a want is opened by one of the rounds' data. -/
theorem wants_opens (a : Nat) (dep : Nat → Option Nat) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn)
    (j x : Nat), Want.tree j x ∈ wantsOf a dep ds Rs → ∃ d ∈ ds, j ∈ d.opens
  | [], _, _, _, h => by simp [wantsOf] at h
  | _ :: _, [], _, _, h => by simp [wantsOf] at h
  | d :: ds, R :: Rs, j, x, h => by
    rw [wantsOf] at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 h
        obtain ⟨_, -, e⟩ := List.mem_map.1 hs
        cases e
      · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.1 h
        cases hd : dep i with
        | none =>
          rw [hd] at hs
          cases hs
        | some b =>
          rw [hd] at hs
          obtain ⟨_, -, e⟩ := List.mem_map.1 hs
          cases e
          exact ⟨d, List.mem_cons_self, hi⟩
    · obtain ⟨d', hd', hj⟩ := wants_opens a dep ds Rs j x h
      exact ⟨d', List.mem_cons_of_mem _ hd', hj⟩

section
variable (C : CK) (S : StageD)

/-- A column of a stretch's view, with the tree among those that the data open. -/
theorem opened_want (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (c : Nat × Nat × List UInt64)
    (hc : c ∈ (sView C S y τ).opened) :
    (∃ item, c.1 = Fmt.storedKey item) ∨
      ∃ j, (∃ d ∈ S.ds, j ∈ d.opens) ∧ c.1 = S.key j ∧
        sCol C S y τ (.tree j c.2.1) = some c.2.2 := by
  unfold sView at hc
  obtain ⟨w, hw0, hw⟩ := List.mem_filterMap.1 hc
  obtain ⟨col, h1, rfl⟩ := Option.map_eq_some_iff.1 hw
  cases w with
  | table item x => exact Or.inl ⟨item, rfl⟩
  | tree j x => exact Or.inr ⟨j, wants_opens _ _ _ _ j x hw0, rfl, h1⟩

/-- The column of a tree at hand is orcS's, if that tree is the first at hand with its key. -/
theorem orcS_first (y : S.Ei.Str) (j x : Nat) (col : List UInt64)
    (hF : (S.Lin.find? fun L => S.key L.no == S.key j).map (·.no) = some j)
    (h : (posL S.Lin j x).map y.2 = some col) : col = orcS S y (S.key j) x := by
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hF
  unfold orcS
  rw [hT]
  simp only [h, Option.getD_some]

/-- **Every column that the text is shown is the oracles' own.** -/
theorem colsOf_first {St Cl : Type} (b : Block St Cl) (p : P2) (hr : b.rounds = rounds p)
    (hFirst : ∀ j, j < S.base → (S.Lin.find? fun L => S.key L.no == S.key j).map (·.no) = some j)
    (h16 : ∀ r ∈ p.read, r.1 < 2 ^ 16)
    (hOld : ∀ d ∈ S.ds, ∀ j ∈ d.opens, j < S.base)
    (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (rs : List Fmt.RoundView)
    (hF : b.Fits p.firstTree rs (sView C S y τ).opened) :
    ColsOf (orcS S y) (flat p (b.shown p.firstTree rs (sView C S y τ).opened)) := by
  intro c hc
  obtain ⟨r, hrm, hk⟩ := flat_key p _ c hc
  rcases opened_want C S y τ c (flat_sub b p hr rs _ hF c hc) with
    ⟨item, e⟩ | ⟨j, ⟨d, hd, hj⟩, e, hcol⟩
  · have := h16 r hrm
    rw [← hk, e] at this
    unfold Fmt.storedKey at this
    omega
  · have hlt := hOld d hd j hj
    have h' : (posL S.Lin j c.2.1).map y.2 = some c.2.2 := by
      have h0 : (if j < S.base then (posL S.Lin j c.2.1).map y.2
          else colAtST C S.ds τ (j - S.base) c.2.1) = some c.2.2 := hcol
      rwa [if_pos hlt] at h0
    rw [e]
    exact orcS_first S y j c.2.1 c.2.2 (hFirst j hlt) h'

end

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.wants_opens
#print axioms VerifiableInference.Desc.First.K2.opened_want
#print axioms VerifiableInference.Desc.First.K2.orcS_first
#print axioms VerifiableInference.Desc.First.K2.colsOf_first
