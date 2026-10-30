-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RowsBlankWord.lean: `RowsBlank` holds of the library's group's word by the way
that word is made. Statements and proofs.

`RowsBlank` (Johnson/Desc/K12/Law/TabWords.lean) holds of the library's group's word (`Gp.word`,
OnBytes/Slice/KeyGroup.lean) and of every word that the library ties to a group's sent words
(`Gp.Tie`). Public data and a definition: no view stands in it.
Main names:
  `SeatsAre G oM oZ S L`: the seats are the layout's: each member of the library's group is an
    oracle message o that the layout finds, not kept; its numbers of main and mask rows are the
    shape's real rows; where it has rows, its seat begins at the first row of the layout's block.
  `realRows_le`: the real rows are at most 2 ^ rowBits (the library's `le_two_pow_ceilLog2`).
  `real_main`, `real_mask`: a member's real row is neither in no block nor in a block's padding: not
    in its own (it lies below first + realRows), and not in another's: the padded blocks are apart
    (`LayFacts.main_apart`, `LayFacts.mask_apart`, Johnson/Desc/Means/Layout.lean). Were they not,
    `RowsBlank` would be false at an honest word.
  `rowsBlank_of_tie`: `Gp.Numbered`, `LayFacts`, L.k = s.h + s.g, L.h = s.h, `SeatsAre` and `Gp.Tie
    yw f` give `RowsBlank s S L f` (by the fields freeM and freeZ of `Gp.Tie`).
  `rowsBlank_word`: the same of `G.word yw` (the library's `tie_word`).
`RowsBlank` takes a row's number modulo 2 ^ (s.h + s.g) or 2 ^ s.h, and `OffMain` and `PadMain`
modulo 2 ^ L.k or 2 ^ L.h: they are one under the two equations on L, which are premises here.
Limits: `SeatsAre` is shown here of no group. Nothing is said on the members' own words. No
soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `le_two_pow_ceilLog2`
(OnBytes/Slice/ProgCodes.lean), `vtx_inj` and `Gp.Numbered.apart` (OnBytes/Slice/KeyPlaces.lean),
`Gp.tie_word` (OnBytes/Slice/KeyGroup.lean), and fields of `Gp.Tie` and `Gp.Numbered`; fields of
`LayFacts`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.TabWords
import OnBytes.Slice.KeyPlaces

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

/-- The seats are the layout's: each member of the library's group (with seats by numbers oM, oZ) is
an oracle message o of the statement that the layout finds, not kept; its numbers of main and mask
rows are the shape's real rows; where it has rows, its seat begins where the layout's block begins.
-/
structure SeatsAre {s : Sg} (G : Gp s) (oM oZ : G.ι → ℕ) (S : Statement) (L : GroupLayout) : Prop
    where
  at_ : ∀ i : G.ι, ∃ o n, L.find o = some n ∧ L.kept.getD n false = false ∧
    realRows S o .main = (G.mb i).nM ∧ realRows S o .mask = (G.mb i).nZ ∧
    (0 < (G.mb i).nM → L.mainFirst.getD n none = some (oM i)) ∧
    (0 < (G.mb i).nZ → L.maskFirst.getD n none = some (oZ i))

theorem realRows_le (S : Statement) (o : Nat) (part : Part) :
    realRows S o part ≤ 2 ^ S.rowBits o part := by
  unfold realRows Statement.rowBits
  cases S.oracles[o]? with
  | none => exact Nat.zero_le _
  | some x => exact le_two_pow_ceilLog2 _

/-- A real main row of a member is neither in no block nor in a block's padding. -/
theorem real_main {S : Statement} {G' : Group} {L : GroupLayout} (F : LayFacts S G' L) {o n first r
    J : Nat}
    (hf : L.find o = some n) (hk : L.kept.getD n false = false)
    (hm : L.mainFirst.getD n none = some first) (hr : r < realRows S o .main)
    (hJ : J % 2 ^ L.k = first + r) : ¬ (OffMain S L J ∨ PadMain S L J) := by
  have hle := realRows_le S o .main
  rintro (h | ⟨o', n', first', hf', hk', hm', h1, h2⟩)
  · exact h o n first hf hk hm ⟨by omega, by omega⟩
  · by_cases ho : o = o'
    · subst ho
      rw [hf] at hf'
      obtain rfl := Option.some.inj hf'
      rw [hm] at hm'
      obtain rfl := Option.some.inj hm'
      omega
    · rcases F.main_apart o o' n n' first first' ho hf hf' hm hm' with h3 | h3 <;> omega

theorem real_mask {S : Statement} {G' : Group} {L : GroupLayout} (F : LayFacts S G' L) {o n first r
    J : Nat}
    (hf : L.find o = some n) (hm : L.maskFirst.getD n none = some first)
    (hr : r < realRows S o .mask) (hJ : J % 2 ^ L.h = first + r) :
    ¬ (OffMask S L J ∨ PadMask S L J) := by
  have hle := realRows_le S o .mask
  rintro (h | ⟨o', n', first', hf', hm', h1, h2⟩)
  · exact h o n first hf hm ⟨by omega, by omega⟩
  · by_cases ho : o = o'
    · subst ho
      rw [hf] at hf'
      obtain rfl := Option.some.inj hf'
      rw [hm] at hm'
      obtain rfl := Option.some.inj hm'
      omega
    · rcases F.mask_apart o o' n n' first first' ho hf hf' hm hm' with h3 | h3 <;> omega

/-- RowsBlank of every word that the library ties to a group's sent words (Gp.Tie): so of Gp.word.
-/
theorem rowsBlank_of_tie {s : Sg} (G : Gp s) (oM oZ : G.ι → ℕ) (hN : G.Numbered oM oZ)
    (S : Statement) (G' : Group) (L : GroupLayout) (F : LayFacts S G' L) (hk : L.k = s.h + s.g)
    (hh : L.h = s.h) (hS : SeatsAre G oM oZ S L) (yw : G.Words) (f : s.cIn.Word) (hT : G.Tie yw f) :
    RowsBlank s S L f where
  main := fun J hJ x => by
    refine hT.freeM _ _ fun n hn => ?_
    obtain ⟨o, m, a1, a2, a3, _, a5, _⟩ := hS.at_ n.1
    have hr := n.2.isLt
    rw [hN.pM] at hn
    have hv := vtx_inj (lt_of_lt_of_le (Nat.add_lt_add_left hr _) (hN.roomM n.1))
      (Nat.mod_lt J (Nat.two_pow_pos _)) hn
    exact real_main F a1 a2 (a5 (by omega)) (by rw [a3]; exact hr) (by rw [hk]; exact hv.symm) hJ
  mask := fun J hJ x => by
    refine hT.freeZ _ _ fun n hn => ?_
    obtain ⟨o, m, a1, _, _, a4, _, a6⟩ := hS.at_ n.1
    have hr := n.2.isLt
    rw [hN.pZ] at hn
    have hv := vtx_inj (lt_of_lt_of_le (Nat.add_lt_add_left hr _) (hN.roomZ n.1))
      (Nat.mod_lt J (Nat.two_pow_pos _)) hn
    exact real_mask F a1 (a6 (by omega)) (by rw [a4]; exact hr) (by rw [hh]; exact hv.symm) hJ

/-- Of the group's word. -/
theorem rowsBlank_word {s : Sg} (G : Gp s) (oM oZ : G.ι → ℕ) (hN : G.Numbered oM oZ)
    (S : Statement) (G' : Group) (L : GroupLayout) (F : LayFacts S G' L) (hk : L.k = s.h + s.g)
    (hh : L.h = s.h) (hS : SeatsAre G oM oZ S L) (yw : G.Words) : RowsBlank s S L (G.word yw) :=
  rowsBlank_of_tie G oM oZ hN S G' L F hk hh hS yw _ (G.tie_word hN.apart yw)

end H2K.ClaimSays

#print axioms H2K.ClaimSays.rowsBlank_of_tie
#print axioms H2K.ClaimSays.rowsBlank_word
