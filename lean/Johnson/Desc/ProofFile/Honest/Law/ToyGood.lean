-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyGood.lean: theorems about the toy example of
Honest/Law/ToyRow.lean and about two sides of Honest/FrameToy.lean: `Good` (Honest/Side.lean) at
these sides, at the parameters that Honest/Law/ToyRow.lean supplies; and the four as the field
`good` of `Owed` (Honest/Owed.lean). The theorems are about these files' own made-up objects alone.
None is one of the library's goals.

  1  `plays_of_whole`, `acc_of_whole`   the fields `plays` and `acc` of `Good` from one condition on
     a whole list's run (`WholeAt`, Honest/Law/ToyWhole.lean)
  2  `good_look`, `good_send`, `good_tell`, `good_carry`, `good_zSide`, `good_zSide₂`, `side_…`,
     `good_row`   `Good` at the sides

The fields `fits` and `exact`, and the lists' lemmas, are those of Honest/Law/ToyExact.lean; `fresh`
is derived here, side by side, from its `look_fresh` and `fresh_unspent`. `pre` is a bound letter:
each `Good` holds at every `pre`: no part here reads the opened columns, and `exact` is proved
without its hypothesis on the field `opened`. `good_row` has the field beside each A and B by
`Lettered.goodAt_withField` (Honest/FieldFree.lean).

Limits.
  * A toy example.
  * No side here has a fall, and each sub-protocol accepts its list's own run at every coin at which
    its A holds (at `zSide₂` A is `oddAt`, which does not hold at all coins).
  * That `Good` can be met is proved at these sides alone; nothing is said to follow from it.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `plays_of_whole`, `acc_of_whole`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyWhole
import Johnson.Desc.ProofFile.Honest.FieldFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn itemOf roundsFit drawsMarkedNonzeroHaveNonzeroWords need)
open VerifiableInference.Desc.BlockToy (St look send₃ ask tree tree₃ drawT sendS openA sendR orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 The two fields from the one condition -/

section
variable {S Cl V W X Pb : Type} {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts}
  {chain firstTree : Nat} {A B : Coins Bk → S → Mid W X → Env → Prop}

/-- The field `plays` of `Good`, from the one condition. -/
theorem plays_of_whole (h : WholeAt φ σ Bk chain firstTree A B) :
    ∀ k s m E ds, A k s m E → drawsFit σ.block.rounds ds = true →
    σ.stopAt φ m.st.input m.loc ds = none →
    ∃ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c ∧
      play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y ∧
      fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds) [] =
        .ok cols ∧
      ∀ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) →
        B k s' (y.2.took cols) (E.add y.1) := by
  intro k s m E ds hA hd hs
  obtain ⟨c, y, cols, s', n, h1, h2, h3, h4, h5⟩ := h k s m E ds hA hd hs
  refine ⟨c, y, cols, h1, h2, h3, fun s'' n'' h6 => ?_⟩
  have e : s' = s'' := congrArg Prod.fst (Except.ok.inj (h4.symm.trans h6))
  exact e ▸ h5

/-- The field `acc` of `Good`, from the one condition: whatever the side's fall is. -/
theorem acc_of_whole (h : WholeAt φ σ Bk chain firstTree A B) :
    ∀ k s m E ds, A k s m E → drawsFit σ.block.rounds ds = true →
    σ.stopAt φ m.st.input m.loc ds = none → σ.fall s ds = none →
    ∀ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c →
      play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y →
      fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds) [] =
        .ok cols →
      ∃ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) := by
  intro k s m E ds hA hd hs _ c' y' cols' h1' h2' h3'
  obtain ⟨c, y, cols, s', n, h1, h2, h3, h4, _⟩ := h k s m E ds hA hd hs
  have ec : c = c' := Except.ok.inj (h1.symm.trans h1')
  subst ec
  have ey : y = y' := Except.ok.inj (h2.symm.trans h2')
  subst ey
  have ek : cols = cols' := Except.ok.inj (h3.symm.trans h3')
  subst ek
  exact ⟨s', n, h4⟩

end

/-! ## 2 `Good` at the sides -/

theorem not_look_place {a : Place} (ha : pLook ≠ a) (Bk : ProverCoinCounts)
    (h : ∀ e ∈ Bk.ahead, e.once = true → e.owner.place = pLook) :
    ∀ e ∈ Bk.ahead, e.once = true → e.owner.place ≠ a :=
  fun e he ho hq => ha ((h e he ho).symm.trans hq)

/-- **`Good` at the owner's and the spender's side**, at the example's book and order. About this
folder's own made-up objects alone; none of the library's goals. -/
theorem good_look {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .shared zSide By (orderOf Fy) 1 0 noTree lookSent onAny budOne :=
  ⟨look_fits, plays_of_whole (look_whole By lendsLook_By),
    acc_of_whole (look_whole By lendsLook_By),
    fun u hu ca m front ds asks hO hs _ =>
      look_exact u hu ca m front ds asks hO hs,
    look_fresh By (orderOf Fy) By_spent rfl rfl⟩

/-- **`Good` at the second owner's side.** About this folder's own made-up objects alone; none of
the library's goals. -/
theorem good_send {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own ySide₂ By (orderOf Fy) 2 Fy.lastChainFirstTreeNumber noTree sendSent onAny budOne :=
  ⟨send_fits, plays_of_whole send_whole, acc_of_whole send_whole,
    fun u hu ca m front ds asks hO hs _ =>
      send_exact Fy.lastChainFirstTreeNumber u hu ca m front ds asks hO hs,
    fresh_unspent .own ySide₂ By (orderOf Fy) budOne
      (not_look_place (a := ySide₂.block.place) (by decide) By By_spent_place)⟩

/-- **`Good` at the teller's side**, whose simulator reads `front`. About this folder's own made-up
objects alone; none of the library's goals. -/
theorem good_tell {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own ySide₃ By (orderOf Fy) 2 Fy.lastChainFirstTreeNumber sendSent sendSent onTeller budAny :=
  ⟨tell_fits, plays_of_whole tell_whole, acc_of_whole tell_whole,
    fun u hu ca m front ds asks hO hs _ =>
      tell_exact Fy.lastChainFirstTreeNumber u hu ca m front ds asks hO hs,
    fresh_unspent .own ySide₃ By (orderOf Fy) budAny
      (not_look_place (a := ySide₃.block.place) (by decide) By By_spent_place)⟩

/-- **`Good` at the carrier's side.** About this folder's own made-up objects alone; none of the
library's goals. -/
theorem good_carry {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own ySide₄ By (orderOf Fy) 2 Fy.lastChainFirstTreeNumber anyAt anyAt onAny budAny :=
  ⟨carry_fits, plays_of_whole carry_whole, acc_of_whole carry_whole,
    fun u hu ca m front ds asks hO hs _ =>
      carry_exact Fy.lastChainFirstTreeNumber u hu ca m front ds asks hO hs,
    fresh_unspent .own ySide₄ By (orderOf Fy) budAny
      (not_look_place (a := ySide₄.block.place) (by decide) By By_spent_place)⟩

/-- The same as `good_look`, at the book and description of Honest/FrameToy.lean. -/
theorem good_zSide {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .shared zSide Bz (orderOf Fz) 1 0 noTree lookSent onAny budOne :=
  ⟨look_fits, plays_of_whole (look_whole Bz lendsLook_Bz),
    acc_of_whole (look_whole Bz lendsLook_Bz),
    fun u hu ca m front ds asks hO hs _ =>
      look_exact u hu ca m front ds asks hO hs,
    look_fresh Bz (orderOf Fz) Bz_spent rfl rfl⟩

/-- `Good` at the carrier's side of Honest/FrameToy.lean, whose sub-protocol is `BlockToy.ask`. Its
A, `oddAt`, is a condition that no B of an earlier place gives at all coins: the running total holds
the owner's column as a number, which changes with the owner's coins. -/
theorem good_zSide₂ {pre : List (Nat × Nat × List Fmt.DeclaredRound)} :
    Good pre .own zSide₂ Bz (orderOf Fz) 2 Fz.lastChainFirstTreeNumber oddAt anyAt onAny budAny :=
  ⟨zSide₂_fits, plays_of_whole zSide₂_whole, acc_of_whole zSide₂_whole,
    fun u hu ca m front ds asks hO hs _ =>
      zSide₂_exact Fz.lastChainFirstTreeNumber u hu ca m front ds asks hO hs,
    fresh_unspent .own zSide₂ Bz (orderOf Fz) budAny
      (not_look_place (a := zSide₂.block.place) (by decide) Bz Bz_spent_place)⟩

/-! The sides that the description's own lists give at the four places are these four. -/

theorem side_look : yLook.side Fy.shared.blocksInOrder = some zSide := rfl
theorem side_send : ySendL.side Fy.second.blocksInOrder = some ySide₂ := rfl
theorem side_tell : yTellL.side Fy.second.blocksInOrder = some ySide₃ := rfl
theorem side_carry : yCarryL.side Fy.second.blocksInOrder = some ySide₄ := rfl

/-- **The field `good` of `Owed` (Honest/Owed.lean) at the lists `Gy`**, letter for letter. About
this folder's own made-up objects alone; none of the library's goals. -/
theorem good_row :
    (∀ r ∈ Gy.first, (r.withField 0 0 Fy.first.blocksInOrder [] 0).goodAt (earlierOf Fy 0) .own
        Fy.first.blocksInOrder (orderOf Fy) 0 0 Gy.falls₁) ∧
    (∀ r ∈ Gy.shared, (r.withField 1 0 Fy.shared.blocksInOrder [] 0).goodAt (earlierOf Fy 1) .shared
        Fy.shared.blocksInOrder (orderOf Fy) 1 0 Gy.falls₂) ∧
    ∀ r ∈ Gy.second, ∀ base skip,
      (r.withField 2 Fy.lastChainFirstTreeNumber Fy.second.blocksInOrder base skip).goodAt (earlierOf Fy 2) .own
        Fy.second.blocksInOrder (orderOf Fy) 2 Fy.lastChainFirstTreeNumber Gy.falls₃ := by
  refine ⟨fun r hL => absurd hL List.not_mem_nil, fun r hL => ?_, fun r hL base skip => ?_⟩
  · obtain rfl := List.mem_singleton.1 hL
    refine Lettered.goodAt_withField fun σ hσ => ?_
    obtain rfl := Option.some.inj (side_look.symm.trans hσ)
    exact good_look
  · rcases List.mem_cons.1 hL with rfl | hL
    · refine Lettered.goodAt_withField fun σ hσ => ?_
      obtain rfl := Option.some.inj (side_send.symm.trans hσ)
      exact good_send
    · rcases List.mem_cons.1 hL with rfl | hL
      · refine Lettered.goodAt_withField fun σ hσ => ?_
        obtain rfl := Option.some.inj (side_tell.symm.trans hσ)
        exact good_tell
      · obtain rfl := List.mem_singleton.1 hL
        refine Lettered.goodAt_withField fun σ hσ => ?_
        obtain rfl := Option.some.inj (side_carry.symm.trans hσ)
        exact good_carry

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.plays_of_whole
#print axioms ProofFile.Honest.Toy.acc_of_whole
#print axioms ProofFile.Honest.Toy.not_look_place
#print axioms ProofFile.Honest.Toy.good_look
#print axioms ProofFile.Honest.Toy.good_send
#print axioms ProofFile.Honest.Toy.good_tell
#print axioms ProofFile.Honest.Toy.good_carry
#print axioms ProofFile.Honest.Toy.good_zSide
#print axioms ProofFile.Honest.Toy.good_zSide₂
#print axioms ProofFile.Honest.Toy.side_look
#print axioms ProofFile.Honest.Toy.side_send
#print axioms ProofFile.Honest.Toy.side_tell
#print axioms ProofFile.Honest.Toy.side_carry
#print axioms ProofFile.Honest.Toy.good_row
