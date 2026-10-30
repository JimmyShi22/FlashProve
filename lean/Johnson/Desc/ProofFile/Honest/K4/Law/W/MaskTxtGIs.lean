-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskTxtGIs.lean: Three statements with their proofs. The last
is CONDITIONAL on its one hypothesis, that the text answers.

What is here. On `k4MaskTextG` (Lot/MaskTxtG.lean), the text of the member of the feed-forward
layers' own rounds (sub-protocol K4) for its segment's mask row, whose look-up in the list can fail.
`k4Takes_three`: the number of slots that the hearing takes is 3 or more at every public data: so
the fences hold two entries or more. (1) `mask_lookup_some`: INSIDE THE TEXT's FENCES THE LOOK-UP IN
THE LIST OF WHAT THE ROW's PARTS SPEND RETURNS, at every value that the book can lend: no hypothesis
but the two fences. (2) `k4MaskTextG_val`: WHERE THE TEXT ANSWERS y, THE ENTRY LIES INSIDE THE
FENCES AND y IS THE READING OF MEMBER NUMBER place - e OF
`rowSpent Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0` (Honest/Law/Rule/Spent.lean, of other
writers): ON THAT SIDE STAND THE BOOK, THE COINS OF THE FIRST CHAIN, AND Qp: neither cells nor
weights nor tokens nor look, no input and no challenge.

How. `k4_coins_b` (Law/SlotsTrue.lean) with `k4_coins_total` (Law/W/MaskBelowHead.lean).
`spent_total` (the same file): the list has `k4Takes` members at every value. `spent_same`
(Law/TieIs.lean) and `spentOf_row` (Honest/Law/Rule/Spent.lean): where the book lends a row, what
its parts spend is a function of the book and the coins alone.

Not shown here. WHETHER THE TEXT ANSWERS: that hangs on whether `lendRow` returns, of which nothing
is said here. WHOSE COINS THE MEMBERS OF `rowSpent` ARE: by its text they are runs cut off the coins
of the owners that the book's entries name; whether two members are one coin of an owner's hangs on
the book: nothing is shown. Nothing on what `Reading.gl.val` does to a coin. A program's walk from
import to import, which reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/,
Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `k4Takes_three`   three slots or more
  `mask_lookup_some`   inside the fences the look-up returns
  `k4MaskTextG_val`   **what it answers, with no reader on the right**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskBelowHead
import Johnson.Desc.ProofFile.Honest.K4.Law.TieIs
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskTxtG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub)

/-- **The hearing takes three slots or more**, at every public data. -/
theorem k4Takes_three : 3 ≤ k4Takes Qp.P Qp.hp Qp.g := by
  have a := (k4_coins_b Qp).2.2.2.2
  rw [k4_coins_total] at a
  omega

/-- **Inside the fences the look-up returns.** -/
theorem mask_lookup_some
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts) {e place : ℕ}
    (h1 : e ≤ place) (h2 : place + 1 < e + k4Takes Qp.P Qp.hp Qp.g) :
    ((spentOf _ c)[place - e]?).isSome = true := by
  have hl : place - e < (spentOf _ c).length := by
    rw [spent_total cells weights tokens look Qp c]
    omega
  rw [List.getElem?_eq_getElem hl]
  rfl

/-- CONDITIONAL on hy. **What the text answers, with no reader on the right.** -/
theorem k4MaskTextG_val {e : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr} {hd : List Fmt.Drawn}
    {mask : Bool} {row place : ℕ} {y : Cb.Gl.E}
    (hy : Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place = some y) :
    (mask = true ∧ row = 0 ∧ e ≤ place ∧ place + 1 < e + k4Takes Qp.P Qp.hp Qp.g) ∧
      ∃ c₀, (rowSpent Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[place - e]? = some c₀ ∧
        y = Reading.gl.val c₀ := by
  unfold Lot.k4MaskTextG at hy
  split at hy
  · rename_i hc
    refine ⟨hc, ?_⟩
    cases hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0 with
    | error s =>
      rw [hl] at hy
      have hy' : (none : Option Cb.Gl.E) = some y := hy
      cases hy'
    | ok c =>
      rw [hl] at hy
      have hy' : ((spentOf _ c)[place - e]?).map Reading.gl.val = some y := hy
      obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 hy'
      refine ⟨c₀, ?_, rfl⟩
      have eL : (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts.length =
          (k4RowIn Qp).length := List.length_map _
      rw [spent_same, spentOf_row Bk _ _ _ _ 0 c hl, eL] at h0
      exact h0
  · cases hy

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Takes_three
#print axioms ProofFile.Honest.K4.W.mask_lookup_some
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_val
