-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ItemsOfRows.lean: the kind "the code switch" (K2): FROM "EVERY
ROW OF THE NEW GROUP's LIST SAYS ITS CLAIM OF THE WITNESS's WORDS" TO THE TABLE OF JOINTS' TWO ITEMS
ON CLASSES OF ROWS ("row m carried" · "row m position", as the layer `rowSays` fills them:
Johnson/Desc/First/Close/Law/FillRow.lean). Two statements with their proofs; no definition. No
prover, no coin, no thread.

  `items_of_rows` the new group's list behind is c₀ :: samples ++ gens, in two stretches · the
                    table's `rowsAt` at the two classes are these stretches · `N.groupAt m` is the
                    group's number · every row of the list says its claim ⊢ the two items hold at
                    the state behind
  `yes_items_of_rows` the same at a yes of the kind's own decision (`AtYes`,
                    Johnson/Top/H0/K2Hears/Whole.lean): every row that the switch made says its
                    claim at the state behind ⊢ the two items

THE OTHER WAY ROUND OF THE LIBRARY's `rows_say_all` AND `yes_rows_say`
(Johnson/Top/H0/Tw/K2C/RowsSayAll.lean): the same letters and the same premises on the state and the
numbers; their two items are this file's ends, their end is its last premise. The numbers' equations
stand in the form that the library gives them there (two fields of `SwitchDebts`,
K2C/HandsCore.lean). By: `rowSays_list` (FillRow.lean) · `yes_row_classes` (K2C/RowsClasses.lean).

Limits. That the rows say their claims is a premise: shown of no rows here. KeptPos, that the group
had no open row in front, and the three equations on the table's numbers are premises. At the state
behind the kind's own decision: nothing on what a place's block lays behind it. Nothing on any
property.
-/
import Johnson.Top.H0.Tw.K2C.RowsSayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers rowSays rowSays_list)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos frameAt keptSamples targetRows
  yes_row_classes)

variable {P W : Type}

/-- **From the rows to the two items.** -/
theorem items_of_rows (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
    (s' : S) (y : Strs) (w : W) {G' : Group} {c₀ : OnBytes.Row} {samples gens : List OnBytes.Row}
    (hG : s'.st.groups[N.groupAt m]? = some G')
    (hrows : G'.rows = (c₀ :: samples ++ gens).toArray)
    (h5 : (List.range (1 + samples.length)).filterMap (fun j => G'.rows[0 + j]?) =
      c₀ :: samples)
    (h6 : (List.range gens.length).filterMap (fun j => G'.rows[1 + samples.length + j]?) = gens)
    (hc : N.rowsAt m .carried = (0, 1 + samples.length))
    (hp : N.rowsAt m .position = (1 + samples.length, gens.length))
    (h : ∀ r ∈ G'.rows.toList, Says rdE s'.st r (words (z, s') y w)) :
    rowSays N words m .carried (z, s') y w ∧ rowSays N words m .position (z, s') y w := by
  refine ⟨(rowSays_list N words m .carried rfl (z, s') y w).2 ?_,
    (rowSays_list N words m .position rfl (z, s') y w).2 ?_⟩
  · simp only [hG, hc]
    rw [h5]
    intro r hr
    refine h r ?_
    rw [hrows]
    exact List.mem_append_left _ hr
  · simp only [hG, hp]
    rw [h6]
    intro r hr
    refine h r ?_
    rw [hrows]
    exact List.mem_append_right _ hr

/-- **The same at a yes of the kind's own decision.** -/
theorem yes_items_of_rows (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
    (yy : Strs) (w : W) {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hk : KeptPos x.T) (hf : G.rows = #[])
    (hg : N.groupAt m = x.f.group)
    (hc : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + keptSamples x W₀))
    (hp : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .position =
      (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)))
    (h : ∀ r ∈ rows, Says rdE s'.st r (words (z, s') yy w)) :
    rowSays N words m .carried (z, s') yy w ∧ rowSays N words m .position (z, s') yy w := by
  obtain ⟨W₀, c₀, samples, gens, G', h1, h2, h3, h4, h5, h6, h7, h8⟩ := yes_row_classes A hk hf
  refine items_of_rows N words m z s' yy w (by rw [hg]; exact h2) h3 h5 h6
    (by rw [hc W₀ h1, h7]) (by rw [hp W₀ h1, h7, h8]) fun r hr => h r ?_
  rw [h3] at hr
  rw [h4]
  exact hr

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.items_of_rows
#print axioms ProofFile.Honest.K2.Law.yes_items_of_rows
