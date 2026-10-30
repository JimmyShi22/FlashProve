-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/RowsSayAll.lean: code switching (the kind K2): FROM THE TABLE OF JOINTS' TWO
ITEMS ON CLASSES OF ROWS («row m carried» · «row m position», as the layer rowSays fills them:
Johnson/Desc/First/Close/Law/FillRow.lean) TO «EVERY ROW OF THE NEW GROUP's LIST SAYS ITS CLAIM OF
THE WITNESS's WORDS». For the tie t3 (the premise hrow of rowsHoldT_of_says, its first half). NO
BLOCK IMPORTS THIS FILE.
  rows_say_all   the new group's list behind is c₀ :: samples ++ gens, in two stretches (what
                 yes_row_classes gives at an accept, K2C/RowsClasses.lean) · the table's rowsAt at
                 the two classes are these stretches (the two debts «carried» | «position» of
                 K2.SwitchDebts) · N.groupAt m is the group's number · the two items hold at the
                 state behind ⟹ every row of the list says its claim
  yes_rows_say   the same at an accept (AtYes), with the debts in K2.SwitchDebts' own letters
No soundness is claimed.
-/
import Johnson.Desc.First.Close.Law.FillRow
import Johnson.Top.H0.Tw.K2C.RowsClasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc (Strs)

variable {P W : Type}

theorem rows_say_all (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
    (s' : S) (y : Strs) (w : W) {G' : Group} {c₀ : OnBytes.Row} {samples gens : List OnBytes.Row}
    (hG : s'.st.groups[N.groupAt m]? = some G')
    (hrows : G'.rows = (c₀ :: samples ++ gens).toArray)
    (h5 : (List.range (1 + samples.length)).filterMap (fun j => G'.rows[0 + j]?) =
      c₀ :: samples)
    (h6 : (List.range gens.length).filterMap (fun j => G'.rows[1 + samples.length + j]?) = gens)
    (hc : N.rowsAt m .carried = (0, 1 + samples.length))
    (hp : N.rowsAt m .position = (1 + samples.length, gens.length))
    (i1 : rowSays N words m .carried (z, s') y w)
    (i2 : rowSays N words m .position (z, s') y w) :
    ∀ r ∈ G'.rows.toList, Says rdE s'.st r (words (z, s') y w) := by
  have j1 := (rowSays_list N words m .carried rfl (z, s') y w).1 i1
  have j2 := (rowSays_list N words m .position rfl (z, s') y w).1 i2
  simp only [hG, hc, hp] at j1 j2
  rw [h5] at j1
  rw [h6] at j2
  intro r hr
  rw [hrows] at hr
  rcases List.mem_append.1 hr with h | h
  · exact j1 r h
  · exact j2 r h

theorem yes_rows_say (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
    (yy : Strs) (w : W) {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hk : KeptPos x.T) (hf : G.rows = #[])
    (hg : N.groupAt m = x.f.group)
    (hc : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + keptSamples x W₀))
    (hp : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .position =
      (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)))
    (i1 : rowSays N words m .carried (z, s') yy w)
    (i2 : rowSays N words m .position (z, s') yy w) :
    ∃ G', s'.st.groups[x.f.group]? = some G' ∧ G'.rows = rows.toArray ∧
      ∀ r ∈ G'.rows.toList, Says rdE s'.st r (words (z, s') yy w) := by
  obtain ⟨W₀, c₀, samples, gens, G', h1, h2, h3, h4, h5, h6, h7, h8⟩ := yes_row_classes A hk hf
  refine ⟨G', h2, by rw [h3, h4], ?_⟩
  exact rows_say_all N words m z s' yy w (by rw [hg]; exact h2) h3 h5 h6
    (by rw [hc W₀ h1, h7]) (by rw [hp W₀ h1, h7, h8]) i1 i2

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.rows_say_all
#print axioms VerifiableInference.Desc.First.K2.yes_rows_say
