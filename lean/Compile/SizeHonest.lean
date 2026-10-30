-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SizeHonest.lean: three lemmas on lists.

  `length_filterMap_le_filter`
                               If F a = some b only where φ a = true, then l.filterMap F has at most
                               the length of l.filter φ.
  `length_entriesE_le`         If only read positions are opened, and all read positions are in the
                               finite set A, the list of the opened external positions (`entriesE`,
                               Compile/Size.lean) has at most A.card entries (under `we.OK`).
  `forall_mem_pair`            What is true of a and of b is true of every member of [a, b].

Limits: it does not prove a bound on the size of a key or a proof of the honest committer and
prover.
-/
import Compile.Size
import Compile.CompleteStrict

set_option autoImplicit false

noncomputable section

namespace Compile.SizeH
open Iop Rom Compile.Cmpl

variable {I X : Type} {lam K : ℕ}

/-! ("Nothing is opened that is not read" is in Compile/Batch/CompleteStrict.lean:
tri_opensB_only, tri_opensExtB_only.) -/

/-! ## Counting opened positions -/

theorem length_filterMap_le_filter
    {α β : Type} (F : α → Option β) (φ : α → Bool) (h : ∀ a b, F a = some b → φ a = true) :
    ∀ l : List α, (l.filterMap F).length ≤ (l.filter φ).length
  | [] => Nat.le_refl _
  | a :: l => by
      have ih := length_filterMap_le_filter F φ h l
      cases hF : F a with
      | none =>
        rw [List.filterMap_cons_none hF]
        exact le_trans ih (List.Sublist.filter _ (List.sublist_cons_self a l)).length_le
      | some b =>
        rw [List.filterMap_cons_some hF, List.filter_cons_of_pos (h a b hF),
          List.length_cons, List.length_cons]
        exact Nat.succ_le_succ ih

theorem length_entriesE_le {E : ExtSpec} {we : WireE E} (hw : we.OK)
    (g : E.Pos → Option (Opening lam E.Sym)) (isR : E.Pos → Bool)
    (hg : ∀ p op, g p = some op → isR p = true) (A : Finset E.Pos)
    (hA : ∀ p, isR p = true → p ∈ A) :
    (entriesE we g).length ≤ A.card := by
  refine le_trans (length_filterMap_le_filter _ isR (fun p e he => ?_) _)
    (length_filter_le_card _ hw.nodup isR A hA)
  obtain ⟨op, hop, -⟩ := Option.map_eq_some_iff.1 he
  exact hg p op hop



/-! ## Pairs -/

section Scheme

variable (p : Params)


variable {Z}

theorem forall_mem_pair {α : Type} {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    ∀ x ∈ [a, b], P x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · cases hx


end Scheme

end Compile.SizeH
