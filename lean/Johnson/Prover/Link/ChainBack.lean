-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainBack.lean: FROM A FOLD's YES OVER SOME BLOCKS BACK TO THE BLOCKS' DECISIONS
IN A ROW (Walks, Johnson/Prover/Link/ChainDefs.lean): the converse of fold_of_walks (ChainYes.lean).
General in the blocks. Statements and proofs.

  colsFor_split   the converse of colsFor_app (ChainYes.lean): columns looked up along two lists in
                  a row are those of the first, then those of the second. (The library's
                  colsFor_append, Johnson/Desc/Plain/OneYes.lean, says of the first part its length
                  and its positions and columns; here: that it is colsFor's own value.)
  walks_of_fold   where the fold over some blocks goes through all its rounds, on columns that begin
                  with those looked up by key along groupsOf's list: Walks. What lies behind these
                  columns, and what is left of them, is free
  walks_congr     Walks reads of a block its rounds and its decide alone

By: Block.step_ok, foldBlocks_cons_ok (Johnson/Desc/RunLaws.lean); groupsOf_app
(Johnson/Top/H0/StepLaws/StepLaws.lean); regroup_colsFor (OneYes.lean).

Limits. The fold's yes is a premise. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (readG colsFor regroup_colsFor)

/-- The converse of colsFor_app. -/
theorem colsFor_split (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (g r : List (ℕ × ℕ × ℕ)) (cs : List OpenedColumn), colsFor L (g ++ r) = some cs →
      ∃ c₁ c₂, colsFor L g = some c₁ ∧ colsFor L r = some c₂ ∧ cs = c₁ ++ c₂
  | [], _, cs, h => ⟨[], cs, rfl, h, rfl⟩
  | w :: g, r, cs, h => by
    have h' : (match L w.1 w.2.1, colsFor L (g ++ r) with
      | some c, some cs => some ((w.1, w.2.1, c) :: cs)
      | _, _ => none) = some cs := h
    cases hL : L w.1 w.2.1 with
    | none =>
      rw [hL] at h'
      cases h'
    | some c =>
      cases hr : colsFor L (g ++ r) with
      | none =>
        rw [hL, hr] at h'
        cases h'
      | some cs' =>
        rw [hL, hr] at h'
        obtain rfl := Option.some.inj h'
        obtain ⟨c₁, c₂, k1, k2, rfl⟩ := colsFor_split L g r cs' hr
        refine ⟨(w.1, w.2.1, c) :: c₁, c₂, ?_, k2, rfl⟩
        show (match L w.1 w.2.1, colsFor L g with
          | some c, some cs => some ((w.1, w.2.1, c) :: cs)
          | _, _ => none) = _
        rw [hL, k1]

variable {S Cl : Type}

/-- **From the fold's yes to the blocks' decisions in a row.** -/
theorem walks_of_fold (ft : ℕ) (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (bs : List (Block S Cl)) (s e : S) (rs : List Fmt.RoundView) (c more left : List OpenedColumn),
      colsFor L ((groupsOf ft (bs.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id) = some c →
      foldBlocks ft bs s rs (c ++ more) = .ok (e, [], left) → Walks ft L bs s rs e
  | [], s, e, rs, c, more, left, _, hf => by
    have h := Except.ok.inj hf
    exact ⟨congrArg (·.2.1) h, (congrArg (·.1) h).symm⟩
  | b :: l, s, e, rs, c, more, left, hc, hf => by
    obtain ⟨-, s', k, hstep, hrest⟩ := foldBlocks_cons_ok.1 hf
    obtain ⟨-, -, hd, hk⟩ := Block.step_ok.1 hstep
    rw [List.flatMap_cons, groupsOf_app, ← List.map_take, ← List.map_drop,
      List.flatMap_append] at hc
    obtain ⟨c₁, c₂, k1, k2, rfl⟩ := colsFor_split L _ _ c hc
    have hlen : c₁.length = k := by
      obtain ⟨a, b', kb, e', k3, -⟩ :=
        VerifiableInference.Desc.Plain.One.colsFor_append L _ [] c₁
          (by rw [List.append_nil]; exact k1)
      have hb : b' = [] := (Option.some.inj kb).symm
      rw [hk, e', hb, List.append_nil, k3]
    subst hlen
    rw [List.append_assoc, List.take_left' rfl, regroup_colsFor L _ c₁ k1] at hd
    rw [List.append_assoc, List.drop_left' rfl] at hrest
    exact ⟨s', hd, walks_of_fold ft L l s' e _ c₂ more left k2 hrest⟩

/-- Walks reads of a block its rounds and its decide alone. -/
theorem walks_congr (ft : ℕ) (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (bs bs' : List (Block S Cl)) (s e : S) (rs : List Fmt.RoundView),
      List.Forall₂ (fun b b' => b.rounds = b'.rounds ∧ b.decide = b'.decide) bs bs' →
      Walks ft L bs s rs e → Walks ft L bs' s rs e
  | [], [], _, _, _, _, h => h
  | b :: l, b' :: l', s, e, rs, hh, h => by
    cases hh with
    | cons h1 h2 =>
      obtain ⟨s', hd, hw⟩ := h
      rw [h1.1, h1.2] at hd
      rw [h1.1] at hw
      exact ⟨s', hd, walks_congr ft L l l' s' e _ h2 hw⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.colsFor_split
#print axioms Johnson.Prover.Link.walks_of_fold
#print axioms Johnson.Prover.Link.walks_congr
