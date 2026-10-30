-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshColumns.lean: kind K14: OF WHAT THE COLUMNS OF THE TREES OF
"send o_omega" ARE MADE (columnOf, sentTables: Honest/K14/Sendings.lean, at jobOmega): of o_omega's
main rows and their tails, and, in the tree that holds o_sp, of ONE element of the field: the symbol
of o_sp's mask row at the position modulo the mask code's length.

  column_congr    **two families of rows have the same column of a tree at a position**, where
                  o_omega's main rows and tails agree and, if the tree holds o_sp, the symbols of
                  o_sp's two rows at that position agree in the field
  shown_tables_congr   a list of tables, each made of a member of a list and its number, as
                  sentTables makes them of the trees' shapes: what is shown of them at asked
                  positions, in the form in which the frame's shownOf
                  (Honest/Side.lean) lists it, is the same where the tables' columns at these
                  positions are. General: no sending is named
  sent_shown_congr   so for a sending's tables, from its trees' columns

What is assumed. The shape splits; o_omega has no mask row; SpShape.
What is not claimed. Nothing on how coins are sampled. Nothing on roots or paths. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshRows
import Johnson.Desc.ProofFile.Honest.K14.FreshSymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E Codes OracleNotice)
open OnBytes.Slice (readE ofE codeOf)
open Johnson.Prover.Link (symG words3)
open Desc.K14.Honest (SpShape)

/-- **The column of a tree at a position, of two families of rows.** -/
theorem column_congr (A : SendPub) {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (hz : A.P.S.omega.maskRows = 0) (H : SpShape A.P.codes A.P.S n) (L L' : Nat → Laid)
    (tree x : Nat) (hm : ∀ r j, (L 0).main r j = (L' 0).main r j)
    (ht : ∀ r q, r < A.P.S.omega.mainRows →
      q < (A.P.codes.base.getD A.P.S.omega.code default).r →
      (L 0).mainTail r q = (L' 0).mainTail r q)
    (hsp : ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
        (jobOmega A).Q.sent).getD {}).tree[1]? = some tree →
      symG (codeOf (spMaskCode A)) (x % 2 ^ (spMaskCode A).logN)
          (fun j => readE ((L 1).mask 0 j)) (fun q => readE ((L 1).maskTail 0 q)) =
        symG (codeOf (spMaskCode A)) (x % 2 ^ (spMaskCode A).logN)
          (fun j => readE ((L' 1).mask 0 j)) fun q => readE ((L' 1).maskTail 0 q)) :
    columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent L tree x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent L' tree x := by
  have two : ∀ k, k ∈ (List.range (jobOmega A).Q.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
        (jobOmega A).Q.sent).getD {}).tree[k]? == some tree) →
      (k = 0 ∨ k = 1) ∧ ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
        (jobOmega A).Q.sent).getD {}).tree[k]? = some tree := fun k hk => by
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hk
    have h3 : k < (jobOmega A).Q.sent.size := List.mem_range.1 h1
    rw [omega_sent A hs] at h3
    have h4 : k < 2 := h3
    exact ⟨by omega, by simpa using h2⟩
  unfold columnOf
  refine congrArg₂ (· ++ ·) (List.flatMap_congr fun k hk => ?_)
    (List.flatMap_congr fun k hk => ?_)
  · show symbolsOf ((jobOmega A).Q.codes.base.getD
        ((jobOmega A).Q.sent.getD k default).shape.code default) x
        ((jobOmega A).Q.sent.getD k default).shape.mainRows (L k).main (L k).mainTail =
      symbolsOf ((jobOmega A).Q.codes.base.getD
        ((jobOmega A).Q.sent.getD k default).shape.code default) x
        ((jobOmega A).Q.sent.getD k default).shape.mainRows (L' k).main (L' k).mainTail
    rcases (two k hk).1 with rfl | rfl
    · rw [omega_shape0 A hs]
      exact symbolsOf_congr _ _ _ _ _ _ _ (fun r _ j _ => hm r j) fun r hr q hq => ht r q hr hq
    · rw [omega_shape1 A hs, H.noMain]
      rfl
  · show symbolsOf ((jobOmega A).Q.codes.mask.getD
        ((jobOmega A).Q.sent.getD k default).shape.maskCode default)
        (x % 2 ^ ((jobOmega A).Q.codes.mask.getD
          ((jobOmega A).Q.sent.getD k default).shape.maskCode default).logN)
        ((jobOmega A).Q.sent.getD k default).shape.maskRows (L k).mask (L k).maskTail =
      symbolsOf ((jobOmega A).Q.codes.mask.getD
        ((jobOmega A).Q.sent.getD k default).shape.maskCode default)
        (x % 2 ^ ((jobOmega A).Q.codes.mask.getD
          ((jobOmega A).Q.sent.getD k default).shape.maskCode default).logN)
        ((jobOmega A).Q.sent.getD k default).shape.maskRows (L' k).mask (L' k).maskTail
    obtain ⟨h01, htree⟩ := two k hk
    rcases h01 with rfl | rfl
    · rw [omega_shape0 A hs, hz]
      rfl
    · rw [omega_shape1 A hs, H.oneRow, symbolsOf_one, symbolsOf_one]
      exact congrArg (fun y => words3 (ofE y)) (hsp htree)

/-- **What is shown, at asked positions, of tables that are each made of a member of a list and its
number.** -/
theorem shown_tables_congr {α : Type} (l : List α) (f f' : α × Nat → Table)
    (ask : Nat → List Nat) (h : ∀ t, ∀ p ∈ ask t.2, (f t).col p = (f' t).col p) :
    (((l.zipIdx.map f).map some).zipIdx.map fun y =>
        match y.1 with
        | some t => (ask y.2).map fun p => (p, t.col p)
        | none => []) =
      ((l.zipIdx.map f').map some).zipIdx.map fun y =>
        match y.1 with
        | some t => (ask y.2).map fun p => (p, t.col p)
        | none => [] := by
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  cases l[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Function.comp_apply, Nat.zero_add]
    exact congrArg some (List.map_congr_left fun p hp => by rw [h (a, i) p hp])

/-- **What is shown of a sending's tables**, from its trees' columns. -/
theorem sent_shown_congr (codes : Codes) (sent : Array OracleNotice) (L L' : Nat → Laid)
    (ask : Nat → List Nat)
    (h : ∀ tree, ∀ p ∈ ask tree, columnOf codes sent L tree p = columnOf codes sent L' tree p) :
    (((sentTables codes sent L).map some).zipIdx.map fun y =>
        match y.1 with
        | some t => (ask y.2).map fun p => (p, t.col p)
        | none => []) =
      ((sentTables codes sent L').map some).zipIdx.map fun y =>
        match y.1 with
        | some t => (ask y.2).map fun p => (p, t.col p)
        | none => [] := by
  unfold sentTables
  refine shown_tables_congr _ _ _ ask fun t p hp => ?_
  unfold Table.col
  simp only [h t.2 p hp]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.column_congr
#print axioms ProofFile.Honest.K14.shown_tables_congr
#print axioms ProofFile.Honest.K14.sent_shown_congr
