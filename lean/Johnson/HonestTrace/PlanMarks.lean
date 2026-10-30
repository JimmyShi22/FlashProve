-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlanMarks.lean

Four fields of the entries of the verifier's plans' lists of matrices (TMat,
OnBytes/Model/Frame.lean: name, kind, aId, ttOff), as a function of the segment and the matrix's
name; and the condition that the plans of a public part X have them.

Main definitions:
* "idOf": the identifier of a segment's sub-proof: 1 + g for group g's feed-forward segment, 13 for
  the head, 14 + g for group g's attention segment.
* "markOf σ μ": the label of μ; 1 if another segment owns the matrix (Sz.ref.owner,
  Johnson/HonestTrace/Places.lean), else 0; 256 times the owner's identifier plus the matrix's
  number in the owner's list; 0.
* "PlanMarks X": X.p4 = true, X.NGr = 12, and for every k and σ with Seg.ofNo 12 k = some σ: the
  list of (name, kind, aId, ttOff) over planMats X k is the list of markOf σ over MatName.all 3 1 1
  4 σ.

Main theorems: "marks_ff", "marks_att", "marks_head": the list of markOf σ over MatName.all 3 1 1 4
σ, written out, for a group (9 entries; the last by cases on g = 0), an attention sub-proof (5) and
the head (8).

Limits. idOf and markOf are typed after a reading of the routines that make the lists (tailsOf,
OnBytes/Model/LayerPlan.lean; matrices, OnBytes/Model/AttentionPlan.lean; matsH,
OnBytes/Model/HeadPlan.lean), at 12 groups and the numbers of parts 3, 1, 1, 4. PlanMarks is a
condition: it is shown here of no X (for public files in scope:
Johnson/Goal/HonestTrace/PlanMarksInScope.lean, which also compares idOf and markOf's identifiers
with terms of the library). The entries' other fields (rows, columns, foreign, wp) are not among the
four.

Not claimed: anything on a prover or on what a verifier accepts.

-/
import Johnson.HonestTrace.Full
import Johnson.HonestTrace.Places

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

/-- The identifier of a segment's sub-proof in the plans' marks, at 12 groups: 1 + g for group g's
feed-forward segment, 13 for the head, 14 + g for group g's attention segment. -/
def idOf : Seg → ℕ
  | .ff g => 1 + g
  | .head => 13
  | .att g => 14 + g

/-- **The four marks of an entry of a plan's list**, of the segment and the name: the name's label;
1 if another segment owns the matrix (Sz.ref.owner), else 0; 256 times the owner's identifier plus
the number of the matrix in the owner's list, at the numbers of parts 3, 1, 1, 4; and 0. They are
meant for the fields name, kind, aId and ttOff of TMat (OnBytes/Model/Frame.lean). -/
def markOf (σ : Seg) (μ : MatName) : String × ℕ × ℕ × ℕ :=
  (μ.label, if Sz.ref.owner σ μ = (σ, μ) then 0 else 1,
    idOf (Sz.ref.owner σ μ).1 * 256 +
      (MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).getD 0, 0)

/-- **The plans' lists bear the marks**: X has attention and 12 groups, and in the plan of each of
the 25 sub-proofs the entries' names, kinds, identifiers and first columns are, in the list's order,
markOf at the names of the segment's list. -/
structure PlanMarks (X : Model.Verify.Public) : Prop where
  /-- attention sub-proofs stand between the groups' -/
  p4 : X.p4 = true
  /-- twelve groups -/
  groups : X.NGr = 12
  /-- the four marks, list by list -/
  marks : ∀ k σ, Seg.ofNo 12 k = some σ →
    (planMats X k).toList.map (fun M => (M.name, M.kind, M.aId, M.ttOff)) =
      (MatName.all 3 1 1 4 σ).map (markOf σ)

/-! ## The marks, list by list -/

/-- The marks at the names of a group's list. -/
theorem marks_ff (g : ℕ) : (MatName.all 3 1 1 4 (.ff g)).map (markOf (.ff g)) =
    [("af0", 0, (1 + g) * 256 + 0, 0), ("af1", 0, (1 + g) * 256 + 1, 0),
      ("af2", 0, (1 + g) * 256 + 2, 0), ("ad0", 0, (1 + g) * 256 + 3, 0),
      ("ar", 0, (1 + g) * 256 + 4, 0), ("b", 0, (1 + g) * 256 + 5, 0),
      ("qa", 0, (1 + g) * 256 + 6, 0), ("xbO", 0, (1 + g) * 256 + 7, 0),
      if g = 0 then ("xbI", 0, (1 + g) * 256 + 8, 0) else ("xbI", 1, g * 256 + 7, 0)] := by
  have e : MatName.all 3 1 1 4 (.ff g) =
      [.af 0, .af 1, .af 2, .ad 0, .ar, .b, .qa, .xbO, .xbI] := rfl
  rw [e]
  have own : ∀ (μ : MatName) (n : ℕ), Sz.ref.owner (.ff g) μ = (.ff g, μ) →
      MatName.no? 3 1 1 4 (.ff g) μ = some n →
      markOf (.ff g) μ = (μ.label, 0, (1 + g) * 256 + n, 0) := by
    intro μ n h1 h2
    unfold markOf
    rw [h1, if_pos rfl, h2]
    rfl
  simp only [List.map_cons, List.map_nil]
  rw [own (.af 0) 0 rfl rfl, own (.af 1) 1 rfl rfl, own (.af 2) 2 rfl rfl, own (.ad 0) 3 rfl rfl,
    own .ar 4 rfl rfl, own .b 5 rfl rfl, own .qa 6 rfl rfl, own .xbO 7 rfl rfl]
  by_cases h0 : g = 0
  · subst h0
    rfl
  · have ho : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := by
      show (if g = 0 then _ else _) = _
      rw [if_neg h0]
    have hx : markOf (.ff g) .xbI = ("xbI", 1, g * 256 + 7, 0) := by
      unfold markOf
      rw [ho, if_neg (by simp)]
      show ("xbI", 1, (1 + (g - 1)) * 256 + 7, 0) = _
      rw [show 1 + (g - 1) = g by omega]
    rw [hx, if_neg h0]
    rfl

/-- The marks at the names of an attention sub-proof's list. -/
theorem marks_att (g : ℕ) : (MatName.all 3 1 1 4 (.att g)).map (markOf (.att g)) =
    [("as0", 0, (14 + g) * 256 + 0, 0), ("ah", 0, (14 + g) * 256 + 1, 0),
      ("ao", 0, (14 + g) * 256 + 2, 0), ("bA", 0, (14 + g) * 256 + 3, 0),
      ("qa", 1, (1 + g) * 256 + 6, 0)] := by
  have e : MatName.all 3 1 1 4 (.att g) = [.as 0, .ah, .ao, .bA, .qa] := rfl
  rw [e]
  have own : ∀ (μ : MatName) (n : ℕ), Sz.ref.owner (.att g) μ = (.att g, μ) →
      MatName.no? 3 1 1 4 (.att g) μ = some n →
      markOf (.att g) μ = (μ.label, 0, (14 + g) * 256 + n, 0) := by
    intro μ n h1 h2
    unfold markOf
    rw [h1, if_pos rfl, h2]
    rfl
  have hq : markOf (.att g) .qa = ("qa", 1, (1 + g) * 256 + 6, 0) := by
    unfold markOf
    have ho : Sz.ref.owner (.att g) .qa = (.ff g, .qa) := rfl
    rw [ho, if_neg (by simp)]
    rfl
  simp only [List.map_cons, List.map_nil]
  rw [own (.as 0) 0 rfl rfl, own .ah 1 rfl rfl, own .ao 2 rfl rfl, own .bA 3 rfl rfl, hq]
  rfl

/-- The marks at the names of the head's list. -/
theorem marks_head : (MatName.all 3 1 1 4 .head).map (markOf .head) =
    [("hf0", 0, 13 * 256 + 0, 0), ("hf1", 0, 13 * 256 + 1, 0), ("hf2", 0, 13 * 256 + 2, 0),
      ("hf3", 0, 13 * 256 + 3, 0), ("hd", 0, 13 * 256 + 4, 0), ("hr", 0, 13 * 256 + 5, 0),
      ("bH", 0, 13 * 256 + 6, 0), ("xbL", 1, 12 * 256 + 7, 0)] := by
  decide

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.marks_ff
#print axioms OnBytes.HonestTrace.marks_att
#print axioms OnBytes.HonestTrace.marks_head
