-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawWide.lean: THE SMALLNESS TEST: THE READING OF THE CARRIED RECORD THAT MUST
STAY FROM THE DRAW OF THE MATRIX TO THE RUN THAT SPENDS IT: ALL THAT THE LAW'S LETTERS READ OFF THE
RECORD.

The count of the round of the draw binds, outside the drawn matrix, a tuple of messages and an
explicit statement. At the library's letters these read off the smallness test's record: the weights
(the closed list's tables), the sizes (the number of matrices, the matrices, the number of
combinations, the list's shapes) and the cut of the messages itself (the symbol arrays' numbers, the
arrays' index). The run that spends them, "K8.equations", is called later, at the link's batching.
  `wide s`: WITH CODE: these fields of the record in s: `Ready.seven`
    (Johnson/Desc/First/K8/Cond.lean: the symbol arrays' numbers, the arrays' index whole, the
    digits' two numbers of columns, the number of matrices, the shapes, the matrices), the number of
    combinations, the mark "closed" and the list of tables.
  `wideM s`: `wide s` WITH THE DRAWN MATRIX (the record's `cfF`, `cfFirst`), which the block of the
    draw lays: it must stay from BEHIND the draw.
  `wide_congr`: two records with the same `wide` have the same sizes (`sizeOf`), the same cut
    (`early`, at every address), the same arrays (`Named.arrays`), the same closed list, the same
    numbers of the symbol arrays and the same index of the arrays.
  `leaves_wide_of_tl`: a block that leaves the smallness test's record leaves `wide`.
  `wide_putTl`: laying a record that agrees in these fields leaves `wide`.
  `hear_leaves_wide`: **the block of the draw leaves it.**
  `foldLeavesWide`: so does a fold over blocks each of which leaves it.
Definitions, statements and proofs.
Limits. THAT A GIVEN BLOCK BETWEEN THE DRAW AND THE BATCHING, OR A RUN OF CLAIMS AHEAD OF
"K8.equations" IN A LINK'S ORDER, LEAVES `wide` IS THAT BLOCK'S OR RUN'S OWN LAW: shown here of the
block of the draw alone. `recOf` whole is NOT claimed to stay: other fields of the record are turned
behind the draw. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Cond
import Johnson.Desc.First.K8.LawEarly
import Johnson.Desc.First.K8.LawSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model

/-- What the law's letters read off the smallness test's record. -/
def wideOf (tl : HTailF2) := (Ready.seven tl, tl.tau, tl.funClosed, tl.funs)

/-- That, of the record in the carried record. -/
def wide (s : S) := s.tl?.map wideOf

/-- The same with the drawn matrix: as one sequence, and each matrix's first column. -/
def wideMOf (tl : HTailF2) := (wideOf tl, tl.cfF, tl.cfFirst)

/-- That, of the record in the carried record. -/
def wideM (s : S) := s.tl?.map wideMOf

/-- **Two records with the same reading**: the same sizes, the same cut, the same arrays, the same
closed list. -/
theorem wide_congr {tl tl' : HTailF2} (h : wideOf tl = wideOf tl') :
    OnBytes.Tie.Pv.Tail.sizeOf tl = OnBytes.Tie.Pv.Tail.sizeOf tl' ∧
      (∀ a, OnBytes.Tie.Pv.Tail.early tl a = OnBytes.Tie.Pv.Tail.early tl' a) ∧
      Named.arrays tl = Named.arrays tl' ∧ tl.funClosed = tl'.funClosed ∧ tl.funs = tl'.funs ∧
      tl.gtTree = tl'.gtTree ∧ tl.ix = tl'.ix := by
  simp only [wideOf, Ready.seven, Prod.mk.injEq] at h
  obtain ⟨⟨a1, a2, _, _, a5, _, a7⟩, a8, a9, a10⟩ := h
  refine ⟨?_, fun a => ?_, ?_, a9, a10, a1, a2⟩
  · unfold OnBytes.Tie.Pv.Tail.sizeOf
    rw [a5, a7, a8, a10]
  · unfold OnBytes.Tie.Pv.Tail.early
    rw [a1, a2]
  · unfold Named.arrays
    rw [a1, a2]

/-- A block that leaves the smallness test's record leaves the reading. -/
theorem leaves_wide_of_tl {Cl : Type} {b : Block S Cl} (h : b.Leaves S.tl?) : b.Leaves wide :=
  fun s rs gs s' hd => by
    unfold wide
    rw [h s rs gs s' hd]

/-- Laying a record that agrees in these fields leaves the reading. -/
theorem wide_putTl (s : S) (tl tl' : HTailF2) (ht : s.tl? = some tl) (h : wideOf tl' = wideOf tl) :
    wide (s.putTl tl') = wide s := by
  unfold wide
  rw [putTl_tl s tl tl' ht, ht, Option.map_some, Option.map_some, h]

/-- **The block of the draw leaves it.** -/
theorem hear_leaves_wide {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves wide := by
  intro s rs gs s' hd
  obtain ⟨r, rfl⟩ := decide_one atS p s s' rs gs hd
  obtain ⟨tl, ht, hm⟩ := (decide_atS_iff p s s' r gs).1 hd
  rw [hm.2.2.2.2.2.2.2.2]
  exact wide_putTl s tl _ ht rfl

/-- A fold over blocks each of which leaves it. -/
theorem foldLeavesWide {Cl : Type} (ft : Nat) (l : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List Col) (out : S × List Fmt.RoundView × List Col) (hl : ∀ b ∈ l, b.Leaves wide)
    (H : foldBlocks ft l s rs cols = .ok out) : wide out.1 = wide s :=
  foldLeaves S Cl _ wide ft l s rs cols out hl H

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.wide_congr
#print axioms VerifiableInference.Desc.First.K8.wide_putTl
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_wide
#print axioms VerifiableInference.Desc.First.K8.foldLeavesWide
