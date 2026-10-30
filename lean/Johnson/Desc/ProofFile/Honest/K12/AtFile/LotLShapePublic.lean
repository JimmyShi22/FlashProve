-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapePublic.lean

It states no goal. No property of the protocol is claimed.

THE PUBLIC PREMISES OF «finish_lays» (LotLShapeFinish.lean) AS
ONE TEST WITH CODE ON THE REQUEST's SHAPE AND THE CODES, the law from that test, and the closed line at the written
shape and codes.

  (`targetOfShape`, `maskNoticeOfShape`, `treesOfFinish`: LotLShapePublicTerms.lean)
  `finishPublicB`          the test: the groups' list has the last test's; its target has no kept member, its shape no
                           mask row and an answer; the carrier and the mask sit in one new tree at parts 0 and 1
  `finish_lays_of_public`  «finish_lays» from the test, where the frame's groups are the shape's
  `finish_public_written`  THE CLOSED LINE, by Lean's kernel; `finish_mask_not_at_part_zero`: its control
  `finish_values_written`  the written values of what is laid, by Lean's kernel: the two codes of the group; the carrier's
                           shape; its pad; with a control

IMPORTS OF Johnson.Top.H0.*: none by name (through LotLShapeFinish.lean: see its head).

Limits. The full size alone for the closed lines. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeFinish
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapePublicTerms
import Johnson.Desc.ReqLit.Full
import Johnson.G.PackLit
import Johnson.Loose.H2K12.ClosedOfPins354

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.LotL
open OnBytes (OracleNotice TreeShape TreeLay SwitchTarget Codes foldMaskNotice ioppFoldShape reqGroups
  singleRowsOracles)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc (Block Own.treesMade Own.padMade)
open VerifiableInference.Desc.Ground.Sh (stSh bookSh freshOrc)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2)

/-- **The test.** -/
def finishPublicB (shape : ReqShape) (codes : Codes) : Bool :=
  decide (shape.link.length < (reqGroups shape).size) && (targetOfShape shape).kept.isEmpty &&
    (targetOfShape shape).shape.maskRows == 0 && (targetOfShape shape).shape.answers != 0 &&
    (treesOfFinish shape codes).any fun lay =>
      lay.shapes.size == 1 && lay.tree.getD 0 0 == 0 && lay.tree.getD 1 0 == 0 &&
        lay.part.getD 0 0 == 0 && lay.part.getD 1 0 == 1

/-- **«finish_lays» from the test.** -/
theorem finish_lays_of_public (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (accept : (finishPlace p : Block S Unit).decide s rs gs = .ok s')
    (groups : s.check.frame.groups = reqGroups s.check.frame.shape)
    (isPublic : finishPublicB s.check.frame.shape s.st.codes = true)
    (oldBelow : ∀ o ∈ (singleRowsOracles s.check.frame.rows).toList, o < s.book.place.size)
    (placesBelow : ∀ (i : ℕ) (q : ℕ × ℕ), s.book.place[i]? = some q → q.1 < s.book.trees.size) :
    ∃ places n o lay τ, treesOfFinish s.check.frame.shape s.st.codes = some lay ∧
      lay.shapes = #[τ] ∧
      Own.padMade s.st.codes (targetOfShape s.check.frame.shape).shape = some places ∧
      s'.here = .fin o ∧ o.mask = some (s.st.oracles.size + 1) ∧ o.fr.group = s.st.groups.size ∧
      s'.st.codes = s.st.codes ∧ s'.roots = s.roots + 1 ∧ s'.failed = s.failed ∧
      ClosingGroupLaid ⟨stSh s'.st, bookSh s'.book, s'.roots⟩ s.st.groups.size s.st.oracles.size
        (s.st.oracles.size + 1) s.book.trees.size
        ⟨s.check.frame.shape.code, s.check.frame.shape.maskCode, [s.st.oracles.size], [false],
          .plain :: List.replicate n .generator, false⟩
        ⟨(targetOfShape s.check.frame.shape).shape, true,
          (targetOfShape s.check.frame.shape).shape.answers,
          places.map fun x => (x.part, x.index), [s.st.groups.size],
          OnBytes.Slice.freshLedger s.st.codes (targetOfShape s.check.frame.shape).shape, false⟩
        (freshOrc (maskNoticeOfShape s.check.frame.shape))
        ⟨τ, p.firstTree + s.roots, .own s.roots, [s.st.oracles.size, s.st.oracles.size + 1], true,
          0⟩ := by
  have hl := link_in_front p accept
  unfold finishPublicB at isPublic
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at isPublic
  obtain ⟨⟨⟨⟨hlt, hk⟩, hm⟩, ha⟩, ht⟩ := isPublic
  have hgroup : s.check.frame.groups[s.check.frame.link]? =
      some ((reqGroups s.check.frame.shape).getD s.check.frame.shape.link.length {}) := by
    rw [groups, hl, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  have hmask : foldMaskNotice (s.check.frame.foldShape s.check.frame.link {}) =
      maskNoticeOfShape s.check.frame.shape := by
    unfold maskNoticeOfShape OnBytes.ReqFrame.foldShape
    rw [groups, hl]
  cases hlay : treesOfFinish s.check.frame.shape s.st.codes with
  | none =>
    rw [hlay] at ht
    cases ht
  | some lay =>
    rw [hlay] at ht
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨⟨⟨h1, t0⟩, t1⟩, p0⟩, p1⟩ := ht
    obtain ⟨τ, hτ⟩ : ∃ τ, lay.shapes = #[τ] := by
      rcases hs : lay.shapes with ⟨l⟩
      rw [hs] at h1
      match l, h1 with
      | [x], _ => exact ⟨x, rfl⟩
    obtain ⟨places, n, o, r⟩ := finish_lays p hp accept hgroup
      (Array.isEmpty_iff.1 hk) hm ha (lay := lay) (τ := τ) (by rw [hmask]; exact hlay) hτ t0 t1 p0 p1
      oldBelow placesBelow
    rw [hmask] at r
    exact ⟨places, n, o, lay, τ, rfl, hτ, r⟩

/-- **THE CLOSED LINE.** By Lean's kernel. -/
theorem finish_public_written : finishPublicB shapeFull codesFull2 = true := by decide +kernel

/-- Control: the mask does not sit at part 0. -/
theorem finish_mask_not_at_part_zero :
    ((treesOfFinish shapeFull codesFull2).any fun lay => lay.part.getD 1 0 == 0) = false := by
  decide +kernel

/-- **The written values of what is laid.** By Lean's kernel. -/
theorem finish_values_written :
    (shapeFull.code, shapeFull.maskCode, (targetOfShape shapeFull).shape,
      (Own.padMade codesFull2 (targetOfShape shapeFull).shape).map
        (·.map fun x => (x.part, x.index))) =
      (0, 0, H2K12.shL, some [(OnBytes.Part.main, 8388607)]) := by decide +kernel

/-- Control: the mask's shape is not the carrier's. -/
theorem finish_mask_is_not_carrier :
    decide ((maskNoticeOfShape shapeFull).shape = H2K12.shL) = false := by decide +kernel

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.finishPublicB
#print axioms ProofFile.Honest.K12.LotL.finish_lays_of_public
#print axioms ProofFile.Honest.K12.LotL.finish_public_written
#print axioms ProofFile.Honest.K12.LotL.finish_mask_not_at_part_zero
#print axioms ProofFile.Honest.K12.LotL.finish_values_written
#print axioms ProofFile.Honest.K12.LotL.finish_mask_is_not_carrier
