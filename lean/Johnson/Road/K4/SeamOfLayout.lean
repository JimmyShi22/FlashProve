-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SeamOfLayout.lean: `SeamFit` (Johnson/Road/K4/K4PinsIdn.lean), THE CONDITIONS ON
PUBLIC LETTERS AT THE SEAM BETWEEN TWO GROUPS OF LAYERS, WITHOUT A WALK OVER THE CELLS. At the full
size the stream that crosses a seam has 8,738,400 cells: a test that walks them cannot run.
`SeamFit.seats` and `SeamFit.each` speak of every cell. Here they follow, at the seats that the
model's files make off the layout (`seatBy (fLay layout num) X s`,
Johnson/Goal/Meaning/HidSeatsOf.lean), from tests on blocks, on ONE array, on two labels, and from
three conditions that stay premises. One definition with code and one theorem. Glue: calls; no draw,
no count.

  `seamArrB`: the array that the stream's label names is there, has the entry's rows of symbols and
    columns, and the number of its message has just one tenant in the reader's group and in the
    owner's: ONE QUESTION A SEAM, AT ONE ENTRY OF ONE LIST.
  `seamFit_of_layout`: `SeamFit arr (msOf L) N s (seatBy (fLay layout num) X s) codes X.y g`, for
    0 < g < 12.

CALLED: `sizeAt_of_pairFit`, `seatAt_of_pairFit`
(Johnson/Goal/Meaning/HidPlan.lean: a test on two labels) · `laidAt_of_layout`
(Johnson/Goal/Meaning/LaidCovered.lean: the programs' own count of the blocks' areas gives the
cover) · `array_inside`, `arrayOf_mem` (Johnson/Goal/Meaning/LaidInsideSeats.lean: at a named array
every seat that is there lies off its message's pad) · `padB_of_key`
(Johnson/Desc/Sound/PlanMemProofs.lean). ELDERS NOT CALLED: `seat_inside`, `seat_inside_members`
(LaidInsideSeats.lean) say the same of every entry of all 25 lists under the test `laidThere`, which
`namedThere` pays: 176 entries, the attention sub-proofs' and the head's among them, where a seam
spends one: so their few lines are walked here anew at that one entry. THIS FILE ITSELF imports
K4PinsIdn.lean, and through it Johnson/Desc/Sound/ReadAt.lean.

PREMISES, AND WHO CAN PAY EACH. Three tests of the programs: `Codes.lengthsOk`, `reqShapeOk`,
`reqLayoutOk`: Bools with code, a block at a time. `pairFit`: a Bool on two labels; proved in the
goals' scope (`planFit_of_core`, Johnson/Goal/Meaning/HidPlanFit.lean, with `pairs_of_planFit`).
`seamArrB`: a Bool with code. THREE ARE NO TESTS: `Follows X s`: proved at the plans' own sizes
under the Bool `nmFit` (`follows_sizesOf`). `ShapesTied`: a condition on lists; another file's Bool
`shapesTiedB` gives it. `GroupsSeated`: another file's theorem from two Bools and "the groups
beyond the last segment are empty".

Limits. K04_law IS NOT PROVED BY THIS. NONE OF THE TESTS HAS RUN AT A PLAN HERE. ONE LETTER, THREE
ROLES: 2 g is the sub-proof (labAt, s), the segment (N.group) and, through the label's owner, the
link of the layout and of the shape: that sub-proof k is link k of the layout and segment k of
N.group, that entry a's array bears the name "M" and a, and that the programs read a borrowed array
at its owner's seat, is said by no theorem. The seats are `seatBy (fLay layout num) X s`. g between
1 and 11.
-/
import Johnson.Road.K4.K4PinsIdn
import Johnson.Goal.Meaning.LaidCovered
import Johnson.Goal.Meaning.LaidInsideSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Model.Layer (matIx)
open VerifiableInference.Desc (MemberLists arrayOf seatIn)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (msOf namedOnce GroupsSeated padB_of_key)
open Meaning (Follows pairFit ShapesTied seatBy fLay labAt ownerK ownerA nameOf)
open Cb.Pv.Tail (Size)

/-- The array that the label of entry a of sub-proof k names is there, has the entry's rows of
symbols and columns, and its message's number has just one tenant in segment k's group and in
segment k''s. -/
def seamArrB (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ)
    (N : Numbers) (k k' a : ℕ) : Bool :=
  match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
  | none => false
  | some A => A.sizeI == Alg.symRows ((s k).m a) && A.sizeC == (s k).k a &&
      namedOnce arr N k (num (ownerK (labAt X k a)) A.message) &&
      namedOnce arr N k' (num (ownerK (labAt X k a)) A.message)

/-- **The conditions at the seam, at the seats off the layout, for 0 < g < 12, without a walk over
the cells**: from the programs' three tests, the Bools `pairFit` and `seamArrB`, and three
conditions that are premises here: `Follows`, `ShapesTied`, `GroupsSeated`. -/
theorem seamFit_of_layout {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (hC : codes.lengthsOk = true) (hS : reqShapeOk shape = true)
    (h : reqLayoutOk codes shape layout = true) {X : Model.Verify.Public} {s : ℕ → Size}
    (F : Follows X s) {num arr : ℕ → ℕ → ℕ} {L : MemberLists} {N : Numbers}
    (tie : ShapesTied codes shape layout num arr (msOf L) fun k => N.group k)
    (seated : GroupsSeated (msOf L) N) {g : ℕ} (h0 : 0 < g) (hg : g < 12)
    (p : pairFit X (2 * g) (matIx X.y).iXI (2 * (g - 1)) (matIx X.y).iXO = true)
    (hB : seamArrB X s layout num arr N (2 * g) (2 * (g - 1)) (matIx X.y).iXI = true) :
    SeamFit arr (msOf L) N s (seatBy (fLay layout num) X s) codes X.y g := by
  have hk : 2 * g < 25 := by omega
  have hk' : 2 * (g - 1) < 25 := by omega
  refine ⟨Meaning.sizeAt_of_pairFit F hk hk' p, Meaning.seatAt_of_pairFit _ p, seated,
    fun ha i hi c hc => ?_⟩
  unfold seamArrB at hB
  cases hA : arrayOf layout (ownerK (labAt X (2 * g) (matIx X.y).iXI))
      (nameOf (ownerA (labAt X (2 * g) (matIx X.y).iXI))) with
  | none =>
    simp only [hA] at hB
    cases hB
  | some A =>
    simp only [hA, Bool.and_eq_true, beq_iff_eq] at hB
    obtain ⟨⟨⟨e1, e2⟩, o1⟩, o2⟩ := hB
    obtain ⟨as, hl, hmem⟩ := Meaning.arrayOf_mem hA
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1
      (Meaning.laidAt_of_layout h hl hmem (by rw [e1]; exact hi) (by rw [e2]; exact hc))
    obtain ⟨m, hm, -, hP⟩ := Meaning.array_inside hC hS h hA hx
    have es : seatBy (fLay layout num) X s (2 * g) ⟨(matIx X.y).iXI, ha⟩ i c =
        (num (ownerK (labAt X (2 * g) (matIx X.y).iXI)) A.message, x.1, x.2) := by
      unfold seatBy fLay seatIn
      rw [hA]
      simp [hx]
    rw [es]
    refine ⟨o1, o2, fun y hy hgr hn => ?_, fun y hy hgr hn => ?_⟩
    · rw [padB_of_key codes _ _ (tie _ as A m hl hmem hm (2 * g) hk y hy hgr hn)]
      exact hP
    · rw [padB_of_key codes _ _ (tie _ as A m hl hmem hm (2 * (g - 1)) hk' y hy hgr hn)]
      exact hP

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seamFit_of_layout
