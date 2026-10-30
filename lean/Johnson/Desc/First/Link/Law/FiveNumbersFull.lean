-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FiveNumbersFull.lean (kind K10): THE FIVE COMPARISONS OF PUBLIC NUMBERS (FiveNumbers.lean beside this file) AT THE FULL SIZE's 25
LINKS: THE CLOSED FACTS BY THE KERNEL, AND THE FIVE FROM THE FRAME's THREE FACTS, `ShapesAre`, `LayFacts` AND THE STATEMENT's CODES. Theorems.

What is said.
  `fiveBy g cs mc l`: A CLOSED TEST at link l, a group's sizes g l, codes cs and a number mc of a mask code: the written request's group l has the stage's k and h; a member of the written list
    has a main code whose length is a power of two; a member HAS A MASK ROW, its mask code's length is a power of two, and its maskCode is the written
    request's (mc). `fiveFullB l` := at g := gsAt (LPFE1R/RowPubAt.lean), cs := codesFull2, mc := shapeFull.maskCode.
  `five_full`: **true at all 25 links: by the kernel.** THE TEST CAN SAY NO, EACH TIME AT EVERY LINK, BY THE KERNEL: `five_full_no`: at the next link's
    sizes (the first two conjuncts) · `five_no_codes`: at no codes (the lengths) · `five_no_mask`: at another number of the mask code (the last conjunct).
  `five_at`: what its yes says, in the forms that the laws take.
  `five_of_shapes`: **l < 25; cs = codesFull2; the frame's groups are reqGroups of its shape, its shape is shapeFull, its link is l; the statement's codes
    are cs; at a statement T' with codes cs, a group G' and a layout L: `LayFacts T' G' L`, `ShapesAre T' G' (loAt l) kb no` ⊢ (N1) ∧ (N2) ∧ (N3) ∧ (N4) ∧
    (N5) at s := stageOf (gsAt l) 219.** cs is a letter (it is laid in at At.cs Zp).

Limits. The premises on the state (the frame's three; the codes; ShapesAre; LayFacts) are shown of no state here: the first three are fields of `FoldFacts`
(liveGroups, liveShape with the first pin, frameIs); the codes: `RowAsks.codes`. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FiveNumbers
import Johnson.LPFE1R.RowPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- **A closed test at a link and a group's sizes.** -/
def fiveBy (g : ℕ → GroupSize) (cs : Codes) (mc l : ℕ) : Bool :=
  decide (((reqGroups shapeFull)[l]?.getD default).k =
      (stageOf (g l) 219).h + (stageOf (g l) 219).g) &&
    decide (((reqGroups shapeFull)[l]?.getD default).h = (stageOf (g l) 219).h) &&
    (membersOf (loAt l)).any (fun i => powerOfTwo (pMain cs ((loAt l).get i).1).ell) &&
    (membersOf (loAt l)).any fun i => decide (((loAt l).get i).1.maskRows ≠ 0) &&
      powerOfTwo (pMask cs ((loAt l).get i).1).ell &&
      decide (mc = ((loAt l).get i).1.maskCode)

def fiveFullB (l : ℕ) : Bool := fiveBy gsAt codesFull2 shapeFull.maskCode l

set_option maxRecDepth 1000000 in
/-- **TRUE AT ALL 25 LINKS.** -/
theorem five_full : (List.range 25).all fiveFullB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At the next link's sizes: false at every link. -/
theorem five_full_no : (List.range 25).any
    (fiveBy (fun l => gsAt (l + 1)) codesFull2 shapeFull.maskCode) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At no codes: false at every link. -/
theorem five_no_codes : (List.range 25).any (fiveBy gsAt {} shapeFull.maskCode) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At another number of the mask code: false at every link. -/
theorem five_no_mask : (List.range 25).any
    (fiveBy gsAt codesFull2 (shapeFull.maskCode + 1)) = false := by decide +kernel

/-- What the yes says. -/
theorem five_at {l : ℕ} (hl : l < 25) :
    ((reqGroups shapeFull)[l]?.getD default).k =
        (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      ((reqGroups shapeFull)[l]?.getD default).h = (stageOf (gsAt l) 219).h ∧
      (∃ a : {i // memMain (loAt l) i},
        powerOfTwo (pMain codesFull2 ((loAt l).get a.1).1).ell = true) ∧
      ∃ a : {i // memMain (loAt l) i}, ((loAt l).get a.1).1.maskRows ≠ 0 ∧
        powerOfTwo (pMask codesFull2 ((loAt l).get a.1).1).ell = true ∧
        shapeFull.maskCode = ((loAt l).get a.1).1.maskCode := by
  have h := List.all_eq_true.1 five_full l (List.mem_range.2 hl)
  unfold fiveFullB fiveBy at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, i, hi, h3⟩, j, hj, ⟨h4, h5⟩, h6⟩ := h
  exact ⟨h1, h2, ⟨⟨i, mem_members.1 hi⟩, h3⟩, ⟨j, mem_members.1 hj⟩, h4, h5, h6⟩

/-- **THE FIVE, AT A LINK OF THE FULL SIZE.** -/
theorem five_of_shapes {l : ℕ} (hl : l < 25) {cs : Codes} (hcs : cs = codesFull2)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask cs ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (es : List Fmt.Entry) (x : Option Nat × ReqFrame × Statement)
    (hg : x.2.1.groups = reqGroups x.2.1.shape) (hs : x.2.1.shape = shapeFull)
    (hk : x.2.1.link = l) (hx : x.2.2.codes = cs) {T' : Statement} {G' : Group}
    {L : GroupLayout} {kb : Fin (loAt l).length → Bool} {no : Fin (loAt l).length → ℕ}
    (hc : T'.codes = cs) (Y : LayFacts T' G' L) (H : ShapesAre T' G' (loAt l) kb no) :
    (planOf es x).k = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (planOf es x).h = (stageOf (gsAt l) 219).h ∧
      2 ^ L.logEll = (stageOf (gsAt l) 219).C.l ∧ 2 ^ L.logEllZk = (stageOf (gsAt l) 219).Z.l ∧
      (x.2.2.codes.mask.getD (planOf es x).maskCode default).ell =
        (stageOf (gsAt l) 219).Z.l := by
  obtain ⟨c1, c2, ⟨a, c3⟩, b, c4, c5, c6⟩ := five_at hl
  obtain ⟨p1, p2, p3⟩ := plan_of_frame es x hg hs hk
  subst hcs
  exact ⟨p1.trans c1, p2.trans c2, logEll_of_shapes hM Y H hc a c3,
    logEllZk_of_shapes hZ Y H hc b c4 c5, code_of_member hZ hx b c4 (p3.trans c6)⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.five_full
#print axioms VerifiableInference.Desc.LinkJoin.five_full_no
#print axioms VerifiableInference.Desc.LinkJoin.five_no_codes
#print axioms VerifiableInference.Desc.LinkJoin.five_no_mask
#print axioms VerifiableInference.Desc.LinkJoin.five_at
#print axioms VerifiableInference.Desc.LinkJoin.five_of_shapes
