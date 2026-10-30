-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LettersNumerals.lean: THE RECORD OF THE TABLE's LETTERS OFF THE PUBLIC RECORD X
(`LW X`, LettersAtX.lean) WITH THREE MORE LETTERS IN NUMERALS: K2's numbers (k2n), K1's four numbers
of a link (nums), the merge's numbers (k11, but for the weights' layout): `LWn X`; A TEST ON X UNDER
WHICH THE TWO RECORDS ARE ALIKE; AND THAT TEST's ACCEPT AT THE MAKERS' TWINS, BY LEAN's KERNEL, WITH
TWO CONTROLS.

What it is for. "The run on shapes returns" at given public files is to be shown by the kernel in
lines at a record of letters. A letter that stands as a reader's own term is evaluated anew in every
line that opens it. With LWn the lines are free of K2's preparing, of K1's reader of a link's
numbers and of the merge's reader; the carrier ground is still read by hpL and k8.

Main names.
* `numsL l`, `k11L X`, `k11T`, `k11_of_T`. **`LWn X`** := { LW X with k2n := k2nL, nums := numsL,
  k11 := k11L X } (k2nL: K2NumsWritten.lean).
* `lettersTest X`: at the 25 links (LW X).nums l == numsL l, and the merge's seven numbers are (24,
  9, 0, 76, 1, 3570, 297). **`lwn_alike`**: lettersTest X = true ⊢ LettersAlike (LW X) (LWn X). K2's
  numbers ask no test: `k2n_lit` holds at every X. `yes_at_LWn`: then (shapeL (LW X)).yes a n =
  (shapeL (LWn X)).yes a n.
* **`lettersTest_atXL`**: BY THE KERNEL: atXL lettersTest = true (AtX.lean: at the public record
  that the makers' twins make; atXL_zFull carries it to what publicOfO returns at VerifierAndGoals.storedPublicFiles).
  Controls, by the kernel: `numsTest_no` (one number bent at link 7), `k11Test_no` (one number
  bent): refused.

Limits. The numerals were read off Lean's evaluator; what holds them is lettersTest_atXL. AT THE
MAKERS' TWINS OF THE STORED FULL-SIZE FILES ALONE: at another X the test may refuse, and then
nothing is said. k11L's field lay stays a term in X, and k2nL's field codes the written term
proofSizedFull.codes: no numeral. hpL, k8, look, k4pub, k4own, links, XZ and XG stand as in LW X. LW
X AND LWn X ARE NO TESTS ON X, AND THEIR RUN MAY RETURN WHERE THE TABLE's FIRST TEXT WOULD REFUSE:
the letter look leaves out the tests on the calls' tables and on the padding; k9 and close are never
none, nor is nums in LWn X; the written half and the numerals are constants of the full size
whatever X is. No line on a run is here; nothing says that a step returns. A FACT ON A RUN AT shapeL
(LWn X₀) IS BY ITSELF NO FACT ON THE TABLE's OWN RUN: the law that carries it there is not here.
What such a law has to join: lwn_alike, whose test lettersTest_atXL pays at the makers' twins alone;
atXL_zFull, under the stored layout file's size; and LettersAtX.lean's lw_alike, under the head, at
an opening. The full size alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersAtX
import Johnson.AtFull.Shape.AtX
import Johnson.AtFull.Shape.K2NumsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- K1's four numbers of a link, in numerals. -/
def numsL (l : Nat) : Option (Nat × Nat × Option (List Nat) × Option (List Nat)) :=
  if l == 24 then some (5, 7, some [0], some [8, 9])
  else if l % 2 == 1 then some (4, 6, some [0], some [5, 6])
  else if l == 0 then some (4, 6, some [0], some [10, 11]) else some (4, 6, some [0], some [9, 10])

/-- The merge's numbers but for the weights' layout, as a tuple. -/
def k11T (p : HeadMergeP) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (p.link, p.piece, p.work, p.sent, p.ncl, p.nMsg, p.nLin)

/-- The merge's numbers in numerals; the weights' layout stays a term in X. -/
def k11L (X : Verify.Public) : HeadMergeP :=
  { link := 24, piece := 9, lay := X.layers.wsLay, work := 0, sent := 76, ncl := 1, nMsg := 3570,
    nLin := 297 }

theorem k11_of_T {p : HeadMergeP} {X : Verify.Public} (hl : p.lay = X.layers.wsLay)
    (h : k11T p = (24, 9, 0, 76, 1, 3570, 297)) : p = k11L X := by
  cases p
  simp only [k11T, Prod.mk.injEq] at h
  simp only at hl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 hl
  rfl

/-- **THE RECORD OF LETTERS WITH K2's, K1's AND THE MERGE's NUMBERS IN NUMERALS.** -/
def LWn (X : Verify.Public) : TabLetters :=
  { LW X with k2n := k2nL, nums := numsL, k11 := k11L X }

/-- The test on X: K1's four numbers at the 25 links and the merge's seven are the numerals. -/
def lettersTest (X : Verify.Public) : Bool :=
  ((List.range 25).all fun l => (LW X).nums l == numsL l) &&
    k11T (LW X).k11 == (24, 9, 0, 76, 1, 3570, 297)

/-- **WHERE THE TEST ACCEPTS, THE TWO RECORDS ARE ALIKE.** K2's numbers ask no test: k2n_lit. -/
theorem lwn_alike {X : Verify.Public} (h : lettersTest X = true) :
    LettersAlike (LW X) (LWn X) where
  XZ := rfl
  XG := rfl
  links := rfl
  nums := fun l hl => by
    unfold lettersTest at h
    rw [Bool.and_eq_true] at h
    exact eq_of_beq (List.all_eq_true.1 h.1 l (List.mem_range.2 hl))
  hpL := fun _ _ _ => rfl
  k8 := fun _ _ => rfl
  k2nL := fun _ h0 hl => k2n_lit X (asks_link h0 hl)
  k2nF := k2n_lit X asks_none
  look := fun _ _ _ => rfl
  k4pub := fun _ => rfl
  k4own := fun _ => rfl
  k11 := by
    unfold lettersTest at h
    rw [Bool.and_eq_true] at h
    exact k11_of_T rfl (eq_of_beq h.2)
  ft := rfl
  k1 := fun _ _ _ _ => rfl
  k1First := rfl
  lin := rfl
  k9 := fun _ _ => rfl
  close := fun _ _ => rfl
  wP := fun _ => rfl
  where13 := rfl
  p12 := rfl

/-- So "the run on shapes returns" at the one record is that at the other. -/
theorem yes_at_LWn {X : Verify.Public} (h : lettersTest X = true) (a : ShA) (n : Nat) :
    (shapeL (LW X)).yes a n = (shapeL (LWn X)).yes a n :=
  yes_alike (lwn_alike h) a n

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: the test accepts at the record that the makers' twins make. -/
theorem lettersTest_atXL : atXL lettersTest = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: K1's numbers with one number bent, at link 7: refused. (atXL is false at a maker's
refusal too: only beside lettersTest_atXL does this show that the bent number was refused.) -/
theorem numsTest_no : atXL (fun X => (List.range 25).all fun l => (LW X).nums l ==
    if l == 7 then some (4, 6, some [0], some [5, 7]) else numsL l) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the merge's numbers with one number bent: refused. (Likewise: only beside
lettersTest_atXL.) -/
theorem k11Test_no : atXL (fun X => k11T (LW X).k11 == (24, 9, 0, 76, 1, 3571, 297)) = false := by
  decide +kernel

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k11_of_T
#print axioms Johnson.AtFull.Shape.lwn_alike
#print axioms Johnson.AtFull.Shape.yes_at_LWn
#print axioms Johnson.AtFull.Shape.lettersTest_atXL
#print axioms Johnson.AtFull.Shape.numsTest_no
#print axioms Johnson.AtFull.Shape.k11Test_no
#print axioms Johnson.AtFull.Shape.numsL
#print axioms Johnson.AtFull.Shape.k11T
#print axioms Johnson.AtFull.Shape.k11L
#print axioms Johnson.AtFull.Shape.LWn
#print axioms Johnson.AtFull.Shape.lettersTest
