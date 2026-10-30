-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidHead.lean: the head's copy of the last stream, and the public premises of
Johnson/Goal/Meaning/HidOwn.lean at public files in the goals' scope.

hidOf (Johnson/Goal/Meaning/HidOwn.lean) takes as the head's stream lastOf at group 11's list. The
head's sub-proof does not read that list: its own list has a copy of the stream's matrix, entry NHf
+ 3, which bears the label of the last group's number iXO (Johnson/Road/HeadDict.lean: labH). This
file says what is needed so that the two are one stream.

lastOf y M reads the cells of the array x8 through the library's dictionary cellsAt, and cellsAt
reads feature φ of the stream's matrix in number iXO + φ / fc / k of the list (fc: the features of a
column, k: the columns). So "lastOf reads number iXO alone" is no fact of every layout: it hangs on
three numbers of the layout.

Main names:
  XoNum y   the three numbers: 400 columns, 65,536 rows, 1,024 positions.
  xoNum_of_core   they are those of X.y, at what publicOf returns under Hd.PublicCore.
  lastIn y A   the stream read in one matrix A: lastOf at the list that has A at every number.
  lastOf_lastIn   under XoNum, inside the ranges, lastOf y M is lastIn y (M iXO).
  lastOf_congr   so two lists with one matrix at number iXO have one last stream.
  lastIn_congr   lastIn reads rows below 65,536 and columns below 400 alone.
  HeadWord X seen   THE 24TH EQUATION: the head's copy (number NHf + 3 of seen 24) is the last
    group's number iXO (of seen 22), FENCED: at rows below 65,536 and columns below 400, the sizes
    of a matrix of the stream.
  headPlain_of_copy   HeadPlain at the stream read in the head's own copy, with HeadWord, gives
    HeadPlain at lastOf X.y (seen 22): the premise H of means_of_seen.
  means_of_seen24   each sub-proof's clauses at its own reading, OneWord and HeadWord give Means at
    hidOf.
  xo_lt_of_core, qa_lt_of_core, mgOf_lab_core, maOf_plan_core   the premises of mgOf_lab and
    maOf_plan (iXO < 256, iQA < 256, profile 4, g below the number of groups) hold in scope.

  headStream X Mh, lastIn_head   the stream as the library reads it in the head's own cells (Head.xv
    at cellsH, Inst/Model/Head/Trace.lean, Johnson/Road/HeadPlace.lean) is, in scope and inside the
    ranges, lastIn at the head's copy.
  means_of_cells   the same as means_of_seen24, with the head's clause at headStream X (seen 24).

What is not claimed. HeadWord, like OneWord, is concluded by no theorem: it is a matter of the
commitments. That a law on the head's own rounds ends in HeadPlain at headStream. The full size
alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidOwn
import Johnson.Road.HeadPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)

/-- Three numbers of a layout: the columns and the rows of a matrix of the stream, the positions. -/
structure XoNum (y : Lay) : Prop where
  kxb : y.kxb = 400
  mxb : y.mxb = 65536
  T : y.T = 1024

/-- They are the numbers of the layout that publicOf returns, under the public core. -/
theorem xoNum_of_core {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P) : XoNum X.y := by
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  obtain ⟨e, -⟩ := laid_of_layout B.lay B.switches.p3
  have hT : X.y.T = 2 ^ X.y.h.lt := (laid2_of_layout B.lay).T
  have hl : DF.lT = X.y.h.lt := by
    rw [e]
    exact B.sized.lT
  refine ⟨Bd.kxb, Bd.mxb, ?_⟩
  rw [hT, ← hl]
  rfl

/-- The stream read in one matrix. -/
def lastIn (y : Lay) (A : ℕ → ℕ → ℤ) : ℕ → Vec := lastOf y fun _ => A

/-- A cell of the stream that goes out stands in number iXO of the list. -/
theorem x8_at {y : Lay} (N : XoNum y) (M : Mats ℤ) {k j : ℕ} (hk : k < 5) (hj : j < ppref.d)
    (pos : ℕ) :
    cellsOf DF (cellsAt y M) ⟨.x8, k, 0, j, pos⟩ =
      M (matIx y).iXO ((5120 * k + j) % 64 * 1024 + pos) ((5120 * k + j) / 64) := by
  have hj' : j < 5120 := hj
  have hf : FFSeg.feat DF .x8 k 0 j = 5120 * k + j := by
    show 0 + (k * 1 + 0) * 5120 + j = 5120 * k + j
    omega
  show M ((matIx y).iXO + FFSeg.feat DF .x8 k 0 j / (y.mxb / y.T) / y.kxb)
      (FFSeg.feat DF .x8 k 0 j % (y.mxb / y.T) * y.T + pos)
      (FFSeg.feat DF .x8 k 0 j / (y.mxb / y.T) % y.kxb) = _
  rw [hf, N.kxb, N.mxb, N.T, show 65536 / 1024 = 64 from rfl,
    show (5120 * k + j) / 64 / 400 = 0 by omega,
    show (5120 * k + j) / 64 % 400 = (5120 * k + j) / 64 by omega, Nat.add_zero]

/-- **Inside the ranges lastOf reads number iXO alone.** -/
theorem lastOf_lastIn {y : Lay} (N : XoNum y) (M : Mats ℤ) :
    Agree ppref (lastOf y M) (lastIn y (M (matIx y).iXO)) := by
  intro pos _ j hj
  show FFSeg.val (cellsOf DF (cellsAt y M)) .x8 0 j pos =
    FFSeg.val (cellsOf DF (cellsAt y fun _ => M (matIx y).iXO)) .x8 0 j pos
  unfold FFSeg.val
  refine congrArg (· + _) (Finset.sum_congr rfl fun k hk => congrArg (_ * ·) ?_)
  have hk' : k < 5 := Finset.mem_range.1 hk
  rw [x8_at N M hk' hj, x8_at N _ hk' hj]

/-- Two lists with one matrix at number iXO have one last stream. -/
theorem lastOf_congr {y : Lay} (N : XoNum y) {M M' : Mats ℤ}
    (h : ∀ r c, M (matIx y).iXO r c = M' (matIx y).iXO r c) :
    Agree ppref (lastOf y M) (lastOf y M') := by
  have e : M (matIx y).iXO = M' (matIx y).iXO := funext fun r => funext fun c => h r c
  intro pos hp j hj
  rw [lastOf_lastIn N M pos hp j hj, lastOf_lastIn N M' pos hp j hj, e]

/-- lastIn reads its matrix within 65,536 rows and 400 columns alone. -/
theorem lastIn_congr {y : Lay} (N : XoNum y) {A A' : ℕ → ℕ → ℤ}
    (h : ∀ r < 65536, ∀ c < 400, A r c = A' r c) : Agree ppref (lastIn y A) (lastIn y A') := by
  intro pos hp j hj
  have hp' : pos < 1024 := hp
  have hj' : j < 5120 := hj
  show FFSeg.val (cellsOf DF (cellsAt y fun _ => A)) .x8 0 j pos =
    FFSeg.val (cellsOf DF (cellsAt y fun _ => A')) .x8 0 j pos
  unfold FFSeg.val
  refine congrArg (· + _) (Finset.sum_congr rfl fun k hk => congrArg (_ * ·) ?_)
  have hk' : k < 5 := Finset.mem_range.1 hk
  rw [x8_at N _ hk' hj, x8_at N _ hk' hj]
  exact h _ (by omega) _ (by omega)

/-- **The 24th equation: the head's copy of the stream is the last group's**, within the sizes of a
matrix of the stream. seen k: the list of sub-proof k as that sub-proof itself reads it. -/
def HeadWord (X : Model.Verify.Public) (seen : ℕ → Mats ℤ) : Prop :=
  ∀ r < 65536, ∀ c < 400, seen 24 (X.hS.NHf + 3) r c = seen 22 (matIx X.y).iXO r c

section
variable {X : Model.Verify.Public} {seen : ℕ → Mats ℤ} {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref}

/-- The head's clause, from the stream read in the head's own copy. -/
theorem headPlain_of_copy (N : XoNum X.y) (W : HeadWord X seen)
    (H : HeadPlain pp i x (lastIn X.y (seen 24 (X.hS.NHf + 3)))) :
    HeadPlain pp i x (lastOf X.y (seen 22)) :=
  SaysHead.congr (fun pos hp j hj => (lastIn_congr N W pos hp j hj).trans
    (lastOf_lastIn N (seen 22) pos hp j hj).symm) (fun _ _ _ => rfl) H

/-- **From each of the 25 sub-proofs' clauses at its own reading, and the 24 equations, to Means at
hidOf.** -/
theorem means_of_seen24 (tok : Fin ppref.V) (N : XoNum X.y) (A : OneWord X seen)
    (W : HeadWord X seen) (hO : ∀ g < 12, OwnApart (Hd.shapeA X g))
    (G : ∀ g < 12, OwnG X i x (seen (2 * g)) g)
    (At : ∀ g < 12, OwnA (Hd.shapeA X g) (seen (2 * g + 1)))
    (H : HeadPlain pp i x (lastIn X.y (seen 24 (X.hS.NHf + 3)))) :
    Means X pp i x (hidOf X tok seen) :=
  means_of_seen tok A hO G At (headPlain_of_copy N W H)

end

/-! ## The head's own reading of its copy -/

/-- The last stream as the library reads it in the head's cells, and these as the verifier's rule
reads them in the head's list Mh. -/
def headStream (X : Model.Verify.Public) (Mh : Mats ℤ) : ℕ → Vec := fun pos j =>
  Inst.Model.Head.xv (Hd.cellsH X.hS X.HLy (Model.Verify.borderOf X.y) Mh) j pos

/-- **In scope the head's own reading of its copy is lastIn at the copy.** -/
theorem lastIn_head {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P) (Mh : Mats ℤ) :
    Agree ppref (lastIn X.y (Mh (X.hS.NHf + 3))) (headStream X Mh) := by
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  have NH := Hd.numH_of_layout B.full B.head
  have N := xoNum_of_core h A
  intro pos _ j hj
  have hj' : j < 5120 := hj
  show FFSeg.val (cellsOf DF (cellsAt X.y fun _ => Mh (X.hS.NHf + 3))) .x8 0 j pos =
    Inst.Model.Head.xv (Hd.cellsH X.hS X.HLy (Model.Verify.borderOf X.y) Mh) j pos
  unfold FFSeg.val Inst.Model.Head.xv Inst.Model.Head.rd Inst.Model.Head.bl
  show _ + (0 : ℤ) = _
  rw [add_zero]
  refine Finset.sum_congr rfl fun k hk => congrArg (_ * ·) ?_
  have hk' : k < 5 := Finset.mem_range.1 hk
  have hφ : Inst.Model.Head.fX k j < 25600 := by
    show 5120 * k + j < 25600
    omega
  show _ = (Hd.cellsH X.hS X.HLy (Model.Verify.borderOf X.y) Mh).x (Inst.Model.Head.fX k j) pos
  rw [x8_at N _ hk' hj, Hd.x_at NH _ Mh Bd hφ pos, NH.NHf]
  rfl

/-- **From each of the 25 sub-proofs' clauses at its own reading, the head's at the stream that the
library reads in the head's own cells, and the 24 equations, to Means at hidOf.** -/
theorem means_of_cells {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {seen : ℕ → Mats ℤ} {pp : ScalesAndPolicy}
    {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V) (A : OneWord X seen)
    (W : HeadWord X seen) (hO : ∀ g < 12, OwnApart (Hd.shapeA X g))
    (G : ∀ g < 12, OwnG X i x (seen (2 * g)) g)
    (At : ∀ g < 12, OwnA (Hd.shapeA X g) (seen (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (seen 24))) : Means X pp i x (hidOf X tok seen) :=
  means_of_seen24 tok (xoNum_of_core h C) A W hO G At
    (SaysHead.congr (fun pos hp j hj => (lastIn_head h C (seen 24) pos hp j hj).symm)
      (fun _ _ _ => rfl) H)

/-! ## The public premises of the theorems on labels, in scope -/

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

theorem xo_lt_of_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P) :
    (matIx X.y).iXO < 256 := by
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  obtain ⟨h3, h1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 < 256
  omega

theorem qa_lt_of_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P) :
    (matIx X.y).iQA < 256 := by
  have k := xo_lt_of_core h A
  have k' : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 < 256 := k
  show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 < 256
  omega

/-- In scope a group's list, as hidOf makes it, is the arrays under the plan's labels. -/
theorem mgOf_lab_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P)
    (own : ℕ → Mats ℤ) (g : ℕ) {a : ℕ} (ha : a < 256) :
    mgOf X.y own g a = mzA X.y (byLab own) g a := mgOf_lab X.y own g (xo_lt_of_core h A) ha

/-- In scope attention's copy of qa, as hidOf makes it, is the array under the label that the plan
X.A[g] itself gives to number NAs + 3 of its list. -/
theorem maOf_plan_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) (own : ℕ → Mats ℤ) :
    ∃ Ag lab, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      (Ag.seam.tl.mats[Ag.S.cf.NAs + 3]?).map (fun M => M.aId) = some lab ∧
      maOf X own g ((Hd.shapeA X g).cf.NAs + 3) = byLab own lab := by
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  exact maOf_plan h B.p4 (by rw [B.groups]; exact hg) (qa_lt_of_core h A) own

end Core

end Meaning

#print axioms Meaning.xoNum_of_core
#print axioms Meaning.x8_at
#print axioms Meaning.lastOf_lastIn
#print axioms Meaning.lastOf_congr
#print axioms Meaning.lastIn_congr
#print axioms Meaning.headPlain_of_copy
#print axioms Meaning.means_of_seen24
#print axioms Meaning.lastIn_head
#print axioms Meaning.means_of_cells
#print axioms Meaning.xo_lt_of_core
#print axioms Meaning.qa_lt_of_core
#print axioms Meaning.mgOf_lab_core
#print axioms Meaning.maOf_plan_core
