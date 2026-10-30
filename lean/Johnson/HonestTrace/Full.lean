-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Full.lean

The trace of the model's run on a request at the full (reference) size: for each of the 25
sub-proofs the list of its matrices of cells, by the numbers of the verifier's plans.

The pieces of an honest prover, which are written elsewhere, read the cells of the model's run on a
request. The library has these cells as a term on names of cells ("Cm.trace") and lays them into one
matrix for each segment ("Cm.Seg.toMat"). Johnson/Road/Lane5TopLTrue.lean reads these matrices back:
"zTrue", one family by the labels of the verifier's plans, and "zaTrue", the attention lists by
their numbers. "listsOf" here reads "zTrue" through the labels, so that every list goes by the
numbers that a sub-proof's matrices have in the byte format's list (docs/format/11-2, 11-3, 11-4).
This file makes one object of them, "trFull", with two changes. The matrix of the lookup's
multiplicities (b, bA, bH), for which the library's model has no cell, is filled from a letter pl.
And every matrix is cut to the rows and columns that the verifier's plan gives it: outside them, at
a number beyond a list and at a sub-proof's number beyond 24 the trace is 0. "The verifier" is, in
this file, the verifier of OnBytes/Model/ ("OnBytes.Model.Verify"); X is its public part (what its
"publicOf" returns), a letter here.

It is a specification, not a program: "Cm.Seg.toMat" picks the name that stands at a place by
choice, so "honMx", "trFull" and "traceFull" are noncomputable. Nothing here forbids a formula for
the same matrices.

Cells without a meaning. The sizes of the format's matrices are rounded up, so some committed cells
hold no named cell and no bit of a multiplicity; the smallness test alone reads them
(docs/format/11-2-feed-forward-segment.md, "Indices beyond the true width";
11-3-attention-segment.md, "Cells and entries that no claim of this part reads";
11-4-output-head.md). The format does not give an honest prover's choices where a verifier accepts
several values (docs/format/11-sub-proofs.md; 11-1-machinery.md, "What this part does not specify").
This trace has zeros there, and draws no coin for them. Inside the shapes that is a field of the
bundle "MeetsAll", proved in Johnson/Goal/HonestTrace/FullInScope.lean. Outside them it is
"trFull_out". By the format no cell exists there: in the last packed row of a matrix whose number of
rows is no multiple of 3 the terms of the missing rows are absent (docs/format/11-1-machinery.md,
"Easy to get wrong", 3).

Main definitions:
* "Tr": sub-proof's number → number in the list → row of cells → column → ℤ.
* "honAt", "honMx": the library's honest cells at X's table of scales and policy, by names and in
  the library's matrices.
* "listsOf", "bNo", "withPlanes": the 25 lists read out of the library's matrices; the number of the
  matrix of multiplicities in each list; that matrix replaced by pl.
* "planMats", "InShape", "cut": the plan's list of matrices of a sub-proof; a place inside the rows
  and columns of an entry of that list; 0 at every other place.
* "trFull X pl i x": the trace at the index i and the request x.
* "ServesAt", "traceFull": the weights that i holds serve x at X's scales and policy ("Serves",
  Johnson/HonestTrace/Serves.lean); the trace where they do, "none" elsewhere.
* "noAt", "byName", "cellOf": the trace read by the names of Johnson/HonestTrace/Names.lean, in
  integers, and by the sub-proof's number and the matrix's label, in the field.
* "placeH": the place in the head's list at which "Hd.cellsH" reads a feature at a position.
* "MeetsAll X i x T": a bundle of statements on a trace T, for a caller that cannot import files
  under Johnson/Goal/: it can take the bundle as a hypothesis.
Main theorems:
* "honAt_eq", "listsOf_eq_true": the honest cells are "honTK"; the lists without planes and without
  the cut are "zTrue" read through the labels, and "zaTrue". Both hold by unfolding.
* "trFull_out", "trFull_planes", "trFull_cells": the trace outside a shape, at the planes' number,
  and at the other numbers.
* "trFull_small", "trFull_small_all": at a lawful table of scales, a policy within its bounds and a
  request that is served, every entry off the planes is below 129 in absolute value; all entries
  are, if pl has the values 0 and 1 alone.
* "traceFull_eq_some_iff", "traceFull_eq_none_iff": where "traceFull" has a value, and which.

Limits. All is at the reference model's sizes: 12 groups, "Instance ppref", "Cm.Idx", the tables
"tbRef". X is any value of its type: that it comes from a parameter file is asked nowhere in this
file, and at an X whose plans are empty the trace is 0 everywhere. The formulas behind "listsOf" lay
a group's list by the reference's numbers of parts (3 and 1), whatever X's are, while "bNo" and
"noAt" read X's; they agree for public files in the goals' scope ("parts_in_scope",
Johnson/Goal/HonestTrace/FullInScope.lean). The shapes are those of the plans' lists; that a run's
smallness test goes by the same lists is not a matter of this file. pl is a letter: that it holds
the counts of the lookup's keys is not asked here, and "trFull_small" says nothing of it. Which
requests are served is not said here. Among the theorems of this library that exhibit one are: at
all weights 0 ("serves_met", "serves_met_counted", Johnson/HonestTrace/ServesAtRef.lean); at
synthetic weights whose 48 layers are all zero (Johnson/Road/Lane5TopLTrue.lean, "Limits"); and at
synthetic weights in which of the layers' matrices only W_v and W_o of layer 0 are not 0, at a
request with no counted position ("true_layer_ref", Johnson/Road/Lane5TrueLayerAt.lean). (The last
two conclude Policy.IsTrueUnder, which is "Serves": "serves_iff_isTrueUnder",
Johnson/HonestTrace/ServesAtRef.lean.) None of these is at the weights of a trained model. No
theorem of this file shows that "MeetsAll" holds of any trace. The places of attention's cells
("addrA") are written in Johnson/Road/Lane5AttDef.lean by a reading of the verifier's texts; this
file ties them to no program. The bound 129 admits the value 128, which no signed byte has, while by
docs/format/11-1-machinery.md a cell of the programs is a signed byte.
Johnson/HonestTrace/Places.lean lays cells by formulas of its own, at any size; no theorem of this
file compares its matrices with this trace. Johnson/Goal/HonestTrace/FullIsLayInScope.lean does, for
public files in the goals' scope and off the planes.

Not claimed: that a prover's committed cells are this trace; that a verifier accepts a proof made of
it (completeness of the protocol); that the released provers lay zeros where this trace does.
"MeetsAll" is a definition for the use of other files: it states no goal of the library.

-/
import Johnson.Flat.ScalesAt
import Johnson.Road.HeadLinkLPort
import Johnson.Road.FormsKeysAddr
import Johnson.Road.Lane5ForIn
import Johnson.Road.Lane5ForInG
import Johnson.Road.Lane5BridgeA
import Johnson.Road.Lane5SplitG
import Johnson.Road.Lane5SplitA
import Johnson.Road.Lane5SplitH
import Johnson.Road.Ends.HeadForIn
import Johnson.Meaning.Lists
import Johnson.HonestTrace.ServesAtRef
import Johnson.HonestTrace.Names

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (borderOf layerShape)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-! ## The type -/

/-- **A trace**: for each sub-proof's number (from 0) and each number in that sub-proof's list of
matrices (the byte format's mu), a matrix of integers by row of cells and column. The functions are
total: what stands outside a list or a matrix is said by each trace's own definition. -/
abbrev Tr : Type := ℕ → Mats ℤ

/-! ## The honest cells, as the library has them -/

/-- The library's honest cells by names of cells ("Cm.trace"; its head is the head of
Inst/Model/Head/ whose cells include the policy's cost ledger), at the table of scales and the
policy of the public part X, the index i and the request x. It is defined at every i and x, served
or not. -/
abbrev honAt (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) : All.Trace :=
  Cm.trace (Policy.ppOf (scalesAt X) (Hd.polOf X.hS)) i x

/-- "honAt" is the library's term "honTK" (Inst/Model/All/HonestK.lean) at X's scales, the tables
"tbRef", the matrix of the index, the request's tokens and the head's reading of the request under
X's policy. It holds by unfolding. -/
theorem honAt_eq (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) :
    honAt X i x =
      honTK (scalesAt X).kap (scalesAt X).nf (fun _ => tbRef) i.mat x.prompt
        (Head.Req.of (Hd.polOf X.hS) x) :=
  rfl

/-- The cells "honAt" in the library's own matrices, one for each of its 25 segments: at the place
of a valid name that name's cell, 0 at every other place ("Cm.Seg.toMat" at "Cm.Seg.Hd.main", the
head with the cost ledger). Noncomputable: "Cm.Seg.toMat" picks the name at a place by choice. -/
noncomputable def honMx (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) : Mx :=
  Cm.Seg.toMat Cm.Seg.Hd.main (honAt X i x)

/-! ## From the library's matrices to the 25 lists -/

/-- **The lists of the sub-proofs, read out of a family M of the library's matrices**: sub-proof 24
is the head's, an even number below it a group's, an odd one an attention sub-proof's. The formulas
are those of Johnson/Road/: "Hd.zOf" with "mzA" and "Hd.mzH", and "zsOf". They ask no bound of a
row, a column or a number: beyond a matrix's rows an entry is one of another slot of M, and from
number 25 on the formulas go on. "cut" removes all that. -/
def listsOf (X : Model.Verify.Public) (M : Mx) : Tr := fun k =>
  if k = 24 then Hd.mzH X.hS X.y (Hd.zOf M)
  else if k % 2 = 0 then mzA X.y (Hd.zOf M) (k / 2)
  else zsOf (Hd.shapeA X (k / 2)) (k / 2) M

/-- The number, in the list of sub-proof k, of the matrix that holds the planes of the lookup's
multiplicities: bH in the head's list, b in a group's, bA in an attention sub-proof's. These are the
numbers of the verifier's plans by their texts (OnBytes/Model/HeadPlan.lean: matsH;
LayerForms.lean: matIx; AttentionPlan.lean: matrices); no theorem of this file compares them. -/
def bNo (X : Model.Verify.Public) (k : ℕ) : ℕ :=
  if k = 24 then X.hS.NHf + 2
  else if k % 2 = 0 then (matIx X.y).iB
  else (Hd.shapeA X (k / 2)).cf.NAs + 2

/-- In the list of group g, g < 12, it is the number iB of the layers' layout. -/
theorem bNo_even (X : Model.Verify.Public) {g : ℕ} (hg : g < 12) :
    bNo X (2 * g) = (matIx X.y).iB := by
  unfold bNo
  rw [if_neg (by omega), if_pos (by omega)]

/-- In the list of the attention sub-proof of group g it is NAs + 2. -/
theorem bNo_odd (X : Model.Verify.Public) (g : ℕ) :
    bNo X (2 * g + 1) = (Hd.shapeA X g).cf.NAs + 2 := by
  unfold bNo
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]

/-- In the head's list it is NHf + 2. -/
theorem bNo_head (X : Model.Verify.Public) : bNo X 24 = X.hS.NHf + 2 := if_pos rfl

/-- The lists L with the matrix number "bNo X k" of each sub-proof k replaced by pl k, at all rows
and columns. -/
def withPlanes (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (L : Tr) : Tr :=
  fun k a => if a = bNo X k then pl k else L k a

/-! ## The cut to the shapes -/

/-- The list of matrices of the smallness test in the verifier's plan of sub-proof k (2 g: group g;
2 g + 1: its attention sub-proof; 24: the head): for each matrix its name, rows of cells and
columns. Empty where X has no such plan, and from 25 on. -/
def planMats (X : Model.Verify.Public) (k : ℕ) : Array Model.TMat :=
  if 24 < k then #[]
  else if k = 24 then X.H.tl.mats
  else if k % 2 = 0 then (((X.G[k / 2]?).map fun P : Model.Layer.HPlan2 => P.tl).getD {}).mats
  else (((X.A[k / 2]?).map fun P : Attention.Plan => P.seam.tl).getD {}).mats

/-- The place (a, r, c) lies inside sub-proof k's list: a is a number of the plan's list, r is below
the rows and c below the columns of entry a. -/
def InShape (X : Model.Verify.Public) (k a r c : ℕ) : Prop :=
  a < (planMats X k).size ∧ r < ((planMats X k).getD a {}).m ∧ c < ((planMats X k).getD a {}).k

instance (X : Model.Verify.Public) (k a r c : ℕ) : Decidable (InShape X k a r c) := by
  unfold InShape
  infer_instance

/-- **The cut to the shapes**: L at the places inside the plans' lists, 0 at every other place. -/
def cut (X : Model.Verify.Public) (L : Tr) : Tr := fun k a r c =>
  if InShape X k a r c then L k a r c else 0

/-- Inside a shape the cut changes nothing. -/
theorem cut_in (X : Model.Verify.Public) (L : Tr) {k a r c : ℕ} (h : InShape X k a r c) :
    cut X L k a r c = L k a r c := if_pos h

/-- Outside the shapes the cut is 0. -/
theorem cut_out (X : Model.Verify.Public) (L : Tr) {k a r c : ℕ} (h : ¬ InShape X k a r c) :
    cut X L k a r c = 0 := if_neg h

/-! ## The trace at the full size -/

/-- **The trace at the full size**, at the public part X, planes pl, the index i and the request x:
the library's honest cells in the 25 lists, pl k in place of the matrix of multiplicities of
sub-proof k, all cut to the shapes of X's plans. It is defined at every i and x. That it is small,
that the identities are 0 and that the keys lie in their tables is known where the request is
served; its places, zeros and borrowed matrices are known at every request (all for public files in
the goals' scope: Johnson/Goal/HonestTrace/FullInScope.lean). -/
noncomputable def trFull (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) : Tr :=
  cut X (withPlanes X pl (listsOf X (honMx X i x)))

/-- **The weights that the index i holds serve the request x**, at the reference sizes, the tables
"tbRef" and the table of scales and the policy of the public part X: "Serves" of
Johnson/HonestTrace/Serves.lean. -/
def ServesAt (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) : Prop :=
  Serves ppref (scalesAt X).kap (scalesAt X).nf (fun _ => tbRef) (Hd.polOf X.hS) i.index.val x

/-- "ServesAt" is "true under the policy" (Policy/Rel/True.lean) at X's scales and policy. It holds
by definition. -/
theorem servesAt_iff (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) :
    ServesAt X i x ↔ Policy.IsTrueUnder (scalesAt X) (Hd.polOf X.hS) i x :=
  Iff.rfl

/-- **The trace, where there is one**: "trFull X pl i x" where the weights that i holds serve x, and
"none" elsewhere ("traceOf", Johnson/HonestTrace/Serves.lean). X's scales and policy are asked
nothing: at a table that is not lawful there can be a value of which no theorem speaks. -/
noncomputable def traceFull (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) :
    Cm.Idx → Instance ppref → Option Tr :=
  traceOf ppref (scalesAt X).kap (scalesAt X).nf (fun _ => tbRef) (Hd.polOf X.hS)
    (fun i => i.index.val) (trFull X pl)

/-- "traceFull" has the value T exactly if the request is served and T is "trFull X pl i x". -/
theorem traceFull_eq_some_iff (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) (T : Tr) :
    traceFull X pl i x = some T ↔ ServesAt X i x ∧ trFull X pl i x = T :=
  traceOf_eq_some_iff _ _ i x T

/-- "traceFull" is "none" exactly where the request is not served. -/
theorem traceFull_eq_none_iff (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) : traceFull X pl i x = none ↔ ¬ ServesAt X i x :=
  traceOf_eq_none_iff _ _ i x

/-! ## Laws that read no public premise -/

section Free
variable (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref)

/-- **Outside the shapes the trace is 0**: at every X, pl, index and request. -/
theorem trFull_out {k a r c : ℕ} (h : ¬ InShape X k a r c) : trFull X pl i x k a r c = 0 :=
  cut_out X _ h

/-- Inside the shape of the matrix of multiplicities the trace is pl. -/
theorem trFull_planes {k r c : ℕ} (h : InShape X k (bNo X k) r c) :
    trFull X pl i x k (bNo X k) r c = pl k r c := by
  unfold trFull
  rw [cut_in X _ h]
  unfold withPlanes
  rw [if_pos rfl]

/-- Inside the shape of any other matrix the trace is the list that is read out of the library's
matrices of the honest cells. -/
theorem trFull_cells {k a r c : ℕ} (h : InShape X k a r c) (ha : a ≠ bNo X k) :
    trFull X pl i x k a r c = listsOf X (honMx X i x) k a r c := by
  unfold trFull
  rw [cut_in X _ h]
  unfold withPlanes
  rw [if_neg ha]

/-- **Without planes and without the cut the lists are the library's "zTrue" and "zaTrue"**
(Johnson/Road/Lane5TopLTrue.lean) at X's scales and policy: "zTrue" read through the labels of group
g for g < 12, "zaTrue" at g, and "zTrue" read through the head's labels. Equations of functions, at
every X, index and request; they hold by unfolding. -/
theorem listsOf_eq_true :
    (∀ g, g < 12 → listsOf X (honMx X i x) (2 * g) =
      mzA X.y (zTrue (scalesAt X) (Hd.polOf X.hS) i x (2 * g)) g) ∧
    (∀ g, listsOf X (honMx X i x) (2 * g + 1) =
      zaTrue (Hd.shapeA X) (scalesAt X) (Hd.polOf X.hS) i x g) ∧
    listsOf X (honMx X i x) 24 =
      Hd.mzH X.hS X.y (zTrue (scalesAt X) (Hd.polOf X.hS) i x 24) := by
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · unfold listsOf
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]
    rfl
  · unfold listsOf
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]
    rfl
  · unfold listsOf
    rw [if_pos rfl]
    rfl

end Free

/-! ## Small -/

/-- If all entries of M are below B in absolute value, B > 0, so are all entries of the lists that
are read out of M. -/
theorem listsOf_small {X : Model.Verify.Public} {M : Mx} {B : ℤ} (hB : 0 < B)
    (hM : ∀ s r c, |M s r c| < B) (k a r c : ℕ) : |listsOf X M k a r c| < B := by
  unfold listsOf
  split_ifs
  · exact Hd.zOf_small hM hB _ _ _
  · exact Hd.zOf_small hM hB _ _ _
  · unfold zsOf
    split_ifs
    · exact hM _ _ _
    · exact hM _ _ _
    · exact hM _ _ _
    · exact hM _ _ _
    · rw [abs_zero]
      exact hB

/-- **Off the planes every entry of the trace is below 129 in absolute value**, at all sub-proofs'
numbers, numbers in the list, rows and columns, whatever pl is: if X's table of scales is lawful,
its policy is within the library's bounds, and the request is served. Of the matrix of
multiplicities nothing is said. -/
theorem trFull_small {X : Model.Verify.Public} (hs : (scalesAt X).Lawful)
    (hpol : Policy.PolCond (Hd.polOf X.hS)) (pl : ℕ → ℕ → ℕ → ℤ) {i : Cm.Idx}
    {x : Instance ppref} (T : ServesAt X i x) (k a r c : ℕ) (ha : a ≠ bNo X k) :
    |trFull X pl i x k a r c| < 129 := by
  by_cases h : InShape X k a r c
  · rw [trFull_cells X pl i x h ha]
    exact listsOf_small (by norm_num) (honest_smallL hs hpol T) k a r c
  · rw [trFull_out X pl i x h]
    norm_num

/-- **Every entry of the trace is below 129 in absolute value**, the planes' too: if X's table of
scales is lawful, its policy is within the library's bounds, the request is served, and pl has the
values 0 and 1 alone. -/
theorem trFull_small_all {X : Model.Verify.Public} (hs : (scalesAt X).Lawful)
    (hpol : Policy.PolCond (Hd.polOf X.hS)) {pl : ℕ → ℕ → ℕ → ℤ}
    (h01 : ∀ k r c, pl k r c = 0 ∨ pl k r c = 1) {i : Cm.Idx} {x : Instance ppref}
    (T : ServesAt X i x) (k a r c : ℕ) : |trFull X pl i x k a r c| < 129 := by
  by_cases ha : a = bNo X k
  · by_cases h : InShape X k a r c
    · subst ha
      rw [trFull_planes X pl i x h]
      rcases h01 k r c with e | e <;> rw [e] <;> norm_num
    · rw [trFull_out X pl i x h]
      norm_num
  · exact trFull_small hs hpol pl T k a r c ha

/-! ## The format's names -/

/-- The number of a name in the list of a segment ("MatName.no?", Johnson/HonestTrace/Names.lean) at
X's numbers of parts: those of af and ad from the layers' layout, NAs from the shape of the group's
attention plan, NHf from the head's shape. "none" for a name that is not of the segment's sort and
for a part beyond the parts. -/
def noAt (X : Model.Verify.Public) (σ : Seg) (μ : MatName) : Option ℕ :=
  MatName.no? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0) (Hd.shapeA X (σ.no 12 / 2)).cf.NAs
    X.hS.NHf σ μ

/-- A trace read by names, in integers: the entry of the matrix with the name's number in the list
of the segment's sub-proof (12 groups: the head is number 24); 0 where the name has no number, and 0
at a segment of a group from 12 on. A borrowed matrix (qa in an attention segment, xbI from group 1
on, xbL) is answered under the borrower's name from the borrower's list. -/
def byName (X : Model.Verify.Public) (T : Tr) (σ : Seg) (μ : MatName) (r c : ℕ) : ℤ :=
  if Seg.ofNo 12 (σ.no 12) = some σ then
    match noAt X σ μ with
    | some a => T (σ.no 12) a r c
    | none => 0
  else 0

/-- **A trace read by the sub-proof's number and the matrix's label, in the field**: the image of
the integer that "byName" gives at the segment with the number k and the first name of that
segment's list with the label s. A label is a name of the format's pages; a part of af, ad, as or hf
is spelt by the name followed by the part's number ("af0", "af1", "as0", "hf3": "MatName.label"). 0
at every other string, at a label of another sort of segment, at a part beyond the parts, and from
k = 25 on. -/
def cellOf (X : Model.Verify.Public) (T : Tr) (k : ℕ) (s : String) (r c : ℕ) : Cb.Gl.F :=
  match Seg.ofNo 12 k with
  | some σ =>
    match MatName.ofLabel? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
        (Hd.shapeA X (k / 2)).cf.NAs X.hS.NHf σ s with
    | some μ => ((byName X T σ μ r c : ℤ) : Cb.Gl.F)
    | none => 0
  | none => 0

/-! ## Where the head's reader finds a cell -/

/-- A place in a matrix that lies in parts, as a place in a list: n is the number of the first part.
-/
def fromNo (n : ℕ) (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (n + p.1, p.2.1, p.2.2)

/-- The place (number in the head's list, row, column) at which the library's reader of the head's
cells, "Hd.cellsH" at X's shapes, reads feature φ at position t of the matrix hf, hd, hr or of the
borrowed stream x. The library's model has no cell in b: there the value is a placeholder, which no
statement of this file reads, since b has no feature. -/
def placeH (X : Model.Verify.Public) : Head.Mx → ℕ → ℕ → ℕ × ℕ × ℕ
  | .hf, φ, t => fromNo 0 (Hd.placeIn X.HLy.k (X.HLy.m / X.hS.T) X.hS.T φ t)
  | .hd, φ, t => fromNo X.hS.NHf (Hd.placeIn X.HLy.kD (X.HLy.mD / X.hS.T) X.hS.T φ t)
  | .hr, φ, t => fromNo (X.hS.NHf + 1) (Hd.placeIn X.HLy.kR (X.HLy.mR / X.hS.T) X.hS.T φ t)
  | .b, _, _ => (X.hS.NHf + 2, 0, 0)
  | .x, φ, t =>
    fromNo (X.hS.NHf + 3) (Hd.placeIn (borderOf X.y).kxb ((borderOf X.y).mxb / X.hS.T) X.hS.T
      ((borderOf X.y).cell (φ / X.hS.d) (φ % X.hS.d)) t)

/-- "Hd.cellsH" reads the entry at "placeH", for all four matrices, every list M, feature and
position. It holds by unfolding. -/
theorem cellsH_placeH (X : Model.Verify.Public) (M : Mats ℤ) (φ t : ℕ) :
    (Hd.cellsH X.hS X.HLy (borderOf X.y) M).hf φ t = zAt M (placeH X .hf φ t) ∧
    (Hd.cellsH X.hS X.HLy (borderOf X.y) M).hd φ t = zAt M (placeH X .hd φ t) ∧
    (Hd.cellsH X.hS X.HLy (borderOf X.y) M).hr φ t = zAt M (placeH X .hr φ t) ∧
    (Hd.cellsH X.hS X.HLy (borderOf X.y) M).x φ t = zAt M (placeH X .x φ t) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## What is known of the honest trace, in one bundle -/

/-- **What is known of the honest trace, as statements on a trace T**, at the public part X, the
index i and the request x. Every field is stated with predicates that lie outside Johnson/Goal/. A
file that cannot import the files under Johnson/Goal/ can take the bundle as a hypothesis; that it
holds of "trFull X pl i x" is shown there, for public files in the goals' scope, a request that is
served and planes with the values 0 and 1 (Johnson/Goal/HonestTrace/FullInScope.lean:
"meetsAll_in_scope"). Keys, identities, tables and readers are this library's terms. Of the planes
the bundle says that their entries are below 129 and 0 outside the shape, and no more. It states no
goal of the library. -/
structure MeetsAll (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (T : Tr) :
    Prop where
  /-- every entry, at all numbers, rows and columns, is below 129 in absolute value -/
  small : ∀ k a r c, |T k a r c| < 129
  /-- outside the shapes of the plans' lists every entry is 0 -/
  out : ∀ k a r c, ¬ InShape X k a r c → T k a r c = 0
  /-- in a group's list: an entry of a matrix other than b, and other than the borrowed xbI of a
  later group, is 0 at every place where the library's rule "placeOf" puts no valid name's cell -/
  fillG : ∀ g < 12, ∀ a r c, a ≠ (matIx X.y).iB → (0 < g → a ≠ (matIx X.y).iXI) →
    (∀ q : FFSeg.Cell, q.Valid DF → placeOf X.y DF q ≠ (a, r, c)) → T (2 * g) a r c = 0
  /-- in an attention sub-proof's list: an entry of a matrix other than bA and the borrowed qa is 0
  at every place where the library's rule "addrA" puts no valid name's cell -/
  fillA : ∀ g < 12, ∀ a r c, a ≠ (Hd.shapeA X g).cf.NAs + 2 → a ≠ (Hd.shapeA X g).cf.NAs + 3 →
    (∀ q : AttSeg.Raw, q.Valid DA → addrA (Hd.shapeA X g) q ≠ (a, r, c)) →
    T (2 * g + 1) a r c = 0
  /-- in the head's list: an entry of a matrix other than bH and the borrowed stream is 0 at every
  place where "placeH" puts no feature that holds a cell, at any position -/
  fillH : ∀ a r c, a ≠ X.hS.NHf + 2 → a ≠ X.hS.NHf + 3 →
    (∀ μ : Head.Mx, μ ≠ .x → ∀ φ < Head.nFeat μ, ∀ t < Head.nT, placeH X μ φ t ≠ (a, r, c)) →
    T 24 a r c = 0
  /-- at every valid name of a feed-forward segment the library's reader finds in the group's list
  the honest cell, own or borrowed -/
  readG : ∀ g < 12, ∀ q : FFSeg.Cell, q.Valid DF →
    cellsOf DF (cellsAt X.y (T (2 * g))) q = (honAt X i x).vFF g q
  /-- the same at every valid name of an attention segment -/
  readA : ∀ g < 12, ∀ q : AttSeg.Raw, q.Valid DA →
    cellsA (Hd.shapeA X g) (T (2 * g + 1)) q = (honAt X i x).vAtt g q
  /-- the same at every position and every feature that holds a cell of hf, hd, hr and of the stream
  that the head borrows -/
  readH : ∀ t < Head.nT,
    (∀ φ < Head.nFeat .hf,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (T 24)).hf φ t = (honAt X i x).vHead.hf φ t) ∧
    (∀ φ < Head.nFeat .hd,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (T 24)).hd φ t = (honAt X i x).vHead.hd φ t) ∧
    (∀ φ < Head.nFeat .hr,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (T 24)).hr φ t = (honAt X i x).vHead.hr φ t) ∧
    ∀ φ < Head.nFeat .x,
      (Hd.cellsH X.hS X.HLy (borderOf X.y) (T 24)).x φ t = (honAt X i x).vHead.x φ t
  /-- "OrdsN" (Johnson/Meaning/Lists.lean): each of the 25 lists meets its statement "LayerOrd",
  "AttOrd" or "Hd.HeadOrdLB" (small; identities 0; keys in their tables), and each borrowed matrix
  has its owner's entries at all rows and columns -/
  ords : OrdsN (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
    (Hd.shapeA X) i.mat x (fun g => T (2 * g)) (fun g => T (2 * g + 1)) (T 24)
  /-- the clause "Alg.ForInG" of a group's lookup: every entry of the library's key vectors "kvG",
  at the group's list and the index's matrix of the weights' digits (i.mat), is a row of its call's
  table; whatever the tokens that are laid into the layers' public numbers -/
  keysG : ∀ g < 12, ∀ tokv : Array ℕ,
    Alg.ForInG { X.layers with tokv := tokv } g (T (2 * g)) i.mat
  /-- the clause "ForInA" of an attention sub-proof's lookup, and the same as "InTables" at
  "callsA": every entry of the library's key vectors "kvA" is a row of its call's table, at the
  lookup shape of the group's attention plan -/
  keysA : ∀ g < 12,
    ForInA (Hd.shapeA X g) (((X.A[g]?).map (·.fs)).getD default) (cellZ (T (2 * g + 1))) ∧
    (callsA (Hd.shapeA X g) (((X.A[g]?).map (·.fs)).getD default) (T (2 * g + 1))).InTables
  /-- the clause "Hd.ForInH" of the head's lookup, at every value R of the head's run data that has
  X's shape and layout, whose covered and counted positions are the request's, and whose checked
  token at each covered position is the request's ("Hd.ReqFits"). "Hd.runReq R0 x" is such a value
  for every R0 with that shape and layout (Johnson/Road/Ends/HeadWit.lean) -/
  keysH : ∀ R : Model.Head.Run, R.h = X.hS → R.L = X.HLy →
    Hd.ReqFits R HeadSizes.ref (Head.Req.of (Hd.polOf X.hS) x) →
    Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay (T 24) i.mat).K

section Bundle
variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- From the bundle: the meaning of a group of layers without its lookup clause ("LayerR0": entries
inside the shapes of the matrices that hold cells below 2^18; every identity of the library 0 modulo
the prime). -/
theorem MeetsAll.layerR0 (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) :
    LayerR0 (layerShape X.P) X.layers.sc X.y g (T (2 * g)) i.mat x :=
  (layerOrd_iff_split.1 (M.ords.layer g hg)).1

/-- From the bundle: the meaning of an attention sub-proof without its lookup clause ("AttR0": the
cells at valid names below 2^18; every identity of the library 0 modulo the prime). -/
theorem MeetsAll.attR0 (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) :
    AttR0 (Hd.shapeA X g) (T (2 * g + 1)) :=
  (attOrd_iff_split.1 (M.ords.att g hg)).1

/-- From the bundle: the meaning of the head without its lookup clause ("HeadR0"). -/
theorem MeetsAll.headR0 (M : MeetsAll X i x T) :
    HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) x (T 24) :=
  (headOrdLB_iff_split.1 M.ords.head).1

end Bundle

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.honAt_eq
#print axioms OnBytes.HonestTrace.bNo_even
#print axioms OnBytes.HonestTrace.bNo_odd
#print axioms OnBytes.HonestTrace.bNo_head
#print axioms OnBytes.HonestTrace.cut_in
#print axioms OnBytes.HonestTrace.cut_out
#print axioms OnBytes.HonestTrace.servesAt_iff
#print axioms OnBytes.HonestTrace.traceFull_eq_some_iff
#print axioms OnBytes.HonestTrace.traceFull_eq_none_iff
#print axioms OnBytes.HonestTrace.trFull_out
#print axioms OnBytes.HonestTrace.trFull_planes
#print axioms OnBytes.HonestTrace.trFull_cells
#print axioms OnBytes.HonestTrace.listsOf_eq_true
#print axioms OnBytes.HonestTrace.listsOf_small
#print axioms OnBytes.HonestTrace.trFull_small
#print axioms OnBytes.HonestTrace.trFull_small_all
#print axioms OnBytes.HonestTrace.cellsH_placeH
#print axioms OnBytes.HonestTrace.MeetsAll.layerR0
#print axioms OnBytes.HonestTrace.MeetsAll.attR0
#print axioms OnBytes.HonestTrace.MeetsAll.headR0
#print axioms OnBytes.HonestTrace.honAt
#print axioms OnBytes.HonestTrace.InShape
#print axioms OnBytes.HonestTrace.ServesAt
#print axioms OnBytes.HonestTrace.fromNo
#print axioms OnBytes.HonestTrace.MeetsAll
#print axioms OnBytes.HonestTrace.honMx
#print axioms OnBytes.HonestTrace.listsOf
#print axioms OnBytes.HonestTrace.bNo
#print axioms OnBytes.HonestTrace.withPlanes
#print axioms OnBytes.HonestTrace.planMats
#print axioms OnBytes.HonestTrace.cut
#print axioms OnBytes.HonestTrace.trFull
#print axioms OnBytes.HonestTrace.traceFull
#print axioms OnBytes.HonestTrace.noAt
#print axioms OnBytes.HonestTrace.byName
#print axioms OnBytes.HonestTrace.cellOf
#print axioms OnBytes.HonestTrace.placeH
