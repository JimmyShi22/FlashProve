-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionPlan.lean: the plan of an attention sub-proof.

The plan is everything about the sub-proof that follows from public numbers, before a word of a
proof is read: the shape with its lookup calls, the matrices of the smallness test, the list of
committed arrays, and the counts of scalars and of linear claims. The check of the sub-proof
(OnBytes/Model/Attention.lean) starts from a plan and compares its own counts with the plan's.

The smallness test is the last part of every kind of sub-proof (OnBytes/Model/Tail.lean). The record
Seam stores what the attention sub-proof needs of it. Seam.shape and Seam.plan set it up.

The matrices of the smallness test are, in their order: the parts of `as` (as0, as1 and so on), ah,
ao, bA and qa. The layer sub-proof has committed to qa, and this sub-proof reads it there.
OnBytes/Model/AttentionHeard.lean explains the five matrices and the other terms.

A function here returns its result or the name of the test that failed. The names and the order of
the tests are those of the C++ verifier (verifier/src/vf_attention_check.h: AttentionSeam and
AttentionSubProof::plan), by a reading of that source (no theorem).

The section The plan says how the natural numbers here relate to the C++ verifier's words (Widths).
The caller must have tested the ranges that the docstring of Cfg (AttentionShape.lean) lists; that
the two then agree is arithmetic outside Lean, and no theorem and no test here covers it.

Main definitions: In, Seam, Seam.shape, Seam.plan, Counts, matrices, ownScalars, ownClaims,
tableReads, Plan, plan, planNames.

This file reads no proof and holds no theorem.
-/
import OnBytes.Params.SubRounds
import OnBytes.Model.Tail
import OnBytes.Model.AttentionShape
import OnBytes.Model.AttentionSums

namespace OnBytes.Attention

/-! ## What the caller passes -/

/-- What the caller of plan passes besides the configuration. No line of the parameter file sets a
width parameter (TMat.wp), so all five are 0. -/
structure In where
  /-- the security target in bits (the line sec) minus the bits of proof of work before a draw of
  positions in a request's own rounds (Settings.pow); not 0 -/
  hb : Nat := 0
  /-- the number of this sub-proof among all sub-proofs -/
  gid : Nat := 0
  /-- the columns of the owner's array that holds qa -/
  ktO : Nat := 0
  /-- the first column of qa in the owner's array that holds it; must be 0 -/
  col0Q : Nat := 0
  /-- 1 plus the number of sub-proofs other than the owner that read the owner's array that holds
  qa; not 0 -/
  aO : Nat := 0
  /-- the number that names the matrix qa, as its owner gave it -/
  midQ : Nat := 0
  /-- the width parameter of every part of `as` -/
  wpS : Nat := 0
  /-- the width parameter of ah -/
  wph : Nat := 0
  /-- the width parameter of ao -/
  wpo : Nat := 0
  /-- the width parameter of bA -/
  wpbA : Nat := 0
  /-- the width parameter of qa: its owner's value -/
  wpq : Nat := 0
  deriving Repr, Inhabited

/-! ## The seam to the smallness test -/

/-- What the plan stores of the sub-proof's smallness test. -/
structure Seam where
  /-- the smallness test -/
  tl : Model.HTailF2 := {}
  /-- a state of a sub-proof whose field trees lists the arrays -/
  Fp : Model.Fork := {}
  /-- what the list stores of each array besides its entry in Fp.trees -/
  Tp : Model.Tail2 := {}
  /-- the lengths of the vectors U1 to U3; the sub-proof has only U3 -/
  nU : Array Nat := #[0, 0, 0]

/-- The last matrix of the list that another sub-proof has committed to, if there is one. -/
def foreignOf (m : Array Model.TMat) : Option Model.TMat :=
  m.foldl (fun r M => if M.kind == 1 then some M else r) none

/-- Sets the shapes of the smallness test from the list m of matrices. The one matrix of kind 1, qa,
is read from an array that the layer sub-proof committed to. col0F is the first column of qa in that
array and must be 0. ktO is the width of that array and must be the number of columns of qa, so that
qa fills the array. aO is the owner's count of the array's users. g holds the run's numbers. tau is
the number of random combinations and must be g.tau. Of the vectors U1 to U4 an attention sub-proof
has only U3. No other sub-proof reads one of its own matrices. The record of the owner's array (PXo)
is rebuilt here and not taken from the owner's plan: K and a are the arguments ktO and aO, and m and
wp are those of qa in the list m. OnBytes/Model/VerifyCross.lean compares the array's shape in this
plan with its shape in the owner's plan (internal-a-owner-shape). -/
def Seam.shape (g : Model.Settings) (m : Array Model.TMat) (tau col0F ktO aO : Nat) :
    Except String Seam := do
  let seed : Model.HTailF2 := { tau := g.tau, lidb := g.lidb }
  if m.any (fun M => M.kind != 0 && M.kind != 1) then throw "hid-a-weight-matrix"
  let m1 := m.map fun M => if M.kind == 1 then { M with foreign := some 0, ttOff := 0 } else M
  let q := foreignOf m1
  if col0F != 0 || ktO != (q.map (·.k)).getD 0 then throw "internal-a-TX-place"
  let f : Model.T2Foreign :=
    { name := "PXo", K := ktO, a := aO, m := (q.map (·.m)).getD 0, wp := (q.map (·.wp)).getD 0 }
  let tl ← seed.shape m1 (Array.replicate m1.size none) #[f] #[false, false, true, false] tau
  pure { tl := tl }

/-- The index of U3 in the list of arrays. U3 is in the list, since Seam.shape requests it. -/
def Seam.iU3 (s : Seam) : Nat := (s.tl.ix.U.getD 2 none).getD 0

/-- The number of scalars that the smallness test sends. -/
def Seam.smallElems (s : Seam) : Nat := s.tl.smallElems

/-- Makes the list of arrays: U3, one symbol array for each own matrix, the two arrays of the
smallness test, and the owner's array that holds qa. addTrees makes the list, and of the list this
function itself tests only the length. nU3 is the length of U3. For hb and hbLine see
Model.HTailF2.addTreesF. -/
def Seam.plan (s : Seam) (nU3 hb hbLine : Nat) : Except String Seam := do
  let nU := #[0, 0, nU3]
  let (tl, Fp, T) ← s.tl.addTrees {} {} nU #[] hb hbLine
  if Fp.trees.size != 1 + tl.pkMat.size + 2 + 1 then throw "internal-a-tree-list"
  let Tp ← Model.t2Plan Fp T
  pure { tl := tl, Fp := Fp, Tp := Tp, nU := nU }

/-! ## The counts over the calls -/

/-- What one pass over the lookup calls counts. -/
structure Counts where
  /-- the scalars sent for the key forms of the calls of kinds KR and KFD -/
  msg : Nat := 0
  /-- the pieces of all score segments together -/
  sumNp : Nat := 0
  /-- the segments rm and rd that are present in a call of kind KR -/
  nKRp : Nat := 0
  /-- the segments fm and fd that are present in a call of kind KFD -/
  nKFp : Nat := 0
  /-- for each segment fm or fd that is present in a call of kind KFD, in the order of the calls:
  the number of variables of its sumcheck and the number of the segment's pieces -/
  score : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- Adds a segment of a call of kind KR, if the call holds it: three plane values. -/
def Counts.plane (k : ACall) (x : Counts) (s : Seg) : Counts :=
  if k.holds s then { x with nKRp := x.nKRp + 1, msg := x.msg + 3 } else x

/-- Adds a segment of a call of kind KFD, if the call holds it: seven values and a sumcheck of
products with one pair for each piece. -/
def Counts.scores (S : Shape) (k : ACall) (x : Counts) (s : Seg) : Counts :=
  if k.holds s then
    let np := k.npOf s
    { x with
      nKFp := x.nKFp + 1
      sumNp := x.sumNp + np
      msg := x.msg + (7 + sc3Slots (S.nvKF s) np)
      score := x.score.push (S.nvKF s, np) }
  else x

/-- Adds one call. -/
def Counts.call (S : Shape) (x : Counts) (k : ACall) : Counts :=
  let y := if k.kind == .kr then [Seg.rm, Seg.rd].foldl (Counts.plane k) x else x
  if k.kind == .kfd then [Seg.fm, Seg.fd].foldl (Counts.scores S k) y else y

/-- The counts over all calls of the shape. -/
def Counts.of (S : Shape) : Counts := S.calls.foldl (Counts.call S) {}

/-! ## The matrices of the smallness test -/

/-- A matrix that this sub-proof commits to. Its number is 256 gid plus its index in the list. -/
def ownMatrix (i : In) (name : String) (m k place wp : Nat) : Model.TMat :=
  { name := name, m := m, k := k, kind := 0, aId := i.gid * 256 + place, wp := wp }

/-- The list of matrices of the smallness test. qa has the number that its owner gave it. -/
def matrices (S : Shape) (i : In) : Array Model.TMat :=
  let c := S.cf
  let parts := (List.range c.NAs).map fun q =>
    ownMatrix i ("as" ++ toString q) (2 ^ c.lmS) (S.kAs / c.NAs) q i.wpS
  parts.toArray ++ #[
    ownMatrix i "ah" (c.wcH * S.T) (S.fillH / c.wcH) c.NAs i.wph,
    ownMatrix i "ao" (c.wcO * S.T) (S.fillO / c.wcO) (c.NAs + 1) i.wpo,
    ownMatrix i "bA" (2 ^ c.lmb) S.kbA (c.NAs + 2) i.wpbA,
    { name := "qa", m := c.wcQ * S.T, k := S.fillQ / c.wcQ, kind := 1, foreign := some 0,
      aId := i.midQ, wp := i.wpq }]

/-! ## The counts of scalars, claims and reads -/

/-- The number of scalars that the sub-proof sends, without those of the smallness test. x holds the
counts over the calls. The lines follow the order of the messages: the lookup and the values for
the key forms of the calls of kinds KR and KFD; the division; the value product; the maximum and the
bits of the index. -/
def ownScalars (S : Shape) (fs : Model.Forest.Shape) (x : Counts) : Nat :=
  let lt := S.cf.lt
  Model.Forest.elems fs + x.msg +
  (7 + lt + sc3Slots S.nvE S.NP) +
  (2 + sc3Slots S.nvVM S.NP + sc3Slots S.nvVD S.NP) +
  (S.NP + sc3Slots S.nvF S.NP +
    Model.sumcheckSlotsDegrees S.scdDegrees (S.Lam + S.NP * lt) (lt + 1) + sc3Slots S.nvH S.NP)

/-- The number of linear claims of the sub-proof, without those of the smallness test. The terms
are, in this order: the lookup's own claims; those on the plane values, on the scores and on the
division; the join; those on the value product; those on the maximum and on the bits of the index;
the lookup's three claims on bA; and one row for each sumcheck. (The comments of
AttentionSubProof::plan number these groups 1 to 9.) -/
def ownClaims (S : Shape) (fs : Model.Forest.Shape) (x : Counts) : Nat :=
  let lt := S.cf.lt
  Model.Forest.lins fs + 3 * x.nKRp + (6 * x.nKFp + 2 * x.sumNp) + (5 + lt + 2 * S.NP) + 1 +
  (1 + 4 * S.NP) + (4 * S.NP + S.Lam + S.NP * lt) + 3 + (x.nKFp + 5 + 1)

/-- The number of reads of the smallness test: one for each table and each block of rows of the
table's matrix. -/
def tableReads (S : Shape) (x : Counts) : Nat :=
  let c := S.cf
  3 * c.NAs + (x.nKFp + 6) * c.wcH + c.wcO * S.T / 2 ^ c.la +
  (2 * x.nKFp + 5) * (c.wcQ * S.T / 2 ^ c.la) + 3

/-! ## The plan

Widths. All numbers here are natural numbers. The C++ verifier counts in 64 bits, and it stores the
number of slots and the sizes of the own rounds, except rows, in 32 bits. The two agree as long as
no count reaches 2^64 and none of the numbers stored in 32 bits reaches 2^32. The number of slots is
tested to be below 2^30 (hid-a-slots). The caller must have tested the ranges of the configuration's
numbers that the docstring of Cfg lists. Within these ranges every count stays far below 2^64, and
the sizes of the own rounds far below 2^32. The number of slots stays below 2^19 there, so
hid-a-slots refuses no configuration within these ranges: the plan's formulas for the slots give at
most 310,209 over these ranges. That is arithmetic outside Lean; no theorem and no test here covers
it.
-/

/-- The plan of an attention sub-proof. -/
structure Plan where
  /-- the shape, with the lookup calls -/
  S : Shape
  /-- the shape of the one group of all calls, with the padding keys of each tree -/
  fs : Model.Forest.Shape
  /-- the numbers that the parameter file sets for the run -/
  settings : Model.Settings
  /-- what the caller passed -/
  inp : In
  /-- the smallness test and the list of arrays -/
  seam : Seam
  /-- the number of slots: one for each scalar sent, so it equals nMsg -/
  ns : Nat
  /-- the number of scalars sent -/
  nMsg : Nat
  /-- the number of linear claims -/
  nLin : Nat
  /-- the number of lookup calls -/
  NC : Nat
  /-- the number of pairs (lam, a) -/
  NP : Nat
  /-- the number of units with a segment rm or rd; stored because the C++ record has it: nothing
  reads it -/
  nKRp : Nat
  /-- the number of units with a segment fm or fd; stored because the C++ record has it: nothing
  reads it -/
  nKFp : Nat
  /-- the length of U3, the vector that holds the tables -/
  nW : Nat
  /-- the sizes of the sub-proof's own rounds -/
  own : Params.AttentionRounds

/-- The limit on the depth of a tree of a lookup. -/
def Plan.lid (P : Plan) : Nat := P.settings.lidb

/-- The index of U3 in the list of arrays. -/
def Plan.iU3 (P : Plan) : Nat := P.seam.iU3

/-- The matrices of the smallness test. -/
def Plan.mats (P : Plan) : Array Model.TMat := P.seam.tl.mats

/-- Makes the plan from the run's numbers, what the caller passes, and the configuration. cf.Ty must
be 2^(1 + lbz) (2 beta_z in the C++). own.rows counts the linear claims and the equations of the
smallness test: the equations have no challenge of their own and are under further powers of the
element that batches the claims. plan takes its arguments as given: it does not compare i.hb with
settings.hb, and it ties nothing to what the chain has hashed (HTailF2.shapeF and addTreesF,
OnBytes/Model/Tail.lean, leave both to it). Its caller, group (OnBytes/Model/AttentionConfig.lean),
forms i.hb from the same settings and fills the configuration from the parameter file as read, the
layers' layout and the file of scales. OnBytes/Model/VerifyStatement.lean compares the parameter
file's numbers with the statement that the chain binds. -/
def plan (settings : Model.Settings) (i : In) (cf : Cfg) : Except String Plan := do
  if i.hb == 0 then throw "hid-hb"
  if i.aO == 0 then throw "hid-a-owner-uses"
  if cf.Ty != 2 ^ (1 + Model.lbz) then throw "internal-a-Ty"
  let (S, fs) ← shapeHid settings.lidb cf
  let c := S.cf
  if c.NAs + 4 > 256 then throw "hid-a-fold-list"
  let seam0 ← Seam.shape settings (matrices S i) settings.tau i.col0Q i.ktO i.aO
  let x := Counts.of S
  let msg := ownScalars S fs x + seam0.smallElems
  if seam0.tl.NM != c.NAs + 4 then throw "internal-a-claim-count"
  let reads := tableReads S x
  let nLin := ownClaims S fs x + seam0.tl.lins reads
  let own : Params.AttentionRounds :=
    { lt := c.lt, lgk := c.lgk, pairs := S.NP, Lam := S.Lam, planeMessages := x.nKRp,
      score := x.score.toList, e := S.nvE, valueM := S.nvVM, valueD := S.nvVD, attained := S.nvF,
      bits := S.nvH, rows := nLin + seam0.tl.equationsF reads }
  if msg ≥ 2 ^ 30 then throw "hid-a-slots"
  let nW := S.tableElems
  let seam ← seam0.plan nW i.hb settings.hb
  pure { S := S, fs := fs, settings := settings, inp := i, seam := seam, ns := msg, nMsg := msg,
         nLin := nLin, NC := S.calls.size, NP := S.NP, nKRp := x.nKRp, nKFp := x.nKFp, nW := nW,
         own := own }

/-- The names under which this file refuses. The functions that it calls refuse under further names,
which their files list. -/
def planNames : List String :=
  ["hid-a-weight-matrix", "internal-a-TX-place", "internal-a-tree-list", "hid-hb",
    "hid-a-owner-uses", "internal-a-Ty", "hid-a-fold-list", "internal-a-claim-count", "hid-a-slots"]

end OnBytes.Attention
