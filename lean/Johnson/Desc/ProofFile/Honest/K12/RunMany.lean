-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunMany.lean: a `RunJob` (RunJob.lean) for a group of several
oracle messages. Each member gives its own rows and tails as lists of words, computed from the
prover's input, what precedes the test, and its own random values alone. `ManyJob.toRun` places them
at the members' blocks and lists the trees. Definitions only. It imports Mathlib through
RunJob.lean; rows and trees are computed on words (RunLay.lean, RunRows.lean, ColW.lean).

  `Mem`          a member: who sent it and how many random values it has (as in `TestJob.members`);
                 its public numbers; its rows
  `ManyJob`, `ManyJob.s₀`   what a caller supplies: the test's parameters; the members, in the
                 group's order; who sent the first fresh table; the state on entry to the test; each
                 tree as its depth and its pieces
  `ManyJob.toRun`   the `RunJob`. The theorems on a `RunJob` apply to it as they are: `runJob_eq`
                 (RunJobLaw.lean), `lightHalfOf_eq` (PartsByJobLaw.lean)
  `firstOr`, `sameCode`, `ManyJob.layFits`   a check: the job's public numbers are those of a
                 verifier's state: the stage's k, h and two codes, and each member's counts of rows,
                 first rows and base field (`Statement.layout`, OnBytes/Iop/Ground.lean)

Random values. The function for member t's rows receives `mem t`, that member's random values, and
no other. Nothing else here reads a random value.

Limits.
- `layFits` and `RunJob.rowsFit` are checks that a caller may evaluate; no definition of a run or of
  a part asks them, and none fails where one is false. Together they are meant to tell a member's
  short or missing row or tail: `layFits` compares the counts, `rowsFit` the lists; no lemma says
  that they do (see RunLay.lean's limits). `layFits` takes the state as an argument; that it is the
  job's state on entry is up to the caller. By type neither is a function of public data alone.
  `rowsFit` reads the prover's input, what precedes the test and the members' random values.
  `layFits` reads the state's public part (`layFits_pub`, FitSharedLaw.lean) and, of the job, the
  parameters and the members' shapes alone (`layFits_pubJob`, FitSharedAt.lean).
- Both are true in these cases, in which a 0 or another use's value still stands where a random
  value is due: a member whose stated count of random values (`Mem.sent`) is below what its rows
  read (beyond the count a reader gives 0); a first fresh table that its sender made at another k, h
  or code than the first stage's (it is no member). For the shared chain's two jobs FitShared.lean
  has checks on public data for the lists' lengths and for that table's numbers; the theorems on
  them are in FitSharedLaw.lean and FitSharedAt.lean.
- A kept member is not supported: `layFits` is false at one.
- Nothing compares the trees with what the senders sent.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunJob
import Johnson.Desc.ProofFile.Honest.K12.RunLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt)
open VerifiableInference.Desc.K12 (P12 T12)

variable {W X : Type}

/-- **A member of the group.** -/
structure Mem (W X : Type) where
  /-- the address of the part that sent it, its number in that sending, how many random values it
  has -/
  sent : Addr × ℕ × Due
  shape : MemShape
  /-- its main rows, their tails, its mask rows, their tails, computed from the input, what precedes
  the test, and its own random values. The two fields for a fresh table are not read -/
  rows : W → Front X → Stretch → PSt

/-- **What a caller supplies for a test on a group of several members.** -/
structure ManyJob (W X : Type) where
  p : P12
  /-- in the group's order -/
  mems : List (Mem W X)
  fresh : Option (Addr × ℕ)
  rec₀ : W → Front X → T12
  /-- the trees that the first round of positions opens, in the order of the declared openings -/
  trees : List (ℕ × List Piece)

/-- The first stage; a stage of zeros where there is none. -/
def ManyJob.s₀ (A : ManyJob W X) : Stage := A.p.nums.stages.headD default

/-- **The `RunJob`.** -/
def ManyJob.toRun (A : ManyJob W X) : RunJob W X :=
  { p := A.p, members := A.mems.map (·.sent), fresh := A.fresh, rec₀ := A.rec₀
    rows := fun w fr mem =>
      layFirst A.s₀ (A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2)))
    trees := treesOf A.s₀ (A.mems.map (·.shape)) A.trees }

/-- The first row of a block, as `Statement.layout` has it: none where there is no such row. -/
def firstOr (rows first : ℕ) : Option ℕ := if rows == 0 then none else some first

/-- A code of OnBytes/ and a code of Fmt/ have the same three numbers. -/
def sameCode (c : OnBytes.Code) (d : Fmt.M1.Code) : Bool :=
  c.logN == d.a && c.ell == d.l && c.r == d.r

/-- **The job's public numbers are those of the state t**, for the group under test; t is any value
of the type of the verifier's state. The first stage's k and h are the layout's
(`Statement.layout`), and its two codes are the group's. There are as many members, and for each: it
is not kept; its numbers of main and mask rows are its oracle message's; the first rows of its two
blocks are the layout's; where it has main rows, `base` says whether they are over the base field.
-/
def ManyJob.layFits (A : ManyJob W X) (t : T12) : Bool :=
  match t.st.layout t.g, t.st.groups[t.g]? with
  | some L, some G =>
    L.k == A.s₀.k && L.h == A.s₀.h && L.members.size == A.mems.length &&
      sameCode (t.st.codes.base.getD G.code default) A.s₀.C &&
      sameCode (t.st.codes.mask.getD G.maskCode default) A.s₀.Z &&
      A.mems.zipIdx.all fun m =>
        let o := (t.st.oracles.getD (L.members.getD m.2 OnBytes.noId) default).shape
        !L.kept.getD m.2 false && o.mainRows == m.1.shape.mainRows &&
          o.maskRows == m.1.shape.maskRows &&
          (o.mainRows == 0 || (o.mainDeg == 1) == m.1.shape.base) &&
          L.mainFirst.getD m.2 none == firstOr m.1.shape.mainRows m.1.shape.mainFirst &&
          L.maskFirst.getD m.2 none == firstOr m.1.shape.maskRows m.1.shape.maskFirst
  | _, _ => false

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Mem
#print axioms ProofFile.Honest.K12.Light.ManyJob
#print axioms ProofFile.Honest.K12.Light.ManyJob.s₀
#print axioms ProofFile.Honest.K12.Light.ManyJob.toRun
#print axioms ProofFile.Honest.K12.Light.firstOr
#print axioms ProofFile.Honest.K12.Light.sameCode
#print axioms ProofFile.Honest.K12.Light.ManyJob.layFits
