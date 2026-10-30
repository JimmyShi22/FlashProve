-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqTailReturns.lean: THE SMALLNESS TEST: THE TEXT OF THE LIST "K8.equations"
BEHIND ITS FIRST FOUR CLAIMS (`eqTail`, Johnson/Desc/First/TailClaims/EquationsTotal.lean: the
weights and sums, one tie a matrix, the reads in four nested loops, nine tests at the end) RETURNS,
UNDER PREMISES ON NUMBERS, FLAGS, MARKS AND LENGTHS AND ONE TEST ON VALUES. A FEW DEFINITIONS AND
ONE STATEMENT, as a definition of a proposition; no proof stands here. A lemma; none of the
library's goals.

The reads' order is the library's own list `readsList tl funs` (OnBytes/Tie/Pv/Tail/EndLoops.lean):
the premises on the nest are said over it.
  `noMarks tl`        no entry of the vectors of reads is marked
  `marksOf tl funs`   the marks behind all reads: the library's `markRead`, read by read
  `tiesOnOf tl n`     for each of n arrays: how many ties lie on it
  `numbersFrom a n`   the n numbers from a on
  `LaidBy R q l cs`   the claims cs are laid for the members of l, one each, in order; R: what a
                       claim is to its number, from q on, and its member
  `TailReady …`       the premises: see each field
  THE TEST ON VALUES: `LiveAt tl' x` (Johnson/Desc/K8/Honest/FallLive.lean) for each read x of the
                       list: behind the weights' step no sum of a column of a matrix on which a
                       read lies is the element 0
  `Spec.eqTail_returns`
Behind: the data that `eqWeights` leaves (`Laid`), with the ties' numbers, the counts of ties and
the number of reads laid in; the ledger as it was; behind the claims in front one tie for each
matrix (`TieClaim`), then one claim for each read of the list (`ReadClaim`), in the list's order.
EVERY FIELD OF `TailReady` IS A DEBT WITH A NAME: whoever says that this text returns at a state of
a run has to show all seventeen, and a test on the state's shape that is to stand for them has to
hold them all: `four` · `drawn` · `plan` · `one` · `fresh` · `fits` · `table` · `reads` · `marks` ·
`allSet` · `inList` · `tile1` · `tile3` · `kinds` · `sum` · `count` · `apart`.
Limits. Nothing says that the premises hold at any state of a run. NO ARITHMETIC ON A PLAN's NUMBERS
IS DONE HERE: that no read is marked twice, that all marks are set, that the tables tile and that
the counts meet are premises, each a test with code. The test on values speaks of the data behind
the weights' step; that it follows where no column's weight at the batching element is 0 is said
elsewhere. That the data behind that step have the numbers of the data in front (the matrices, their
list's length and so on) is not said field by field: it is `Laid.rest`.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqReturns
import Johnson.Desc.First.TailClaims.EquationsTotal
import Johnson.Desc.First.TailClaims.RetRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret eqTail)
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- No entry of the vectors of reads is marked. -/
def noMarks (tl : HTailF2) : Array (Array Bool) := tl.tabLen.map fun n => Array.replicate n false

/-- The marks behind all reads. -/
def marksOf (tl : HTailF2) (funs : Array HFun) : Option (Array (Array Bool)) :=
  (readsList tl funs).foldlM (fun rd x => tl.markRead x.1 x.2 rd) (noMarks tl)

/-- For each of n arrays: how many ties lie on it. -/
def tiesOnOf (tl : HTailF2) (n : Nat) : Array Nat :=
  (List.range tl.NM).foldl (fun a mu => a.modify (tl.gtTree.getD mu 0) (· + 1))
    (Array.replicate n 0)

/-- The n numbers from a on. -/
def numbersFrom (a n : Nat) : Array Nat := ((List.range n).map (a + ·)).toArray

/-- The claims are laid for the members of a list, one each, in order. -/
def LaidBy {α : Type} (R : Nat → α → Claim → Prop) : Nat → List α → List Claim → Prop
  | _, [], [] => True
  | q, x :: l, c :: cs => R q x c ∧ LaidBy R (q + 1) l cs
  | _, _, _ => False

/-- The premises on numbers, flags, marks and lengths. rd: the marks behind all reads; s1, s3: the
segments of the tables on the two vectors. -/
structure TailReady (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork)
    (cs : Array Claim) (rd : Array (Array Bool)) (s1 s3 : Nat) : Prop where
  /-- four claims have been laid since the count was taken -/
  four : front + cs.size - before = 4
  drawn : F.thetaDrawnF = true
  plan : F.planClaimsF ≠ 0
  one : oneRow tl = true
  fresh : ∀ mu, mu < tl.NM → (takenOf tl).getD mu true = false
  /-- each matrix's shape has its columns, and it has a row of cells -/
  fits : ∀ mu, mu < tl.NM →
    (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k ∧ 0 < (tl.mats.getD mu {}).m
  /-- each table on a matrix of the list and on one of the two vectors: the vector is there; the
  table's rows divide the matrix's; one weight a row -/
  table : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM → (Fn.tree = 0 ∨ Fn.tree = 2) →
    (tl.ix.U.getD Fn.tree none).isSome = true ∧ Fn.len ≠ 0 ∧
      (tl.mats.getD Fn.mat {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len
  /-- each read is ready. Of the six clauses four follow from the read's lying in the list and from
  `table`; new are: the vector's array has columns, and the last entry's row is below 2^32 -/
  reads : ∀ x ∈ readsList tl funs, ∃ tU, ReadReady tl F x.1 x.2 tU
  marks : marksOf tl funs = some rd
  allSet : (rd.all fun a => a.all id) = true
  inList : (funs.all fun Fn =>
    decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) = true
  tile1 : tl.tablesTile funs 0 = some s1
  tile3 : tl.tablesTile funs 2 = some s3
  /-- one tie on each symbol array, none on any other -/
  kinds : ((List.range F.trees.size).all fun t =>
    (tiesOnOf tl F.trees.size).getD t 0 ==
      (if (F.trees.map (·.kind)).getD t .table == .symbols then 1 else 0)) = true
  sum : (tiesOnOf tl F.trees.size).foldl (· + ·) 0 = tl.NM
  count : (readsList tl funs).length = s1 + s3
  apart : allDistinct tl.gtTree.toList = true

namespace Spec

/-- States: under the premises the text behind the first four claims returns; the ledger stays; one
tie for each matrix and one claim for each read are laid, in order. The test on values is asked of
whatever data the weights' step returns. -/
def eqTail_returns : Prop :=
  ∀ (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (rd : Array (Array Bool)) (s1 s3 : Nat), TailReady before front tl funs F cs rd s1 s3 →
    (∀ tl', eqWeights tl front (F, cs) = .ok (tl', (F, cs)) →
      ∀ x ∈ readsList tl funs, LiveAt tl' x) →
    Ret (eqTail before tl funs) front (F, cs) fun out s' =>
      ∃ (tl' : HTailF2) (ties reads : List Claim), Laid tl tl' ∧
        out = { tl' with
          tieObj := numbersFrom (front + cs.size) tl.NM
          tiesOn := tiesOnOf tl F.trees.size
          nX4Laid := (readsList tl funs).length } ∧
        s' = (F, cs ++ (ties ++ reads).toArray) ∧
        LaidBy (fun _ mu c => TieClaim tl' mu c) 0 (List.range tl.NM) ties ∧
        LaidBy (fun q x c => ∃ tU, ReadClaim tl' F x.1 x.2 q tU c) 0 (readsList tl funs) reads

end Spec

end VerifiableInference.Desc.First.K8.Honest
