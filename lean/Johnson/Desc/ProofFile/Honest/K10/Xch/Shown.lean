-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Shown.lean: four forms in which the lemmas on the item `carry` at the closing of
a segment (kind K10) state their premises and conclusions, so that the file on what the played rounds show
(Xch/ShowsAt.lean) and the files that join the lemmas (Xch/Carry.lean, Xch/CarryTop.lean) name the same things.
One structure, three definitions and one small lemma.

The words. The closing has 2 + k rounds: "BAT", which draws the element that batches the group's rows into one row
(the batched row); "FOLD epsilon", in which the prover sends the sum of a hiding polynomial; and k rounds "FOLD
round". D and r are the data of `CloseBase` and the record before the closing (Johnson/Desc/K10/Honest/Base.lean);
`stageB D r` (Johnson/Desc/K10/Honest/LeftClaim.lean) is the library's stage with the group's numbers.

  `StepAt T Said b blk k s m En ds y cols s'`   a stand of a thread at border b together with an accepted step of the
      block blk from it: the invariant with its second condition holds (`ThrS`, Honest/Thread/Said.lean), the
      challenges ds are such as the block's rounds can draw (`drawsFit`), and the block has stepped from the
      verifier's state s to s' (`Thread.Stepped`, Honest/Thread/Pays.lean). These are three of the four hypotheses of
      `ExchangeAtS` (Honest/Thread/SharesS.lean), as one structure; the fourth, that blk is the thread's block number
      b, is not among them: blk is a variable
  `rowWords D r R`   the entries of the prover's own rows R of a group (`GroupData`, Honest/K10/Job.lean), read in the
      field, as words: `askWords` of `wordAt` and `rowsAt` (Honest/K10/AskLaw.lean, Job.lean), at the statement behind
      the beginning of the test (`D.S1 r`) and the group `D.G`. It is the term at which `ask_of_base` and `ask_law`
      (AskLaw.lean) speak
  `CoefOf u W`   W is the list of coefficients of the hiding polynomial in n variables that the run u of 2 n' + 1
      elements gives: W is `coefU` of `uOfBook` of a run u' of 2 n + 1 elements that has, at each index, the element
      that u has at the index of the same value. Where n' = n that is u itself (`coefOf_cast`). The form names no cast
      between the two index types
  `ShownAt D r row rE rR Tb W`   the round "FOLD epsilon" rE shows the sum of the polynomial with the coefficients W,
      and the rounds "FOLD round" rR show the honest round polynomials at the batched row, the group's tables Tb and
      W, at some point γ. At Tb := `tablesOf` of words these are the premises hσ and hR of `carryExact_from_front`
      (Johnson/Desc/K10/Honest/CarryWords.lean) at the record of t₀, with γ bound by ∃
  `coefOf_cast`   where n' = n, `CoefOf u` holds of the coefficients that u gives through `Fin.cast`

Limits. Definitions, meant as hypotheses and as forms of conclusions: nothing is shown here of any thread, run, rows or
rounds. `StepAt` holds of nothing where the invariant holds at no state of the border or the block accepts no step.
`rowWords` is 0 at a number that is no member's (`rowsAt`, Job.lean), beyond a row's message (`wordAt`), and on rows
that nobody sent (`askWords_padded`, AskLaw.lean). In `CoefOf u W`, W is the run's list of coefficients where n' = n
alone. Where n > n' the members of u' beyond u's length are free, so u does not fix W; where n < n' u fixes W, but u' is
a beginning of u read in the order for n variables, so W is not the run's list. Each use in Xch/ShowsAt.lean,
Xch/Carry.lean and Xch/CarryTop.lean stands behind `CloseBase`, which makes the two numbers equal (`stretch`;
`stageB_k`, LeftClaim.lean). D, r, R, row, the rounds, Tb, W and u are variables. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.AskLaw
import Johnson.Desc.K10.Honest.LeftClaim
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Cb (HIdx HPt hMu sVars)
open OnBytes.Means (Words Tables)
open OnBytes.Slice (GE readE vecG)
open Johnson.Prover.Link (sentOf drawnOf Shows foldQK keptVal coefU uOfBook)
open H2K.ClaimSays (msgOf)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First.Close (Rec)
open ProofFile.Honest.K10.YesFree (BaseData)
open ProofFile.Honest.K10.Values (keptLen)
open ProofFile.Honest.K10.LeftIs (stageB)

/-- **A stand of a thread at a border, with an accepted step of a block from it**: three of the four hypotheses of
`ExchangeAtS`, as one structure; that blk is the thread's block at the border is not asked. -/
structure StepAt {S' Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S' Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (blk : Block S' Cl) (k : Coins Bk) (s : S') (m : Mid W X)
    (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S') : Prop where
  /-- the invariant holds at the border, together with `Said` -/
  thr : ThrS T Said b k s m En
  /-- the challenges are such as the block's rounds can draw -/
  fit : drawsFit blk.rounds ds = true
  /-- the prover's side has played, and the block's own step has accepted -/
  step : T.Stepped blk k s m En ds y cols s'

/-- **The entries of the prover's own rows of a group, read in the field, as words.** -/
def rowWords (D : BaseData) (r : Rec) (R : GroupData) : Words GE :=
  askWords (fun o => wordAt (D.S1 r) R.base.ell (rowsAt D.G R (·.main)) o .main)
    (fun o => wordAt (D.S1 r) R.zk.ell (rowsAt D.G R (·.mask)) o .mask)

/-- **W is the list of coefficients that the run u gives**, said without a cast between the two index types. That is
what it says where n' = n; the head's Limits tell the two other cases. -/
def CoefOf {n n' : Nat} (u : Fin (2 * n' + 1) → OnBytes.E) (W : HIdx (sVars GE 2 n) → GE) : Prop :=
  ∃ u' : Fin (2 * n + 1) → OnBytes.E,
    (∀ (i : Fin (2 * n + 1)) (j : Fin (2 * n' + 1)), i.val = j.val → u' i = u j) ∧
      W = coefU n (uOfBook n fun i => (u' i).triple)

/-- Where the two numbers of variables are equal, the run's own coefficients, read through `Fin.cast`, are such a
list. -/
theorem coefOf_cast {n n' : Nat} (e : 2 * n + 1 = 2 * n' + 1) (u : Fin (2 * n' + 1) → OnBytes.E) :
    CoefOf u (coefU n (uOfBook n fun i => (u (Fin.cast e i)).triple)) := by
  unfold CoefOf
  exact ⟨fun i => u (Fin.cast e i), fun _ _ hij => congrArg u (Fin.ext hij), rfl⟩

/-- **The closing's last 1 + k rounds show the honest sum and round polynomials** at the batched row, the tables Tb
and the coefficients W. -/
def ShownAt (D : BaseData) (r : Rec) (row : OnBytes.GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (Tb : Tables GE)
    (W : HIdx (sVars GE 2 ((stageB D r).h + (stageB D r).g)) → GE) : Prop :=
  readE ((sentOf rE).getD 0 OnBytes.zeroE) = hMu (sVars GE 2 ((stageB D r).h + (stageB D r).g)) W ∧
    ∃ γ : HPt (sVars GE 2 ((stageB D r).h + (stageB D r).g)),
      Shows ((stageB D r).h + (stageB D r).g) rR
        (foldQK (stageB D r) (vecG (stageB D r) row) (msgOf (stageB D r) Tb) W (readE (drawnOf rE))
          (keptVal (keptLen (D.S1 r)) Tb.kept row.kept) γ) γ

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.StepAt
#print axioms ProofFile.Honest.K10.rowWords
#print axioms ProofFile.Honest.K10.CoefOf
#print axioms ProofFile.Honest.K10.coefOf_cast
#print axioms ProofFile.Honest.K10.ShownAt
