-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqAllReturns.lean: THE SMALLNESS TEST: THE WHOLE LIST "K8.equations"
(`eqAll`, Johnson/Desc/First/TailClaims/Equations.lean) RETURNS, UNDER PREMISES ON NUMBERS, FLAGS,
MARKS AND LENGTHS AND THREE TESTS ON VALUES. A FEW DEFINITIONS AND ONE STATEMENT, as a definition of
a proposition; no proof stands here. A lemma; none of the library's goals.

The list: five tests at its head (the list of tables is closed and as long as the one handed in; it
is that list, weights and all; the ledger's coefficients on the test's own slots are 0; something
was heard; the lookup's rows are as many as its shape says: the second and the third are among the
three tests on values below); the claim on the lookup's key vectors (`eqKeys`); three claims on
the planes of the lookup's counts (`eqCounts`); then the text of
Johnson/Desc/K8/Honest/EqTailReturns.lean. The laws for the two routines are those of
Johnson/Desc/First/TailClaims/EqKeysReturns.lean and EqCountsReturns.lean; their premises are taken
over as they stand, and the first four claims are said by the shapes of
Johnson/Desc/First/Shape/Parts.lean.
  `AllReady …`   THE PREMISES ON NUMBERS, FLAGS, MARKS AND LENGTHS, each a debt with a name:
                  `closed` · `heard` · `rows` · `key` · `idx` · `laid` · `leaves` (the leaves'
                  sumcheck is still open at the ledger: its flags, sizes and free slots) · `tail`
                  (the seventeen of `TailReady`, but for its count of claims, which holds by the
                  make). `closed` also follows from the first test on values, which begins with the
                  same two clauses: it is kept as that test's half on numbers and flags
  THE THREE TESTS ON VALUES: the list of tables handed in is the list that was closed, weights and
                  all (`funsHeld`) · the ledger's coefficients on the test's own slots are all 0 ·
                  `LiveCols tl funs chi`: at the batching element chi no column of a matrix on
                  which a read lies has the weight 0
  `Spec.eqAll_returns`
Behind: the data with the claim's number and a factor laid in, then what `eqWeights` lays (`Laid`),
then the ties' numbers, the counts of ties and the number of reads; a ledger that differs from the
one in front on the side alone (`OnlySide`), with its shape as the two routines' laws give it;
behind the claims in front: four claims of the stated shapes, one tie for each matrix, one claim for
each read.
The counts of ties are said at the ledger in front and the reads' claims at the ledger behind: the
two have the same arrays (`OnlySide`).
Limits. Nothing says that the premises hold at any state of a run. No arithmetic on a plan's numbers
is done here, and what the data behind keep of the data in front is `Laid.rest`: as in
Johnson/Desc/K8/Honest/EqTailReturns.lean. The shapes of the first four claims and of the ledger
behind are those of the two routines' own laws. Through Johnson/Desc/First/Shape/Parts.lean this
file leans on OnBytes/K/Kc/Returns/FlReturns.lean, FlReturns2.lean and FlReturns6.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailReturns
import Johnson.Desc.First.TailClaims.EqKeysReturns
import Johnson.Desc.First.TailClaims.EquationsTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret OnlySide idxOk keysClaim countsClaims)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- The premises on numbers, flags, marks and lengths. g: what the lookup heard. -/
structure AllReady (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (g : Forest.Heard) (rd : Array (Array Bool)) (s1 s3 : Nat) : Prop where
  closed : tl.funClosed = true ∧ funs.size = tl.funs.size
  heard : tl.heard = some g
  rows : g.rows.size = lookRows tl
  key : padKeyDigits tl = true
  idx : ∀ q ∈ [0, 1], ∀ p ∈ (tl.zOf q).pieces.toList, idxOk tl g q p = true
  laid : laidDigits tl = some g.shape.pub
  leaves : D6.Ret.Open g.leaves F
  tail : ∀ c4 : Array Claim, c4.size = cs.size + 4 →
    TailReady (front + cs.size) front tl funs F c4 rd s1 s3

/-- At chi no column of a matrix on which a read lies has the weight 0. -/
def LiveCols (tl : HTailF2) (funs : Array HFun) (chi : E) : Prop :=
  ∀ x ∈ readsList tl funs, ∀ c, c < (tl.mats.getD x.1.mat {}).k →
    isZeroE (foldColumn tl.cfF ((tl.cfFirst.getD x.1.mat 0 + c) * tl.tau) tl.tau
      (powers chi tl.tau)) = false

namespace Spec

/-- States: under the premises the whole list returns. -/
def eqAll_returns : Prop :=
  ∀ (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (g : Forest.Heard) (rd : Array (Array Bool)) (s1 s3 : Nat),
    AllReady front tl funs F cs g rd s1 s3 → tl.funsHeld funs = true →
    (F.LS.extract tl.slotA tl.slotB).all isZeroE = true → LiveCols tl funs F.theta →
    Ret (eqAll tl funs) front (F, cs) fun out s' =>
      ∃ (bf : E) (tl' : HTailF2) (four ties reads : List Claim),
        Laid { tl with joinObj9 := some (front + cs.size), bitFactor9 := bf } tl' ∧
        out = { tl' with
          tieObj := numbersFrom (front + (cs.size + 4)) tl.NM
          tiesOn := tiesOnOf tl F.trees.size
          nX4Laid := (readsList tl funs).length } ∧
        OnlySide F s'.1 ∧
        ledSh s'.1 = ((ledSh (F.paid g.owedJoin)).setGot
          (fillB (ledSh (F.paid g.owedJoin)).got g.leaves.first (D6.Ret.taken g.leaves))).setOwed
            (paidB (ledSh (F.paid g.owedJoin)).owed g.owedPlanes) ∧
        s'.2 = cs ++ (four ++ (ties ++ reads)).toArray ∧
        four.map claimSh = keysClaim tl g :: countsClaims tl g ∧
        LaidBy (fun _ mu c => TieClaim tl' mu c) 0 (List.range tl.NM) ties ∧
        LaidBy (fun q x c => ∃ tU, ReadClaim tl' s'.1 x.1 x.2 q tU c) 0 (readsList tl funs) reads

end Spec

end VerifiableInference.Desc.First.K8.Honest
