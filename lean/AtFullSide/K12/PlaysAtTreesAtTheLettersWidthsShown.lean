-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K12/PlaysAtTreesAtTheLettersWidthsShown.lean

It states no goal. No property of the protocol is claimed.

`Socket.playsAtTrees₃` (AtFullSide/Honest/TheSocketStatements.lean) AT THE LETTERS AS DEFINITIONS
(AtFullSide/Honest/TheLettersLast.lean): NO PREMISE BUT THE HEAD AT A RETURN OF THE MAKER AND THAT RETURN, at every value of
the named holes `OpenShared` and `OpenLast`. Four theorems: calls.

  `widths_at_the_letters`                  `WidthsAt` at the first Script's table and the shared letters' table
  `playsAtTrees_at_the_letters_whole`      at `thread₃`, at `said₃Field`, the letter without the tie
  `playsAtTrees_at_the_letters_tied_whole` at `said₃`
  `socket_playsAtTrees_at_the_letters`     the first of these two, written as the socket

By what. `playsAtTrees_at_the_letters`, `playsAtTrees_at_the_letters_tied` (PlaysAtTreesAtTheLetters.lean); `widthsAtW`
(AtFullSide/K12/Part4/WidthsAtW.lean): `WidthsAt` at `(firstScriptAt I S Op A cF).table` and `tableShared (K1.qAt A.Z Np) …`, at
every r₁ and toCommon, under the head and the maker's return; `(first h).script` and `(later O).table` are these terms by
unfolding. `threadThree h first reads last R` (AtFullSide/Honest/TheThreeThreads.lean) is `lastThread h first reads last R.own`:
at the letters' parts it is `thread₃`, and `saidThree` is `said₃Field`: one text.

Hypotheses. h: the head at a return of the maker. made: that return is the base prover's filling's, at matrixInput, Sz.ref
and openHonest. O, P: values of the named holes; P holds two propositions of its own: ownIsTheFilling and depths. Two
instances (but in the first theorem): `Inhabited P5J.TS`, `Inhabited Desc.K14.St`: `endsAt` is made by choice with a default.

Limits.
- THAT THERE IS A VALUE OF `OpenLast` IS NOT SHOWN HERE: it owes its field depths. At no such value these laws say nothing.
- The three widths rest on `widthsAtW`.
- All limits of PlaysAtTreesAtTheLetters.lean hold here: stands alone; the base prover's return, NOT THE ONLINE PROVER; the
  full size and the format's second hash function alone; one member of one chain.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: the last three bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. They inherit it from the two laws of PlaysAtTreesAtTheLetters.lean, which they
call, keeping every letter that stands under a premise that names a coin.
This file's own ground, in the rule's terms.
- h and made name no coin, no run's input and no Script: of neither kind.
- O, P and R are letters under no premise in front; O stands under P's field depths, which speaks of the shared letters' table
  and is itself bound over all coins; R's field own holds the committer's coins (rc) and the hidden input.
- The end, `PlaysS` (in the last theorem inside `Socket.playsAtTrees₃`), binds a run's coins k and, beside k, the letters s, m
  and E under `ThrS … b k s m E` and l under the return of `chainSteps … (k.look …) …`: of the first kind: each names k, and at
  fixed letters can hold at some values of the coins and fail at others. ds stands under `drawsFit` (no coin) and
  `chainStopAt (T.φ.sees m.st.input) …`: of the first kind as far as a second stop reads rc, of the second as far as it reads
  the index or the trace; where the field is spent (`saidNextThree`, AtFullSide/Honest/ThreadsAtTheTerm.lean) `chainStop_none` at
  `quiet_second_at_return` is called beside it for this premise: their statements are not read here. The invariant's clause
  `valid` has two halves: that the input of m IS R.own compares rc: at a fixed m it holds at one value of the committer's coins
  and fails at the others: of the first kind: m is tied to rc as well as to k; that it meets `ReadyInput` reads the hidden
  input and no coin: of the second kind.
- `widths_at_the_letters` binds the coins by "for all" under no premise: it bears none.
- What lifts the bar: the honest run's terms for s, m, E and l, with a lemma that shows the premises at them at every value
  of the coins; for ds a lemma that the stop's answer does not hang on rc. None is known to this file: the bar is flat.
-/
import AtFullSide.K12.PlaysAtTreesAtTheLetters
import AtFullSide.K12.Part4.WidthsAtW
import AtFullSide.Honest.TheSocketStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtFile
open ProofFile.Honest.Term (matrixInput)
open OnBytes (TableKey)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The three widths at the letters as definitions.** -/
theorem widths_at_the_letters (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) :
    WidthsAt (firstRounds h) (toCommon (A := A)) (first h).script.table (later (h := h) O).table :=
  ProofFile.Honest.K12.Part4.widthsAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest h.head made _ _ _ _ _
    (firstRounds h) (toCommon (A := A))

/-- **At a member of the last chain with a new tree the sender plays, at the letter without the tie.** -/
theorem playsAtTrees_at_the_letters_whole (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ b, b < (thread₃ h P R).bs.length → (thread₃ h P R).fresh b ≠ [] →
      PlaysS (thread₃ h P R) (said₃Field h P R) b :=
  playsAtTrees_at_the_letters h made O P R (widths_at_the_letters h made O)

/-- **The same at `said₃`**, the letter with the tie. -/
theorem playsAtTrees_at_the_letters_tied_whole (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ b, b < (thread₃ h P R).bs.length → (thread₃ h P R).fresh b ≠ [] →
      PlaysS (thread₃ h P R) (said₃ h P R) b :=
  playsAtTrees_at_the_letters_tied h made O P R (widths_at_the_letters h made O)

/-- **The socket playsAtTrees₃ at the letters as definitions.** -/
theorem socket_playsAtTrees_at_the_letters (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    AtFullSide.Honest.Socket.playsAtTrees₃ h (first h) (reads h) (lastParts h (first h) (last h P)) R :=
  playsAtTrees_at_the_letters_whole h made O P R

end AtFullSide.K12

#print axioms AtFullSide.K12.widths_at_the_letters
#print axioms AtFullSide.K12.playsAtTrees_at_the_letters_whole
#print axioms AtFullSide.K12.playsAtTrees_at_the_letters_tied_whole
#print axioms AtFullSide.K12.socket_playsAtTrees_at_the_letters
