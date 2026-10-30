-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PlaysAtTreesFilled.lean

It states no goal. No property of the protocol is claimed.

THE FIELD playsAtTrees₃ OF `TheThreadsHalf` (AtFullSide/Honest/TheOneObject.lean), IN THE FIELD's OWN TYPE, with the fit held by
Lean. One theorem: a call; and one example, a check of types.

  `playsAtTrees₃_filled`   ∀ r : TiedRun h hr, `Socket.playsAtTrees₃` at the letters as definitions, at r.R
  the example              a value of `TheThreadsHalf h hr` with this field laid anew by that theorem: it elaborates

By what. `socket_playsAtTrees_at_the_letters` (PlaysAtTreesAtTheLettersWidthsShown.lean), at R := r.R.

Hypotheses. h: the head at a return of the maker. hr: the files are read. made: that return is the base prover's filling's
(`matrixFilling`, E2E/ThruAtTerm.lean). open₂, open₃: values of the named holes `OpenShared`, `OpenLast`; open₃ holds two
propositions of its own: ownIsTheFilling and depths. Two instances: `Inhabited P5J.TS`, `Inhabited Desc.K14.St`. Of r its field R
alone is read: that r is a tied run is not spent.

Limits.
- THE EXAMPLE SHOWS NO VALUE OF `TheThreadsHalf`: it takes one, T, and lays one field of it anew. It is a check that the
  theorem's type is the field's.
- THAT THERE IS A VALUE OF `OpenLast` IS NOT SHOWN HERE.
- All limits of PlaysAtTreesAtTheLettersWidthsShown.lean hold here: stands alone: at no stand the end says nothing; the base
  prover's return, NOT THE ONLINE PROVER; the full size and the format's second hash function alone; one member of one chain; the three
  widths rest on `widthsAtW`.
- MODULES Johnson/HonestTrace/Run/SetUp* OF THE EXECUTABLE MODEL's FOLDER LIE BENEATH: beneath
  AtFullSide/Honest/TheOneObject.lean (fourteen, through three files in Shape/Scope): by their
  import lines they bring in nothing else of that folder.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `playsAtTrees₃_filled` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. It inherits it from `socket_playsAtTrees_at_the_letters`, which it calls, keeping every
letter that stands under a premise that names a coin.
This file's own ground, in the rule's terms.
- h, hr and made name no coin, no run's input and no Script: of neither kind. open₂ and open₃ are letters under no premise in
  front; open₂ stands under open₃'s field depths, which is itself bound over all coins.
- r is bound by "for all": a value of `TiedRun h hr` HOLDS A PROVER's COIN (its field c), a private input (w), and two
  propositions on them (tied; ready: that `ready` returns r.R at `pursesOf r.c`): premises of the first kind on r.R, inside the
  type of r. The theorem reads r.R alone and spends neither.
- The end, `PlaysS` inside `Socket.playsAtTrees₃`, binds a run's coins k and, beside k, the letters s, m and E under
  `ThrS … b k s m E` and l under the return of `chainSteps … (k.look …) …`: of the first kind: each names k, and at fixed letters
  can hold at some values of the coins and fail at others. ds stands under `drawsFit` (no coin) and
  `chainStopAt (T.φ.sees m.st.input) …`: of the first kind as far as a second stop reads rc, of the second as far as it reads the
  index or the trace. The invariant's clause `valid` has two halves: that the input of m IS r.R.own compares rc: of the first
  kind: m is tied to rc as well as to k; that it meets `ReadyInput` reads the hidden input and no coin: of the second kind.
- What lifts the bar: the honest run's terms for s, m, E and l, with a lemma that shows the premises at them at every value of
  the coins; for ds a lemma that the stop's answer does not hang on rc. None is known to this file: the bar is flat.
-/
import AtFullSide.K12.PlaysAtTreesAtTheLettersWidthsShown
import AtFullSide.Honest.TheOneObject

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling)
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles readFiles)
open AtFullSide.Honest

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The field playsAtTrees₃ of `TheThreadsHalf`, in its own type.** -/
theorem playsAtTrees₃_filled (h : HeadAtReturn Z A) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (open₂ : TheLetters.OpenShared A) (open₃ : TheLetters.OpenLast h open₂) :
    ∀ r : TiedRun h hr, Socket.playsAtTrees₃ h (TheLetters.first h) (TheLetters.reads h)
      (lastParts h (TheLetters.first h) (TheLetters.last h open₃)) r.R :=
  fun r => socket_playsAtTrees_at_the_letters h made open₂ open₃ r.R

/-- A check of types: the theorem fills the field. It shows no value of the structure. -/
example (h : HeadAtReturn Z A) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (T : TheThreadsHalf h hr) :
    TheThreadsHalf h hr :=
  { T with playsAtTrees₃ := playsAtTrees₃_filled h hr made T.open₂ T.open₃ }

end AtFullSide.K12

#print axioms AtFullSide.K12.playsAtTrees₃_filled
