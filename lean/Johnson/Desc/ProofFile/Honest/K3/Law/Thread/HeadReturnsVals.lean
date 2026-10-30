-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadReturnsVals.lean: the kind "lookup" (K3).
Conditional: the step without a round behind the lookup on the head's digits returns, where one test
with code on the state accepts along the thread: `headReturns_of_thr`
(Honest/K3/Law/Thread/HeadReturnsOf.lean), called with its hypothesis `hRest` shown by
`headVals_gives` (Honest/K3/Law/Thread/ClaimReturns.lean). The thread is a variable. One theorem.

Terms. Honest/K3/GLOSSARY.md: see there thread, step without a round, site, seat, hearing and link.
In this file: T is a thread's structure of letters (`Thread`, Honest/Thread/Thr.lean), a variable;
the test on values is `headVals` (Honest/K3/Law/Thread/ClaimReturns.lean), a Boolean test with code
on the verifier's state: it is false unless the chain stands in the head's link with x and t set and
the covered positions return; then it says whether `weightsClaim` returns.

What is shown.
  `headReturns_of_vals`: the conclusion of `headReturns_of_thr`: at the digits of the head's link,
    at every state at which the thread stands, behind the return of `hearV` and of the lookup's
    decision: ∃ t, HeadBehind Z.p.X s' t.

Hypotheses that remain.
  `hHead`: from the thread: the chain stands in the head's link, that link is opened, and x and t
    are set. It is that of `headReturns_of_thr`.
  `hN`: `Z.p.X.H.NCL == 1`: public. It is that of `headReturns_of_thr`.
  `hV`: from the thread: `headVals` accepts at the state. It stands in the stead of `hRest` (two
    returns that are other kinds').

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/HeadReturnsThin.lean calls it. `values_of_headVals`
(Honest/K3/Law/Thread/HeadValsValues.lean [not in this library]) takes the same hypothesis `hV`.

Limits. An implication. No instance of these hypotheses is exhibited in this file. `hV` asks no less
than `hRest` did: at a state in the head's link at which x and t are set, `headVals` accepts just
where the two returns of `hRest` hold; at every other state it rejects, where `hRest` asks nothing.
(By the text of `headVals`. In Lean: where the test accepts, the two returns hold
(`headVals_gives`); and `headVals_of` (Honest/K3/Law/Thread/HeadValsOf.lean) shows its acceptance at
such a state from three further hypotheses: the covered positions return, `layoutOk` accepts, and
the checked token of every covered position is an entry of the vocabulary.) What is gained is a form
that a program can evaluate. `headVals` is evaluated in Honest/K3/Law/Thread/CarriesGuardsHead.lean
[not in this library], at states that the test
makes up: it accepts at one of three small synthetic public parts and rejects at the two others.
That is no instance of `hV`, which speaks of every state at which the thread stands. No synthetic
thread of this folder stands in the head's link: the instance of
Honest/K3/Law/Thread/ToyLetters.lean [not in this library] has one link, of the sort "layers".
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsOf
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ClaimReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf quietHead seatDigits)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **The step behind the head's digits returns where the test on values accepts along the thread.**
Conditional on `hHead`, `hN` and `hV`. No instance of these hypotheses is exhibited in this file. -/
theorem headReturns_of_vals (b : Nat) (Z : Pub) (s : Site)
    (hHead : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∃ a, st.here = .head a ∧ a.opened = true ∧ a.x.isSome = true ∧ a.t.isSome = true)
    (hN : (Z.p.X.H.NCL == 1) = true)
    (hV : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      headVals Z.p.X st = true) :
    s.digits = true → s.caller = .head → ∀ (k : Coins Bk) (st : FS) (m : Mid W X)
    (E : Env) (F : Fork) (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (s' : FS), Thr T b k st m E →
    (seatOf K3Lot.ofForm s.digits).fork st = some F → rs.length = (s.p.entries.getD []).length →
    hearV (faceOf s.shape) F rs = some (g, G) →
    decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' →
    ∃ t, HeadBehind Z.p.X s' t :=
  headReturns_of_thr T b Z s hHead hN fun k st m E _ _ _ hA ha hx ht =>
    headVals_gives (hV k st m E hA) ha hx ht

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_of_vals
