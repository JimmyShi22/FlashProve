-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindStep.lean: the honest side of the kind "lookup"
(K3): what Honest/K3/Law/Thread/BehindPays.lean shows from an acceptance by a sub-protocol's
decision, shown from an acceptance by the sub-protocol's step, which is where the sentences on the
played rounds end; the test on the rounds' words is carried along. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the stated sub-protocol B is the value of `K3.theStated`
(Johnson/Desc/First/Look/K3Stated.lean) at the address a. The lookup's promise in front and its
promise behind are the Boolean tests `k3OnIn` and `k3OnOut`
(Johnson/Desc/First/Look/K3Borders.lean). The test on the rounds' words is `okRoundsE`
(Johnson/Top/H/K3LawKind.lean): the words are below the prime.

What is shown.
  `step_decide_at`: an acceptance by a sub-protocol's step is an acceptance by its decision at the
    rounds without their digests.
  `narrows_self`: a sub-protocol narrows itself.
  `step_digits`: at the address of a lookup on the digits, from an acceptance by the stated
    sub-protocol's step: `SameBut` (Johnson/Desc/First/Look/K3CallsTurns.lean), `DigLeft`
    (Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean), and the lookup's promise behind from its
    promise in front.
  `step_calls`: at the address of a lookup on the calls, from such an acceptance on rounds whose
    words are below the prime: `SameBut`, and an acceptance by the decision of the library's own
    sub-protocol at rounds whose words are below the prime. This is what `form_calls`
    (Honest/K3/Law/Thread/BehindCalls.lean [not in this library]) asks of its letter
    "Yes".
  `step_calls_course`: the same on a course's rounds. Conditional on `Fit`
    (Honest/K3/Law/Statements.lean), from which the test on the words is shown.

Hypotheses that remain.
  `h`, `hOk`: B is the value of `K3.theStated` at a; its test on the plan accepts.
  `hi`, `hpc`: the address's link is i; its piece is that of the lookup on the digits, or on the
    calls, of link i.
  `hlook`, `hsh`: (in `step_digits`) `lookAt` returns at link i's digits; the public parameters made
    of what it returns have a shape.
  `hst`: the step of B accepts.
  `hw`: (in `step_calls`) the words of the rounds are below the prime.
  `hF`, `hx`: (in `step_calls_course`) the course fits; x is the list of its rounds.

Users. A description's member at a lookup's place accepts just where the stated sub-protocol's step
does, no mark stands behind and the reply is as in front (`memberAtSite`,
Honest/K3/Law/MemberAtSite.lean): so these theorems serve the member. `step_decide_at` is called in
these files under Honest/K3/Law/Thread/: CEndBelow.lean, MemberBack.lean, PutG.lean,
StateBehind.lean.

Limits. Conditional on an acceptance by the step. No instance of these hypotheses is exhibited in
this file. On the verifier's side alone, but for `step_calls_course`, which reads a course's rounds.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindPays
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OkRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Place Block OpenedColumn noDigest)
open VerifiableInference.Desc.K3 (theStated Readers pieceAt k3OnIn k3OnOut seatCalls)
open VerifiableInference.Desc.First.Look (P lookAt placeAt)
open VerifiableInference.OnPublicFiles (SameBut DigLeft okRoundsE okRoundsE_take)
open ProofFile.Honest.K3.Law

local notation "FS" => VerifiableInference.Desc.First.S

/-- An acceptance by a sub-protocol's step is an acceptance by its decision at the rounds without
their digests. Conditional on that acceptance. gs is bound by "∃" and held by what functions return
at it alone: some value: not said to be the step's own. -/
theorem step_decide_at {Cl : Type} (b : Block FS Cl) (ft : Nat) (s s' : FS) (k : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  simp only [VerifiableInference.Desc.need, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, _⟩ := h
       exact ⟨_, by assumption⟩)
    | cases h

theorem narrows_self {Cl : Type} (b : Block FS Cl) : b.Narrows b := ⟨rfl, fun _ _ _ _ h => h⟩

section
variable {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
  (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
  (a : Place) (B : Block FS Cl) (h : theStated claim readers X codes shape a = some B)
  (hOk : B.planOk = true) (i : Nat) (hi : a.link = some i)

include h hOk hi in
/-- **At the address of a lookup on the digits**: `SameBut`, `DigLeft`, and the lookup's promise
behind from its promise in front. Conditional on an acceptance by the stated sub-protocol's step.
No instance of these hypotheses is exhibited in this file. -/
theorem step_digits (hpc : a.piece = pieceAt X i true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i true = some x)
    {hs : OnBytes.Model.Forest.Shape}
    (hsh : (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x).shape = some hs) (ft : Nat)
    (s t : FS) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hst : B.step ft s rs cols = .ok (t, k)) :
    SameBut s t ∧ DigLeft s t ∧
      (k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true →
        k3OnOut (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) t = true) := by
  obtain ⟨gs, hd⟩ := step_decide_at B ft s t k rs cols hst
  obtain ⟨a1, a2⟩ := digits_turns claim readers X codes shape a B B h hOk (narrows_self B) i hi hpc
    hlook hsh s t _ gs hd
  exact ⟨a1, digits_left claim readers X codes shape a B B h hOk (narrows_self B) i hi hpc s t _ gs
    hd, a2⟩

include h hOk hi in
/-- **At the address of a lookup on the calls**: `SameBut`, and an acceptance by the decision of the
library's own sub-protocol at rounds whose words are below the prime. Conditional on an acceptance
by the stated sub-protocol's step on rounds whose words are below the prime. No instance of these
hypotheses is exhibited in this file. sent, laid, rs' and gs' are bound by "∃" and held by what
functions return at them alone: some values: not said to be the step's own. -/
theorem step_calls (hpc : a.piece = pieceAt X i false) (ft : Nat) (s t : FS) (k : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hst : B.step ft s rs cols = .ok (t, k))
    (hw : okRoundsE rs = true) :
    SameBut s t ∧ ∃ P' sent laid rs' gs', placeAt X i false = some P' ∧ okRoundsE rs' = true ∧
      (VerifiableInference.Desc.K3.block (seatCalls claim) a.piece laid sent P' []).decide s rs' gs'
        =
        .ok t := by
  obtain ⟨gs, hd⟩ := step_decide_at B ft s t k rs cols hst
  obtain ⟨P', sent, laid, n, gs', hP, hyes⟩ :=
    calls_yes claim readers X codes shape a B B h hOk (narrows_self B) i hi hpc s t _ gs hd
  exact ⟨calls_sameBut claim readers X codes shape a B B h hOk (narrows_self B) i hi hpc s t _ gs
    hd,
    P', sent, laid, _, gs', hP, okRoundsE_take _ n (okRounds_noDigest rs hw), hyes⟩

include h hOk hi in
/-- **At the address of a lookup on the calls**, on a course's rounds: the test on the words is
shown from `Fit`. Conditional on `Fit` and on an acceptance by the stated sub-protocol's step on the
course's rounds. No instance of these hypotheses is exhibited in this file. sent, laid, rs' and gs'
are bound by "∃" and held by what functions return at them alone: some values: not said to be the
step's own. -/
theorem step_calls_course {W : Type} (R : Course W) (x : List Fmt.RoundView) (hF : Fit R)
    (hx : R.rounds = some x) (hpc : a.piece = pieceAt X i false) (ft : Nat) (s t : FS) (k : Nat)
    (cols : List OpenedColumn) (hst : B.step ft s x cols = .ok (t, k)) :
    SameBut s t ∧ ∃ P' sent laid rs' gs', placeAt X i false = some P' ∧ okRoundsE rs' = true ∧
      (VerifiableInference.Desc.K3.block (seatCalls claim) a.piece laid sent P' []).decide s rs' gs'
        =
        .ok t :=
  step_calls claim readers X codes shape a B h hOk i hi hpc ft s t k x cols hst
    (okRounds_course R x hF hx)

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.step_decide_at
#print axioms ProofFile.Honest.K3.Law.AtThr.narrows_self
#print axioms ProofFile.Honest.K3.Law.AtThr.step_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.step_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.step_calls_course
