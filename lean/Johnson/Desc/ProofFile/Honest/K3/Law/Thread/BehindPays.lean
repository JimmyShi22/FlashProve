-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindPays.lean: the honest side of the kind "lookup"
(K3): what the thread's clause on the form asks of the two states around a lookup's sub-protocol
(Honest/K3/Law/Thread/Behind.lean and Honest/K3/Law/Thread/BehindCalls.lean [not in this library]),
shown from an acceptance by the
sub-protocol's decision. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: B is the value of `K3.theStated`
(Johnson/Desc/First/Look/K3Stated.lean) at the address a, and its test on the plan accepts. B' is
any sub-protocol that narrows B (`Block.Narrows`, Johnson/Desc/Sound/MergeNarrow.lean): it has B's
rounds, and it accepts only where B accepts, with the same state. The lookup's promise in front and
its promise behind are the Boolean tests `k3OnIn` and `k3OnOut`
(Johnson/Desc/First/Look/K3Borders.lean). "The same but for what the lookup lays" is `SameBut`
(Johnson/Desc/First/Look/K3CallsTurns.lean).

What is shown.
  `digits_turns`: at the address of a lookup on the digits, the two states are the same but for what
    the lookup lays; and the lookup's promise behind holds where its promise in front does. No
    hypothesis on the rounds' words is needed, by the library's `k3_digits_lookOut_any`
    (Johnson/Desc/First/Look/K3DigitsStep.lean). Another way to that promise, from the promise in
    front and the honest row's play at a site, is `member_in_out`
    (Honest/K3/Law/Thread/FrontSite.lean).
  `digits_left`: at the same address, `DigLeft` (Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean).
  `calls_yes`: at the address of a lookup on the calls, an acceptance by B' is an acceptance by the
    library's own sub-protocol on the first n of the rounds, for some n.
  `calls_sameBut`: at the same address, the two states are the same but for what the lookup lays.

Hypotheses that remain.
  `h`, `hOk`, `hN`: B is the value of `K3.theStated` at a; its test on the plan accepts; B' narrows
    B.
  `hi`, `hpc`: the address's link is i; its piece is that of the lookup on the digits, or on the
    calls, of link i.
  `hlook`, `hsh`: (in `digits_turns`) `lookAt` returns at link i's digits; the public parameters
    made of what it returns have a shape.
  `hd`: the decision of B' accepts from s, on the rounds rs and the columns cols, and returns t.

Follows. The library's own theorems on these states, `k3_digits_seated_turns`
(Johnson/Desc/First/Look/K3DigitsSeatedYes.lean) and `k3_digits_seated_leaves`
(Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean), speak of a piece of the verifier's side. Of
that piece their proofs use one thing: an acceptance by the sub-protocol's decision. Here their
conclusions are stated from that acceptance, over the same lemmas.

Users. Honest/K3/Law/Thread/BehindStep.lean calls all four theorems.

Limits. Conditional on an acceptance by the decision of B'. No instance of these hypotheses is
exhibited in this file. That a description's member narrows B is not shown here. That the words of
the played rounds are below the prime, which is asked at the calls beside `calls_yes`, is treated in
Honest/K3/Law/Thread/OkRounds.lean. On the verifier's side alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.Desc.First.Link.Law.K4AtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K3 (theStated Readers pieceAt k3OnIn k3OnOut quietAt seatDigits
  seatCalls)
open VerifiableInference.Desc.First.Look (P lookAt placeAt)
open VerifiableInference.OnPublicFiles

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
  (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
  (a : Place) (B B' : Block FS Cl) (h : theStated claim readers X codes shape a = some B)
  (hOk : B.planOk = true) (hN : B'.Narrows B) (i : Nat) (hi : a.link = some i)

include h hOk hN hi in
/-- **At the address of a lookup on the digits the two states are the same but for what the lookup
lays; and the lookup's promise behind holds where its promise in front does.** Conditional on an
acceptance by the decision. No instance of these hypotheses is exhibited in this file. -/
theorem digits_turns (hpc : a.piece = pieceAt X i true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i true = some x)
    {hs : OnBytes.Model.Forest.Shape}
    (hsh : (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x).shape = some hs) (s t : FS)
    (rs : List Fmt.RoundView) (cols : List (List (Nat × List UInt64)))
    (hd : B'.decide s rs cols = .ok t) :
    SameBut s t ∧ (k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true →
      k3OnOut (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) t = true) := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s t _ cols
      (hN.2 _ _ _ _ hd)
  have eP : P' = (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  have hS := k3_digits_sameBut claim a.piece laid sent _ [] s s' _ gs' hyes
  have hO : k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s = true →
      k3OnOut (P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x) s' = true :=
    fun hIn => k3_digits_lookOut_any claim a.piece laid sent _ [] hsh rfl s s' _ gs' hyes hIn
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨hS, hO⟩
  · unfold quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, ho, e⟩ := VerifiableInference.Desc.K3.quietHead_ok X s' t hfs
      rw [e]
      exact ⟨hS.trans (headClaim_sameBut s' ah c ha ho),
        fun hIn => k3OnOut_headClaim _ rfl s' ah c ha (hO hIn)⟩
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, hF, -, e⟩ := VerifiableInference.Desc.K3.quietDigits_ok _ _ s' t hfs
         obtain ⟨F₂, hF₂, hG₂⟩ := VerifiableInference.Desc.K3.quietDigits_fork _ _ s' t hfs
         obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
         have hh : VerifiableInference.Desc.K3.heardAt true t =
             VerifiableInference.Desc.K3.heardAt true s' := by
           rw [e]
           simp [VerifiableInference.Desc.K3.heardAt, tl_putFork]
         exact ⟨hS.trans (e ▸ putFork_sameBut s' F _ hF),
           fun hIn => k3OnOut_planClaims _ s' t F _ hF hG₂ hh (hO hIn)⟩)

include h hOk hN hi in
/-- **At the address of a lookup on the digits: `DigLeft`.** Conditional on an acceptance by the
decision. No instance of these hypotheses is exhibited in this file. -/
theorem digits_left (hpc : a.piece = pieceAt X i true) (s t : FS) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (hd : B'.decide s rs cols = .ok t) : DigLeft s t := by
  unfold DigLeft
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s t _ cols
      (hN.2 _ _ _ _ hd)
  obtain ⟨F, y, hF, hn, e, hE⟩ :=
    decide_exact (seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have hF0 : s.fork? = some F := hF
  have hsome : ((seatDigits claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have hF' : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have hL : s'.lookHeard? = s.lookHeard? := by
    rw [e]
    exact putDigits_look claim s y.1 F y.2 hF
  have hO : ∀ pc : P, pc.digits = false → k3OnOut pc s = true → k3OnOut pc s' = true :=
    fun pc hdc hIn => k3OnOut_other_rides claim a.piece laid sent P' [] pc hdc s s' _ gs' hyes hIn
  have hZ : OnBytes.PscRun.Sized F → _root_.Fo.Later F y.2 ∧ OnBytes.PscRun.Sized y.2 ∧
      (((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) = true →
        ((List.range (y.2.ns - y.2.next)).all fun j => !y.2.gotF.getD (y.2.next + j) true) =
          true) := by
    intro hz
    obtain ⟨E, hLat⟩ := hE hz
    exact ⟨⟨hLat.next, hLat.ns, hLat.keep⟩, hLat.sized hz,
      freeAbove_hearing E hLat.ns (hLat.sized hz)⟩
  rcases hstep with e' | ⟨f, hf, hfs⟩
  · rw [e']
    refine ⟨F, y.2, hF0, hF', hL, fun hz => ⟨(hZ hz).1, (hZ hz).2.1, fun hfr => ?_⟩, hO⟩
    unfold freeAboveB at hfr ⊢
    rw [hF0] at hfr
    rw [hF']
    exact (hZ hz).2.2 hfr
  · obtain ⟨F₂, c, hF₂, hG₂, hL₂⟩ := quietAt_ledger X i f hf s' t hfs
    obtain rfl : y.2 = F₂ := Option.some.inj (hF'.symm.trans hF₂)
    refine ⟨F, _, hF0, hG₂, hL₂.trans hL, fun hz => ⟨?_, ?_, fun hfr => ?_⟩, fun pc hdc hIn => ?_⟩
    · exact (hZ hz).1.trans (later_planClaims y.2 c)
    · exact (hZ hz).2.1
    · unfold freeAboveB at hfr ⊢
      rw [hF0] at hfr
      rw [hG₂]
      exact (hZ hz).2.2 hfr
    · refine k3OnOut_planClaims pc s' t y.2 c hF' hG₂ ?_ (hO pc hdc hIn)
      rw [hdc]
      exact hL₂

include h hOk hN hi in
/-- **At the address of a lookup on the calls an acceptance is an acceptance by the library's own
sub-protocol**, on the first n of the rounds, for some n. Conditional on an acceptance by the
decision. No instance of these hypotheses is exhibited in this file. sent, laid and gs' are bound by
"∃" and held by what functions return at them alone: some values: not said to be the step's own. -/
theorem calls_yes (hpc : a.piece = pieceAt X i false) (s t : FS) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (hd : B'.decide s rs cols = .ok t) :
    ∃ P' sent laid n gs', placeAt X i false = some P' ∧
      (VerifiableInference.Desc.K3.block (seatCalls claim) a.piece laid sent P' []).decide s
        (rs.take n) gs' = .ok t :=
  VerifiableInference.Desc.LinkJoin.theStated_yes_calls claim readers X codes shape a B h hOk i hi
    hpc
    s t rs cols (hN.2 _ _ _ _ hd)

include h hOk hN hi in
/-- **At the address of a lookup on the calls the two states are the same but for what the lookup
lays.** Conditional on an acceptance by the decision. No instance of these hypotheses is exhibited
in this file. -/
theorem calls_sameBut (hpc : a.piece = pieceAt X i false) (s t : FS) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (hd : B'.decide s rs cols = .ok t) : SameBut s t := by
  obtain ⟨P', sent, laid, n, gs', _, hyes⟩ :=
    calls_yes claim readers X codes shape a B B' h hOk hN i hi hpc s t rs cols hd
  exact k3_calls_sameBut claim a.piece laid sent P' [] s t _ gs' hyes

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.digits_turns
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_left
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_yes
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_sameBut
