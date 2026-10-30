-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/DigitsBehindState.lean: the kind "lookup" (K3).
Conditional: behind an acceptance of the decision of the lookup on the digits of a link's smallness
test (an approximate range proof) every public test that the table of borders asks there holds, the
tests "formsIn" under one named hypothesis; said of two states of the verifier. At the library's
composed meaning, for every value of its data; at all three sorts of link in one statement.
Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table of borders is Johnson/Desc/First/Borders.lean,
whose head calls it the table of joints. A public test is the Boolean test of a public item: the
meaning's field pub. The tests in front and behind are the lists `frontDig mgMore l` and
`behindDig mgMore l` (Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean). An item is the kind's own if
`k3Like` (Johnson/Desc/First/Look/K3DigitsBehind.lean) accepts it. The decision: at the digits the
library's lemmas stand at the decision of the stated sub-protocol itself (the value of
`K3.theStated` at the lot's own letters: `k3Const`, Johnson/Desc/First/Look/K3Base.lean): the
lookup's own rounds and then the step without a round. `hd` is its acceptance.

What is shown.
  `othersPub_dig_state`: the items that are none of the kind's own constructors.
  `like_dig_state`: the kind's own. By a test on the table that the kernel evaluates, only three
    sorts stand behind the digits: lookOut at the digits' piece (made), lookOut at the calls' piece,
    and leftOn where it is open in front (both kept; the test of leftOn is "true").
  `behind_dig_state`: the whole. `SameBut` and `DigLeft` between the two states follow from the
    acceptance alone (the library's `k3_digits_step_turns` and `k3_digits_step_leaves`,
    Johnson/Desc/First/Look/K3DigitsStep.lean).
These theorems show the Boolean tests. At leftOn the test is "true" by the meaning's own text and
says nothing; what that item says beside its test (the field pubP: the library's `k3LeftOnItemAt`,
Johnson/Desc/First/Look/K3LeftItem.lean) is not here, as at left at the calls.
The statements speak of two states alone: no piece, transcript or string occurs in them, nor the
table's promise as a whole, nor "reached". The file is the fellow of
Honest/K3/Law/Total/CallsBehindState.lean and Honest/K3/Law/Total/CallsBehindAll.lean at the calls.

Hypotheses that remain, in the last theorem. None of them is shown in this file.
  `hb`, `hOk`, `hd`: b' is the stated sub-protocol; it passes its test on the plan; its decision
    accepts from s to s'.
  `hl`, `hsub`: the link is below 25; its sort is the written full list's at that number.
  `hlook`: x is the lookup's place (`lookAt`).
  `hfront`: the public tests that are open or tied in front hold at s.
  `hM`, `hlinks`, `hBase`: terms of the composed meaning: the meaning beneath has no extra public
    test; the data's links are the written full list; the public test of the meaning beneath has one
    value at all states.
  `hF`: the tests "formsIn" of the two written lists hold at s'.
  `T`, `DL`: (in the first theorem) `SameBut s s'` (Johnson/Desc/First/Look/K3CallsTurns.lean) and
    `DigLeft s s'` (Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean).

Follows. The first proof is the library's own, taken over by a program
from its text: `othersPub_dig_mgAll` (Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean), which stands at
a piece's acceptance with a transcript, under the table's whole promise in front, "reached" and "no
mark in front". It parts from that proof in the following, and nowhere else.
  (1): the two steps that lead from the piece's acceptance to `hd` are removed; `hd` is a
    hypothesis; the piece and its seat go. The library's piece is that of `below B'`, which tests
    the rounds' words; `hd` is the acceptance of the decision of b' as it stands. So in the words
    this statement is wider.
  (2): the place is had by `lookAt` (`hlook`), theirs by `digAt`
    (Johnson/Desc/First/Look/K3CallerTests.lean), out of which they draw `hlook` in seven lines:
    removed.
  (3): the promise in front gives way to `hfront`; their eight lines that open the promise are
    removed.
  (4): the lists stand at the library's closed list of extra public tests (`mgMore`); their
    rewriting of the list behind is removed.
  (5): their hypothesis on the tests "formsIn", asked at every acceptance, is asked at the one state
    behind (`hF`).
  (6): u.1 and v.1 are s and s'.
  (7): in one line the type of the table's public items is written by its full name: in this
    file's namespace the short name is another type's.
Every other line is theirs token for token.

Users. `madeOwed_digits` (Honest/K3/Law/Total/MadeOwedDigits.lean) calls `behind_dig_state`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
The Boolean tests alone; at leftOn the test says nothing: see under "What is shown". At the written
full list of links and the library's closed list of extra public tests alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAt.K3DigitsOthers
import Johnson.Desc.First.Look.K3DigitsMade
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.Desc.First.Look.K3DigitsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start pubAll_ledger pubAll_freeAbove)

section
variable {Xi P Tok : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols₀ nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols₀) Tok MsgT))

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **The other kinds' public tests behind the acceptance.** Here s is the verifier's state in front
of the lookup on the digits and s' the state behind the acceptance of the stated sub-protocol's
decision. Conditional on that acceptance; `SameBut` and `DigLeft`; the tests in front; the tests
"formsIn" behind; the place; terms. No instance of these hypotheses is exhibited in this file. -/
theorem othersPub_dig_state (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {})
    (hlinks : Dm.links = linksFull)
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s)) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {x : Desc.First.Look.Place} (hlook : lookAt X l true = some x)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hd : b'.decide s rs cols = .ok s')
    (T : SameBut s s') (DL : DigLeft s s') (z : P)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, s) = true)
    (hF : ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
      (mgAll Dm Mg).pub r (z, s') = true) :
    ∀ r ∈ behindDig mgMore l, k3Like r = false → (mgAll Dm Mg).pub r (z, s') = true := by
  intro r hr hlike
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  obtain ⟨hsort, hkept⟩ := digits_sorted hl hsub
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s = true := by
    have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
      (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp := hfront _ (List.mem_append_left _ hOpen)
    rw [hpcT.symm.trans hpc] at hp
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z s hp)
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have hT : ∀ p ∈ keptDigits l sub', (mgAll Dm Mg).pub p (z, s) = true := fun p hp =>
    hfront p (hkept p hp)
  have three : ∀ p ∈ [Desc.First.Pub.unheard, Desc.First.Pub.indexIs, Desc.First.Pub.indexThere],
      (mgAll Dm Mg).pub p (z, s) = true → (mgAll Dm Mg).pub p (z, s') = true := by
    intro p hp ht
    rw [mgAll_pub] at ht ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z T (fun r _ => hBase r z s s') p hp
      ht
  have led : (mgAll Dm Mg).pub (.ledger l) (z, s) = true →
      (mgAll Dm Mg).pub (.ledger l) (z, s') = true := by
    intro ht
    rw [mgAll_pub, pubAll_ledger] at ht ⊢
    exact digLeft_ledgerB DL ht
  have fre : (mgAll Dm Mg).pub (.ledger l) (z, s) = true →
      (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
      (mgAll Dm Mg).pub (.freeAbove l) (z, s') = true := by
    intro hL ht
    rw [mgAll_pub, pubAll_ledger] at hL
    rw [mgAll_pub, pubAll_freeAbove] at ht ⊢
    cases hn : Dm.pubD.nsOf l with
    | none =>
      rw [hn] at ht
      cases ht
    | some n =>
      rw [hn] at ht
      exact digLeft_freeAboveB DL hL n ht
  rcases hsort r hr with h1 | h1 | h1
  · rw [hlike] at h1
    cases h1
  · have ht := hT r h1
    have h1m := h1
    have hLd : (mgAll Dm Mg).pub (.ledger l) (z, s) = true :=
      hT _ (by cases sub' <;> simp [keptDigits])
    cases sub' with
    | layers =>
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | h1
      · exact three _ (by simp) ht
      · exact led ht
      · exact fre hLd ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_hasRow Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z s s' _ cols hd hlook hsh l ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
    | attention =>
      have hAtt : Dm.pubD.d5.isAtt l = true := by
        show (Dm.links[l]? == some ModelPart.attention) = true
        rw [hlinks, hsub]
        rfl
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h1
      · exact three _ (by simp) ht
      · exact led ht
      · exact fre hLd ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_okAt Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z s s' _ cols hd hlook hsh l hAtt ht
      · rw [mgAll_pub] at ht ⊢
        exact digits_keeps_plain Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
          (IM.k3Place l true) b' hb hOk l rfl hpc z s s' _ cols hd hlook hsh hIn l hAtt ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
    | head =>
      simp only [keptDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl | h1
      · exact led ht
      · exact fre hLd ht
      · exact three _ (by simp) ht
      · exact three _ (by simp) ht
      · refine hF r (List.mem_append_left _ h1m) ?_
        rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · refine hF r (List.mem_append_right _ h1) ?_
    simp only [newDigits, List.mem_cons, List.not_mem_nil, or_false] at h1
    exact ⟨_, _, h1⟩

/-- **The kind's own public tests behind the acceptance: their Boolean tests.** Conditional on the
acceptance and the tests in front. No instance of these hypotheses is exhibited in this file. -/
theorem like_dig_state (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hd : b'.decide s rs cols = .ok s')
    (z : P) (hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, s) = true) :
    ∀ r ∈ behindDig mgMore l, k3Like r = true → (mgAll Dm Mg).pub r (z, s') = true := by
  intro r hr hlike
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hTab := hTab_mgAll Dm Mg hM l hl sub' hsub
  rw [eM] at hTab
  unfold digTableB at hTab
  have h1 := List.all_eq_true.1 hTab r hr
  rw [hlike] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  unfold digAllowedB at h1
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · obtain rfl : r = .lookOut l (7 + shift sub') := eq_of_beq h1
    have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
      (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp := hfront _ (List.mem_append_left _ hOpen)
    rw [mgAll_pub, ← hpcT] at hp ⊢
    exact digits_makes_lookOut Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
      (IM.k3Place l true) b' hb hOk l rfl hpc z s s' rs cols hd hp
  · rw [Bool.and_eq_true, Bool.or_eq_true] at h1
    obtain ⟨hQ, h2⟩ := h1
    rcases h2 with h2 | h2
    · obtain rfl : r = .lookOut l (2 + shift sub') := eq_of_beq h2
      have hp := hfront _ (List.mem_append_left _ (List.contains_iff_mem.1 hQ))
      have e2 : 2 + shift sub' = Desc.K3.pieceAt X l false :=
        piece_calls X l (shift sub') (hpcT.symm.trans hpc)
      rw [mgAll_pub, e2] at hp ⊢
      exact digits_keeps_lookOut Dm.pubD Mg.pub K3Lot.ofForm (K3Lot.readersAt X) codes shape
        (IM.k3Place l true) b' hb hOk l rfl hpc z s s' rs cols hd hp
    · cases r with
      | leftOn m =>
        rw [mgAll_pub]
        exact digits_makes_leftOn Dm.pubD Mg.pub m (z, s')
      | _ => cases h2

/-- **Every public test behind the acceptance: the Boolean tests.** Conditional on the acceptance of
the stated sub-protocol's decision; the place; the tests in front; the tests "formsIn" behind;
terms. No instance of these hypotheses is exhibited in this file. -/
theorem behind_dig_state (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {})
    (hlinks : Dm.links = linksFull)
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s)) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {x : Desc.First.Look.Place} (hlook : lookAt X l true = some x)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hd : b'.decide s rs cols = .ok s')
    (z : P) (hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, s) = true)
    (hF : ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
      (mgAll Dm Mg).pub r (z, s') = true) :
    ∀ r ∈ behindDig mgMore l, (mgAll Dm Mg).pub r (z, s') = true := by
  intro r hr
  obtain ⟨hpc, p, hp, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b'
    hb
  cases hlike : k3Like r with
  | true =>
    exact like_dig_state Dm Mg codes shape hM hl hsub b' hb hOk s s' rs cols hd z hfront r hr hlike
  | false =>
    have DL := k3_digits_step_leaves K3Lot.ofForm (K3Lot.readersAt X) X codes shape
      (IM.k3Place l true) b' hb hOk l rfl hpc s s' rs cols hd
    obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
    have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
    have hIn : Desc.K3.k3OnIn
        (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s = true := by
      have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
        (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub
        hpcT (.lookIn l (7 + shift sub')) (by simp)
      rw [eM] at hOpen
      have hp := hfront _ (List.mem_append_left _ hOpen)
      rw [hpcT.symm.trans hpc] at hp
      exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z s hp)
    obtain ⟨hs, hsh⟩ : ∃ hs,
        (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs := by
      cases e : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape with
      | none =>
        unfold Desc.K3.k3OnIn at hIn
        rw [e] at hIn
        cases hIn
      | some hs => exact ⟨hs, rfl⟩
    have T := (k3_digits_step_turns K3Lot.ofForm (K3Lot.readersAt X) X codes shape
      (IM.k3Place l true) b' hb hOk l rfl hpc hlook hsh s s' rs cols hd).1
    exact othersPub_dig_state Dm Mg codes shape hM hlinks hBase hl hsub hlook b' hb hOk s s' rs cols
      hd T DL z hfront hF r hr hlike

end

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.othersPub_dig_state
#print axioms ProofFile.Honest.K3.Law.Total.like_dig_state
#print axioms ProofFile.Honest.K3.Law.Total.behind_dig_state
