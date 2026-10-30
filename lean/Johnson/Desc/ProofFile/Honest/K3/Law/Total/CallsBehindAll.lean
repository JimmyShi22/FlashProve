-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/CallsBehindAll.lean: the kind "lookup" (K3). Conditional:
behind an acceptance of the decision of the lookup on a link's calls every public test that the
table of borders asks there holds; said of two states of the verifier, whatever the rounds' words.
Honest/K3/Law/Total/CallsBehindState.lean has all but five; here are the five (the library's
`paidCallsR`, Johnson/Desc/First/Look/K3CallsBehindR.lean: lookOut, ledger, freeAbove, linkFresh,
left), and the whole. At the library's composed meaning, for every value of its data. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table of borders is Johnson/Desc/First/Borders.lean,
whose head calls it the table of joints. A public test is the Boolean test of a public item: the
meaning's field pub. The tests in front and behind are the lists `frontAtK mgMore k` and
`behindAtK mgMore k a` (Johnson/Desc/Sound/MgAt/K3CallsTable.lean), at the head's link `headFront`
and `headBehind` (Johnson/Desc/Sound/MgAt/K3HeadBehindAt.lean). The lookup's promise in front is
`k3OnIn` (Johnson/Desc/First/Look/K3Borders.lean).

What is shown.
  `calls_free_anyWords`: the library's `k3_calls_freeAbove`
    (Johnson/Desc/First/Look/K3CallsKeeps.lean) without its hypothesis that each word of the rounds
    is below the prime.
  `calls_ledger_anyWords`: `k3_calls_ledger` (K3CallsKeeps.lean) without the same hypothesis.
  `calls_ns_anyWords`: the ledger's number of slots is as it was.
  `paid_state`: the five, at the composed meaning.
  `front_three`: out of the tests in front: the lookup's promise in front; freeAbove; linkFresh.
  `behind_att_state`, `behind_lay_state`, `behind_head_state`: the whole, by the link's sort.
What "every public test" is and is not. These theorems show the Boolean tests (the meaning's field
pub). At the item left the test is "true" by the meaning's own text and says nothing. What that item
says beside its test (the field pubP: the library's `k3LeftItemAt`,
Johnson/Desc/First/Look/K3LeftItem.lean) is not here; the library's `k3_calls_leftItem_anyWords`
(Johnson/Top/H/Keep/K3LeftAnyWords.lean) shows it without a hypothesis on the words.
Against the three theorems of CallsBehindState.lean: the hypothesis `SameBut` is gone (it follows
from the acceptance alone: the library's `k3_calls_sameBut`,
Johnson/Desc/First/Look/K3CallsTurns.lean), and so is the clause "none of the five". `hns` (the
built link has the place's number of slots) is asked at all three sorts: it is new at an attention
link and at the head's; at the head's link `hsP` (the place's shape) is new too.

Hypotheses that remain. As in CallsBehindState.lean; none of them is shown in this file.
  `hd`: the decision of the kind's sub-protocol accepts from s to s'.
  `hfront`: the public tests in front hold at s.
  public facts and terms: `hla`, `hpcX`, `hpc`: the place's link and piece; `hl`, `hsub`: the link's
    number and sort; `here`: the place's number in the written list; `hlook`, `hsP`: the lookup's
    place and its shape; `hmore`, `hM`: the meaning beneath has no extra public test; `hlinks`: the
    data's links are the written full list; `hhd`, `hmH`: the link is not the head's, or the head's
    is number 24; `hfit`: the table's test `pubFit` passes; `hns`: the built link's slots; `hBase`:
    the public test of the meaning beneath has one value at all states.
  `hh5`, `hown`, `hlay`: on the state in front: nothing of attention's own rounds is heard; nothing
    of the layers' own rounds is heard; a layers' link stands open.
  `hObj`: on the state behind: the test formsInT l 2 "objects" (at the head's link formsInT 24 3
    "objects") holds.
  `hIn`, `hfa`, `h0`, `hFree`, `hFresh`: (in the first four theorems) the lookup's promise in front;
    "free above" in front; the number of slots in front; the public items freeAbove l and linkFresh
    l hold at s.
  `hs`: (in the first three theorems) the parameters make the shape.

Follows. The proof of `calls_free_anyWords` is the proof of `k3_calls_freeAbove` token for token,
taken over by a program, but for the first step: `k3_calls_made`
(Johnson/Desc/First/Look/K3CallsMade.lean) stands in the place of `k3_calls_leaves`
(Johnson/Desc/First/Look/K3CallsLookOut.lean); both give what the hearing left. The proof of
`calls_ledger_anyWords` is made of that of `k3_calls_ledger` likewise.

How the proof goes. That the three tests of `front_three` are open in front is by the library's
`calls_asks_open` (Johnson/Desc/First/Look/K3CallsMean.lean) and its closed test `k3_open_calls`
(Johnson/Desc/Sound/MgAt/K3Open.lean), which the kernel evaluates.

Users. `madeOwed_calls_lay` and `madeOwed_calls_att` (Honest/K3/Law/Total/MadeOwedCalls.lean) and
`madeOwed_calls_head` (Honest/K3/Law/Total/MadeOwedCallsHead.lean) call the last three.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
The Boolean tests alone; at the item left the test says nothing: see the paragraph on "every public
test" under "What is shown". At the written full list of links and the library's closed list of
extra public tests alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.CallsBehindState
import Johnson.Desc.First.Look.K3CallsKeeps
import Johnson.Desc.First.Look.K3KeeperRides
import Johnson.Desc.Sound.MgAt.K3CallsBorder
import Johnson.Desc.Sound.MgAt.K3Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  pubFit shift pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc.K3 (sizedB freeB k3OnIn k3OnOut)

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (hs : p.shape = some h) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

include hs in
/-- **"Free above" is kept, whatever the rounds' words.** Conditional on the acceptance of the
decision, the lookup's promise in front, "free above" in front, and that the parameters make the
shape (`hs`). No instance of these hypotheses is exhibited in this file. -/
theorem calls_free_anyWords
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (hfa : freeAboveB s = true) : freeAboveB s' = true := by
  obtain ⟨F, F', g, _, hF, -, -, -, -, -, hF', -, L, E⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold freeAboveB at hfa ⊢
  rw [hF] at hfa
  rw [hF']
  simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hfa ⊢
  intro j hj
  have hns : F'.ns = F.ns := L.padLeft.rest.2.1
  have hin : F'.next + j < F'.gotF.size := by
    rw [L.padLeft.fit.2.2]
    omega
  refine getD_out _ _ hin ?_
  have e : F.next + (Forest.elems h + j) = F'.next + j := by
    rw [E.next]
    omega
  have q := hfa (Forest.elems h + j) (by
    rw [E.next, hns] at hj
    omega)
  rw [e] at q
  have hFn : ¬ Filled F (F'.next + j) := by
    intro hc
    unfold Filled at hc
    rw [getD_in _ _ q] at hc
    cases hc
  have hF'n : ¬ Filled F' (F'.next + j) := by
    intro hc
    rcases (E.marks _).1 hc with h1 | ⟨-, h2, -⟩
    · exact hFn h1
    · rw [E.next] at h2
      omega
  unfold Filled at hF'n
  cases hv : F'.gotF.getD (F'.next + j) false with
  | false => rfl
  | true => exact absurd hv hF'n

include hs in
/-- **The ledger behind is there and has its sizes, whatever the words.** Conditional on the
acceptance, the lookup's promise in front, and `hs`. No instance of these hypotheses is exhibited in
this file. -/
theorem calls_ledger_anyWords
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : (s'.fork?.any sizedB) = true := by
  obtain ⟨F, F', g, _, -, -, -, -, -, -, hF', -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  rw [hF']
  exact sizedB_of L.padLeft.fit

include hs in
/-- **The ledger's number of slots is as it was.** Conditional on the acceptance, the lookup's
promise in front, that number in front, and `hs`. No instance of these hypotheses is exhibited in
this file. -/
theorem calls_ns_anyWords
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (n : ℕ)
    (h0 : (s.fork?.any fun G => G.ns == n) = true) : (s'.fork?.any fun G => G.ns == n) = true := by
  obtain ⟨F, F', g, _, hF, -, -, -, -, -, hF', -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  rw [hF] at h0
  rw [hF']
  have hns : F'.ns = F.ns := L.padLeft.rest.2.1
  simp only [Option.any_some] at h0 ⊢
  rw [hns]
  exact h0

end

section
variable {Xi P Tok Cl : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols₀ nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols₀) Tok MsgT)) (claim : Aff → Cl)
  {l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **The five items of `paidCallsR` hold behind the acceptance: their Boolean tests.** Conditional
on the acceptance; the lookup's promise, freeAbove and linkFresh in front; the built link having the
place's number of slots. No instance of these hypotheses is exhibited in this file. -/
theorem paid_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hIn : k3OnIn theP s = true) (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns) (z : P)
    (hFree : (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true)
    (hFresh : (mgAll Dm Mg).pub (.linkFresh l) (z, s) = true) :
    ∀ p ∈ paidCallsR l (Desc.K3.pieceAt X l false), (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp
  have hK := k3At_mgAll Dm Mg
  simp only [paidCallsR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact fOut_at hK l false hlook z s'
      (k3_calls_lookOut_anyWords claim piece laid before theP guests s s' rs cols hsP rfl hd hIn)
  · show Desc.First.ledgerB s' = true
    rw [ledgerB_is]
    exact calls_ledger_anyWords claim piece laid before theP guests hsP s s' rs cols hd hIn
  · have f1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s) = true := hFree
    show ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s') = true
    have hns' : Dm.pubD.nsOf l = some (theP).ns := hns
    rw [hns', Option.any_some, freeAboveB_is] at f1 ⊢
    unfold freeAboveAtB at f1 ⊢
    rw [Bool.and_eq_true] at f1 ⊢
    exact ⟨calls_free_anyWords claim piece laid before theP guests hsP s s' rs cols hd hIn f1.1,
      calls_ns_anyWords claim piece laid before theP guests hsP s s' rs cols hd hIn _ f1.2⟩
  · rw [hK.linkFresh] at hFresh ⊢
    unfold linkFreshB at hFresh ⊢
    rw [k3_calls_unheard claim piece laid before theP guests s s' rs cols hd,
      k3_calls_linkSame claim piece laid before theP guests s s' rs cols hd]
    exact hFresh
  · exact hK.left l (z, s')

/-- **Out of the tests in front: the lookup's promise in front, freeAbove, linkFresh.** Conditional
on the tests that are open or tied in front, and public facts on the place. No instance of these
hypotheses is exhibited in this file. -/
theorem front_three (s : Desc.First.S) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) {sub : ModelPart} (hpc : a.piece = 2 + shift sub)
    (hl : l < 25) (hsub : linksFull[l]? = some sub) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hmore : Mg.more = {})
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true) (z : P)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll Dm Mg).pub q (z, s) = true) :
    k3OnIn theP s = true ∧ (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true ∧
      (mgAll Dm Mg).pub (.linkFresh l) (z, s) = true := by
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  have hOpen := calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l sub hfit here hla
    hsub hpc
  rw [hM] at hOpen
  refine ⟨k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z s ?_),
    hfront _ (List.mem_append_left _ (hOpen _ (by simp))), hfront _ (List.mem_append_left _ ?_)⟩
  · rw [← hpcX, hpc]
    exact hfront _ (List.mem_append_left _ (hOpen _ (by simp)))
  · rw [kOfCalls_border l]
    exact (MgAt.k3_open_calls hl).2.2

/-- **Every public test behind the acceptance, at an attention link: the Boolean tests.**
Conditional on the acceptance; the tests in front; nothing of attention's own rounds heard in front;
formsInT l 2 "objects" behind; public facts and terms. No instance of these hypotheses is exhibited
in this file. -/
theorem behind_att_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .attention) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns) (z : P)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll Dm Mg).pub q (z, s) = true)
    (hh5 : ∀ o, s.here = .att o → o.heard5 = none)
    (hObj : (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, s') = true) :
    ∀ p ∈ behindAtK mgMore (kOfCalls l) a, (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp
  obtain ⟨hIn, hFree, hFresh⟩ := front_three Dm Mg s hla hpcX (sub := .attention) hpc hl hsub here
    hlook hmore hfit z hfront
  by_cases hpaid : p ∈ paidCallsR l 2
  · refine paid_state Dm Mg claim piece laid before guests s s' rs cols hd hlook hsP hIn hns z hFree
      hFresh p ?_
    rw [← hpcX, hpc]
    exact hpaid
  · exact othersPub_att_state Dm Mg claim piece laid before guests s s' rs cols hd
      (k3_calls_sameBut claim piece laid before theP guests s s' rs cols hd) hla hpcX hpc hl hsub
      here hlook hsP hmore hlinks hhd hfit z hfront hh5 hObj p hp hpaid

/-- **The same at a layers' link.** Conditional on the like, with: a layers' link stands open in
front and nothing of its own rounds is heard. No instance of these hypotheses is exhibited in this
file. -/
theorem behind_lay_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .layers) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns) (z : P)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll Dm Mg).pub q (z, s) = true)
    (hown : ∀ o, s.here = .lay o → o.own = none) (hlay : ∃ o, s.here = .lay o)
    (hObj : (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, s') = true) :
    ∀ p ∈ behindAtK mgMore (kOfCalls l) a, (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp
  obtain ⟨hIn, hFree, hFresh⟩ := front_three Dm Mg s hla hpcX (sub := .layers) hpc hl hsub here
    hlook hmore hfit z hfront
  by_cases hpaid : p ∈ paidCallsR l 2
  · refine paid_state Dm Mg claim piece laid before guests s s' rs cols hd hlook hsP hIn hns z hFree
      hFresh p ?_
    rw [← hpcX, hpc]
    exact hpaid
  · exact othersPub_lay_state Dm Mg claim piece laid before guests s s' rs cols hd
      (k3_calls_sameBut claim piece laid before theP guests s s' rs cols hd) hla hpcX hpc hl hsub
      here hlook hsP hmore hlinks hhd hfit hns z hfront hown hlay hObj p hp hpaid

/-- **The same at the head's link.** Conditional on the acceptance; the tests in front; formsInT 24
3 "objects" behind; the place's shape; public facts and terms. No instance of these hypotheses is
exhibited in this file. -/
theorem behind_head_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hM : Mg.more = {})
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s))
    (hmH : headLink X = 24) (hlook : lookAt X 24 false = some x)
    (hsP : (theP).shape = some x.fs)
    (hpc : 2 + shift ModelPart.head = Desc.K3.pieceAt X 24 false)
    (hns : (Dm.built[24]?).map (·.ns) = some (theP).ns) (z : P)
    (hfront : ∀ r ∈ headFront mgMore, (mgAll Dm Mg).pub r (z, s) = true)
    (hObj : (mgAll Dm Mg).pub (.formsInT 24 3 "objects") (z, s') = true) :
    ∀ p ∈ headBehind mgMore, (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp
  have hfront' : ∀ q ∈ frontAtK mgMore (kOfCalls 24), (mgAll Dm Mg).pub q (z, s) = true := hfront
  obtain ⟨hIn, hFree, hFresh⟩ := front_three Dm Mg (l := 24) (a := IM.k3Place 24 false) s rfl hpc
    (sub := .head) rfl (by decide) (by decide) (K3Lot.k03_at_full 24 (by decide) false) hlook hM
    (hfit_mgAll Dm Mg hM) z hfront'
  by_cases hpaid : p ∈ paidCallsR 24 (2 + shift ModelPart.head)
  · refine paid_state Dm Mg claim piece laid before guests s s' rs cols hd hlook hsP hIn hns z hFree
      hFresh p ?_
    rw [← hpc]
    exact hpaid
  · exact othersPub_head_state Dm Mg claim piece laid before guests s s' rs cols hd
      (k3_calls_sameBut claim piece laid before theP guests s s' rs cols hd) hM hBase hmH hlook hpc
      z hfront hObj p hp hpaid

end

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.calls_free_anyWords
#print axioms ProofFile.Honest.K3.Law.Total.calls_ledger_anyWords
#print axioms ProofFile.Honest.K3.Law.Total.calls_ns_anyWords
#print axioms ProofFile.Honest.K3.Law.Total.paid_state
#print axioms ProofFile.Honest.K3.Law.Total.front_three
#print axioms ProofFile.Honest.K3.Law.Total.behind_att_state
#print axioms ProofFile.Honest.K3.Law.Total.behind_lay_state
#print axioms ProofFile.Honest.K3.Law.Total.behind_head_state
