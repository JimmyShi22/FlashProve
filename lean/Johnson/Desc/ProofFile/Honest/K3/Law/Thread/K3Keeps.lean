-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/K3Keeps.lean: the kind "lookup" (K3): what a lookup's
member leaves of the verifier's state as it was, and how what it changes may have changed: a
sentence on the state in front (s) and the state behind (s'), one for each of the three sorts of
member, each shown from the member's accepting step. Theorems.

Terms. Honest/K3/GLOSSARY.md ("keeps"). In this file: the sentences `LedgerKept`, `K3KeepsCalls`,
`K3KeepsDigits` and `K3KeepsHead`, and `DigitsArms`, are defined in Honest/K3/Law/KeepsDefs.lean.
The hearing is `hearVia p F rs`, and the decision is `decideVia` (both
Johnson/Desc/First/Look/Via/Via.lean). The state bears no mark if `failed = none`.

What is shown.
  `hearVia_back`, `ledgerKept_of`: the hearing's return gives `LedgerKept`, which says what the
    hearing does to the ledger, at every sort.
  `keepsCalls_of_decide`: `K3KeepsCalls` from an acceptance by the decision `decideVia` at a state
    without a mark.
  `k3Keeps_calls`, `k3Keeps_digits`, `k3Keeps_head`: the three sentences (at a lookup on the calls;
    at a lookup on the digits of a layers' or an attention link; at the lookup on the digits of the
    head's link), each from the accepting step of the description's own member, at any state and on
    any rounds.
  `keepsCalls_sameBut`, `keepsDigits_sameBut`, `keepsHead_sameBut`: each sentence gives the
    library's `SameBut` (Johnson/Desc/First/Look/K3CallsTurns.lean).
  Helpers: `site_shape`, `digits_arms_of`.

What each sentence says. The state behind bears no mark. By the sort of the link that is open, the
state behind is the state in front with named fields of the link's own part set: this is an
equation. At the calls: the ledger, what was heard, and in a layers' or an attention link the field
that the caller reads. At the digits: the ledger (with the plan's number of claims) and four fields
of the smallness test's structure. At the head's digits: the ledger, these four fields and the claim
on the weights. Every other field of the state and of the link's part is as it was. Of the ledger:
it is later (what lies under a slot that was filled is kept; the number of slots stays); its field
`trees` stays; the number of its slots' coefficients stays; its count has grown by the lookup's
slots; the claims owed in front are kept as they were, and what is appended is owed, not yet added;
and, where its three arrays had their size, at least three claims are appended.

Hypotheses that remain, in `k3Keeps_calls`, `k3Keeps_digits` and `k3Keeps_head`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); its sort.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: (at the digits; public) which step without a round stands behind the lookup:
    `quietDigits used claims`, or `quietHead` at the head's link
    (Johnson/Desc/First/Look/K3Whole.lean).
  `h`: the member's step accepts from sj to sj'.
In the others: the public parameters have the shape (`hs`); the hearing, or the decision, returns
(`hv`, `hd`); in `keepsCalls_of_decide` the state in front bears no mark (`h0`); in `digits_arms_of`
a ledger is open in front, and the state behind is the one in front with the structure and two
ledgers written in (`hF`, `e`); in the three theorems on `SameBut` the clause in question (`hK`).

Users. The sentences are for the thread's letter "keeps" (Honest/Thread/Thr.lean) at
the lookups' members: they are all that another kind has in hand when an item of its
own is
carried past a lookup. In these files under Honest/K3/Law/Thread/: `k3Keeps_calls`, `k3Keeps_digits`
and `k3Keeps_head` are called in K3KeepsAt.lean and RidersAtSite.lean, `k3Keeps_calls` and
`k3Keeps_head` also in LaysNext.lean, and `k3Keeps_head` also in LaysFold.lean and
LaysNextLight.lean; the three theorems on `SameBut` in RidersAtHead.lean; `hearVia_back` in
PutFo.lean and OnOutMember.lean, among others. K3KeepsSh.lean [not in this library] and
MemberDecides.lean import this file too.

Limits. What the sentences do not say: of a slot that was not filled in front and lies outside the
lookup's own stretch nothing is said. What was heard and the ledger behind stand under "there is":
each is fixed by the equation on the state behind. Of the ledger's other numbers and flags nothing
is said here. On the verifier's side alone. No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.Link.Law.SlotsVia
import Johnson.Desc.ProofFile.Honest.K3.Parts.Packs
import Johnson.Desc.ProofFile.Honest.K3.Law.DigitsBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.KeepsDefs
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CEndBelow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateHere
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehindHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork HTailF2)
open OnBytes.PscRun (Sized Later)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf quietAt quietDigits quietHead toHeard
  toHeardG seatCalls)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.OnPublicFiles (SameBut)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape
local notation "VFace" => VerifiableInference.Desc.K3.Face

/-! ## 1 The ledger -/

/-- The return of `hearVia` is the return of `hearV`; what it hands back is made of what `hearV`
heard. -/
theorem hearVia_back {p : P} {h : FShape} {F G : Fork} {rs : List Fmt.RoundView}
    {H : OnBytes.Model.Forest.Heard} (hs : p.shape = some h) (hv : hearVia p F rs = some (H, G)) :
    ∃ g, hearV (faceOf h) F rs = some (g, G) ∧ toHeard h (toHeardG g) = some H := by
  unfold hearVia at hv
  rw [hs] at hv
  simp only at hv
  split at hv
  · obtain ⟨x, hx, hm⟩ := Option.bind_eq_some_iff.1 hv
    obtain ⟨g', hg', e⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨gv, G'⟩ := x
    obtain rfl : G' = G := congrArg (·.2) e
    obtain rfl : g' = H := congrArg (·.1) e
    exact ⟨gv, hx, hg'⟩
  · exact nomatch hv

/-- **The hearing's return gives `LedgerKept`.** -/
theorem ledgerKept_of {p : P} {h : FShape} {F G : Fork} {rs : List Fmt.RoundView}
    {H : OnBytes.Model.Forest.Heard} (hs : p.shape = some h) (hv : hearVia p F rs = some (H, G)) :
    LedgerKept (faceOf h) F G := by
  obtain ⟨g, hg, _⟩ := hearVia_back hs hv
  exact ⟨hearV_later hg, VerifiableInference.Desc.LinkJoin.ViaL.hearVia_arrays hv,
    congrArg (·.2) (VerifiableInference.Desc.LinkJoin.ViaS.hearVia_slots hv),
    messagesV_next (hearV_messages hg).2, ProofFile.Honest.K3.Law.Digits.owed_grows hg,
    fun hS => ProofFile.Honest.K3.Parts.hearV_owed3 (faceOf h) hS hg⟩

/-! ## 2 The sentences, from an acceptance -/

/-- **From an acceptance by the decision `decideVia`**, at a state without a mark. -/
theorem keepsCalls_of_decide {Cl : Type} (claim : Aff → Cl) {p : P} {h : FShape} {s s' : FS}
    {rs : List Fmt.RoundView} (hs : p.shape = some h) (h0 : s.failed = none)
    (hd : decideVia (seatCalls claim) p s rs = .ok s') : K3KeepsCalls h s s' := by
  obtain ⟨F, H, G, a1, a2, _, _, a5, e⟩ := decideVia_whole _ p s s' rs hd
  have hC : CallsHere s s' H G := calls_here_of a1 a2 e
  refine ⟨?_, F, H, G, a1, hC, ledgerKept_of hs a5⟩
  rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, _, rfl⟩ <;> exact h0

/-- At a site the shape of the public parameters is the site's. -/
theorem site_shape {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) : s.p.shape = some s.shape := by
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  exact f2

/-- `DigitsArms`, from the equation in the state's own setters. -/
theorem digits_arms_of {sj sj' : FS} {F G G' : Fork} {tl' : HTailF2} (hF : sj.fork? = some F)
    (e : sj' = ((sj.putTl tl').putFork G).putFork G') : DigitsArms sj sj' tl' G' := by
  subst e
  unfold S.fork? at hF
  cases hh : sj.here with
  | lay a =>
    refine Or.inl ⟨a, hh, ?_⟩
    simp [S.putTl, S.putFork, hh]
  | att a =>
    refine Or.inr (Or.inl ⟨a, hh, ?_⟩)
    simp [S.putTl, S.putFork, hh]
  | head a =>
    rw [hh] at hF
    have hF' : (if a.opened = true then some a.F else none) = some F := hF
    cases ho : a.opened with
    | false =>
      rw [ho] at hF'
      exact nomatch hF'
    | true =>
      refine Or.inr (Or.inr ⟨a, hh, ho, ?_⟩)
      simp [S.putTl, S.putFork, hh, ho]
  | between =>
    rw [hh] at hF
    exact nomatch hF
  | fin a =>
    rw [hh] at hF
    exact nomatch hF
  | mem a =>
    rw [hh] at hF
    exact nomatch hF

section
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
  (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
  (hs : s ∈ lookSites Z)
include O hs

/-- **At a lookup on the calls.** No instance of these hypotheses is exhibited in this file. -/
theorem k3Keeps_calls (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    K3KeepsCalls s.shape sj sj' := by
  obtain ⟨F, H, G, a1, _, a5, hC, hf⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot
    m hb hbs hm hmp hpk ft sj sj' n rs c h
  exact ⟨hf, F, H, G, a1, hC, ledgerKept_of (site_shape hs) a5⟩

/-- **At a lookup on the digits of a layers' or an attention link.** No instance of these hypotheses
is exhibited in this file. -/
theorem k3Keeps_digits (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    K3KeepsDigits s.shape claims sj sj' := by
  obtain ⟨tl, F, H, G, htl, a1, _, _, _, a5, _, e, hf⟩ := digits_state o pol lay KL Fd Z Bs base ch
    A B O s hs hd lot m hb hbs hm hmp hpk used claims hq ft sj sj' n rs c h
  exact ⟨hf, tl, F, H, G, htl, a1, digits_arms_of a1 e,
    ledgerKept_of (site_shape hs) a5⟩

/-- **At the lookup on the digits of the head's link.** No instance of these hypotheses is exhibited
in this file. -/
theorem k3Keeps_head (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    K3KeepsHead s.shape sj sj' := by
  obtain ⟨tl, F, H, G, a, claim, htl, a1, _, _, _, a5, eh, _, e, hf⟩ := headDigits_state o pol lay
    KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq ft sj sj' n rs c h
  have hL := ledgerKept_of (site_shape hs) a5
  cases hh : sj.here with
  | head a₀ =>
    have hF' : (if a₀.opened = true then some a₀.F else none) = some F := by
      have := a1
      unfold S.fork? at this
      rw [hh] at this
      exact this
    cases ho₀ : a₀.opened with
    | false =>
      rw [ho₀] at hF'
      exact nomatch hF'
    | true =>
      simp only [S.putTl, S.putFork, hh, ho₀, if_true] at eh e
      obtain rfl := VerifiableInference.Desc.First.Here.head.inj eh
      refine ⟨hf, tl, F, H, G, a₀, claim, htl, a1, hh, ho₀, ?_, hL⟩
      rw [e, ho₀]
  | lay a₀ => simp [S.putTl, S.putFork, hh] at eh
  | att a₀ => simp [S.putTl, S.putFork, hh] at eh
  | between => simp [S.putTl, S.putFork, hh] at eh
  | fin a₀ => simp [S.putTl, S.putFork, hh] at eh
  | mem a₀ => simp [S.putTl, S.putFork, hh] at eh

end

/-! ## 3 Each gives the library's `SameBut` -/

theorem keepsCalls_sameBut {h : FShape} {s s' : FS} (hK : K3KeepsCalls h s s') : SameBut s s' := by
  obtain ⟨_, F, H, G, _, hC, _⟩ := hK
  rcases hC with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh], Or.inl ⟨a, _, hh, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh],
      Or.inr (Or.inl ⟨a, _, hh, rfl⟩)⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh, ho],
      Or.inr (Or.inr ⟨a, _, hh, rfl, ho, ho⟩)⟩

theorem keepsDigits_sameBut {h : FShape} {claims : Nat} {s s' : FS}
    (hK : K3KeepsDigits h claims s s') : SameBut s s' := by
  obtain ⟨_, tl, F, H, G, _, _, hC, _⟩ := hK
  rcases hC with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh], Or.inl ⟨a, _, hh, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh],
      Or.inr (Or.inl ⟨a, _, hh, rfl⟩)⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh, ho],
      Or.inr (Or.inr ⟨a, _, hh, rfl, ho, ho⟩)⟩

theorem keepsHead_sameBut {h : FShape} {s s' : FS} (hK : K3KeepsHead h s s') : SameBut s s' := by
  obtain ⟨_, tl, F, H, G, a₀, claim, _, _, hh, ho, rfl, _⟩ := hK
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, hh, ho],
    Or.inr (Or.inr ⟨a₀, _, hh, rfl, ho, ho⟩)⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.hearVia_back
#print axioms ProofFile.Honest.K3.Law.AtThr.ledgerKept_of
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsCalls_of_decide
#print axioms ProofFile.Honest.K3.Law.AtThr.site_shape
#print axioms ProofFile.Honest.K3.Law.AtThr.k3Keeps_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_arms_of
#print axioms ProofFile.Honest.K3.Law.AtThr.k3Keeps_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.k3Keeps_head
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsCalls_sameBut
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsDigits_sameBut
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsHead_sameBut
