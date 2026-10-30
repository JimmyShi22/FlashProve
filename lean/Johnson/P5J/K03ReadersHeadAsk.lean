-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03ReadersHeadAsk.lean: the kind "lookup" (K3): what a segment's readers answer in front
of the lookup on the digits they answer behind it: one theorem at all 25 segments, in three forms:
the first two in the asked form's own text with all its binders, the third from the table's promise
whole. Conditional: under two hypotheses more: the sentence of the public item leftOn at the state
in front, and, at segment 24 alone, what the output head's own sub-protocol has heard, or "reached"
in the narrower form. Over Johnson/P5J/K03ReadersHeadLay.lean, K03ReadersHeadAtt.lean and
K03ReadersHeadOut.lean. One closed test with code and nine theorems: two by the kernel's evaluation
(one a negative test), the others compositions.

Terms. lean/GLOSSARY.md; the head of Johnson/P5J/K03ReadersHeadLay.lean.

What is shown.
  `k03_pieceAt_calls`: in scope the calls' piece, by the kind's own text, is the written place's:
    the counterpart of the library's `k03_pieceAt_dig` (Johnson/P5J/K03RidesDigAt.lean).
  `lookOutAskedB`, `lookOutAsked_full`, `lookOutAsked_control`: at each of the 25 borders k3K l true
    the public item lookOut of the segment's lookup on the calls is among the items over which the
    promise's public test runs, at the written lists of the files under Johnson/IMR/ and the closed
    list of extra tests moreAll: by the kernel's evaluation; the neighbour's item is not.
  `k03_hO_of_EW`: the hypothesis `hO` of the three files follows from the asked form's own tests at
    the border, at any letter base: LPFK9.HandsAt.EW D base z k s is the promise's public test at
    border k over pubAll D base; at lookOut pubAll has a clause of its own, which does not read base
    (`k3At_mgAll`'s field lookOut, at a meaning whose public tests are base).
  `k03_hO_of_pub`, `k03_hL_of_pubP`: `hO` is the composed meaning's test at the public item lookOut,
    at the written place's piece; `hL` is its sentence at the public item leftOn (`k3At_mgAll`'s
    fields lookOut and pLeftOn).
  `k3_digits_readers_head`: the first form: the asked statement, every binder as it was written (h,
    hl, hb, base, z, ft, hreach, h0, hx, hy, m, k, ρ, ho, ho'), with `hP` and `hK` laid in front of
    hy.
  `k3_digits_readers_head_below`: the second form: the same with `hB` in `hK`'s place: at segment 24
    the state is reached by the sub-protocols with the test on the words in front.
  `k3_digits_readers_head_on`: the third form: from the table's promise whole (onAt) at a state
    without a mark, at any meaning whose public tests, public sentences and list of extra tests are
    the composed meaning's, at any numbers and any strings; with hreach and `hB`. hx, base and `hP`
    are not asked: the promise holds the test on the shape, lookOut's test and leftOn's sentence;
    that the two items stand in its lists is by the kernel's evaluation (`planesFront_mgMore`,
    Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean).

Hypotheses that remain.
  Those of the asked form: `h`: the library's hypothesis `AtMgA` (in `k03_pieceAt_calls`: `AtMg`);
    `hl`: l < 25; `hb`: blk is the chain's sub-protocol at the border; `hreach`: the state in front
    is reached (the bare `Reach`); `h0`: no mark in front; `hx`: the Boolean tests at the border
    (`IM.XK`); `hy`: the step (`IM.Yes`); `ho`, `ho'`: the sentence forms is open in front of the
    border, and behind it.
  The hypotheses more. hP : (mgAtAll h).pubP (.leftOn l) (z, s): what the open public item leftOn
    says at the state in front: of the asked form's fourth kind. hK : l = 24 → K6HeardAt … s: of
    none of the asked form's four kinds; who shows it: the head of
    Johnson/P5J/K03ReadersHeadOut.lean. hB : l = 24 → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp)
    (k3K l true) (z, s): the narrower family.
  In the third form: `hon`: the table's promise whole; `ePub`, `eP`, `eM`: the meaning's public
    tests, public sentences and list of extra tests are the composed meaning's.
  In the small theorems: `he` (`k03_hO_of_EW`): the asked form's tests at the border hold; `hT`
    (`k03_hO_of_pub`): the composed meaning's test at lookOut holds.
What is used of the asked form's own binders: hreach at the twelve layers' segments alone; of hx the
test on the shape (at attention's and the head's) and the further tests E (for `hO`); h0 ("no mark
in front") in the third form alone, where it opens the promise.

Options. `maxRecDepth` is raised to 100000 for the file and to 1000000 in front of two theorems; the
file is one `noncomputable section`. These raise limits on Lean's own work or switch off a check on
a notation's names: none loosens a check on a proof.

Limits. Compositions. `h` is a hypothesis. An instance of it at each of the two named sets of public
files stands in the library's side files: `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean)
and `headMember_zGap` (AtFullSide/Top/HeadMemberAtGap.lean). No state is
shown at which the hypotheses hold together. At 25 of the 126 pairs the item stands for no run and
the conclusion is true of nothing. At OnBytes.secondHashFunction. The full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P5J.K03ReadersHeadOut
import Johnson.LPFK9R.SharesAtE
import Johnson.Desc.Sound.MgAt.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain Wit Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Pub pubAll Meaning Numbers onAt pubHeld openSets pubSets
  pubOfItems start shapeAt)
open VerifiableInference.Desc.First.Look (k3OnOutAt)
open VerifiableInference.Desc.LinkJoin (askedAt ePubAt_mem)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- In scope the calls' piece, by the kind's own text, is the written place's. -/
theorem k03_pieceAt_calls (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (l : ℕ) :
    (IM.k3Place l false).piece = VerifiableInference.Desc.K3.pieceAt (At.X Zp) l false := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
  rw [p4, ng]
  by_cases e : l = 24
  · subst e
    rfl
  · simp [IM.k3Ix, e]

/-- At each of the 25 borders the calls' item lookOut is among the items that the promise's public
test runs over. -/
def lookOutAskedB : Bool :=
  (List.range 25).all fun l =>
    (askedAt moreAll IM.linksW IM.placesW (k3K l true)).contains
      (.lookOut l (IM.k3Place l false).piece)

set_option maxRecDepth 1000000 in
theorem lookOutAsked_full : lookOutAskedB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the neighbour's item is not among them. -/
theorem lookOutAsked_control :
    (askedAt moreAll IM.linksW IM.placesW (k3K 0 true)).contains
      (.lookOut 1 (IM.k3Place 1 false).piece) = false := by decide +kernel

/-- **hO from the asked form's own tests at the border, at any base.** -/
theorem k03_hO_of_EW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (base : Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub) {s : S}
    (he : LPFK9.HandsAt.EW h.𝔇.pubD base z (k3K l true) s = true) :
    k3OnOutAt (At.X Zp) l false s = true := by
  have h0 := List.all_eq_true.1 lookOutAsked_full l (List.mem_range.2 hl)
  have hq : Pub.lookOut l (IM.k3Place l false).piece ∈
      askedAt moreAll IM.linksW IM.placesW (k3K l true) := List.contains_iff_mem.1 h0
  have h1 : pubAll h.𝔇.pubD base (.lookOut l (IM.k3Place l false).piece) (z, s) = true :=
    ePubAt_mem he hq
  rw [k03_pieceAt_calls h.toAtMg l] at h1
  have h2 := (k3At_mgAll h.𝔇 { mgBase with pub := base }).lookOut l false (z, s)
  exact h2.symm.trans h1

/-- **hO is the composed meaning's test at lookOut**, at the written place's piece. -/
theorem k03_hO_of_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (l : ℕ) (z : ProofFile.InstPub)
    {s : S} (hT : (mgAtAll h).pub (.lookOut l (IM.k3Place l false).piece) (z, s) = true) :
    k3OnOutAt (At.X Zp) l false s = true := by
  rw [k03_pieceAt_calls h.toAtMg l] at hT
  exact ((k3At_mgAll h.𝔇 mgBase).lookOut l false (z, s)).symm.trans hT

/-- **hL is the composed meaning's sentence at leftOn.** -/
theorem k03_hL_of_pubP (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (l : ℕ) (z : ProofFile.InstPub)
    {s : S} (hP : (mgAtAll h).pubP (.leftOn l) (z, s)) : k3LeftOnItemAt (At.X Zp) l s :=
  Eq.mp ((k3At_mgAll h.𝔇 mgBase).pLeftOn l (z, s)) hP

-- from here on the closed lists are not unfolded
attribute [local irreducible] IM.openAt VerifiableInference.Desc.First.flatPlacesOf

set_option linter.unusedVariables false in
/-- **The first form: the asked statement at every l < 25**, with hP and hK in front of hy. The
binder h0 is idle: it is kept, under the asked form's name, for the text's sake. -/
theorem k3_digits_readers_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K l true]? = some blk)
    (base : Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K l true) (z, s)) (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z)
      (k3K l true) s = true)
    (hP : (mgAtAll h).pubP (.leftOn l) (z, s))
    (hK : l = 24 →
      K6HeardAt (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) s)
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  have hO := k03_hO_of_EW h hl base z (IM.xk_parts hx).2.2.2.2
  have hL := k03_hL_of_pubP h l z hP
  by_cases e24 : l = 24
  · subst e24
    exact k3_digits_readers_out h hb _ _ ft hx hO hL (hK rfl) hy m k ρ ho ho'
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact k3_digits_readers_lay h (by omega) hb z ft hreach hO hL hy m k ρ ho ho'
    · exact k3_digits_readers_att h (by omega) hb _ _ ft hx hO hL hy m k ρ ho ho'

/-- **The same with hK shown, at segment 24, from "reached by the sub-protocols with the test on the
words in front".** -/
theorem k3_digits_readers_head_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ}
    (hl : l < 25) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K l true]? = some blk)
    (base : Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K l true) (z, s)) (h0 : s.failed = none)
    (hx : IM.XK (At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z)
      (k3K l true) s = true)
    (hP : (mgAtAll h).pubP (.leftOn l) (z, s))
    (hB : l = 24 → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  refine k3_digits_readers_head h hl hb base z ft hreach h0 hx hP (fun e => ?_) hy m k ρ ho ho'
  subst e
  obtain ⟨Bs, base', O⟩ := h.laid.opened
  have hr' : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 345 (z, s) := hB rfl
  have kk := heardAt_345 h.scope h.reads O h.laid.planOk hr'
  rw [O.W] at kk
  exact kk

/-- **From the table's promise whole, at a state without a mark**: at any meaning Mg whose public
tests, public sentences and list of extra tests are the composed meaning's; at any numbers and any
strings. Neither the tests at the border nor their letter base is asked. -/
theorem k3_digits_readers_head_on (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ}
    (hl : l < 25) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[k3K l true]? = some blk)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT))
    (ePub : Mg.pub = (mgAtAll h).pub) (eP : Mg.pubP = (mgAtAll h).pubP)
    (eM : Mg.more = (mgAtAll h).more) (N : Numbers) (y : Strs) (z : ProofFile.InstPub) (ft : ℕ)
    {s s' : S} (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (k3K l true) (z, s))
    (h0 : s.failed = none)
    (hon : onAt N Mg At.links At.ps[k3K l true]?
      (((openSets At.links At.ps (start At.links))[k3K l true]?).getD [])
      (((pubSets Mg.more At.links At.ps)[k3K l true]?).getD []) (z, s) y)
    (hB : l = 24 → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hy : IM.Yes ft blk s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (k3K l true + 1)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  obtain ⟨-, hm | ⟨h1, -, -, h4⟩⟩ := hon
  · exact absurd h0 hm
  simp only [Bool.and_eq_true] at h1
  have hsh : shapeAt linksFull (VerifiableInference.Desc.First.flatPlacesOf linksFull true)[k3K l
      true]? s = true := h1.1.1.1.1.1
  have hp := h1.1.2
  unfold pubHeld at hp
  rw [List.all_eq_true] at hp
  have eMM : Mg.more = mgMore := eM.trans (mgAll_more_closed h.𝔇 mgBase rfl)
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Pub.lookOut l (IM.k3Place l false).piece ∈ frontDig mgMore l := by
    simpa using hFr.1
  have m2 : Pub.leftOn l ∈ (pubSets mgMore linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true))[k3K l true]?.getD [] := by
    simpa using hFr.2
  have hT : (mgAtAll h).pub (.lookOut l (IM.k3Place l false).piece) (z, s) = true := by
    rw [← ePub]
    exact hp _ (by rw [eMM]; exact m1)
  have hP : (mgAtAll h).pubP (.leftOn l) (z, s) := by
    rw [← eP]
    exact h4 _ (by rw [eMM]; exact m2)
  have hO := k03_hO_of_pub h l z hT
  have hL := k03_hL_of_pubP h l z hP
  by_cases e24 : l = 24
  · subst e24
    obtain ⟨Bs, base', O⟩ := h.laid.opened
    have hr' : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 345 (z, s) := hB rfl
    have kk := heardAt_345 h.scope h.reads O h.laid.planOk hr'
    rw [O.W] at kk
    obtain ⟨e, h3⟩ := open_cut (by have h9 := outsOpen_full; rwa [outsOpenB_def] at h9) ho ho'
    subst e
    exact k03_readers_out_items h hb ft hsh hO hL kk hy k ρ h3
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact k3_digits_readers_lay h (by omega) hb z ft hreach hO hL hy m k ρ ho ho'
    · have hg : g < 12 := by omega
      have h5 := List.all_eq_true.1 attsOpen_full g (List.mem_range.2 hg)
      obtain ⟨e, h3⟩ := open_cut h5 ho ho'
      subst e
      exact k03_readers_att_items h hg hb ft hsh hO hL hy k ρ h3

end P5J

#print axioms P5J.k03_pieceAt_calls
#print axioms P5J.lookOutAsked_full
#print axioms P5J.lookOutAsked_control
#print axioms P5J.k03_hO_of_EW
#print axioms P5J.k03_hO_of_pub
#print axioms P5J.k03_hL_of_pubP
#print axioms P5J.k3_digits_readers_head
#print axioms P5J.k3_digits_readers_head_below
#print axioms P5J.k3_digits_readers_head_on
