-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriesHeadDigits.lean: the kind "lookup" (K3): the
fiftieth step on the first chain's shape, the lookup on the digits of the head's link: its guards
and update as code, with `Carries` and `Returns` (Honest/Thread/Shape.lean) for them. Definitions
and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a state is `chainSh`
(Johnson/Desc/First/Shape/Chain.lean), of nineteen components. The guards of a member are the field
g of `Shape` (Honest/Thread/Shape.lean) at its border, and vals is that structure's field of named
tests on values. Behind this lookup stands the library's step without a round `quietHead`
(Johnson/Desc/First/Look/K3Whole.lean): it lays the claim on the weights in the own part of the
head's link.

What is shown.
  `claimShOf`, `claim_shape`: the shape of the claim that the library's `weightsClaim`
    (Johnson/Desc/First/Look/LookQuiet.lean) returns: a function of public data and of the size of
    the array rs that the head heard. Conditional on `layoutOk`, a test with code on public data
    (Honest/K3/Law/Thread/ClaimSizes.lean).
  `headDigits_hereSh`: the head's component behind the member's accepting step; six readers that
    stay.
  `headDigitsB`, `headDigitsU`, `headDigitsG`: the Boolean test, the update, the guards (helpers:
    `headDigitsU_at`, `sized_of_headDigitsB`).
  `carriesR_headDigits`, `carries_headDigits`: `Carries`, at one member and in the form of
    Shape.lean.
  `headDigitsB_reads`: what the test says of the state.
  `headBehind_of_vals`: the step without a round returns behind the lookup's own decision, from the
    test on values `headVals` (Honest/K3/Law/Thread/ClaimReturns.lean) at the state in front.
  `returns_headDigits`: `Returns`, in the form of Shape.lean.
The update changes three of the nineteen components: tl and led as at the other lookups on the
digits (but the plan's count of claims is not laid), and head: its claim.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk). In `carries_headDigits` and `returns_headDigits` the
    one hypothesis `hm` says the three of the entry of bs at b.
  `hq`: (for `Carries`) what stands behind the lookup is `quietHead`.
  `hL`: (for `Carries`) `layoutOk` passes.
  `hc`: (for `Returns`) the site's caller is the head.
  `hok`: (for `Returns`) the face's test passes.
  `hN`: (for `Returns`) there is one claim on the weights; a public fact.
  `hv`: (for `Returns`) the letter vals at this border gives `headVals`. That is a test on what the
    head heard, not on its shape: the library's `weightsClaim` refuses at values.
  `hg`: the guards at b are `headDigitsG s.shape s.p.first Z.p.X`.
  `h`: (in `headDigits_hereSh` and `carriesR_headDigits`) the member's step accepts from sj to sj'.
  `ha`, `ho`, `hdv`: (in `headBehind_of_vals`) the state stands in the head's link; it is opened;
    the seated decision accepts. In the helpers: `ht`, `hl`, `hh`, `hF`: what the shape, or the
    state, holds; `hB`: `headDigitsB` accepts.
  Second senses: `h` in `claim_shape`: `weightsClaim` returns; `hg` in `carriesR_headDigits`: the
    guards return t; `hv` in `headBehind_of_vals`: headVals Z.p.X sj = true at the one state.

Follows. This file is the counterpart of Honest/K3/Law/Thread/CarriesCalls.lean, CarriesDigits.lean
and ReturnsLook.lean, which have the other forty-nine steps.

Imported: Johnson/Desc/First/Shape/Chain.lean and Honest/Thread/Shape.lean.

Users. Honest/K3/Law/Thread/HeadDigitsAtLink.lean calls `carries_headDigits` and
`returns_headDigits`.

Limits. `Carries` speaks from an acceptance alone. `Returns` says that the member's decision
returns, not that its step accepts. `Carries` assumes `hq` and `Returns` assumes `hc`: no theorem of
this file ties the two. Since: `quiet_of_caller` (Honest/K3/Law/Thread/CallerAtLink.lean) gives hq
from hc under `P5J.AtMgA`; the converse is not shown there. The tests are not evaluated in this
file. They are evaluated in Honest/K3/Law/Thread/CarriesGuardsHead.lean [not in this library], at
three small synthetic public parts and at states
that the test makes up: the guard `headDigitsB` is seen to accept and to reject; `layoutOk` and
`headVals` accept at one of the three parts and reject at the two others. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ReturnsLook
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadParts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadDigitsBack
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadValsOf
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf quietAt quietHead seatDigits)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim sameShape)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LedSh TailSh HeadSh WsClaimSh ledSh
  tailSh headSh wsClaimSh heardAll sizedB freeB hereNo endSh attOf finOf)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape
local notation "headShOf" => VerifiableInference.Desc.First.Shape.headOf

/-! ## 1 The claim's shape -/

/-- **The shape of the claim on the weights**: a function of public data and of n, the size of the
array rs. Where the layout has no unit, or its last unit no second group, the defaults are read;
`claim_shape` is conditional on `layoutOk`. -/
def claimShOf (X : OnBytes.Model.Verify.Public) (n : Nat) : WsClaimSh :=
  let U := X.layers.wsLay.U
  let gk := (U.getD (U.size - 1) default).g.getD 1 default
  { ui := U.size - 1
    f := [(0, 0, X.hS.V), (min gk.o (2 ^ (min X.H.lamS n - gk.z)), gk.z, 0)] }

/-- **What `weightsClaim` returns has that shape.** Conditional on `hL`. -/
theorem claim_shape {X : OnBytes.Model.Verify.Public} {cov : OnBytes.Model.Head.Covered}
    {x : OnBytes.Model.Head.Heard} {tt : OnBytes.Model.Head.Tables} {cl : OnBytes.Model.WsClaim}
    (hL : layoutOk X.HLy X.layers.wsLay = true)
    (h : weightsClaim
      { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
        x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 }
      X.layers.wsLay = .ok cl) :
    wsClaimSh cl = claimShOf X x.rs.size := by
  obtain ⟨gx, gk, hg, hx, hk⟩ := layoutOk_groups hL
  obtain ⟨e1, e2⟩ := claim_sizes h hg hx hk
  have hgk : (X.layers.wsLay.U.getD (X.layers.wsLay.U.size - 1) default).g.getD 1 default = gk := by
    rw [hg]
    rfl
  unfold wsClaimSh claimShOf
  rw [e1, e2]
  dsimp only
  rw [hgk]

/-- **The head's component behind the member's accepting step; six readers that stay.** Conditional
on the hypotheses of `headDigits_stateW` (Honest/K3/Law/Thread/HeadDigitsBack.lean), and on `hL`.
No instance of these hypotheses is exhibited in this file. -/
theorem headDigits_hereSh (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n))
    (hL : layoutOk Z.p.X.HLy Z.p.X.layers.wsLay = true) :
    ∃ a₀, sj.here = .head a₀ ∧
      headShOf sj'.here = some { headSh a₀ with
        claim := (headSh a₀).x.map fun xs => claimShOf Z.p.X xs.rs } ∧
      sj'.failed = sj.failed ∧ hereNo sj'.here = hereNo sj.here ∧
      endSh sj'.here = endSh sj.here ∧ sj'.own? = sj.own? ∧ attOf sj'.here = attOf sj.here ∧
      finOf sj'.here = finOf sj.here := by
  obtain ⟨tl, F, H, G, a₀, cov, x, tt, claim, _, _, _, hh, ho, hx, _, hw, rfl, _⟩ :=
    headDigits_stateW o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq ft sj
      sj' n rs c h
  have hc := claim_shape hL hw
  refine ⟨a₀, hh, ?_, rfl, by simp [hereNo, hh, ho], by simp [endSh, hh], by simp [S.own?, hh],
    by rw [hh]; rfl, by rw [hh]; rfl⟩
  simp [VerifiableInference.Desc.First.Shape.headOf, headSh, ho, hx, hc,
    VerifiableInference.Desc.First.Shape.headHeardSh]

/-! ## 2 Guards and update -/

/-- **The Boolean test.** Here h is the lookup's shape and first is its first slot. -/
def headDigitsB (h : FShape) (first : Nat) (a : ChainSh) : Bool :=
  !a.marked && VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits a.rowsOwed &&
    a.tl.any (fun T => T.heard.isNone) &&
    (a.led.any fun Ld =>
      Ld.next == first && sizedB Ld && freeB Ld first (OnBytes.Model.Forest.elems h)) &&
    a.head.any fun H => H.x.isSome && H.t && H.shut.isNone

/-- **The update**, written out component by component: sixteen components stay as they are, three
are set. -/
def headDigitsU (h : FShape) (X : OnBytes.Model.Verify.Public) (a : ChainSh) : ChainSh :=
  match a.tl, a.led, a.head with
  | some T, some Ld, some H =>
    ChainSh.mk a.marked a.here
      (some { T with
        foldDrawn := T.foldDrawn + 1, slotA := Ld.next, slotB := (lookUpd (faceOf h) Ld).next,
        heard := some (lookHeardSh h Ld.next Ld.owed.length) })
      (some (lookUpd (faceOf h) Ld)) a.tables a.rowsOwed a.core a.reply
      a.indexMasks a.pile a.atEnd a.check a.link a.look a.lookHeard a.own
      (some { H with claim := H.x.map fun xs => claimShOf X xs.rs }) a.att a.fin
  | _, _, _ => a

/-- **The guards.** -/
def headDigitsG (h : FShape) (first : Nat) (X : OnBytes.Model.Verify.Public) (a : ChainSh) :
    Except String ChainSh :=
  if headDigitsB h first a then .ok (headDigitsU h X a)
  else .error "K3: the lookup on the head's digits"

/-- The update where the three shapes are there. -/
theorem headDigitsU_at {h : FShape} {X : OnBytes.Model.Verify.Public} {a : ChainSh} {T : TailSh}
    {Ld : LedSh} {H : HeadSh} (ht : a.tl = some T) (hl : a.led = some Ld) (hh : a.head = some H) :
    headDigitsU h X a = ChainSh.mk a.marked a.here
      (some { T with
        foldDrawn := T.foldDrawn + 1, slotA := Ld.next, slotB := (lookUpd (faceOf h) Ld).next,
        heard := some (lookHeardSh h Ld.next Ld.owed.length) })
      (some (lookUpd (faceOf h) Ld)) a.tables a.rowsOwed a.core a.reply
      a.indexMasks a.pile a.atEnd a.check a.link a.look a.lookHeard a.own
      (some { H with claim := H.x.map fun xs => claimShOf X xs.rs }) a.att a.fin := by
  unfold headDigitsU
  rw [ht, hl, hh]

/-- The test includes the test on the ledger's three sizes. -/
theorem sized_of_headDigitsB {h : FShape} {first : Nat} {sj : FS}
    (hB : headDigitsB h first (chainSh sj) = true) (F : Fork) (hF : sj.fork? = some F) :
    sizedB (ledSh F) = true := by
  have hl : (chainSh sj).led = some (ledSh F) := by
    show sj.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold headDigitsB at hB
  rw [hl] at hB
  simp only [Bool.and_eq_true, Option.any_some] at hB
  exact hB.1.2.1.2

/-! ## 3 `Carries` -/

/-- **At one member.** Conditional on the description's return, the site, the lot's sub-protocol and
the member at its place, which passes its own test on the plan, the member's acceptance, the guards'
return, `hq` and `hL`. No instance of these hypotheses is exhibited in this file. -/
theorem carriesR_headDigits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hL : layoutOk Z.p.X.HLy Z.p.X.layers.wsLay = true) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (t : ChainSh)
    (h : m.step ft sj rs c = .ok (sj', n))
    (hg : headDigitsG s.shape s.p.first Z.p.X (chainSh sj) = .ok t) : t = chainSh sj' := by
  unfold headDigitsG at hg
  cases hB : headDigitsB s.shape s.p.first (chainSh sj) with
  | false =>
    rw [hB] at hg
    exact nomatch hg
  | true =>
    rw [hB] at hg
    have ht : headDigitsU s.shape Z.p.X (chainSh sj) = t := Except.ok.inj hg
    obtain ⟨tl, F, _, _, htl, a1, _, _, _, _, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _,
      _⟩ := headDigits_parts o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq
        ft sj sj' n rs c h (sized_of_headDigitsB hB)
    obtain ⟨a₀, hh, qH, q1, q2, q3, q4, q6, q7⟩ := headDigits_hereSh o pol lay KL Fd Z Bs base ch A
      B O s hs hd lot m hb hbs hm hmp hpk hq ft sj sj' n rs c h hL
    have hl : (chainSh sj).led = some (ledSh F) := by
      show sj.fork?.map ledSh = _
      rw [a1]
      rfl
    have hT : (chainSh sj).tl = some (tailSh tl) := by
      show sj.tl?.map tailSh = _
      rw [htl]
      rfl
    have hH : (chainSh sj).head = some (headSh a₀) := by
      show headShOf sj.here = _
      rw [hh]
      rfl
    rw [← ht, headDigitsU_at hT hl hH, ← heardSh_led]
    unfold chainSh
    rw [q1, q2, q3, q4, qH, q6, q7, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
    rfl

/-- **`Carries` at the lookup on the digits of the head's link**, in the form of
Honest/Thread/Shape.lean. Conditional on the description's return, the site, `hq`, `hL`, `hm` and
`hg`. No instance of these hypotheses is exhibited in this file. -/
theorem carries_headDigits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hL : layoutOk Z.p.X.HLy Z.p.X.layers.wsLay = true)
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = headDigitsG s.shape s.p.first Z.p.X) :
    Carries bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols sj' n t hst hgt
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  exact carriesR_headDigits o pol lay KL Fd Z Bs base ch A B O s hs hd lot blk hb hbs h1 h2 h3 hq hL
    ft sj sj' n rs cols t hst hgt'

/-! ## 4 `Returns` -/

/-- **What the test says of the state.** -/
theorem headDigitsB_reads {h : FShape} {first : Nat} {sj : FS}
    (hB : headDigitsB h first (chainSh sj) = true) :
    sj.failed = none ∧ VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      (sj.tl?.bind (·.heard)).isNone = true ∧ (∃ F, sj.fork? = some F ∧ F.next = first ∧
        freeB (ledSh F) F.next (faceOf h).slots = true) ∧
      ∃ a, sj.here = .head a ∧ a.opened = true := by
  unfold headDigitsB at hB
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hB
  have c1 : sj.failed.isSome = false := b1
  have c3 : (sj.tl?.map tailSh).any (fun T => T.heard.isNone) = true := b3
  have c4 : (sj.fork?.map ledSh).any (fun Ld => Ld.next == first && sizedB Ld &&
      freeB Ld first (OnBytes.Model.Forest.elems h)) = true := b4
  have c5 : (headShOf sj.here).any (fun H => H.x.isSome && H.t && H.shut.isNone) = true := b5
  have d1 : sj.failed = none := by
    cases hf : sj.failed with
    | none => rfl
    | some v =>
      rw [hf] at c1
      exact nomatch c1
  have d3 : (sj.tl?.bind (·.heard)).isNone = true := by
    cases hl : sj.tl? with
    | none => rfl
    | some tl =>
      rw [hl] at c3
      have c3' : (tl.heard.map heardAll).isNone = true := c3
      show tl.heard.isNone = true
      cases hx : tl.heard with
      | none => rfl
      | some v =>
        rw [hx] at c3'
        exact nomatch c3'
  have d4 : ∃ F, sj.fork? = some F ∧ F.next = first ∧
      freeB (ledSh F) F.next (faceOf h).slots = true := by
    cases hF : sj.fork? with
    | none =>
      rw [hF] at c4
      exact nomatch c4
    | some F =>
      rw [hF] at c4
      simp only [Option.map_some, Option.any_some, Bool.and_eq_true, beq_iff_eq] at c4
      have hn : F.next = first := c4.1.1
      refine ⟨F, rfl, hn, ?_⟩
      rw [Spec.slots_elems, hn]
      exact c4.2
  have d5 : ∃ a, sj.here = .head a ∧ a.opened = true := by
    cases hh : sj.here with
    | head a =>
      rw [hh] at c5
      cases ho : a.opened with
      | true => exact ⟨a, rfl, ho⟩
      | false => simp [VerifiableInference.Desc.First.Shape.headOf, headSh, ho] at c5
    | lay a => rw [hh] at c5; exact nomatch c5
    | att a => rw [hh] at c5; exact nomatch c5
    | between => rw [hh] at c5; exact nomatch c5
    | fin a => rw [hh] at c5; exact nomatch c5
    | mem a => rw [hh] at c5; exact nomatch c5
  exact ⟨d1, b2, d3, d4, d5⟩

/-- **The step without a round returns behind the lookup's own decision**, from the test on values
at the state in front. Conditional besides on: the site is on the digits; the state stands in the
head's link, opened; one claim on the weights; the seated decision accepts. -/
theorem headBehind_of_vals (Z : Pub) (s : Site) (hd : s.digits = true) {sj : FS}
    {a : VerifiableInference.Desc.First.HeadOwn} (ha : sj.here = .head a) (ho : a.opened = true)
    (hv : headVals Z.p.X sj = true) (hN : (Z.p.X.H.NCL == 1) = true) (rs : List Fmt.RoundView) (s' : FS)
    (hdv : decideVia (seatOf K3Lot.ofForm s.digits) s.p sj rs = .ok s') :
    ∃ t, HeadBehind Z.p.X s' t := by
  obtain ⟨a', ha', hx, ht⟩ := headVals_head hv
  obtain rfl : a = a' := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ha')
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨tt, ht'⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨cov, claim, hcov, hw⟩ := headVals_gives hv ha hx' ht'
  rw [hd] at hdv
  obtain ⟨F₁, H, G₁, a1, _, _, _, _, e⟩ :=
    decideVia_whole (seatDigits K3Lot.ofForm) s.p sj s' rs hdv
  have a1' : sj.fork? = some F₁ := a1
  obtain ⟨tl, htl⟩ := tl_of_fork sj a1'
  rw [digits_put K3Lot.ofForm sj htl a1' H G₁] at e
  simp only [S.putTl, S.putFork, ha, ho, if_true] at e
  refine ⟨_, quietHead_returns Z.p.X s' (a := _) (by rw [e]) ?_ ?_ ?_ ?_ hw hN⟩
  · rfl
  · rw [e]
    exact hcov
  · exact hx'
  · exact ht'

/-- **`Returns` at the lookup on the digits of the head's link**, in the form of
Honest/Thread/Shape.lean. Conditional on the description's return, the site, `hc`, `hok`, `hN`,
`hm`, `hg` and `hv`. No instance of these hypotheses is exhibited in this file. -/
theorem returns_headDigits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (hc : s.caller = .head)
    (lot : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hok : s.at_.face.ok = true)
    (hN : (Z.p.X.H.NCL == 1) = true)
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = headDigitsG s.shape s.p.first Z.p.X)
    (hv : ∀ st rs cols, vals b st rs cols = true → headVals Z.p.X st = true) :
    Returns bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols t hgt hFit hvals
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  have hB : headDigitsB s.shape s.p.first (chainSh sj) = true := by
    unfold headDigitsG at hgt'
    cases hx : headDigitsB s.shape s.p.first (chainSh sj) with
    | true => rfl
    | false => rw [hx] at hgt'; exact nomatch hgt'
  obtain ⟨r1, r2, r3, ⟨F, r4, r5, r6⟩, a, ha, ho⟩ := headDigitsB_reads hB
  refine member_decides o pol lay KL Fd Z Bs base ch A B O s hs lot blk hb hbs h1 h2 h3 hok
    (by rw [hd]; rfl) (by rw [hc]; simp) ft sj F r1 (by rw [hd]; exact r4) (by rw [hd]; exact r3)
    (by rw [hd]; exact r2) r5 r6
    (fun _ _ rs' _ _ s' _ _ hdv =>
      headBehind_of_vals Z s hd ha ho (hv sj _ _ hvals) hN rs' s' hdv) rs cols hFit

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.claim_shape
#print axioms ProofFile.Honest.K3.Law.AtThr.headDigits_hereSh
#print axioms ProofFile.Honest.K3.Law.AtThr.headDigitsU_at
#print axioms ProofFile.Honest.K3.Law.AtThr.sized_of_headDigitsB
#print axioms ProofFile.Honest.K3.Law.AtThr.carriesR_headDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_headDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.headDigitsB_reads
#print axioms ProofFile.Honest.K3.Law.AtThr.headBehind_of_vals
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_headDigits
