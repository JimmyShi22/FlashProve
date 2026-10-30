-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeOpensAtHead.lean: the kind "lookup" (K3): the
frame's share `ExchangeAt` (Honest/Thread/Shares.lean) at a lookup on the digits, at the frame's
letters at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean): at each item that the
table's row opens. Corollaries of the proof of `exchange_headDigits` (ExchangeAtHead.lean in this
folder): each strikes, lays or obtains a premise of that theorem. Theorems alone.

Why. `exchange_headDigits` ends at `Exchange`: all that the row owes. The frame's gathering asks
for the shares at the owed items, and takes on itself the pins that are open in front. Of
the eleven named binders of that theorem hbase and hBack (with the letter nT) serve the pins alone,
and hfit and hb serve only "what the row reads is open in front".

What is shown, at the border of a site s on the digits.
  `exchangeAt_headDigits`: the share at each of the three items that the row opens. The binders of
    `exchange_headDigits` less n, hfit, hb, nT, hbase, hBack.
  `exchangeAt_headDigits_owed`: the same in the row's own words: at every owed item that is no pin.
  `exchangeAt_headDigits_off`: with s.link ≠ 24 in the stead of hH.
  `exchangeAt_headDigits_plan`: hsub struck and hx obtained; hRun is asked at every sub, x, tl that
    the letters' list of links and the plan's reader give at s.link. At most one such triple is
    there, since both are equations "a term = some …"; `hsub_at` and the library's
    `Q38.digAt_at_head` show one: so the premise says what the elder one says at that triple.
  `exchangeAt_headDigits_thin`, `exchangeAt_headDigits_thinner`: the sub-protocol and the fields
    inLot, lotPlace and ok of `SiteRest` obtained; in the second the field shapeIs too, which is
    true by computation on the digits.

Hypotheses that remain. `hRun` : `DigitsRunAll` (ExchangeDigitsAll.lean): the honest run's own facts
at every step on the thread, on the Script and the prover: nobody's. `hH` : `HeadReturns`: at link
24 not paid. `R` : `SiteRest` at the fast filling's asked jobs, or its fields: half (on the prover's
list), fits, usedIs (tests with code on public data). `hsite`, `hd`, `hsub`, `hx`: public. `hj`,
`hp`: the item is owed and is no pin.

Imported. ExchangeOpensDigits.lean, ExchangeAtHead.lean, CallerAtLink.lean, ThinRest.lean in this
folder; the library's Johnson/HB/LLHARD/Q38E/DigAtHead.lean; Johnson/AtFull/Shape/FaceAtSites.lean
(`face_ok_site`).


Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. This pays nothing at a Script: each theorem is a conditional sentence, and none touches what
hRun asks. `exchangeAt_headDigits_owed` is not the binder of the frame's gathering: there the item
is excused if it is open in front and a pin; here if it is a pin. From the thread alone (`Thr`): so,
by the frame's `exchangeAtS_of` (Honest/Thread/SharesS.lean), at every family Said. The border is
the library's `borderOf l d`, which unfolds to 14 * l + ixOf l d + 2
(Johnson/Desc/Sound/MgAt/K3Open.lean). On the digits alone; the full size alone. The frame's letter
for "keeps" by place is a variable, Kp: nothing here reads it. No instance of the hypotheses beside
the head is exhibited in this file. Nothing shows that the thread holds at any run.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOpensDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallerAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ThinRest
import Johnson.HB.LLHARD.Q38E.DigAtHead
import Johnson.AtFull.Shape.FaceAtSites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt sameShape)
open VerifiableInference.Desc.Sound (MsgT seatTab digits_row)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr
open Johnson.AtFull.Shape (face_ok_site)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {W₀' Rc' Xi' Tr' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The share at each of the three items that the row opens.** Conditional on what this file's
head lists: hRun first. No instance of the hypotheses beside the head is exhibited in this file. -/
theorem exchangeAt_headDigits (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ [Item.forms s.link (7 + shift sub) "objects",
      .worth s.link (7 + shift sub) "planes", .worth s.link (7 + shift sub) "keys"]) :
    ExchangeAt (LH).thread (borderOf s.link s.digits) j := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ wit R
  obtain ⟨_, _, e3⟩ := site_border h s hsite lot R.inLot R.lotPlace
  have hp := (place_at h s hsite lot R.inLot R.lotPlace).2
  have hpiece : s.at_.place.piece =
      VerifiableInference.Desc.Sound.MgAt.pieceOf s.link s.digits := by
    rw [hp]
    rfl
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans hsub)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, hd]
    rfl
  have hpc : VerifiableInference.Desc.K3.pieceAt Zp.p.X s.link true = 7 + shift sub := by
    rw [← hd, e3, ← hpiece]
    exact hpcT
  exact exchangeAt_digits_fast src o pol lay KL Fd base A B O hS hH hd
    (fun w' => k3At_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w') hx hpc
    h.𝔇.runs h.𝔇.Rd h.𝔇.N.sent h.𝔇.N.group h.𝔇.ah (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w' => formsText_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w')
    (6 + shift sub) (runs_digits h s.link sub hsub) (ah_objects h _) (ah_guests h _) hRun hj

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The same in the row's own words: the share at every owed item that is no pin.** Conditional on
the same. It is not the binder of the frame's gathering: see this file's Limits. -/
theorem exchangeAt_headDigits_owed (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes)
    (hp : ∀ m t, j ≠ Item.pin m t) : ExchangeAt (LH).thread (borderOf s.link s.digits) j := by
  obtain ⟨_, hk, _⟩ := site_border h s hsite lot R.inLot R.lotPlace
  have hpl := (place_at h s hsite lot R.inLot R.lotPlace).2
  have hl : s.at_.place.link = some s.link := by
    rw [hpl]
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans hsub)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, hd]
    rfl
  obtain ⟨_, ho, hc⟩ := digits_row (LH).links s.at_.place s.link sub hl hsub hpcT
  rw [owes_at_link (LH) hk hl, ho, hc] at hj
  rcases List.mem_append.1 hj with h3 | h3
  · exact exchangeAt_headDigits h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hH
      hd hsub hx hRun h3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with e | e | e
    · exact absurd e (hp _ _)
    · exact absurd e (hp _ _)
    · exact absurd e (hp _ _)

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**Off link 24.** `HeadReturns` holds there emptily (`headReturns_offHead`, CallerAtLink.lean).
Conditional on the rest. -/
theorem exchangeAt_headDigits_off (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (e : s.link ≠ 24) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes)
    (hp : ∀ m t, j ≠ Item.pin m t) : ExchangeAt (LH).thread (borderOf s.link s.digits) j :=
  exchangeAt_headDigits_owed h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R
    (headReturns_offHead (LH) h _ s hsite e) hd hsub hx hRun hj hp

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The link's sort struck, the plan's answer obtained.** hRun is asked at every sub, x, tl that
the two readers give at s.link: there is just one such triple. Conditional on the rest. -/
theorem exchangeAt_headDigits_plan (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true)
    (hRun : ∀ (sub : ModelPart) (x : PlaceL) (tl : HTailF2), (LH).links[s.link]? = some sub →
      digAt Zp.p.X s.link = some (x, tl) →
      DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
        h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes)
    (hp : ∀ m t, j ≠ Item.pin m t) : ExchangeAt (LH).thread (borderOf s.link s.digits) j := by
  obtain ⟨sub, h1, _⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  obtain ⟨x, tl, hx⟩ := Q38.digAt_at_head h (Nat.le_of_lt_succ (link_lt_head h s hsite))
  exact exchangeAt_headDigits_owed h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R
    hH hd h1 hx (hRun sub x tl h1 hx) hj hp

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The sub-protocol and three fields of `SiteRest` obtained.** ok by `face_ok_site`
(Johnson/AtFull/Shape/FaceAtSites.lean); the sub-protocol by `SiteRestThin.rest` (ThinRest.lean) and
`rest_of_rest'` (LotAtSite.lean). Conditional on the rest. -/
theorem exchangeAt_headDigits_thin (src : Sources W₀' Xi' Tr') (s : Site)
    (hsite : s ∈ lookSites Zp) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (hhalf : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((fastFill (Rc := Rc') src).jobs s).asked wit s.at_))
    (hfits : siteFits cF.blocksInOrder s = true)
    (hshape : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true)
    (hused : (!s.digits || s.caller == .head ||
      usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes)
    (hp : ∀ m t, j ≠ Item.pin m t) : ExchangeAt (LH).thread (borderOf s.link s.digits) j := by
  obtain ⟨lot, R⟩ := rest_of_rest' h H.first s hsite _ wit
    (SiteRestThin.rest h ⟨hhalf, hfits, face_ok_site Zp s hsite, hshape, hused⟩ hsite)
  exact exchangeAt_headDigits_owed h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R
    hH hd hsub hx hRun hj hp

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The same without the field shapeIs**, which on the digits is true by computation. -/
theorem exchangeAt_headDigits_thinner (src : Sources W₀' Xi' Tr') (s : Site)
    (hsite : s ∈ lookSites Zp) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (hhalf : H.first.find? (fun g => g.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((fastFill (Rc := Rc') src).jobs s).asked wit s.at_))
    (hfits : siteFits cF.blocksInOrder s = true)
    (hused : (!s.digits || s.caller == .head ||
      usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (hj : j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes)
    (hp : ∀ m t, j ≠ Item.pin m t) : ExchangeAt (LH).thread (borderOf s.link s.digits) j :=
  exchangeAt_headDigits_thin h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite wit hhalf hfits
    (by rw [hd]; rfl) hused hH hd hsub hx hRun hj hp

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits_owed
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits_off
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits_plan
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits_thin
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_headDigits_thinner
