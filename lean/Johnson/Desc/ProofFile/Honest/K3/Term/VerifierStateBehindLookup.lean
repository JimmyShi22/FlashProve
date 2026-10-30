-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: general in the prover H and the Script Q, at the head's letters; no Script is laid.
Johnson/Desc/ProofFile/Honest/K3/Term/VerifierStateBehindLookup.lean: the honest side of the kind
"lookup" (K3): the verifier's state that a lookup's member leaves, read from `ThrS` and the member's
step alone, under the head `P5J.AtMgA`.

Why. The bundles `DigitsRunFactsFromSaid` (DigitsExchangeFromSaid.lean here) and `CallsRunAll`
(Honest/K3/Law/Thread/ExchangeCallsAll.lean) ask twelve clauses at every step on the thread. Six of
them, a segment is open, the readers' two answers, the two public tests and the mask row's message,
speak of the state that the member leaves and of nothing else: no prover, Script or book is read.
This file pays those six, and the public test `planesOk` that the calls' top asks.

  `factsInFrontOfMember`              in front of a member: no mark, the reach, the six Bools
  `maskNumberOfSeat`                  the mask row's message and its seat, out of `maskSeat`
  `verifierStateBehindDigitsAtLink`   the six at a link, at the digits, from `SaidOk`
  `verifierStateBehindCallsAtPlace`   the six at a link and its place, at the calls, from `SaidOk`
  `verifierStateBehindCallsAtLink`    the same at a link, the place by sort
  `verifierStateBehindDigitsLookup`   at a site, from every Said stronger than `SaidOk`
  `verifierStateBehindCallsLookup`    the same on the calls
  `planesOkAtCallsSites`              the packing's test at every site on the calls

Limits. Conditional on the head, `ThrS` and the member's step: where no thread stands these say
nothing, and no state is shown here at which `ThrS` holds. Said must imply `SaidOk`: that the term's
Said does is not shown here. The six clauses alone: the two tests on the book, the sender's law and
the clause on the witness are not touched. The elder row. The full size alone. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.MadeOwedDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.MadeOwedCallsHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.NoMarkBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTable
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono
import Johnson.Top.H.Keep.FormsInTObjects
import Johnson.Desc.Sound.MgAt.K3DigitsObjInFits
import Johnson.HB.LLHARD.Q38E.DigAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift bookAt)
open VerifiableInference.Desc.K9 (segAt? formsIn formsInT maskSeat maskAt seatAt Read)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (lettersHead Script WtF thrS_reach_below xk_of_form)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Law.Exchange
open ProofFile.Honest.K3.Law.Total
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Desc.Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
set_option quotPrecheck false in
local notation "LH" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w
local notation "baseP" => Desc.First.Meaning.pub (mgBase : Desc.First.Meaning ProofFile.InstPub
  (Desc.Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
set_option quotPrecheck false in
local notation "EP" => fun (z : ProofFile.InstPub) (k : ℕ) (s : TS) =>
  Desc.First.ePubAt (mgAtAll h).pub (mgAtAll h).more At.links At.ps k (z, s)

/-- What a border hands every law below: no mark, the reach under "below", the five tests. -/
theorem factsInFrontOfMember {b : Nat} {k : Coins Bk} {st : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hle : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (LH).thread SaidOk b k st m E) :
    st.failed = none ∧
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) b (m.st.input.x.pub, st) ∧
      IM.XK (At.N Zp cF) IM.linksW IM.placesW
        (LPFK9.HandsAt.EW (𝔐).pubD baseP m.st.input.x.pub) b st = true := by
  have hF : (LH).thread.Form b k st m := hT.1.2.2.1
  have h0 : st.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hq : IM.XK (At.N Zp cF) At.links At.ps
      (P1K2.EQ (mgAtAll h) At.links At.ps m.st.input.x.pub) b st = true := xk_of_form (LH) hF
  obtain ⟨hx, -⟩ := xk_ep_of_eq _ _ _ _ m.st.input.x.pub _ st hq
  have hx' : IM.XK (At.N Zp cF) At.links At.ps (EP m.st.input.x.pub) b st = true := hx
  rw [ep_is_ew h, ← linksW_at, ← placesW_at] at hx'
  exact ⟨h0, thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w hle hT, hx'⟩

/-- Clause 10 out of the seat: the mask row's message has a number, and a seat among own. -/
theorem maskNumberOfSeat {own : List (ℕ × ℕ)} {c : Desc.K9.Part}
    (hm : (maskSeat own c).isSome = true) :
    ∃ o x, maskOracle c.L.check.frame = some o ∧ seatAt own c.d.book o = some x := by
  unfold maskSeat at hm
  cases e : maskAt c.L.check.frame with
  | none => rw [e] at hm; cases hm
  | some o =>
    rw [e] at hm
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hm
    exact ⟨o, x, (maskAt_eq _).symm.trans e, hx⟩

set_option maxHeartbeats 4000000 in
/-- **BEHIND THE MEMBER AT A LOOKUP ON THE DIGITS**: clauses 3, 4, 5, 6, 7, 10 of DigitsRunAll, at
every link. Conditional on the head, the pair in front and the member's step. -/
theorem verifierStateBehindDigitsAtLink {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l true]? = some blk) {k : Coins Bk} {st st' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (LH).thread SaidOk (k3K l true) k st m E)
    (hSt : (LH).thread.Stepped blk k st m E ds y cols st') :
    ∃ (a : Desc.K9.Part) (o : ℕ), segAt? st' = some a ∧
      (∀ g', (Desc.K3.seatDigits K3Lot.ofForm).heard st' = some g' →
        (h.𝔇.Rd l).forms (6 + shift sub) "objects" st' =
          some { forms := g'.rows.toList, late := [] }) ∧
      (h.𝔇.Rd l).forms (6 + shift sub) "guests" st' = some { forms := [], late := [] } ∧
      formsIn (h.𝔇.Rd l) (h.𝔇.N.group l) (6 + shift sub) "objects" st' = true ∧
      formsIn (h.𝔇.Rd l) (h.𝔇.N.group l) (6 + shift sub) "guests" st' = true ∧
      maskOracle a.L.check.frame = some o ∧ ∃ x, seatAt (h.𝔇.N.group l) a.d.book o = some x := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h0, hR, hx⟩ := factsInFrontOfMember h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  set z := m.st.input.x.pub
  have hy : IM.Yes 0 blk st st' := ⟨_, _, _, hSt.2⟩
  obtain ⟨b', rs, gs, hat, hOk, hd⟩ := digits_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hat
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, st) = true :=
    front_of_xk _ _ _ z (k3K l true) st hx
  have hshape : Desc.First.shapeAt linksFull PS[k3K l true]? st = true := by
    have h1 := (IM.xk_parts hx).1
    rw [IM.linksW_full, IM.placesW_full] at h1
    exact h1
  have hbook : bookAt (𝔐).N PS[k3K l true]? st = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  obtain ⟨hpc, x, hlook, hIn, F, hF, hSz⟩ := dig_front h hl hsub hat z hfront
  obtain ⟨lk, hlk, -, -, hO6, hG6⟩ := P5J.k03_finds_dig h hl hsub
  -- SameBut: as in objectsNew_dig_at
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have T := (k3_digits_step_turns K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat hOk l rfl hpc hlook hsh st st' rs gs
    hd).1
  have hMask := mask_behind_dig h hl hlook T z hR h0 hF hbook
  obtain ⟨G, g, hG, hg, hNm, hSzG⟩ := digits_behind_named K3Lot.ofForm (K3Lot.readersAt (At.X Zp))
    (At.X Zp) Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat hOk l rfl hpc st st' rs gs hd
    hF hSz
  have hMerge := k3_digits_step_hmerge K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hat hOk l rfl hpc st st' rs gs hd hF hSz
    (fits_dig_at h hl hsub z hshape hR)
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hG
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hG (tl_some_of_fork hG)
  obtain ⟨o, xs, ho, hseat⟩ := maskNumberOfSeat (hMask c hc)
  have hRd : h.𝔇.Rd l = _ := rd_holesAt (𝔐) hlk
  have hFO : ∃ nm run, (Desc.K9.statesOfLink lk (6 + shift sub)).find? (fun r => r.1 == "objects") =
      some (nm, run) ∧ RunOver passR run (objectsRun (Desc.K3.seatDigits K3Lot.ofForm)) :=
    ⟨_, _, hO6, fun _ _ _ hr _ => hr⟩
  have hFG : ∃ nm run, (Desc.K9.statesOfLink lk (6 + shift sub)).find? (fun r => r.1 == "guests") =
      some (nm, run) ∧ RunOver passR run
        (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))) :=
    ⟨_, _, hG6, fun _ _ _ hr _ => hr⟩
  refine ⟨c, o, hc, fun g' hg' => ?_, ?_, ?_, ?_, ho, xs, hseat⟩
  · obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
    rw [hRd]
    exact VerifiableInference.OnPublicFiles.link_answers _ lk _ (by decide) (objects_answers _ atS2_ofForm passR k03_hpass hFO hG hg
            fun f hf => (hNm f hf).1)
  · rw [hRd]
    exact VerifiableInference.OnPublicFiles.link_answers _ lk _ (by decide) (guests_answers passR k03_hsame hFG hG)
  · rw [hRd]
    exact objects_formsIn _ lk _ _ _ atS2_ofForm passR k03_hpass hFO hc hg
      (by rw [hcF]; exact hNm) (by rw [hcF]; exact hSzG) (hMask c hc) (hMerge g hg)
  · rw [hRd]
    exact guests_formsIn _ lk _ _ passR k03_hsame hFG hc

set_option quotPrecheck false in
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false

set_option maxHeartbeats 4000000 in
/-- **BEHIND THE MEMBER AT A LOOKUP ON THE CALLS, AT ITS PLACE y.** -/
theorem verifierStateBehindCallsAtPlace {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (hsP : (theP y).shape = some y.fs)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[k3K l false]? = some blk) {k : Coins Bk} {st st' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {yy : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (LH).thread SaidOk (k3K l false) k st m E)
    (hSt : (LH).thread.Stepped blk k st m E ds yy cols st') :
    ∃ (a : Desc.K9.Part) (o : ℕ), segAt? st' = some a ∧
      (∀ g', (Desc.K3.seatCalls K3Lot.ofForm).heard st' = some g' →
        (h.𝔇.Rd l).forms (1 + shift sub) "objects" st' =
          some { forms := g'.rows.toList, late := [] }) ∧
      (h.𝔇.Rd l).forms (1 + shift sub) "guests" st' = some { forms := [], late := [] } ∧
      formsInT (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (1 + shift sub) "objects" st' = true ∧
      formsInT (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (1 + shift sub) "guests" st' = true ∧
      maskOracle a.L.check.frame = some o ∧ ∃ x, seatAt (h.𝔇.N.sent l 0) a.d.book o = some x := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h0, hR, hx⟩ := factsInFrontOfMember h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  set z := m.st.input.x.pub
  have hy : IM.Yes 0 blk st st' := ⟨_, _, _, hSt.2⟩
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy
  rw [O.W] at hpcW hP
  have eP : P' = theP y := by
    have e0 : placeAt (At.X Zp) l false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  obtain ⟨sub', hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hs'.symm.trans hsub)
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, st) = true := by
    rw [← ek]
    exact front_of_xk _ _ _ z (k3K l false) st hx
  have hbook : bookAt (𝔐).N PS[k3K l false]? st = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  have hIn := (front_three (𝔐) mgBase (a := IM.k3Place l false) st rfl hpcW hpc hl hsub
    (calls_tests hl).1 hlook rfl (hfit_mgAll (𝔐) mgBase rfl) z hfront).1
  have hMask := mask_behind_calls h hl hlook _ laid sent [] st st' rs gs hd z hR h0 hfront hbook
  have hMerge : ∀ g, st'.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ t ∈ f.slots.toList,
      Desc.K9.mergeOf st' ≠ some t.1 := by
    rcases Nat.lt_or_ge l 24 with h24 | h24
    · exact merge_behind_calls h h24 _ _ laid sent [] st st' rs gs hd z hR h0
    · obtain rfl : l = 24 := by omega
      exact merge_behind_head h _ _ laid sent [] st st' rs gs hd z hR
  -- the lines of objInT_state (CallsBehindState.lean:399-418)
  obtain ⟨F, F', g, rs', hF, hz, -, -, -, -, hF', hg, Lf, -⟩ :=
    k3_calls_made K3Lot.ofForm _ laid sent (theP y) [] st st' rs gs hsP hd hIn
  obtain ⟨F1, y1, hF1, hn1, e1, hN⟩ :=
    decide_named (Desc.K3.seatCalls K3Lot.ofForm) _ laid sent (theP y) [] st st' rs gs hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls K3Lot.ofForm).fork st).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatCalls K3Lot.ofForm).heard st' = some y1.1 := by
    rw [e1]
    exact Desc.K3.seatCalls_reads K3Lot.ofForm _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatCalls K3Lot.ofForm).fork st' = some y1.2 := by
    rw [e1]
    exact seatCalls_keeps K3Lot.ofForm _ _ _ hsome hn1
  have ey1 : y1.1 = g := Option.some.inj (hg1.symm.trans hg)
  have ey2 : y1.2 = F' := Option.some.inj (hF1'.symm.trans hF')
  have hNm := (hN hz).rows
  rw [ey1, ey2] at hNm
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hF'
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hF' (tl_some_of_fork hF')
  obtain ⟨o, xs, ho, hseat⟩ := maskNumberOfSeat (hMask c hc)
  obtain ⟨lk, hRd, hfind, hfindG⟩ := k03_hfind2 h l hl
  rw [(k03_ix_dig hl hsub).1] at hfind hfindG
  have hRd' : h.𝔇.Rd l = _ := hRd
  refine ⟨c, o, hc, fun g' hg' => ?_, ?_, ?_, ?_, ho, xs, hseat⟩
  · obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
    rw [hRd']
    exact VerifiableInference.OnPublicFiles.link_answers _ lk _ (by decide)
      (objects_answers _ k03_atS2_calls passR k03_hpass hfind (fork_of_segAt hc) hg
        fun f hf => (hNm f hf).1)
  · rw [hRd']
    exact VerifiableInference.OnPublicFiles.link_answers _ lk _ (by decide)
      (guests_answers passR k03_hsame hfindG (fork_of_segAt hc))
  · rw [hRd']
    exact objects_formsInT _ lk _ _ _ k03_atS2_calls passR k03_hpass hfind hc hg
      (by rw [hcF]; exact hNm) (by rw [hcF]; exact Lf.padLeft.fit) (hMask c hc) (hMerge g hg)
  · rw [hRd']
    exact guests_formsInT _ lk _ _ passR k03_hsame hfindG hc

/-- **At a link, on the calls: the place by sort.** The same end as at a place. -/
theorem verifierStateBehindCallsAtLink {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[k3K l false]? = some blk) {k : Coins Bk} {st st' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {yy : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (LH).thread SaidOk (k3K l false) k st m E)
    (hSt : (LH).thread.Stepped blk k st m E ds yy cols st') :
    ∃ (a : Desc.K9.Part) (o : ℕ), segAt? st' = some a ∧
      (∀ g', (Desc.K3.seatCalls K3Lot.ofForm).heard st' = some g' →
        (h.𝔇.Rd l).forms (1 + shift sub) "objects" st' =
          some { forms := g'.rows.toList, late := [] }) ∧
      (h.𝔇.Rd l).forms (1 + shift sub) "guests" st' = some { forms := [], late := [] } ∧
      formsInT (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (1 + shift sub) "objects" st' = true ∧
      formsInT (h.𝔇.Rd l) (h.𝔇.N.sent l 0) (1 + shift sub) "guests" st' = true ∧
      maskOracle a.L.check.frame = some o ∧ ∃ x, seatAt (h.𝔇.N.sent l 0) a.d.book o = some x := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.mod_two_eq_zero_or_one l with he | ho
    · obtain ⟨y, _, hy, -⟩ := layAt_scope h.scope h.reads h.pubOne h24 he
      exact verifierStateBehindCallsAtPlace h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hl hsub
        (k03_look_lay h hl hy) (k03_shape_lay hy) hb hT hSt
    · obtain ⟨y, a, -, -, hy, -⟩ :=
        attAt_scope h.scope h.reads h.pubOne h24 ho (𝔐).sent (fun _ => 0)
      exact verifierStateBehindCallsAtPlace h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hl hsub
        (k03_look_att h hl hy) (attAt_shape hy) hb hT hSt
  · obtain rfl : l = 24 := by omega
    exact verifierStateBehindCallsAtPlace h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hl hsub
      (k03_look_head h) (k03_shape_head h) hb hT hSt

/-- **Behind the member at a lookup on the digits, at a site, at every Said stronger than
`SaidOk`.** Clauses 3, 4, 5, 6, 7 and 10 of `DigitsRunFactsFromSaid`, and the seat of the mask row's
message. Conditional on the head, hSaid, `ThrS` and the member's step. -/
theorem verifierStateBehindDigitsLookup (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = true) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      ∃ (a : Desc.K9.Part) (o : ℕ), segAt? st' = some a ∧
        (∀ g', (ProofFile.Honest.K3.Law.seatOf K3Lot.ofForm s.digits).heard st' = some g' →
          (h.𝔇.Rd s.link).forms (6 + shift sub) "objects" st' =
            some { forms := g'.rows.toList, late := [] }) ∧
        (h.𝔇.Rd s.link).forms (6 + shift sub) "guests" st' = some { forms := [], late := [] } ∧
        formsIn (h.𝔇.Rd s.link) (h.𝔇.N.group s.link) (6 + shift sub) "objects" st' = true ∧
        formsIn (h.𝔇.Rd s.link) (h.𝔇.N.group s.link) (6 + shift sub) "guests" st' = true ∧
        maskOracle a.L.check.frame = some o ∧
        ∃ x, seatAt (h.𝔇.N.group s.link) a.d.book o = some x := by
  intro blk hb k st m En ds y cols st' hT _ hSt
  have hT' := thrS_mono _ hSaid hT
  have hl := link_lt_head h s hsite
  rw [hd] at hb hT' ⊢
  exact verifierStateBehindDigitsAtLink h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hl hsub hb hT' hSt

/-- **Behind the member at a lookup on the calls, at a site, at every Said stronger than `SaidOk`.**
Clauses 3, 4, 5, 6, 7 and 10 of `CallsRunAll` at `CallsRunHead`'s letters, and the seat of the mask
row's message. Conditional on the head, hSaid, `ThrS` and the member's step. -/
theorem verifierStateBehindCallsLookup (s : Site) (hsite : s ∈ lookSites Zp)
    (hd : s.digits = false) {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      ∃ (a : Desc.K9.Part) (o : ℕ), segAt? st' = some a ∧
        (∀ g', (ProofFile.Honest.K3.Law.seatOf K3Lot.ofForm s.digits).heard st' = some g' →
          (h.𝔇.Rd s.link).forms (1 + shift sub) "objects" st' =
            some { forms := g'.rows.toList, late := [] }) ∧
        (h.𝔇.Rd s.link).forms (1 + shift sub) "guests" st' = some { forms := [], late := [] } ∧
        formsInT (h.𝔇.Rd s.link) ((fun i => h.𝔇.N.sent i 0) s.link) (1 + shift sub) "objects" st' =
          true ∧
        formsInT (h.𝔇.Rd s.link) ((fun i => h.𝔇.N.sent i 0) s.link) (1 + shift sub) "guests" st' =
          true ∧
        maskOracle a.L.check.frame = some o ∧
        ∃ x, seatAt ((fun i => h.𝔇.N.sent i 0) s.link) a.d.book o = some x := by
  intro blk hb k st m En ds y cols st' hT _ hSt
  have hT' := thrS_mono _ hSaid hT
  have hl := link_lt_head h s hsite
  rw [hd] at hb hT' ⊢
  exact verifierStateBehindCallsAtLink h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hl hsub hb hT' hSt

include h in
/-- **The packing's test at every site.** Conditional on the head alone; no thread. -/
theorem packingOfPlanesFitsAtSite (s : Site) (hs : s ∈ lookSites Zp) :
    Desc.First.Look.planesOk s.shape s.p.lm = true := by
  cases hd : s.digits with
  | true =>
    obtain ⟨x, tl, hx⟩ := Q38.digAt_at_head h
      (Nat.le_of_lt_succ (ProofFile.Honest.K3.Law.AtThr.link_lt_head h s hs))
    obtain ⟨-, hlm, -⟩ := ProofFile.Honest.K3.Law.Exchange.table_digits Zp s hs hd hx
    rw [hlm]
    simp [Desc.First.Look.planesOk]
  | false =>
    obtain ⟨pl, h1, h2, h3⟩ := ProofFile.Honest.K3.Law.Exchange.site_place Zp s hs
    rw [hd] at h1 h2
    have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
    have hB : 5 ≤ pl.lm ∧ pl.lm ≤ pl.fs.kT + 5 ∧
        (Desc.First.Look.P.ofPlace (Params.settingOf Zp.p.X.P.frame) false pl).shape =
          some pl.fs := by
      by_cases hh : s.link = (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr
      · have e : lookAt Zp.p.X ((if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr) false = some pl :=
          hh ▸ h1
        obtain ⟨b5, bl, -⟩ := planesAtB_iff.1 (head_planes hpub e).2
        exact ⟨b5, bl, head_shape _ hpub e⟩
      · by_cases h0 : s.link % (if Zp.p.X.p4 then 2 else 1) = 0
        · obtain ⟨tl, -, hq⟩ := lay_planes hpub h1 hh h0
          obtain ⟨b5, bl, -⟩ := planesAtB_iff.1 hq
          exact ⟨b5, bl, lay_shape _ hpub h1 hh h0⟩
        · obtain ⟨a, tl, -, -, hq⟩ := att_planes hpub h1 hh h0
          obtain ⟨b5, bl, -⟩ := planesAtB_iff.1 hq
          exact ⟨b5, bl, att_shape _ hpub h1 hh h0⟩
    obtain ⟨b5, bl, hsh⟩ := hB
    rw [h2] at h3
    have e3 : s.shape = pl.fs := Option.some.inj (h3.symm.trans hsh)
    rw [e3, h2]
    show Desc.First.Look.planesOk pl.fs pl.lm = true
    unfold Desc.First.Look.planesOk
    rw [decide_eq_true b5, decide_eq_true bl]
    rfl

include h in
/-- **The packing's test at every site on the calls**, in the form of the top's premise. -/
theorem planesOkAtCallsSites : ∀ s ∈ lookSites Zp, s.digits = false →
    Desc.First.Look.planesOk s.shape s.p.lm = true :=
  fun s hs _ => packingOfPlanesFitsAtSite h s hs

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.factsInFrontOfMember
#print axioms ProofFile.Honest.K3.Term.maskNumberOfSeat
#print axioms ProofFile.Honest.K3.Term.verifierStateBehindDigitsAtLink
#print axioms ProofFile.Honest.K3.Term.verifierStateBehindCallsAtPlace
#print axioms ProofFile.Honest.K3.Term.verifierStateBehindCallsAtLink
#print axioms ProofFile.Honest.K3.Term.verifierStateBehindDigitsLookup
#print axioms ProofFile.Honest.K3.Term.verifierStateBehindCallsLookup
#print axioms ProofFile.Honest.K3.Term.packingOfPlanesFitsAtSite
#print axioms ProofFile.Honest.K3.Term.planesOkAtCallsSites
