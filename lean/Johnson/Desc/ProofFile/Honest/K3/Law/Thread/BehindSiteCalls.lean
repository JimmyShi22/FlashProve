-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindSiteCalls.lean: the honest side of the kind
"lookup" (K3): BEHIND THE MEMBER'S ACCEPTING STEP AT A LOOKUP ON THE CALLS, THE THREAD'S CLAUSE ON
THE FORM HOLDS ONE BORDER ON. The twin of BehindSite.lean (the lookup on the digits). From the
premises on the place (`SiteAt`) and the frame's own sentence on a step (`Stepped`) to
`Form (b + 1)`. Theorems.

  `headReturns_calls`   the premise on the head's digits is empty at a lookup on the calls
  `calls_onOut`         the library's promise behind an accept of the stated sub-protocol's step,
                        from its promise in front, at rounds whose words are below the prime
  `form_site_callsR`     **the theorem**

What is laid in, and by what: the stated sub-protocol, its test on the plan, the place's link and
sort (BehindSite.lean's lemmas); its accepting step and "no mark behind", from the member's
(Honest/K3/Law/MemberAtSite.lean); the library's promise in front, from the thread (SiteThr.lean);
its promise behind (the library's `k3_calls_lookOut`); that the played rounds' words are below the
prime (OkPlayed.lean); the input unturned (Accepted.lean).

`SiteAt` has the field half: the list of halves holds, at the site's place, the elder row `proverSideOfLookupInChainAtOneOwner`
at these summands. Who pays the field, each at the fast summands and under hypotheses on the list:
where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean
[not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it
holds a lot with the halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like`
(HalfOfLotLike.lean [not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. CONDITIONAL ON the description's return; `SiteAt`; the thread in front; the frame's sentence
on the step; and the premises on public data and on the promise's meaning that
BehindCallsStep.lean's theorem lists, which are handed through: among them OTHER LAYERS' ITEMS THAT
ARE CARRIED PAST THE SUB-PROTOCOL (bPub, bPubP), and that the letter "Reach" holds of the state in
front (hr): NOT PAID HERE. Since this was written: at the frame's letters `lettersAt`, under the
head, bPubP is shown at every state (`bPubP_at`, FormRestAtHeadFill.lean [not in this library; so
here read: not proved in this library]); of bPub: the library has `othersPub_att_mgAll`,
`othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and `head_bPub_mgAll`
(K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the same of two states,
each under hypotheses of its
own; no file of this folder calls them for the field. hr: paid from
the thread with `SaidOk` beside it in BehindSaid.lean (`reach_thrS`). OVER THE SECOND FORM OF THE
LIBRARY'S RULE: no `K3AtLive` (BehindLettersR.lean's head says why). No instance of these hypotheses
is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.First.Look.K3CallsLookOut
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindCallsStep
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OkPlayed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (pieceAt theStated Readers k3OnIn k3OnOut)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit pubFit
  pubStep pubRowM pubOfItems stepOpen)
open VerifiableInference.Desc.First.Look (P Sent lookAt placeAt)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles (K3At K3Letters InOrderReads HeldReads SameBut paidCallsR
        okRoundsE k3_calls_lookOut)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The library's promise behind an accept of the stated sub-protocol's step at the calls'
address**, from its promise in front. CONDITIONAL ON that accept, at rounds whose words are below
the prime. No instance of these hypotheses is exhibited in this file. -/
theorem calls_onOut {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (B : Block FS Cl) (h : theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (i : Nat) (hi : a.link = some i) (hpc : a.piece = pieceAt X i false)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt X i false = some x)
    {hs : OnBytes.Model.Forest.Shape}
    (hsh : (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x).shape = some hs) (ft : Nat)
    (s t : FS) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hst : B.step ft s rs cols = .ok (t, k)) (hw : okRoundsE rs = true)
    (hIn : k3OnIn (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x) s = true) :
    k3OnOut (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x) t = true := by
  obtain ⟨_, P', sent, laid, rs', gs', hP, hw', hyes⟩ :=
    step_calls claim readers X codes shape a B h hOk i hi hpc ft s t k rs cols hst hw
  have eP : P' = P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  exact k3_calls_lookOut claim a.piece laid sent _ [] hsh rfl s t rs' gs' hw' hyes hIn

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- The premise on the head's digits is empty at a lookup on the calls. -/
theorem headReturns_calls (b : Nat) (Z : Pub) (s : Site) (hdg : s.digits = false) :
    HeadReturns L b Z s := by
  intro h1
  rw [hdg] at h1
  cases h1

/-- **Behind the member's accepting step at a lookup on the calls the thread's clause on the form
holds one border on.** CONDITIONAL ON what this file's head lists. No instance of these hypotheses
is exhibited in this file. -/
theorem form_site_callsR (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = false) {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk}
    {st st' : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hA : Thr L.thread b k st m E) (hd : drawsFit blk.rounds ds = true)
    (hSt : L.thread.Stepped blk k st m E ds y cols st') (hIO : InOrderReads L.MgP)
    (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) {Reach : FS × Fr.E.Str → Prop}
    (hr : Reach (st, y₀)) (a' : Place)
    (hk : L.ps[b]? = some s.at_.place) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links s.at_.place a' = true) (sub : ModelPart)
    (hsub : L.links[s.link]? = some sub) (hpcT : s.at_.place.piece = 2 + shift sub)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt Z.p.X s.link false = some x)
    (hsx : (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x).shape = some x.fs)
    {nsOf : Nat → Option Nat}
    (hled : ∀ j u, L.MgP.pub (.ledger j) u = VerifiableInference.Desc.First.ledgerB u.2)
    (hfree : ∀ j u, L.MgP.pub (.freeAbove j) u =
      (nsOf j).any fun n => VerifiableInference.Desc.First.freeAboveB n u.2)
    (hns : nsOf s.link = some (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x).ns)
    (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true) (hn : told[b]? = some [])
    (hfit : pubFit L.MgP.more L.links L.ps = true)
    (askFresh : VerifiableInference.Desc.First.Pub.linkFresh s.link ∈
      (pubSets L.MgP.more L.links L.ps)[b]?.getD [])
    (bPub : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place) ++
          pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
            (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
        q ∉ paidCallsR s.link (2 + shift sub) → L.MgP.pub q (L.pubOf m.st.input.x, v.1) = true)
    (bPubP : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place),
        q ≠ .left s.link → L.MgP.pubP q (L.pubOf m.st.input.x, v.1)) :
    L.thread.Form (b + 1) k st' y.2 := by
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  have hpl := hS.place blk hb
  -- the input stays
  obtain ⟨_, hy2, _⟩ :=
    stepped_look (seated_site hS)
      (joins_site o pol lay KL Fd base A B O hS (headReturns_calls L b Z s hdg)) hb hA hd hSt
  have hm : y.2.st.input = m.st.input := by rw [hy2]
  -- the lookups' own sub-protocol: stated; its test on the plan; its accepting step; no mark
  have hB := lot_stated_at Z Bs.G₀ lot hS.inLot
  rw [hS.lotPlace] at hB
  have hOk := lot_planOk o pol lay KL Fd Z Bs base ch A B O lot blk hS.inLot hmem hpl
    (hS.plan blk hb)
  obtain ⟨_, _, _, _, hiff⟩ :=
    memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hS.inLot blk hmem hpl
  obtain ⟨hst, hf, _⟩ := (hiff _ _ _ _ _ _).1 hSt.2
  -- the place; the promise in front and behind; the rounds' words
  obtain ⟨hi, hpc⟩ := place_link Z s hS.site
  rw [hdg] at hpc
  have hq := hS.lookIn
  rw [hdg] at hq
  have hOnIn := onIn_thr L hS.k3At (placeAt_of_look hlook) hq hA
  have hw := okRounds_moved L.thread hSt.1 hd
  have hout := calls_onOut K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape
    s.at_.place lot hB hOk s.link hi hpc hlook hsx _ _ _ _ _ _ hst hw hOnIn
  exact form_calls_stepR L hS.k3At Fr y₀ K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.first.codes
    Z.first.shape s.at_.place a' lot hB hOk hk hk1 hfitS s.link hi sub hsub hpcT hpc hlook hsx hled
    hfree hns hIO hHe told hbf hn hfit askFresh hA hr hm _ _ _ _ hst hw hout hf bPub bPubP

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.calls_onOut
#print axioms ProofFile.Honest.K3.Law.AtThr.headReturns_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.form_site_callsR
