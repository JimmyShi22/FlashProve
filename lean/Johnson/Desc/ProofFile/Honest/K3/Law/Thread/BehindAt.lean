-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindAt.lean: the honest side of the kind "lookup"
(K3): THE DEBT `Behind` (Honest/Thread/Pays.lean) AT THE DESCRIPTION'S OWN MEMBER AT A LOOKUP'S
PLACE, AT THE FRAME'S OWN NAME: from the thread in front and the member's accepting step: behind it
the clause on the form holds, the letter "rides" holds, and the step has left what the letter
"keeps" names. One theorem for the lookup on the digits, one for the lookup on the calls. Theorems;
one definition.

  `AtStep`              "at every accepting step of the member number b": the form in which a
                        premise on the state behind is asked
  `digits_sameBut`      at the digits' address, from an accept of the decision: `SameBut`, with no
                        premise on the place's parameters
  `reach_thr`, `reach_atStep`   where the thread stands, the state is reached in the library's own
                        sense: so the premise hr below is PAID at that laying of the letter "Reach"
  `site_step`           at a site, from the member's step: the stated sub-protocol, its test on the
                        plan, its own accepting step, no mark behind, the place's link and sort
  `sameBut_site`        **at a site of either sort: the two states are the same but for what the
                        lookup lays**
  `behind_site_digitsK`, `behind_site_callsK`   **the debt**

THE THREE CONJUNCTS, AND WHO PAYS.
  the form    BehindSite.lean's `form_site_digits`, BehindSiteCalls.lean's `form_site_callsR`
  "rides"     hRidesOf: where the letter holds in front and the two states stand in the lookups'
              own clause of "keeps" (below), it holds one border on: A PREMISE ON THE LETTER: owed
              by whoever lays that letter: it must say nothing that a lookup's step turns
  "keeps"     hKeepOf: THE LOOKUPS' OWN CLAUSE (K3Keeps.lean: `K3KeepsCalls`, `K3KeepsDigits`,
              `K3KeepsHead`: an equation in the state's own fields, stronger than `SameBut`) gives
              the letter at this number: A PREMISE ON THE LETTER. The clause itself is PAID at every
              accepting step of the member: `keepsAt_calls`, `keepsAt_digits`, `keepsAt_head`. The
              debt `RidesPast` (RidesPast.lean) asks that the letter gives `SameBut`: the clauses
              do (K3Keeps.lean). An elder text of this file asked that `SameBut` gives the letter:
              FALSE at a letter that is laid as these clauses

WHAT STAYS BESIDE THE TWO. The description's return; `SiteAt`; at the digits `HeadReturns`; the
premises on public data and on the promise's meaning of the two theorems on the form. Those among
them that speak of the state behind are asked at every accepting step (`AtStep`): at the digits
the item "formsIn … objects" (the lookups' own part of it: BehindObjects.lean), the other public
items, what they say beside their Bool. At the calls: OTHER LAYERS' ITEMS THAT ARE CARRIED PAST
(bPub, bPubP), at the value that is handed to the chain at such a step: NOT PAID HERE. Since this
was written: at the frame's letters `lettersAt`, under the head, bPubP is shown at every state
(`bPubP_at`, FormRestAtHeadFill.lean [not in this library]); of bPub: the library has
`othersPub_att_mgAll`, `othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and
`head_bPub_mgAll` (K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the same
of two states, each under hypotheses of its own; no file of this folder calls them for the field.
That the letter "Reach" holds of the state in front (hr): PAID BY
`reach_atStep` where the letter is laid as the library's own `Reach` over the letters' flat list and
first state; the library's condition at the proof file speaks of another list (each member under its
"below") and of the public part besides: NOT JOINED HERE. Since: BehindSaid.lean lays the letter as
`ReachB` and pays it from the thread with `SaidOk` beside it (`reach_thrS`, `behindS_site_callsK`):
the list is joined there; "the public part is an instance's" is not. THE CALLS' HALF GOES OVER THE
SECOND FORM OF THE LIBRARY'S RULE: no `K3AtLive` (BehindLettersR.lean's head says why).

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

Limits. CONDITIONAL ON all of these. No instance of these hypotheses is exhibited in this file.
Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindSiteCalls
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (pieceAt theStated Readers quietAt)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit pubFit
  pubStep pubRowM pubOfItems stepOpen)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles (K3At K3Letters InOrderReads HeldReads SameBut paidCallsR
        digTableB k3Like theStated_yes_digits k3_digits_sameBut headClaim_sameBut putFork_sameBut)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **CONDITIONAL ON an accept of the decision (no instance of it is exhibited in this file): at
the digits' address the two states are the same but for what the lookup lays.** B': any structure
Block that narrows B. No premise on the place's parameters. -/
theorem digits_sameBut {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (B B' : Block FS Cl) (h : theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (hN : B'.Narrows B) (i : Nat) (hi : a.link = some i)
    (hpc : a.piece = pieceAt X i true) (s t : FS) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (hd : B'.decide s rs cols = .ok t) :
    SameBut s t := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s t _ cols
      (hN.2 _ _ _ _ hd)
  have hS := k3_digits_sameBut claim a.piece laid sent P' [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, ho, e⟩ := VerifiableInference.Desc.K3.quietHead_ok X s' t hfs
      rw [e]
      exact hS.trans (headClaim_sameBut s' ah c ha ho)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, hF, -, e⟩ := VerifiableInference.Desc.K3.quietDigits_ok _ _ s' t hfs
         exact hS.trans (e ▸ putFork_sameBut s' F _ hF))

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **"At every accepting step of the member number b"**: φ: of what is handed to the chain, the
state in front and the state behind. -/
def AtStep (b : Nat) (φ : Pp → FS → FS → Prop) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo)
    (cols : List OpenedColumn) (st' : FS), Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
    L.thread.Stepped blk k st m E ds y cols st' → φ (L.pubOf m.st.input.x) st st'

variable {L}

/-- **Where the thread stands, the verifier's state is reached in the library's own sense**
(`Reach`, Johnson/Top/H0/Walk/Reach.lean), over the letters' own flat list and first state. By the
frame's `reach_of_made` (Honest/Thread/MadeLaw.lean). CONDITIONAL ON the thread. -/
theorem reach_thr {b : Nat} (hb : b ≤ L.bs.length) {k : Coins Bk} {st : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k st m E) :
    Johnson.Desc.First.Walk.Tied.Reach 0 L.bs L.first b (L.pubOf m.st.input.x, st) :=
  reach_of_made L.thread L.first (L.pubOf m.st.input.x) hb (fun _ h => h) hA.2.2.2.2.1

/-- The premise hr of `behind_site_callsK`, at the letter "Reach" laid as the library's own. -/
theorem reach_atStep {Str : Type} (b : Nat) (hb : b ≤ L.bs.length) (y₀ : Str) :
    AtStep L b fun z t _ =>
      (fun (z : Pp) (u : FS × Str) => Johnson.Desc.First.Walk.Tied.Reach 0 L.bs L.first b (z, u.1))
        z (t, y₀) :=
  fun _ _ _ _ _ _ _ _ _ _ hA _ _ => reach_thr hb hA

/-- **At a site, from the member's step.** CONDITIONAL ON the description's return, `SiteAt` and the
frame's sentence on the step. No instance of these hypotheses is exhibited in this file. -/
theorem site_step (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk} {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hSt : L.thread.Stepped blk k st m E ds y cols st') :
    theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape s.at_.place =
        some lot ∧ lot.planOk = true ∧
      lot.step L.thread.ft st (roundsOf y.1) cols = .ok (st', cols.length) ∧ st'.failed = none ∧
      s.at_.place.link = some s.link ∧ s.at_.place.piece = pieceAt Z.p.X s.link s.digits ∧
      y.2.st.input = m.st.input := by
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  have hpl := hS.place blk hb
  have hB := lot_stated_at Z Bs.G₀ lot hS.inLot
  rw [hS.lotPlace] at hB
  have hOk := lot_planOk o pol lay KL Fd Z Bs base ch A B O lot blk hS.inLot hmem hpl
    (hS.plan blk hb)
  obtain ⟨_, _, _, _, hiff⟩ :=
    memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hS.inLot blk hmem hpl
  obtain ⟨hst, hf, _⟩ := (hiff _ _ _ _ _ _).1 hSt.2
  obtain ⟨hi, hpc⟩ := place_link Z s hS.site
  obtain ⟨⟨l, _, hy⟩, _⟩ := hSt.1
  exact ⟨hB, hOk, hst, hf, hi, hpc, (play_mid _ _ _ _ _ hy).1⟩

/-- **At a site of either sort the two states around the member's accepting step are the same but
for what the lookup lays.** CONDITIONAL ON the description's return, `SiteAt` and the frame's
sentence on the step. No instance of these hypotheses is exhibited in this file. -/
theorem sameBut_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk} {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hSt : L.thread.Stepped blk k st m E ds y cols st') : SameBut st st' := by
  obtain ⟨hB, hOk, hst, _, hi, hpc, _⟩ := site_step o pol lay KL Fd base A B O hS hb hSt
  obtain ⟨gs, hd⟩ := step_decide_at lot _ st st' _ _ cols hst
  cases hdg : s.digits with
  | true =>
    rw [hdg] at hpc
    exact digits_sameBut _ _ _ _ _ _ lot lot hB hOk (narrows_self lot) s.link hi hpc st st' _ gs hd
  | false =>
    rw [hdg] at hpc
    exact calls_sameBut _ _ _ _ _ _ lot lot hB hOk (narrows_self lot) s.link hi hpc st st' _ gs hd

/-- **The lookups' clause of the letter "keeps" at every accepting step of the member, at a lookup
on the calls** (K3Keeps.lean). CONDITIONAL ON the description's return and `SiteAt`. No instance of
these hypotheses is exhibited in this file. -/
theorem keepsAt_calls (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = false) : AtStep L b fun _ t t' => K3KeepsCalls s.shape t t' := by
  intro blk hb k st m E ds y cols st' _ _ hSt
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  exact k3Keeps_calls o pol lay KL Fd Z Bs base ch A B O s hS.site hdg lot blk hS.inLot hS.lotPlace
    hmem (hS.place blk hb) (hS.plan blk hb) _ st st' _ _ _ hSt.2

/-- The same at a lookup on the digits of a layers' or an attention link. CONDITIONAL ON the same
and on what stands behind the lookup there. No instance of these hypotheses is exhibited in this
file. -/
theorem keepsAt_digits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (VerifiableInference.Desc.K3.quietDigits used claims)) :
    AtStep L b fun _ t t' => K3KeepsDigits s.shape claims t t' := by
  intro blk hb k st m E ds y cols st' _ _ hSt
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  exact k3Keeps_digits o pol lay KL Fd Z Bs base ch A B O s hS.site hdg lot blk hS.inLot
    hS.lotPlace hmem (hS.place blk hb) (hS.plan blk hb) used claims hq _ st st' _ _ _ hSt.2

/-- The same at the head's lookup on the digits. CONDITIONAL ON the like. No instance of these
hypotheses is exhibited in this file. -/
theorem keepsAt_head (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (VerifiableInference.Desc.K3.quietHead Z.p.X)) :
    AtStep L b fun _ t t' => K3KeepsHead s.shape t t' := by
  intro blk hb k st m E ds y cols st' _ _ hSt
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  exact k3Keeps_head o pol lay KL Fd Z Bs base ch A B O s hS.site hdg lot blk hS.inLot hS.lotPlace
    hmem (hS.place blk hb) (hS.plan blk hb) hq _ st st' _ _ _ hSt.2

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
the debt `Behind` at the description's own member at a lookup on the digits.** Kp: the lookups'
clause of the letter "keeps" at this member: `K3KeepsDigits` or `K3KeepsHead`; hPay is paid by
`keepsAt_digits`, `keepsAt_head`. -/
theorem behind_site_digitsK (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hH : HeadReturns L b Z s) (hdg : s.digits = true) {Kp : FS → FS → Prop}
    (hPay : AtStep L b fun _ t t' => Kp t t') (hKeepOf : ∀ t t', Kp t t' → L.keeps b t t')
    (hRidesOf : ∀ w t t', L.rides b w t → Kp t t' → L.rides (b + 1) w t')
    (hIO : InOrderReads L.MgP) (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) (a' : Place)
    (hk : L.ps[b]? = some s.at_.place) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links s.at_.place a' = true) (sub : ModelPart)
    (hsub : L.links[s.link]? = some sub) (hpcT : s.at_.place.piece = 7 + shift sub)
    (hTab : digTableB L.MgP.more L.links L.ps b s.at_.place s.link (shift sub) = true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt Z.p.X s.link true = some x)
    (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true) (hn : told[b]? = some [])
    (hObj : AtStep L b fun z _ t' =>
      L.mgP.pub (.formsIn s.link (7 + shift sub) "objects") (z, t') = true)
    (hRest : AtStep L b fun z _ t' =>
      ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.mgP.more L.links s.at_.place) ++
        pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
          (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
      k3Like r = false → r ≠ .formsIn s.link (7 + shift sub) "objects" →
        L.mgP.pub r (z, t') = true)
    (othersP : AtStep L b fun z _ t' =>
      ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links s.at_.place),
      (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (z, t')) :
    ProofFile.Honest.Behind L.thread b := by
  intro blk hb k st m E ds y cols st' hA hd hSt
  have hb' : L.bs[b]? = some blk := hb
  have hK := hPay blk hb' k st m E ds y cols st' hA hd hSt
  obtain ⟨_, _, _, _, _, _, hm⟩ := site_step o pol lay KL Fd base A B O hS hb' hSt
  refine ⟨form_site_digits L o pol lay KL Fd base A B O hS hH hdg hb' hA hd hSt hIO hHe Fr y₀ a' hk
    hk1 hfitS sub hsub hpcT hTab hlook told hbf hn (hObj blk hb' k st m E ds y cols st' hA hd hSt)
    (hRest blk hb' k st m E ds y cols st' hA hd hSt)
    (othersP blk hb' k st m E ds y cols st' hA hd hSt), ?_,
    hKeepOf st st' hK⟩
  show L.rides (b + 1) y.2.st.input st'
  rw [hm]
  exact hRidesOf _ st st' hA.2.2.2.2.2.1 hK

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
the debt `Behind` at the description's own member at a lookup on the calls.** -/
theorem behind_site_callsK (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = false) (hKeepOf : ∀ t t', K3KeepsCalls s.shape t t' → L.keeps b t t')
    (hRidesOf : ∀ w t t', L.rides b w t → K3KeepsCalls s.shape t t' → L.rides (b + 1) w t')
    (hIO : InOrderReads L.MgP) (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str)
    {Reach : Pp → FS × Fr.E.Str → Prop} (hr : AtStep L b fun z t _ => Reach z (t, y₀))
    (a' : Place)
    (hk : L.ps[b]? = some s.at_.place)
    (hk1 : L.ps[b + 1]? = some a') (hfitS : sameStand L.links s.at_.place a' = true) (sub : ModelPart)
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
    (bPub : AtStep L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → Reach z u → u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place) ++
          pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
            (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
        q ∉ paidCallsR s.link (2 + shift sub) → L.MgP.pub q (z, v.1) = true)
    (bPubP : AtStep L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → Reach z u → u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place),
        q ≠ .left s.link → L.MgP.pubP q (z, v.1)) :
    ProofFile.Honest.Behind L.thread b := by
  intro blk hb k st m E ds y cols st' hA hd hSt
  have hb' : L.bs[b]? = some blk := hb
  have hK := keepsAt_calls o pol lay KL Fd base A B O hS hdg blk hb' k st m E ds y cols st' hA hd
    hSt
  obtain ⟨_, _, _, _, _, _, hm⟩ := site_step o pol lay KL Fd base A B O hS hb' hSt
  refine ⟨form_site_callsR L o pol lay KL Fd base A B O hS hdg hb' hA hd hSt hIO hHe Fr y₀
    (Reach := Reach (L.pubOf m.st.input.x))
    (hr blk hb' k st m E ds y cols st' hA hd hSt) a' hk hk1 hfitS sub hsub hpcT hlook hsx hled
    hfree hns told hbf hn hfit askFresh
    (bPub blk hb' k st m E ds y cols st' hA hd hSt)
    (bPubP blk hb' k st m E ds y cols st' hA hd hSt), ?_,
    hKeepOf st st' hK⟩
  show L.rides (b + 1) y.2.st.input st'
  rw [hm]
  exact hRidesOf _ st st' hA.2.2.2.2.2.1 hK

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.digits_sameBut
#print axioms ProofFile.Honest.K3.Law.AtThr.reach_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.reach_atStep
#print axioms ProofFile.Honest.K3.Law.AtThr.site_step
#print axioms ProofFile.Honest.K3.Law.AtThr.sameBut_site
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsAt_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsAt_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.keepsAt_head
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_site_digitsK
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_site_callsK
