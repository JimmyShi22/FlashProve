-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindSaid.lean: the honest side of the kind "lookup"
(K3): BEHIND THE MEMBER'S ACCEPTING STEP AT A LOOKUP ON THE CALLS, FROM THE THREAD WITH THE
FRAME'S SECOND FAMILY BESIDE IT (`ThrS`, Honest/Thread/Said.lean, at `SaidOk`,
Honest/Thread/SaidOk.lean: "every word that the rounds seen so far show is below the prime"): the
three conjuncts of the debt `Behind`, WITH THE PREMISE "THE STATE IN FRONT IS REACHED" PAID, at
the library's own `Reach` OVER THE LIST ON WHICH THE LIBRARY'S CONDITION AT THE PROOF FILE STANDS:
each member under its "below". Theorems; two definitions.

  `ReachB`       the letter "Reach" of BehindAt.lean's `behind_site_callsK`, laid: the library's
                 `Reach` over the letters' flat list, each member under "below", from the letters'
                 first state
  `reach_thrS`   from `ThrS` at `SaidOk`: by the frame's `reach_below`
  `AtStepS`      BehindAt.lean's `AtStep` with `ThrS` in the stead of `Thr` in its prefix
  `behindS_site_callsK`   **the three conjuncts**: THE FRAME'S OWN `BehindS`
                 (Honest/Thread/PaysS.lean) at the first chain's thread and `SaidOk`: which the
                 chain's rule spends: `playsOn_of_paysS` there

WHY NOT THE FRAME'S `Behind` ITSELF. That debt is asked from `Thr` alone, which says nothing of the
items that the rounds seen so far show; "below" accepts only at rounds whose words are below the
prime. So the premise can be paid from `ThrS` and not from `Thr`.

WHAT THIS JOINS, OF WHAT BehindAt.lean's HEAD NAMES AS NOT JOINED (the list; the public part), AND
OF THE FIRST STATE. The list: joined (where the letters' flat list is the description's). The first
state: the letters' own: at the proof file's letters it is the library's start, by their make: read
off their text, not shown here. "The public part is an instance's": NOT JOINED HERE.

PREMISES BESIDE THOSE OF `behind_site_callsK`. hst: every word of a stored table is below the prime:
the letters'. bPub, bPubP stay: OTHER LAYERS' ITEMS THAT ARE CARRIED PAST, now asked at reached
states alone: NOT PAID HERE. Since this was written: at the frame's letters `lettersAt`, under the
head, bPubP is shown at every state (`bPubP_at`, FormRestAtHeadFill.lean [not in this library; so
here read: not proved in this library]); of bPub: the library has `othersPub_att_mgAll`,
`othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and `head_bPub_mgAll`
(K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the same of two states,
each under hypotheses of its
own; no file of this folder calls them for the field.

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
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindAt
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

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

open VerifiableInference.Desc (fieldPrimeWord)
open VerifiableInference.Desc.Sound (below)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **The letter "Reach", laid**: the library's own, over the letters' flat list, each member under
"below", from the letters' first state. It reads no string. -/
def ReachB {Str : Type} (b : Nat) (z : Pp) (u : FS × Str) : Prop :=
  Johnson.Desc.First.Walk.Tied.Reach 0 (L.bs.map below) L.first b (z, u.1)

/-- "At every accepting step of the member number b, from the thread with `SaidOk` beside it." -/
def AtStepS (b : Nat) (φ : Pp → FS → FS → Prop) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo)
    (cols : List OpenedColumn) (st' : FS), ThrS L.thread SaidOk b k st m E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k st m E ds y cols st' →
    φ (L.pubOf m.st.input.x) st st'

variable {L}

/-- **Where the thread stands with `SaidOk` beside it, the state is reached over the members under
"below".** By the frame's `reach_below`. CONDITIONAL ON that pair and on hst. -/
theorem reach_thrS {Str : Type} {b : Nat} (hb : b ≤ L.bs.length)
    (hst : ∀ w i x u, L.stored w i x = some u → ∀ c ∈ u, c < fieldPrimeWord) {k : Coins Bk} {st : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (h : ThrS L.thread SaidOk b k st m E) {y₀ : Str} :
    ReachB L b (L.pubOf m.st.input.x) (st, y₀) :=
  reach_below L.thread L.first (L.pubOf m.st.input.x) hb (fun _ e => e) hst h

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
the three conjuncts of the debt `Behind` at the description's own member at a lookup on the calls,
from the thread with `SaidOk` beside it; no premise on "reached" is left.** -/
theorem behindS_site_callsK (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hdg : s.digits = false) (hKeepOf : ∀ t t', K3KeepsCalls s.shape t t' → L.keeps b t t')
    (hRidesOf : ∀ w t t', L.rides b w t → K3KeepsCalls s.shape t t' → L.rides (b + 1) w t')
    (hIO : InOrderReads L.MgP) (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str)
    (hst : ∀ w i x u, L.stored w i x = some u → ∀ c ∈ u, c < fieldPrimeWord) (a' : Place)
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
    (bPub : AtStepS L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → ReachB L b z u → u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place) ++
          pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
            (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
        q ∉ paidCallsR s.link (2 + shift sub) → L.MgP.pub q (z, v.1) = true)
    (bPubP : AtStepS L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → ReachB L b z u → u.1.failed = none →
      AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
        v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links s.at_.place),
        q ≠ .left s.link → L.MgP.pubP q (z, v.1)) :
    ProofFile.Honest.BehindS L.thread SaidOk b := by
  intro blk hb k st m E ds y cols st' hAS hd hSt
  have hb' : L.bs[b]? = some blk := hb
  have hA := hAS.1
  have hle : b ≤ L.bs.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb').1
  have hK := keepsAt_calls o pol lay KL Fd base A B O hS hdg blk hb' k st m E ds y cols st' hA hd
    hSt
  obtain ⟨_, _, _, _, _, _, hm⟩ := site_step o pol lay KL Fd base A B O hS hb' hSt
  refine ⟨form_site_callsR L o pol lay KL Fd base A B O hS hdg hb' hA hd hSt hIO hHe Fr y₀
    (Reach := ReachB L b (L.pubOf m.st.input.x)) (reach_thrS hle hst hAS) a' hk hk1 hfitS sub hsub
    hpcT hlook hsx hled
    hfree hns told hbf hn hfit askFresh
    (bPub blk hb' k st m E ds y cols st' hAS hd hSt)
    (bPubP blk hb' k st m E ds y cols st' hAS hd hSt), ?_,
    hKeepOf st st' hK⟩
  show L.rides (b + 1) y.2.st.input st'
  rw [hm]
  exact hRidesOf _ st st' hA.2.2.2.2.2.1 hK


end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.reach_thrS
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_site_callsK
