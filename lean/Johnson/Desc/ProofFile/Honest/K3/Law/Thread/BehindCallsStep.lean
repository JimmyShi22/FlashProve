-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindCallsStep.lean: the honest side of the kind
"lookup" (K3): behind the sub-protocol of a link's lookup on the calls THE THREAD'S CLAUSE ON THE
FORM HOLDS ONE BORDER ON, with the lookups' own premises laid in. A joining of four files of this
folder: BehindCallsR.lean (`form_callsR`), BehindStep.lean (`step_calls`), BehindLettersR.lean
(`behindPartsR_honest`), OkRounds.lean. Theorems; one definition.

OVER THE SECOND FORM OF THE LIBRARY'S RULE (Johnson/Desc/First/Look/K3CallsBehindR.lean). An elder
text of this file went over the first form and took `K3AtLive` as a premise, which by the library's
own words does not hold at its composed meaning: BehindLettersR.lean's head says why.

  `AcceptsCalls`        the letter "Yes" of the library's rule, laid: the library's own structure
                        Block of the lookup on the calls accepts, at rounds whose words are below
                        the prime
  `form_calls_stepR`     **the clause**, from an accept of the stated sub-protocol's step
  `form_calls_courseR`   the same on a course's rounds: the test on the words is paid by `Fit`

WHAT STAYS AS PREMISES.
  Of the run: the thread in front; that the input stays; an accept of the stated sub-protocol's
    step; no mark of failure behind; the library's promise behind (`k3OnOut`: from the hearing's
    return by `member_in_out`, FrontSite.lean).
  On public data: where the sub-protocol stands; tests on the table and the numbers.
  On the meaning: `K3At` (the lookups' layer's equations); two equations on the ledger's items;
    `InOrderReads`, `HeldReads`: ALL FIVE SEEN TO HOLD AT THE LIBRARY'S COMPOSED MEANING OVER ITS
    BASE MEANING (`mgAll Dm mgBase`): BehindLettersAt.lean [not in this library].
  The letter "Reach" (the library's Rc: meant: "this state is reached from the chain's first state
    by the sub-protocols in front") holds of the state in front: NOT PAID HERE; where the letter is
    laid as `ReachB`: `reach_thrS` (BehindSaid.lean), from the thread with `SaidOk` beside it.
  OTHER LAYERS' ITEMS THAT RIDE PAST THE SUB-PROTOCOL (bPub, bPubP): NOT PAID HERE. Since this was
  written: at the frame's letters `lettersAt`, under the head, bPubP is shown at every state
  (`bPubP_at`, FormRestAtHeadFill.lean [not in this library]); of bPub: the library has
  `othersPub_att_mgAll`, `othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) and
  `head_bPub_mgAll` (K3HeadBehindAt.lean), and Honest/K3/Law/Total/CallsBehindState.lean says the
  same of two states, each under hypotheses of its own; no file of this folder calls them for the
  field.

Limits. No instance of these hypotheses is exhibited in this file. Nothing on soundness,
completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindCallsR
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindStep
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindLettersR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Place Block OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (theStated Readers pieceAt k3OnOut seatCalls)
open VerifiableInference.Desc.First (ModelPart openSets pubSets start sameStand bookFit pubFit pubStep
  pubRowM pubOfItems stepOpen rowOf shift)
open VerifiableInference.Desc.First.Look (P Sent lookAt placeAt)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K3.Law

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The letter "Yes" of the library's rule, laid**: the library's own structure Block of the
lookup on the calls, at the parameters p, accepts from the first state with the second, at rounds
whose words are below the prime. -/
def AcceptsCalls {Cl' : Type} (claim : Aff → Cl') (Fr : Frame) (p : P)
    (u c : FS × Fr.E.Str) : Prop :=
  ∃ (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (guests : List (VerifiableInference.Desc.First.Look.Guest FS Cl')) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))), okRoundsE rs = true ∧
    (VerifiableInference.Desc.K3.block (seatCalls claim) piece laid before p guests).decide u.1 rs
      cols = .ok c.1

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)
  {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

local notation "SET" => OnBytes.Params.settingOf X.P.frame

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
behind the sub-protocol of a link's lookup on the calls the thread's clause on the form holds one
border on.** Fr, y₀: any frame of the library's and any of its strings: the promise reads none. -/
theorem form_calls_stepR (hK : K3At X D Lk L.MgP) (Fr : Frame) (y₀ : Fr.E.Str)
    {Reach : FS × Fr.E.Str → Prop} {Cl' : Type} (claim : Aff → Cl')
    (readers : Nat → Option (Readers FS))
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a a' : Place) (B : Block FS Cl')
    (hB : theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) {b : Nat}
    (hk : L.ps[b]? = some a) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links a a' = true) (i : Nat) (hi : a.link = some i) (sub : ModelPart)
    (hsub : L.links[i]? = some sub) (hpcT : a.piece = 2 + shift sub)
    (hpc : a.piece = pieceAt X i false) {x : VerifiableInference.Desc.First.Look.Place}
    (hlook : lookAt X i false = some x) (hsx : (P.ofPlace SET false x).shape = some x.fs)
    {nsOf : Nat → Option Nat}
    (hled : ∀ j u, L.MgP.pub (.ledger j) u = VerifiableInference.Desc.First.ledgerB u.2)
    (hfree : ∀ j u, L.MgP.pub (.freeAbove j) u =
      (nsOf j).any fun n => VerifiableInference.Desc.First.freeAboveB n u.2)
    (hns : nsOf i = some (P.ofPlace SET false x).ns) (hIn : InOrderReads L.MgP)
    (hHe : HeldReads L.MgP) (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true)
    (hn : told[b]? = some []) (hfit : pubFit L.MgP.more L.links L.ps = true)
    (askFresh : VerifiableInference.Desc.First.Pub.linkFresh i ∈
      (pubSets L.MgP.more L.links L.ps)[b]?.getD []) {k : Coins Bk}
    {s s' : FS} {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k s m E)
    (hr : Reach (s, y₀)) (hm : m'.st.input = m.st.input) (ft n : Nat) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn)
    (hst : B.step ft s rs cols = .ok (s', n)) (hw : okRoundsE rs = true)
    (hout : k3OnOut (P.ofPlace SET false x) s' = true) (hf : s'.failed = none)
    (bPub : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls claim Fr (P.ofPlace SET false x) u v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links a) ++
          pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
            (rowOf L.links a)),
        q ∉ paidCallsR i (2 + shift sub) → L.MgP.pub q (L.pubOf m.st.input.x, v.1) = true)
    (bPubP : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls claim Fr (P.ofPlace SET false x) u v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links a),
        q ≠ .left i → L.MgP.pubP q (L.pubOf m.st.input.x, v.1)) :
    L.thread.Form (b + 1) k s' m' := by
  obtain ⟨hsb, P', sent, laid, rs', gs', hP, hw', hyes⟩ :=
    step_calls claim readers X codes shape a B hB hOk i hi hpc ft s s' n rs cols hst hw
  have eP : P' = P.ofPlace SET false x := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  have hy : AcceptsCalls claim Fr (P.ofPlace SET false x) (s, y₀) (s', y₀) :=
    ⟨a.piece, laid, sent, [], rs', gs', hw', hyes⟩
  have hParts := behindPartsR_honest (Fr := Fr) (N := L.N) (z := L.pubOf m.st.input.x) L.ans L.test
    (AcceptsCalls claim Fr (P.ofPlace SET false x)) Reach hK hled hfree hns hIn hHe hlook
    (hpc.symm.trans hpcT) hk hk1 hi hsub hpcT hfitS hbf hn hfit askFresh bPub bPubP
  exact form_callsR L claim Fr y₀ hsx (fun _ _ h => h) hParts hA hr hm hy hsb hout hf

/-- **CONDITIONAL ON `Fit` AND ON what this file's head lists (no instance of them is exhibited in
this file): the same on a course's rounds**: that their words are below the prime is paid. -/
theorem form_calls_courseR {W : Type} (R : Course W) (xs : List Fmt.RoundView) (hF : Fit R)
    (hx : R.rounds = some xs) (hK : K3At X D Lk L.MgP) (Fr : Frame) (y₀ : Fr.E.Str)
    {Reach : FS × Fr.E.Str → Prop} {Cl' : Type} (claim : Aff → Cl')
    (readers : Nat → Option (Readers FS))
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a a' : Place) (B : Block FS Cl')
    (hB : theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) {b : Nat}
    (hk : L.ps[b]? = some a) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links a a' = true) (i : Nat) (hi : a.link = some i) (sub : ModelPart)
    (hsub : L.links[i]? = some sub) (hpcT : a.piece = 2 + shift sub)
    (hpc : a.piece = pieceAt X i false) {x : VerifiableInference.Desc.First.Look.Place}
    (hlook : lookAt X i false = some x) (hsx : (P.ofPlace SET false x).shape = some x.fs)
    {nsOf : Nat → Option Nat}
    (hled : ∀ j u, L.MgP.pub (.ledger j) u = VerifiableInference.Desc.First.ledgerB u.2)
    (hfree : ∀ j u, L.MgP.pub (.freeAbove j) u =
      (nsOf j).any fun n => VerifiableInference.Desc.First.freeAboveB n u.2)
    (hns : nsOf i = some (P.ofPlace SET false x).ns) (hIn : InOrderReads L.MgP)
    (hHe : HeldReads L.MgP) (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true)
    (hn : told[b]? = some []) (hfit : pubFit L.MgP.more L.links L.ps = true)
    (askFresh : VerifiableInference.Desc.First.Pub.linkFresh i ∈
      (pubSets L.MgP.more L.links L.ps)[b]?.getD []) {k : Coins Bk}
    {s s' : FS} {m m' : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k s m E)
    (hr : Reach (s, y₀)) (hm : m'.st.input = m.st.input) (ft n : Nat) (cols : List OpenedColumn)
    (hst : B.step ft s xs cols = .ok (s', n))
    (hout : k3OnOut (P.ofPlace SET false x) s' = true) (hf : s'.failed = none)
    (bPub : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls claim Fr (P.ofPlace SET false x) u v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links a) ++
          pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
            (rowOf L.links a)),
        q ∉ paidCallsR i (2 + shift sub) → L.MgP.pub q (L.pubOf m.st.input.x, v.1) = true)
    (bPubP : ∀ u v : FS × Fr.E.Str,
      onQ L.N L.mgP L.links L.ps (fun t => (L.pubOf m.st.input.x, t)) b u → Reach u →
      u.1.failed = none →
      AcceptsCalls claim Fr (P.ofPlace SET false x) u v → SameBut u.1 v.1 →
      ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.MgP.more L.links a),
        q ≠ .left i → L.MgP.pubP q (L.pubOf m.st.input.x, v.1)) :
    L.thread.Form (b + 1) k s' m' :=
  form_calls_stepR L hK Fr y₀ claim readers codes shape a a' B hB hOk hk hk1 hfitS i hi sub hsub
    hpcT hpc hlook hsx hled hfree hns hIn hHe told hbf hn hfit askFresh hA hr hm ft n xs cols hst
    (okRounds_course R xs hF hx) hout hf bPub bPubP

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.form_calls_stepR
#print axioms ProofFile.Honest.K3.Law.AtThr.form_calls_courseR
