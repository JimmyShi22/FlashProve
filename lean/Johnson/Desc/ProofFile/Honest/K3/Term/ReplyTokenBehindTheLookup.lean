-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk and the thread's other letters are
variables.
Johnson/Desc/ProofFile/Honest/K3/Term/ReplyTokenBehindTheLookup.lean: the honest side of the kind
"lookup" (K3): behind the member's step at a lookup that stands at or behind the border b₀ of the
reply's clause, the token that the verifier's state has heard (`S.replyTok?`,
Johnson/Desc/First/State.lean) is there, and it is the instance's. One theorem, conditional.

Why. The premises at one witness at the head's calls (`AtHead`,
Honest/K3/Law/Thread/ExchangeHeadAll.lean, as `AtCalls` hands it its letters) read the keys at the
token `st'.replyTok?.getD 0`: a default where something is due. The honest row reads the ASKED
token.
At a request that checks the last position the two must be one.

Three facts are joined. In front of the step the thread's riders hold "the reply that the state
holds is the one that the instance asks about", from the border b₀ on (`head_reply`,
Honest/Thread/FirstHead.lean). The lookup's step leaves the field out as it was (`sameBut_site`,
Honest/K3/Law/Thread/BehindAt.lean). Where the input's instance is read as a request, the asked
reply
is a token's image, and its number is the request's token (`asked_of_instOf`,
Johnson/Desc/ProofFile/InstOf.lean; `ofNat_token`, Johnson/Desc/Kinds/Law/ReplyHears.lean).

Hypotheses that remain: the head; the site and `SiteRest` (the seat); replyClauseSpeaksInFront: b₀
is at
most the lookup's border (at the first thread's letters b₀ is 339; the head's calls stand at 340,
its
digits at 345); `ThrS` and the member's step; instanceIsTheRequest.

Limits. An implication from `ThrS` and the step: no state is shown to meet them. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtHead
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.InstOf
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Sound.MgAt.K3HeadIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open Inst.Model (Instance ppref)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_reply)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Wj : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **Behind the member's step at a lookup at or behind the reply's border, the state's heard token
is the request's.** Conditional on what the file's head lists. -/
theorem replyTokenBehindTheLookupIsTheRequests (s : Site) (siteOfThePublicPart : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (summands : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (seat : SiteRest Zp cF H.first s lot summands wit)
    (replyClauseSpeaksInFront : b₀ ≤ borderOf s.link s.digits)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {blk : Block TS ProofFile.Cl} (memberAtTheBorder : (LH).thread.bs[borderOf s.link s.digits]? = some
              blk)
    {k : Coins Bk} {st st' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (pairInFront : ThrS (LH).thread Said (borderOf s.link s.digits) k st m En)
    (memberStepped : (LH).thread.Stepped blk k st m En ds y cols st')
    {request : Instance ppref} (instanceIsTheRequest : ProofFile.instOf m.st.input.x = some request) :
    st'.replyTok? = some request.y.val := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s siteOfThePublicPart lot summands
      wit seat
  have same := sameBut_site o pol lay KL Fd base A B O hS memberAtTheBorder memberStepped
  have heardInFront : st.out.reply = some m.st.input.x.asked :=
    head_reply h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w replyClauseSpeaksInFront
      pairInFront.1.2.2.2.2.2.1
  obtain ⟨numberIs, isAToken⟩ := ProofFile.asked_of_instOf instanceIsTheRequest
  have image := VerifiableInference.Desc.Kinds.Head.Law.ofNat_token ppref.V (by decide)
    m.st.input.x.asked isAToken
  have e := VerifiableInference.Desc.Kinds.Head.replyTok_of_nat st' m.st.input.x.asked
    (by rw [same.out]; exact heardInFront) image
  rw [e]
  exact congrArg some numberIs

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.replyTokenBehindTheLookupIsTheRequests
