-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ScriptFront.lean: SIX FACTS ON THE VERIFIER's STATE IN FRONT OF
THE OUTPUT HEAD's OWN SUB-PROTOCOL, OFF THE THREAD: at the first chain's thread as it is laid at the
library's hypothesis, border 341: each in the very form of the premise that spends it.

WHAT IT IS NOT. It is shown of no run that the thread holds at any stand. THE FULL SIZE ALONE, and
at that family of threads alone. EACH IS A JOINING OF LAWS THAT OTHERS HAVE PROVED: nothing new is
reckoned here. Said is a letter: nothing of it is spent. The third equation of `keyTie_of_three`
(the lookup's points), the guests and the ties on cells and masks are not spoken of. Nothing on any
property.

What the file holds. `k6_front_thr`: what all six start from: no mark; the promise's content at
border 341 (`K6FrontItems`, Johnson/Desc/K6/Honest/Law/FrontItems.lean); the state is reached; its
request's words are the public part's. `k6_request_is`: a helper: the state's request, and the
data's off the public part, are the hidden values' request. `k6_left24`, `k6_tokSmall`,
`k6_request`: the three fields of `K6KeysFront` (Honest/K6/Law/KeysAtThread.lean); `k6_keysFront`:
that structure. `k6_positions`: the premise hw of `idn_at_thread` (Honest/K6/Law/IdnAtThread.lean):
the state's two positions are the request's. `k6_request_ask`, `k6_token`, `k6_token_ask`: the first
and the second equation of `keyTie_of_three` (Honest/K6/Law/KeyTieOfThree.lean); the first is also
the premise hreq of `idn_at_thread`. CONDITIONAL: all on the hypothesis h and the thread; the two on
the token besides on b₀ ≤ 341: the thread's rider on the reply has begun; `k6_request_ask` and
`k6_token_ask` on what the reader of the small input lays as its request and its token: `headWit'`
(Honest/K6/Wit.lean) meets both by unfolding.

Called. `headFrontItems_of_thr` (Honest/K6/Law/FrontAt.lean); `thr_reach`, `foldFacts_thr`
(Honest/Thread/ReachFacts.lean) with the field reqIs of `FoldFacts`
(Johnson/Desc/First/FoldFacts.lean); `head_reply` (Honest/Thread/FirstHead.lean);
`P4.k6_member_at_mg` (Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean: 341 is a border of the chain);
`K6FrontItems.spells` (FrontItems.lean); `IM.tokSmallAt_border` (Johnson/IMR/TokAtReach.lean);
`rqX_at_const`, `reqW_at_const` (Johnson/Desc/Kinds/Law/K06AtConst.lean); `Came.requestOf_words`
(Kinds/Law/HeadPartsAtX.lean); `Meaning.K2.reqOk_of_noMark` (Johnson/IMR/AtReach.lean);
`AtZ.rq_start`, `AtZ.rq_of_req` (Kinds/Law/AtZLaw.lean); `token_is`
(Johnson/Desc/Sound/MgAt/K3HeadIn.lean).

Modules under lean/Johnson/Goal/ are among what this file imports: it imports no module of that
folder by name; by a reader's program on names its text names nothing that is declared there: a
comparison of text, which proves no absence.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Behind
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontAt
import Johnson.Desc.ProofFile.Honest.K6.Law.KeysAtThread
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.HeadPartsAtX
import Johnson.Desc.Kinds.Law.AtZLaw
import Johnson.Desc.Sound.MgAt.K3HeadIn
import Johnson.IMR.TokAtReach
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open VerifiableInference.Desc.Kinds (Reply.token Head.Law.readsOf)
open VerifiableInference.Desc.Kinds.Head (seatAt requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (TokSmall K6FrontItems reqX
  Came.requestOf_words)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (K6KeysFront reqW_at_const rqX_at_const)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach foldFacts_thr head_reply)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **WHAT ALL SIX START FROM**, off the thread at border 341: no mark; the promise's content; the
state is reached; the state's request's words are the public part's. CONDITIONAL: the hypothesis h;
the thread. -/
theorem k6_front_thr {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E) :
    s.failed = none ∧ K6FrontItems h.𝔇 mgBase (m.st.input.x.pub, s) ∧
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (m.st.input.x.pub, s) ∧
      s.req = P5J.At.reqW m.st.input.x.pub := by
  obtain ⟨hm, R⟩ := headFrontItems_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    h.𝔇 rfl rfl rfl rfl hT
  obtain ⟨b, hfl, -⟩ := P4.k6_member_at_mg h.toAtMg
  have hb : 341 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hfl).1
  exact ⟨hm, R, thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT,
    (foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).reqIs 341 (m.st.input.x.pub, s)
      ⟨hb, k, m, E, hT, rfl⟩ hm⟩

/-- **What the public item left 24 says beside its test**, of the state in front. CONDITIONAL: the
hypothesis h; the thread. -/
theorem k6_left24 : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    VerifiableInference.OnPublicFiles.k3LeftItemAt (P5J.At.X Zp) 24 s :=
  fun _ _ _ _ hT => (k6_front_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1).2.1.left

/-- **Every element in the reply's seat is an entry of the vocabulary.** CONDITIONAL: the hypothesis
h; the thread. -/
theorem k6_tokSmall : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    TokSmall (P5J.At.X Zp).hS.V s := by
  intro k s m E hT
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  exact IM.tokSmallAt_border h.scope h.reads O (by decide)
    (k6_front_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1).2.2.1

/-- The state's request is the hidden values' request, as the head's letters have it. CONDITIONAL:
the hypothesis h; the thread. -/
theorem k6_request_is {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E) :
    requestOf s = reqX (h.𝔇.H.req (m.st.input.x.pub, s)).val ∧
      h.𝔇.rq m.st.input.x.pub = reqX (h.𝔇.H.req (m.st.input.x.pub, s)).val := by
  obtain ⟨-, R, -, hq⟩ := k6_front_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  have hb : (_root_.Meaning.backReq m.st.input.x.pub.request).isSome = true := R.spells
  exact ⟨Came.requestOf_words s _ (hq.trans (reqW_at_const h (m.st.input.x.pub, s) hb)),
    rqX_at_const h (m.st.input.x.pub, s) hb⟩

/-- **The data's request off the public part is the seat's reading of the state.** CONDITIONAL: the
hypothesis h; the thread. -/
theorem k6_request : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX }).rq
        (id ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s).1) =
      (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).request s := by
  intro k s m E hT
  obtain ⟨e1, e2⟩ := k6_request_is h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  show h.𝔇.rq m.st.input.x.pub = requestOf s
  rw [e1, e2]

/-- **THE STRUCTURE OF PREMISES ON THE STATE IN FRONT, FOR THE KEYS, IS MET AT THE THREAD.**
CONDITIONAL: the hypothesis h: no more. -/
theorem k6_keysFront :
    K6KeysFront (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 id
      (fun v => { h.𝔇 with decT := fun _ _ => some (Q.cells v), cr1 := carryX }) :=
  ⟨k6_left24 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said,
    k6_tokSmall h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said,
    k6_request h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said⟩

/-- **The state's two positions are the request's.** CONDITIONAL: the hypothesis h; the thread. -/
theorem k6_positions : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    s.rowR = (({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX }).H.req
        (id ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m
          s).1, s)).val.r ∧
      s.rowE = (({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX }).H.req
        (id ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m
          s).1, s)).val.e := by
  intro k s m E hT
  have e1 := (k6_request_is h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1).1
  exact ⟨congrArg (·.r) e1, congrArg (·.e) e1⟩

/-- **The request that the reader of the small input lays is the seat's reading of the state**: the
first equation of `keyTie_of_three`. The reader lays the FIRST state's request: the request's words
have not turned since the start, and the start was not the blank state, since the state in front
bears no mark. CONDITIONAL: the hypothesis h; the thread; hq: what the reader lays as its request.
-/
theorem k6_request_ask (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk)
    (hq : ∀ v, (wit v).request = requestOf (ProofFile.startS Zp v.x.pub)) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    (wit m.st.input).request =
      (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).request s := by
  intro k s m E hT
  obtain ⟨hm, -, hr, hw⟩ := k6_front_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  have hok := _root_.Meaning.K2.reqOk_of_noMark h.scope h.reads O hr hm
  rw [hq]
  show requestOf (ProofFile.startS Zp m.st.input.x.pub) = requestOf s
  rw [VerifiableInference.Desc.Kinds.Head.AtZ.rq_start Zp m.st.input.x.pub hok,
    VerifiableInference.Desc.Kinds.Head.AtZ.rq_of_req Zp m.st.input.x.pub s hw]

/-- **The token that the head reads is the one that the instance asks about.** CONDITIONAL: the
hypothesis h; the thread; hb₀: the thread's rider on the reply has begun at border 341. -/
theorem k6_token (hb₀ : b₀ ≤ 341) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    Reply.token (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).toSeat s =
      some (OnBytes.Desc.Reply.tokOf m.st.input.x.asked) := by
  intro k s m E hT
  have hr : s.out.reply = some m.st.input.x.asked :=
    head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb₀ hT.1.2.2.2.2.2.1
  rw [VerifiableInference.Desc.Kinds.Head.token_is, hr]
  rfl

/-- **The same at a reader of the small input whose token is the instance's**: the second equation
of `keyTie_of_three`. CONDITIONAL: as the last; hy: what the reader lays as the next token. -/
theorem k6_token_ask (hb₀ : b₀ ≤ 341) (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk)
    (hy : ∀ v, (wit v).y = OnBytes.Desc.Reply.tokOf v.x.asked) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    Reply.token (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).toSeat s =
      some (wit m.st.input).y := by
  intro k s m E hT
  rw [hy]
  exact k6_token h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb₀ k s m E hT

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_front_thr
#print axioms ProofFile.Honest.K6.k6_left24
#print axioms ProofFile.Honest.K6.k6_tokSmall
#print axioms ProofFile.Honest.K6.k6_request_is
#print axioms ProofFile.Honest.K6.k6_request
#print axioms ProofFile.Honest.K6.k6_keysFront
#print axioms ProofFile.Honest.K6.k6_positions
#print axioms ProofFile.Honest.K6.k6_request_ask
#print axioms ProofFile.Honest.K6.k6_token
#print axioms ProofFile.Honest.K6.k6_token_ask
