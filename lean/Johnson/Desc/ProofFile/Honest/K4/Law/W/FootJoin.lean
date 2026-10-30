-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FootJoin.lean: CONDITIONAL.

What is here. The share of the debt Exchange at the member's own item, in the threads' own form at
Thr with what is said (`k4_exchangeAtS_own_of_join` : ExchangeAtS T Said b iOwn), with ONE sentence
left behind "back": JoinWorth. The top statement of Law/W/ExchangeOfFoot.lean is called with its
hypothesis K4FootRest paid from `K4FootJoin`: four fields of FootRest, to the letter, and JoinWorth
behind each return of "back". The two own claims behind "back" are paid by `ownBack_layout`
(Law/W/MergeRoadPub.lean: the whole road of the merge's start, and the batched sumcheck's own claim
under JoinWorth); its two small premises by `stand_ok` and `stand_z0` (Law/OkAtStand.lean), the
first from drawsFit, which stands in the hypothesis' own binder.

  `FootJoin h D tl Q o F₀ F₁ mask Mm w hh ds seen`   what is left as a hypothesis at one state: emb,
      idn, hot, look, join.
  `K4FootJoin T At b …`   FootJoin at every state behind the member's step.
  `k4FootRest_of_join`   K4FootRest from K4FootJoin.
  `k4_exchangeAtS_own_of_join`   the top statement.

Not shown here. THAT FootJoin HOLDS ANYWHERE: every field of it is a hypothesis HERE; no example is
known. ITS FIELD join (JoinWorth, Law/StackStart.lean: what the lookup's join and the second token
sumcheck's claim are worth inside the batched sumcheck's start) HOLDS ALL THE CONTENT THAT IS LEFT
OF THAT SUMCHECK's OWN CLAIM; no statement shows it outright: `join_stand` (Law/W/JoinAtFoot.lean)
ends in it at a state behind the step, from the lookup's own sentence and sentences on what was
heard, at the full size alone. For emb, idn, hot, look: the head of Law/W/FootAtStand.lean. EIGHT
PUBLIC HYPOTHESES BESIDE K4Plan: the weights' layout is one that wsLayOf returns for a model with
routed experts (hws); its widths d and fe are the layer sub-proof's (hd, hfe); sw.dq ≤ y.dq, sw.f ≤
h.f, sw.fe ≤ h.f, sw.NE ≤ h.NE; a token's number has at least one bit (hlt; it follows from K4Plan
by `lt_of_plan`, Johnson/Road/K4/C/PlanLt.lean, and is kept as a premise): no statement here ties
the weights' layout to the layer sub-proof's; `wsFacts_head` (Law/W/WsFactsHead.lean) has all eight
under the library's hypothesis on the public files. K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE
WITH THE LIBRARY's ELEVEN SWITCHES: at every other shape the statements say nothing. K4Seated's
field fits (the public test k4Fits) is spent. AT A THREAD NONE OF WHOSE STEPS ACCEPTS, K4FootJoin
AND THE CONCLUSION HOLD EMPTILY. The import closure holds what Law/W/ExchangeOfFoot.lean's,
Law/W/MergeRoadPub.lean's and Law/OkAtStand.lean's hold. Nothing on soundness, on completeness or on
any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeOfFoot
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergeRoadPub
import Johnson.Desc.ProofFile.Honest.K4.Law.OkAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (sclOf cellsOf cellsAt pt)
open OnBytes.Road.K4 (entryTrue)
open OnBytes.Road.K4.W (K4Plan IdnHold HotPoint LookLeft uEOf)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim xS)
open VerifiableInference.Desc (Block Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ matsOfData)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **What is left as a hypothesis at one state.** Four fields of FootRest, to the letter, and
JoinWorth. This defines a hypothesis; the definition claims nothing. -/
structure FootJoin (h : Layer.Shape) (D : Dim) (tl : HTailF2) (Q : K4Pub)
    (o : Own) (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In)
    (hh ds : List Fmt.Drawn) (seen : Seen) : Prop where
  /-- the field emb of OpenedRight, in its own text -/
  emb : o.v.g = 0 → Reading.gl.val (wEmb Q w hh ds) =
    ∑ kh ∈ Finset.range (o.v.y.h.d / o.v.y.S2),
      Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
        ∑ r ∈ Finset.range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
          Blocks.ext D.lT
            (fun p => xS D (cellsOf D (cellsAt o.v.y Mm)) 0 (kh * 2 ^ o.v.y.ls + r) p)
            (uEOf Reading.gl o.v o.H)
  /-- the norms' identities at the cells -/
  idn : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
  /-- the selector's identity, extended over the positions, at the lookup's token point -/
  hot : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)
  /-- what is left of what the lookup's three claims ask -/
  look : LookLeft tl o F₀ mask Mm
  /-- behind "back": what the lookup's join and the second token sumcheck's claim are worth -/
  join : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    ∀ D', stackData Q w (ptsOf Q w (hh ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt seen.rounds (k4TermsEnds Q)) = some D' →
      ∀ weighed parts tT', o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' → JoinWorth o.H tT' parts
          (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) D'

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **FootJoin AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
The binders are K4FootRest's. This defines a hypothesis; the definition claims nothing. -/
def K4FootJoin (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    FootJoin h D tl Q o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim} {names : Array (Nat × String)}
  {sw : WsShape} {lk : ℕ}

/-- **K4FootRest FROM K4FootJoin.** CONDITIONAL: on every hypothesis named. -/
theorem k4FootRest_of_join (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hd : sw.d = Q.P.y.h.d)
    (hfe : sw.fe = Q.P.y.h.fe) (hdq : sw.dq ≤ Q.P.y.dq) (hf : sw.f ≤ Q.P.y.h.f)
    (hfef : sw.fe ≤ Q.P.y.h.f) (hNE : sw.NE ≤ Q.P.y.h.NE) (hlt : 1 ≤ Q.P.y.h.lt)
    (hR : K4FootJoin T At b cells weights tokens look Q M own rdOf tl p h D) :
    K4FootRest T At b cells weights tokens look Q M own rdOf tl p h D := by
  intro blk hblk k s m E ds y cols s' hA hdr hS ds' Aq hseg o fs₁ F₁ ho hfr
  have Se := hSeat blk hblk
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  obtain ⟨_, _, Ak⟩ := (hF blk hblk k s m E ds y cols s' hA hdr hS ds').asks
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' Aq o :=
    ⟨Se, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  have Fl := hR blk hblk k s m E ds y cols s' hA hdr hS ds' Aq hseg o fs₁ F₁ ho hfr
  have AQ : K4Plan h pc Q.P Q.g tl D := by rw [← eP, ← eg]; exact A
  have hfr' := hfr
  rw [seg_fork hseg ho] at hfr'
  exact
    { emb := Fl.emb
      idn := Fl.idn
      hot := Fl.hot
      look := Fl.look
      ownBack := fun fs₂ F₂ hb =>
        ownBack_layout Z (hAt k s m E hA) (hLook k s m E hA) AQ hws hd hfe hdq hf hfef hNE ds'
          hfr' hb _ (stand_ok Z hdr) (stand_z0 Z hlt) (Fl.join fs₂ F₂ hb) }

/-- **THE SHARE OF `Exchange` AT THE MEMBER's OWN ITEM, AT Thr WITH WHAT IS SAID, FROM K4FootJoin.**
CONDITIONAL: on every hypothesis named. -/
theorem k4_exchangeAtS_own_of_join {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, ThrS T Said b k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, ThrS T Said b k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, ThrS T Said b k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T (ThrS T Said b) b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hd : sw.d = Q.P.y.h.d)
    (hfe : sw.fe = Q.P.y.h.fe) (hdq : sw.dq ≤ Q.P.y.dq) (hf : sw.f ≤ Q.P.y.h.f)
    (hfef : sw.fe ≤ Q.P.y.h.f) (hNE : sw.NE ≤ Q.P.y.h.NE) (hlt : 1 ≤ Q.P.y.h.lt)
    (hR : K4FootJoin T (ThrS T Said b) b cells weights tokens look Q M own rdOf tl p h D) :
    ExchangeAtS T Said b iOwn :=
  k4_exchangeAtS_own_of_foot Said Tb hSeat hSit hMask hLook hCells hM hF A
    (k4FootRest_of_join (fun _ _ _ _ hT => hT.1) hSeat hSit hMask hLook hF A hws hd hfe hdq hf
      hfef hNE hlt hR)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4FootRest_of_join
#print axioms ProofFile.Honest.K4.W.k4_exchangeAtS_own_of_join
