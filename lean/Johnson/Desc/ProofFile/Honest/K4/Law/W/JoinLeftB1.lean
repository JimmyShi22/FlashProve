-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinLeftB1.lean: CONDITIONAL.

What is here. `K4JoinLeft` (Law/W/JoinLeft.lean) says: at every state behind the step of the member
of the feed-forward layers' own rounds (sub-protocol K4), `JoinWorth` holds behind each return of
the run "back". HERE IT IS CONCLUDED FROM THE LOOKUP's OWN SENTENCE, SIX SENTENCES ON WHAT WAS HEARD
AND ON THE ROTARY TABLE, AND PUBLIC FACTS (`k4JoinLeft_of_b1`), general in the thread. The statement
on the exchange at the member's own item asks K4JoinLeft as a hypothesis. It is `join_stand`
(Law/W/JoinAtFoot.lean) at every state behind the step, as `k4FootJoin_of_b1` (Law/W/FootB1.lean)
is; against that theorem: the conclusion is K4JoinLeft; the four fields emb, idn, hot, look, which
the proof never read, are not asked; the scales of the queries and keys are paid down to the public
fact D.ChOK (`qk_of_ground`, Law/QkOfPlan.lean). Paid at each state as there: that the cells are the
matrices' (cellsAre_at), the two tensors of the gated products (gated_tensors), that the factor
which the second token sumcheck's claim divides by passes the verifier's test (stand_ok), the list
of the calls of the second pass (the library's ts_of_lines), two bounds on the numbers of layers (by
their definitions); the table of scales is laid as the layer sub-proof's.

  `JoinB1At`   what is left as a hypothesis at one state: seven fields of FootB1, to the letter.
  `K4JoinB1`   JoinB1At at every state behind the member's step.
  `k4JoinLeft_of_b1`   **K4JoinLeft from K4JoinB1.**

Not shown here. THAT JoinB1At HOLDS ANYWHERE: every field is a hypothesis HERE; no example is known
of all seven together. `rope_head` (Law/W/RopeHead.lean) has the field rope under the library's
hypothesis on the public files, where the plan's public data are the public structure's and the
returned environment has the plan's layout, scales and group. ITS FIELD b1 HOLDS ALL THE CONTENT
THAT IS LEFT OF THE BATCHED SUMCHECK's OWN CLAIM: the sum over the lookup's eight calls, at the
keys' vectors of the cells and weights, is what the lookup's end claim is worth in the world behind
"back". `JoinPubLeft` and D.ChOK: hypotheses on the sizes, the tables and the layout; by the head of
Law/JoinMade.lean JoinPubLeft's field floor cannot be met at the small plan: THE FULL SIZE ALONE;
Law/W/JoinPubHead.lean has JoinPubLeft under the library's hypothesis on the public files; the
library has D.ChOK at its reference sizes (`ref_chOK`, Inst/Model/FF/Objects.lean). The ties on the
mask row, on what the lookup has heard and on the cells (hMask, hLook, hCells), K4Seated, K4Sits,
K4Front: hypotheses. K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN
SWITCHES. AT A THREAD NONE OF WHOSE STEPS ACCEPTS, K4JoinB1 AND THE CONCLUSION HOLD EMPTILY.
The import closure holds what Law/W/FootB1.lean's and Law/W/JoinLeft.lean's hold. Nothing on
soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.QkOfPlan
import Johnson.Desc.ProofFile.Honest.K4.Law.W.JoinLeft
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FootB1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (sclOf cellsOf cellsAt pt padOf RopeFits gl_numerals admitted_of_layout)
open OnBytes.Road.K4 (entryTrue kept_atS)
open OnBytes.Road.K4.W (K4Plan kept_ground ground holds_item)
open OnBytes.Road.K4.C (gated_tensors normsPlan_of_plan gatedIn_of_plan)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim aC keyVec layerR)
open VerifiableInference.Desc (Block Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ matsOfData)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **What is left as a hypothesis at one state.** Seven fields of FootB1, to the letter. This
defines a hypothesis; the definition claims nothing. -/
structure JoinB1At (h : Layer.Shape) (D : Dim) (tl : HTailF2) (Q : K4Pub) (o : Own) (F₁ : Fork)
    (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In) (lk : ℕ) (tb : Tables)
    (s0 : Forest.Shape) : Prop where
  /-- the lookup's two points have their sizes -/
  zx : o.H.fo.zx.size = Q.P.y.fo.dT
  zy : o.H.fo.zy.size = Q.P.y.fo.rK
  /-- its calls' points and weights are made of these -/
  zk : o.H.fo.zk = (Array.range Q.P.y.fo.NC).map fun q =>
    o.H.fo.zy.extract (Q.P.y.fo.rK - Q.P.y.fo.iota.getD q 0) o.H.fo.zy.size ++ o.H.fo.zx
  e : o.H.fo.e = (Array.range Q.P.y.fo.NC).map (Forest.callWeight Q.P.y.fo o.H.fo.zy)
  pts : ((List.range s0.NC).all fun q =>
    (o.H.fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true
  /-- the rotary table -/
  rope : ∀ (rt : Array E) (lam : ℕ), lam < Q.P.y.Lam →
    RopeFits Reading.gl
      { v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs, rt := rt } D tb
      (Q.g * Q.P.y.Lam) lam
  /-- THE LOOKUP's OWN SENTENCE, in the world behind "back" -/
  b1 : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    (∑ q : Fin 8, Reading.gl.val (o.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val o.H.fo.alpha - (q.val : Cb.Gl.E) * Reading.gl.val o.H.fo.theta -
          Blocks.ext (aC D q)
            (keyVec (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm)) tb
              (o.v.g * o.v.y.Lam) (fun l => layerR D.P lk (wmOf w.w) (o.v.g * o.v.y.Lam + l)) q)
            (pt Reading.gl (o.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf o.H) -
        o.H.fo.cEnd.value Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) = 0

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **JoinB1At AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
The binders are K4JoinLeft's. This defines a hypothesis; the definition claims nothing. -/
def K4JoinB1 (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim)
    (lk : ℕ) (tb : Tables) (s0 : Forest.Shape) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    JoinB1At h D tl Q o F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) lk tb s0

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim} {names : Array (Nat × String)}
  {sw : WsShape} {lk : ℕ} {tb : Tables} {s0 : Forest.Shape}

/-- **K4JoinLeft FROM K4JoinB1.** CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE
(JoinPubLeft's field floor). -/
theorem k4JoinLeft_of_b1 (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, At k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hdq : sw.dq ≤ Q.P.y.dq)
    (Pl : JoinPubLeft h D Q sw tb s0) (hCh : D.ChOK)
    (hR : K4JoinB1 T At b cells weights tokens look Q M own rdOf tl p h D lk tb s0) :
    K4JoinLeft T At b cells weights tokens look Q M own rdOf tl p := by
  intro blk hblk k s m E ds y cols s' hA hdr hS ds' Aq hseg o fs₁ F₁ ho hfr
  have Se := hSeat blk hblk
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  obtain ⟨_, _, Ak⟩ := (hF blk hblk k s m E ds y cols s' hA hdr hS ds').asks
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' Aq o :=
    ⟨Se, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨r, pts, Gr⟩ := kept_ground (kept_atS hdec) A ho
  have Fl := hR blk hblk k s m E ds y cols s' hA hdr hS ds' Aq hseg o fs₁ F₁ ho hfr
  have AQ : K4Plan h pc Q.P Q.g tl D := by rw [← eP, ← eg]; exact A
  have C := cellsAre_at Se hSit hS hseg ho (hCells k s m E hA) hM (AQ.tails.trans AQ.mats.symm)
    AQ.NM ds'
  rw [eP] at Gr
  have hfr' := hfr
  rw [seg_fork hseg ho] at hfr'
  obtain ⟨_, _, _, _, _, ey⟩ := stand_led Z
  have Ad := admitted_of_layout Gr.lay Gr.sw.p3
  have Sw : OnBytes.Road.Switches o.v.y.h := by rw [Ad.shape]; exact Gr.sw
  refine ⟨fun fs₂ F₂ hb => ?_⟩
  letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
  obtain ⟨_, _, _, _, Ft, _⟩ := ground Gr gl_numerals
    (M s' (dataQ own Aq (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
    (holds_item Gr _ F₂ (dataQ own Aq (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask)
  obtain ⟨ts, tu, hts, htu, Ss, Su⟩ :=
    gated_tensors Ft ey.symm Ad.laid Sw C (normsPlan_of_plan AQ).mats (gatedIn_of_plan AQ)
  exact join_stand Z (hAt k s m E hA) (hLook k s m E hA) AQ ds' F₂
    ((formsFrontWith_later hfr').trans (formsBack_later hb)) _ (stand_ok Z hdr) Pl.cap Pl.lines
    Pl.floor Fl.zx Fl.zy Fl.zk Fl.e Pl.shape0 Fl.pts Pl.sizedW Pl.L hws Pl.p4 Fl.rope Pl.pad rfl C
    hts htu Ss Su (Nat.le_refl _) (Nat.mul_div_le _ 2) hdq
    (OnBytes.Road.ts_of_lines AQ.lay AQ.sw.p3 Pl.lines AQ.reads) (qk_of_ground Gr hCh)
    (Fl.b1 fs₂ F₂ hb)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4JoinLeft_of_b1
