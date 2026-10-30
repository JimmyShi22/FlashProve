-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FootB1.lean: CONDITIONAL.

What is here. The hypothesis `K4FootJoin` (Law/W/FootJoin.lean) of the share of the thread's debt
`Exchange` at the own item of the member of the feed-forward layers' own rounds (sub-protocol K4),
WITH `JoinWorth` NO LONGER A HYPOTHESIS (`k4FootJoin_of_b1`): its field join is paid by `join_stand`
(Law/W/JoinAtFoot.lean); in that field's stead stand the lookup's own sentence (b1), five sentences
on what the lookup has heard, one on the rotary table, one on the scales of the queries and keys,
and eight public facts (`JoinPubLeft`). Paid besides, at each state: that the cells are the
matrices' (cellsAre_at), the two tensors of the gated products (gated_tensors), hok (stand_ok), the
list of the calls of the second pass (the library's ts_of_lines), two bounds on the numbers of
layers (by their definitions); the table of scales is laid as the layer sub-proof's. OVERTAKEN as
the way to the hypothesis hJ of the last form of the exchange (Law/ExchangeTenth.lean, beside the
tree): `k4JoinLeft_of_b1` (Law/W/JoinLeftB1.lean) ends in K4JoinLeft, does not ask emb, idn, hot,
look, which the proof here never reads on that branch, and has the scales of the queries and keys
from D.ChOK. `k4FootJoin_of_b1` IS CALLED BY NOBODY: it stays as the one statement that spends
`FootB1`, whose fields the heads of Law/W/JoinPubHead.lean, Law/W/JoinPubFo.lean,
Law/W/RopeHead.lean, Law/W/KeysLettersHead.lean, Law/QkOfPlan.lean and Law/W/JoinLeftB1.lean name.

  `JoinPubLeft`   eight public facts that join_stand asks.
  `FootB1`   what is left as a hypothesis at one state.
  `K4FootB1`   FootB1 at every state behind the member's step.
  `k4FootJoin_of_b1`   K4FootJoin from K4FootB1.

Not shown here. THAT FootB1 HOLDS ANYWHERE: every field is a hypothesis HERE; no example is known.
ITS FIELD b1 HOLDS ALL THE CONTENT THAT IS LEFT OF THE BATCHED SUMCHECK's OWN CLAIM: the sum over
the lookup's eight calls, at the keys' vectors of the cells and weights, is what the lookup's end
claim is worth in the world behind "back". For emb, idn, hot, look: the head of
Law/W/FootAtStand.lean. JoinPubLeft: hypotheses on the sizes, the tables and the layout: the sizes D
are a variable, but by the head of Law/JoinMade.lean the field floor cannot be met at the small
plan: THE FULL SIZE ALONE; Law/W/JoinPubHead.lean has JoinPubLeft there, under the library's
hypothesis on the public files. Everything that Law/W/FootJoin.lean's head lists as not shown, but
JoinWorth. K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES. AT A
THREAD NONE OF WHOSE STEPS ACCEPTS, K4FootB1 AND K4FootJoin HOLD EMPTILY. The import closure holds
what Law/W/FootJoin.lean's and Law/W/JoinAtFoot.lean's hold. Nothing on soundness, on completeness
or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FootJoin
import Johnson.Desc.ProofFile.Honest.K4.Law.W.JoinAtFoot
import Johnson.Desc.ProofFile.Honest.K4.Law.CellsAt
import Johnson.Road.FormsKeysPansTS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (sclOf cellsOf cellsAt pt padOf RopeFits SizedW LinesAre gl_numerals
  admitted_of_layout)
open OnBytes.Road.K4 (entryTrue kept_atS)
open OnBytes.Road.K4.W (K4Plan IdnHold HotPoint LookLeft uEOf kept_ground ground holds_item)
open OnBytes.Road.K4.C (gated_tensors normsPlan_of_plan gatedIn_of_plan)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim xS used lut aC keyVec layerR)
open VerifiableInference.Desc (Block Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ matsOfData)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **Eight public facts that join_stand asks.** This defines a hypothesis; the definition claims
nothing. -/
structure JoinPubLeft (h : Layer.Shape) (D : Dim) (Q : K4Pub) (sw : WsShape) (tb : Tables)
    (s0 : Forest.Shape) : Prop where
  cap : D.cap = h.lidb
  lines : LinesAre Q.P.y
  floor : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k)
  shape0 : Forest.shape Q.P.y.cl Q.P.y.h.lidb = .ok s0
  sizedW : SizedW sw D.P
  L : sw.L = h.L
  p4 : h.p4 = true
  pad : ∀ k : Fin 8,
    Reading.gl.val (ofF ((Q.P.y.cl.getD k.val {}).tauAt (Q.P.y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : Cb.Gl.E)

/-- **What is left as a hypothesis at one state.** Four fields of FootJoin, to the letter; what
join_stand asks on what the lookup has heard and on the rotary table; the lookup's own sentence.
This defines a hypothesis; the definition claims nothing. -/
structure FootB1 (h : Layer.Shape) (D : Dim) (tl : HTailF2) (Q : K4Pub)
    (o : Own) (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In)
    (hh ds : List Fmt.Drawn) (lk : ℕ) (tb : Tables) (s0 : Forest.Shape) : Prop where
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
  /-- the scales of the queries and keys, at the layer sub-proof's table of scales -/
  qk : letI : Inst.Model.Scl := sclOf h o.v.sc o.v.g o.v.y.Lam
    D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk)
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

/-- **FootB1 AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
The binders are K4FootJoin's. This defines a hypothesis; the definition claims nothing. -/
def K4FootB1 (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
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
    FootB1 h D tl Q o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds lk tb s0

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim} {names : Array (Nat × String)}
  {sw : WsShape} {lk : ℕ} {tb : Tables} {s0 : Forest.Shape}

/-- **K4FootJoin FROM K4FootB1.** CONDITIONAL: on every hypothesis named. -/
theorem k4FootJoin_of_b1 (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, At k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hdq : sw.dq ≤ Q.P.y.dq)
    (Pl : JoinPubLeft h D Q sw tb s0)
    (hR : K4FootB1 T At b cells weights tokens look Q M own rdOf tl p h D lk tb s0) :
    K4FootJoin T At b cells weights tokens look Q M own rdOf tl p h D := by
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
  refine
    { emb := Fl.emb
      idn := Fl.idn
      hot := Fl.hot
      look := Fl.look
      join := fun fs₂ F₂ hb => ?_ }
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
    (OnBytes.Road.ts_of_lines AQ.lay AQ.sw.p3 Pl.lines AQ.reads) Fl.qk (Fl.b1 fs₂ F₂ hb)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4FootJoin_of_b1
