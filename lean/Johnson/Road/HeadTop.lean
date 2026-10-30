-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadTop.lean

From the head's field relation to "the reply is the model's first choice at the last position".

The conclusion is the library's relation "RinfR" (Inst/Model/ProgramR.lean) at a request with
r = 1,023 and e = 1,024, under every policy: the integer program runs on the 1,024 tokens, and the
announced token has a greatest logit at the last position, every smaller token a smaller one.

The order of the steps, which cannot be changed:
  1. the head's conditions modulo p and the bound on its cells ("Cm.Plain.TP.RF");
  2. the same as congruences between integers ("Cm.Plain.TP.rfz_of_rf");
  3. nothing wraps around in the head, for whatever stream its borrowed cells hold; in particular
     that stream is below 2^39 ("stream_bound");
  4. with that bound, the relation of the 24 segments of the layers ("Cm.Lay.RFL": bound, keys AND
     identities of 12 feed-forward and 12 attention segments at one trace, the embedding inside);
  5. so the borrowed cells hold the program's stream after the last layer, and the range tests of
     all 48 layers hold ("LayersGive"; "layersGive_of_cond");
  6. so the head's logits are the program's ("modelS_of_head", "next_token_of_head").
Step 5 cannot be had before step 3. In "modelS_of_head" and "next_token_of_head" the record
"LayersGive" is a HYPOTHESIS: it stands for the whole of steps 4 and 5.

How much is new. Little: most theorems here retell the library, so that what a link to a program
must deliver has a name. "modelS_of_head" is the end of the proof of "Cm.TP.modelS_of"
(Cm/TargetPRelProofs.lean) with its beginning made the hypothesis "LayersGive".
"next_token_of_rno" is "Cm.TP.forces" with "RinfR_next"; "next_token_of_parts" is that with the
witness unpacked. "modelS_next_iff" is the twin of "ModelS_nextOf" (Inst/Model/ProgramR.lean).
"layersGive_of_cond" shows that "LayersGive" does not ask too much: it follows from the library's
conditions on the whole model. It does NOT show that a link on the layers alone can give the
record: its field "ok" is taken from the library's end theorem under "Cm.TP.Cond", which holds the
head's keys too; whoever has these hypotheses has "ModelS" already. Only of the field "stream" does
the proof take the bound from the head and then the stream from the layers. What the layers must
give is "Cm.BelowL" and "Cm.TP.CondL": bound, keys and identities of 24 segments at one trace whose
head cells are the head's.

Main definitions and theorems:
* "abs_H_index": the output matrix of a well-formed index is at most 2^12 in absolute value.
* "modelS_next_iff", "rinfR_of_modelS": at r = T - 1, e = T, exact match on the stretch is "y is the
  next token", so "RinfR" under every policy; for all parameters.
* "LayersGive κ tbs w prompt tz": what the layers must give the head.
* "modelS_of_head": the plain head's relation at "Cm.reqOf x" with "LayersGive": exact match on the
  stretch, for every request. Each hypothesis of the library's theorems that it calls is either a
  hypothesis here or shown: the size condition on p (a hypothesis; "Down.big_gl" at the
  protocol's prime); a lawful final normalisation "nf.OK" (a hypothesis); |H| ≤ 2^12 (shown from
  the type of indices); every checked token is a token, "Req.OK" (shown at "Cm.reqOf x").
* "next_token_of_head": so "RinfR" at r = 1,023, e = 1,024. "next_token_of_alike",
  "next_token_of_ledger": the same from the relation at any request that is like "Cm.reqOf x"
  (HeadReq.lean), with the plain head or the head with the cost ledger.
* "next_token_of_rno": from a witness of the model's own relation "Cm.TP.Rno" at the protocol's
  prime and a lawful table, by "Cm.TP.forces". "next_token_of_parts": the same with the witness
  given in three parts: the layers' bound, the layers' conditions, the head's field relation.
* "hyps_met", "next_true_exists", "next_hyps_met": the hypotheses are met together by the honest
  trace of every true request at a lawful table, and a true request with r = 1,023, e = 1,024
  exists at each (all weights and tokens 0). "lawful_exists": there is a lawful table.
* "rinfR_of_ledger": for every request and a policy with "AcceptancePolicy.OK": the relation of the head with the
  cost ledger at "Head.Req.of pol x", with "LayersGive" and the request's form, gives "RinfR"
  ("Policy.LedgerHead.noWrap_pol"). "ledger_hyps_met": its hypotheses are met by the honest cells,
  for every request in "RinfR"; "ledger_next_hyps_met": and such a request exists, with r = 1,023,
  e = 1,024, at every lawful table and every such policy.

Not claimed: whose matrix H and whose stream the cells hold; that any program or protocol shows one
of the hypotheses; anything at other sizes than the reference (the head on cells is written at
1,024 positions, width 5,120, vocabulary 202,048). All theorems are deductions inside the library.
-/
import Cm.RelTrue
import Cm.Rel2Guards
import Policy.Rel.LedgerHeadNoWrap
import Policy.Rel.LedgerHeadHonest
import Johnson.Road.HeadReq
import Johnson.Road.HeadDown

set_option autoImplicit false

namespace OnBytes.Road.Hd.Top

open Inst.Model Inst.Model.Head

/-! ## 1. Small things -/

/-- The output matrix of a well-formed index: two-byte weights, and 0 outside its size. -/
theorem abs_H_index {P : Params} (i : Index P) (j v : ℕ) : |i.val.H j v| ≤ 2 ^ 12 := by
  have := i.property.2.2 j v
  rw [abs_le]
  split_ifs at this
  · constructor <;> omega
  · rw [this]
    norm_num

section Next
variable (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
include hT

/-- **At r = T - 1, e = T, exact match on the stretch is "y is the next token".** -/
theorem modelS_next_iff (i : Index P) (x : Instance P) (hr : x.r = P.T - 1) (he : x.e = P.T) :
    ModelS P κ nf tbs i.val x ↔ RinfK P κ nf tbs i x := by
  have hz := gapOf_eq_zero_iff P.V (lgK P κ nf tbs i.val x.prompt (P.T - 1)) x.y.isLt
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := h2 (P.T - 1) (le_of_eq hr) (by omega)
    rw [x.w_last hT] at h3
    exact ⟨h1, x.y.isLt, (hz.1 h3).1, (hz.1 h3).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t h3 h4 => ?_⟩
    have e : t = P.T - 1 := by omega
    rw [e, x.w_last hT]
    exact hz.2 ⟨h2.2.1, h2.2.2⟩

/-- .. so it gives the relation of a request, under every policy. -/
theorem rinfR_of_modelS (pol : AcceptancePolicy) (i : Index P) (x : Instance P) (hr : x.r = P.T - 1)
    (he : x.e = P.T) (h : ModelS P κ nf tbs i.val x) : RinfR P κ nf tbs pol i x :=
  (RinfR_next P hT κ nf tbs pol i x hr he).2 ((modelS_next_iff P hT κ nf tbs i x hr he).1 h)

end Next

/-! ## 2. What the layers must give the head -/

/-- The range tests of all 48 layers hold on the prompt, and the cells that the head borrows hold
the program's stream after the last layer. The first clause is the first clause of "RunsK". -/
structure LayersGive (κ : ℕ → LayerScale) (tbs : ℕ → Tables) (w : Weights)
    (prompt : Fin ppref.T → Fin ppref.V) (tz : Cells ℤ) : Prop where
  ok : ∀ L < ppref.layers,
    Att.OK (ppref.at (κ L)) (tbs L) (w.layer L) L (XK ppref κ tbs w prompt (2 * L)) ∧
      FF.OK (ppref.at (κ L)) (tbs L) (w.layer L) L (XK ppref κ tbs w prompt (2 * L + 1))
  stream : ∀ a < nT, ∀ j < nD, xv tz j a = XK ppref κ tbs w prompt (2 * ppref.layers) a j

/-! ## 3. From the head's relation -/

section FromHead
variable {p : ℕ} [Cm.TI.Big p] {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}

/-- **What the layers' relation takes from the head**: the stream that the borrowed cells hold is
below 2^39, whatever it is. -/
theorem stream_bound (hn : nf.OK) {H : Mat} (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {y : Req}
    {tz : Cells ℤ} (h : Cm.Plain.TP.RF (F := ZMod p) nf (fun j v => ((H j v : ℤ) : ZMod p)) y tz) :
    ∀ a < nT, ∀ j < nD, |xAt tz a j| < 2 ^ 39 :=
  fun a ha => ((Cm.Plain.TP.noWrap (Cm.Plain.TP.rfz_of_rf h) hn hH).1 a ha).2.2

/-- **The plain head's relation, with what the layers give: the program runs, and at every covered
position the checked token is the first choice.** -/
theorem modelS_of_head (hn : nf.OK) (i : Index ppref) (x : Instance ppref) {tz : Cells ℤ}
    (hl : LayersGive κ tbs i.val x.prompt tz)
    (h : Cm.Plain.TP.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p))
      (Cm.reqOf x) tz) :
    ModelS ppref κ nf tbs i.val x := by
  have hz : Cm.Plain.TP.RFz p nf i.val.H (Cm.reqOf x) tz := Cm.Plain.TP.rfz_of_rf h
  have hH := abs_H_index i
  have h1 := (Cm.Plain.TP.head_stream hn hH hl.stream hz).1
  have h2 := Cm.Plain.TP.head_stream_gap hn hH (y := Cm.reqOf x) (fun t => x.w_lt t) hl.stream hz
  exact ⟨⟨hl.ok, h1⟩, fun t hr he => h2 t (lt_of_lt_of_le he x.e_le) hr he⟩

/-- **The reply is the first choice at the last position**: the relation of a request with
r = 1,023, e = 1,024, under every policy. -/
theorem next_token_of_head (hn : nf.OK) (i : Index ppref) (x : Instance ppref)
    (hr : x.r = 1023) (he : x.e = 1024) {tz : Cells ℤ}
    (hl : LayersGive κ tbs i.val x.prompt tz)
    (h : Cm.Plain.TP.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p))
      (Cm.reqOf x) tz) (pol : AcceptancePolicy) :
    RinfR ppref κ nf tbs pol i x :=
  rinfR_of_modelS ppref (by decide) κ nf tbs pol i x hr he (modelS_of_head hn i x hl h)

/-- The same from the relation at any request that covers the same positions and checks the same
tokens there. -/
theorem next_token_of_alike (hn : nf.OK) (i : Index ppref) (x : Instance ppref)
    (hr : x.r = 1023) (he : x.e = 1024) {tz : Cells ℤ}
    (hl : LayersGive κ tbs i.val x.prompt tz) {y : Req} (hy : HeadReq.Alike y (Cm.reqOf x))
    (h : Cm.Plain.TP.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p)) y tz)
    (pol : AcceptancePolicy) : RinfR ppref κ nf tbs pol i x :=
  next_token_of_head hn i x hr he hl ((HeadReq.plainRF_req hy).1 h) pol

/-- The same from the relation of the head with the cost ledger: at this request no position is
counted. -/
theorem next_token_of_ledger (hn : nf.OK) (i : Index ppref) (x : Instance ppref)
    (hr : x.r = 1023) (he : x.e = 1024) {tz : Cells ℤ}
    (hl : LayersGive κ tbs i.val x.prompt tz) {y : Req} (hy : HeadReq.Alike y (Cm.reqOf x))
    (h : Policy.LedgerHead.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p)) y tz)
    (pol : AcceptancePolicy) : RinfR ppref κ nf tbs pol i x :=
  next_token_of_alike hn i x hr he hl hy
    (HeadReq.plain_of_ledger
      (fun a _ => (hy.rhoC a).trans
        (HeadReq.rhoC_of_le (y := Cm.reqOf x) (le_of_eq hr.symm) a)) h) pol

end FromHead

/-! ## 4. At the model's own relation -/

section Model
variable {s : Cm.Scales}

/-- **The record "LayersGive" does not ask too much**: bound and conditions of the whole model give
it. For the field "stream" the proof takes the bound on the last stream from the head (inside
"Cm.TP.rfl_of"), then the stream from the layers. The field "ok" is taken from the library's end
theorem, under hypotheses that hold the head's keys too: so this theorem is a witness for the
record, and no way for a link on the layers alone to reach it. -/
theorem layersGive_of_cond {p : ℕ} [Cm.TI.Big p] [Fact p.Prime] (hs : s.Lawful) {i : Cm.Idx}
    {x : Instance ppref} {T : All.Trace} (b : Cm.Below2 (2 ^ 18) T)
    (c : Cm.TP.Cond p s i.mat x T) :
    LayersGive s.kap (fun _ => tbRef) i.weights x.prompt T.vHead where
  ok := (Cm.TP.modelS_of b c hs).1.1
  stream := fun a ha j hj => by
    have hS := Cm.TP.Lay.stream_eqK (p := p) hs.lawfulK i.wf (Cm.TP.rfl_of b c hs)
    rw [T.x_head hj ha]
    exact hS 11 (by decide) 8 le_rfl a ha j hj

/-- **From a witness of the model's relation at the protocol's prime.** -/
theorem next_token_of_rno (hs : s.Lawful) (i : Cm.Idx) (x : Instance ppref) (T : All.Trace)
    (hr : x.r = 1023) (he : x.e = 1024) (h : Cm.TP.Rno Cb.Gl.p s i x T) (pol : AcceptancePolicy) :
    RinfR ppref s.kap s.nf (fun _ => tbRef) pol i.index x :=
  rinfR_of_modelS ppref (by decide) s.kap s.nf (fun _ => tbRef) pol i.index x hr he
    ((Cm.trueAt_iff s.kap s.nf i x).1
      (Cm.TP.forces Cb.Gl.p Code.pGold_prime Down.gl_big s hs i x T h)).2

/-- **The witness in three parts**: the layers' bound, the layers' conditions, the head's field
relation at the trace's cells. -/
theorem next_token_of_parts (hs : s.Lawful) (i : Cm.Idx) (x : Instance ppref) (T : All.Trace)
    (hr : x.r = 1023) (he : x.e = 1024) (bL : Cm.BelowL (2 ^ 18) T)
    (cL : Cm.TP.CondL Cb.Gl.p s.kap s.nf i.mat (All.tokOf x.prompt) T)
    (h : Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) s.nf (Cm.TP.castH Cb.Gl.p i.mat) (Cm.reqOf x)
      T.vHead) (pol : AcceptancePolicy) :
    RinfR ppref s.kap s.nf (fun _ => tbRef) pol i.index x :=
  next_token_of_rno hs i x T hr he
    ⟨by omega,
      ⟨bL, fun a ha => (h.small a ha).1, fun a ha => (h.small a ha).2.1,
        fun a ha => (h.small a ha).2.2.1⟩,
      ⟨cL, h.keys, h.idns, fun h' => absurd h' (by rw [he]; decide)⟩⟩ pol

/-! ## 5. The hypotheses can be met -/

/-- **At a lawful table, for every true request, the honest trace's cells of the head meet the
hypotheses of "modelS_of_head" together.** -/
theorem hyps_met {p : ℕ} [Cm.TI.Big p] [Fact p.Prime] (hs : s.Lawful) (i : Cm.Idx)
    (x : Instance ppref) (ht : Cm.TrueAt s.kap s.nf i x) :
    s.nf.OK ∧
      LayersGive s.kap (fun _ => tbRef) i.index.val x.prompt (Cm.trace2 s i x).vHead ∧
      Cm.Plain.TP.RF (F := ZMod p) s.nf (fun j v => ((i.index.val.H j v : ℤ) : ZMod p))
        (Cm.reqOf x) (Cm.trace2 s i x).vHead :=
  have hR := Cm.TP.sub_at s i x _ (Cm.TP.trace_of_true (p := p) hs i x ht)
  ⟨hs.nf, layersGive_of_cond hs hR.2.1 hR.2.2, Cm.TP.headRF hR.2.1 hR.2.2⟩

/-- **At every lawful table a true request with r = 1,023, e = 1,024 exists**: all weights 0, all
tokens 0. That is enough to show that the hypotheses are not empty, and shows no more. -/
theorem next_true_exists (hs : s.Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧ Cm.TrueAt s.kap s.nf i x :=
  ⟨Cm.Idx.ofIndex ScalesSanity.iZero,
    RequestGuards2.xz ⟨1023, by decide⟩ ⟨1024, by decide⟩, rfl, rfl,
    Cm.true_zero hs.toPP _ _ (by decide)⟩

/-- The two joined, at the protocol's prime: the hypotheses of "next_token_of_head" are met together
at every lawful table. -/
theorem next_hyps_met (hs : s.Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧ s.nf.OK ∧
      LayersGive s.kap (fun _ => tbRef) i.index.val x.prompt (Cm.trace2 s i x).vHead ∧
      Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) s.nf
        (fun j v => ((i.index.val.H j v : ℤ) : ZMod Cb.Gl.p)) (Cm.reqOf x)
        (Cm.trace2 s i x).vHead := by
  haveI := Down.big_gl
  obtain ⟨i, x, hr, he, ht⟩ := next_true_exists hs
  exact ⟨i, x, hr, he, hyps_met hs i x ht⟩

/-- **A lawful table exists**: the library's reference scales ("Cm.lawful_sRef",
Cm/Rel2Guards.lean). So "at every lawful table" is not said of nothing. Whether the scales of a
given file are lawful is not looked at here. -/
theorem lawful_exists : ∃ s : Cm.Scales, s.Lawful := ⟨Cm.sRef, Cm.lawful_sRef⟩

end Model

/-! ## 6. The head with the cost ledger: every request, with its policy -/

section Ledger
variable {p : ℕ} {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables} {pol : AcceptancePolicy}

/-- **The relation of the head with the ledger, with what the layers give and the request's form:
the relation of a request under the policy**, for every request. The form ("Head3") is a test on the
request alone. -/
theorem rinfR_of_ledger [Cm.TI.Big p] (hn : nf.OK) (hpol : pol.OK) (i : Index ppref)
    (x : Instance ppref) (h3 : Head3 x) {tz : Cells ℤ} (hl : LayersGive κ tbs i.val x.prompt tz)
    (h : Policy.LedgerHead.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p))
      (Req.of pol x) tz) :
    RinfR ppref κ nf tbs pol i x :=
  have hz : Policy.LedgerHead.RFz p nf i.val.H (Req.of pol x) tz := Policy.LedgerHead.rfz_of_rf h
  have h2 := (Policy.LedgerHead.noWrap_pol hz hn (abs_H_index i) hpol).2 _ hl.stream
  ⟨⟨hl.ok, h2.1⟩, h3, h2.2⟩

/-- **Its hypotheses can be met**: for every request in the relation, by the honest cells of the
head on the program's stream; modulo every p. -/
theorem ledger_hyps_met (hn : nf.OK) (hpol : pol.OK) (i : Index ppref) (x : Instance ppref)
    (h : RinfR ppref κ nf tbs pol i x) :
    LayersGive κ tbs i.val x.prompt
        (N.honCells nf (XK ppref κ tbs i.val x.prompt (2 * ppref.layers)) i.val.H
          (Req.of pol x)) ∧
      Policy.LedgerHead.RF (F := ZMod p) nf (fun j v => ((i.val.H j v : ℤ) : ZMod p))
        (Req.of pol x)
        (N.honCells nf (XK ppref κ tbs i.val x.prompt (2 * ppref.layers)) i.val.H
          (Req.of pol x)) :=
  ⟨⟨h.1.1, fun a _ _ hj => Policy.LedgerHead.c_xv hj a⟩,
    Policy.LedgerHead.hon_rf p
      (N.honIn_stream hn (abs_H_index i) h.1.2 (Req.of_ok pol x) (Head.Policy.polOK_inst h.2.2)
        hpol.C hpol.theta hpol.cap)⟩

/-- **They are met together somewhere**: at every lawful table and for every policy with "AcceptancePolicy.OK"
there are an index, a request with r = 1,023, e = 1,024 and its form, and cells that meet
"LayersGive" and the relation of the head with the ledger; modulo every p. -/
theorem ledger_next_hyps_met {s : Cm.Scales} (hs : s.Lawful) (hpol : pol.OK) :
    ∃ (i : Index ppref) (x : Instance ppref) (tz : Cells ℤ),
      x.r = 1023 ∧ x.e = 1024 ∧ Head3 x ∧ s.nf.OK ∧
      LayersGive s.kap (fun _ => tbRef) i.val x.prompt tz ∧
      Policy.LedgerHead.RF (F := ZMod p) s.nf (fun j v => ((i.val.H j v : ℤ) : ZMod p))
        (Req.of pol x) tz := by
  obtain ⟨i, x, hr, he, ht⟩ := next_true_exists hs
  have hm := (Cm.trueAt_iff s.kap s.nf i x).1 ht
  have hR : RinfR ppref s.kap s.nf (fun _ => tbRef) pol i.index x :=
    rinfR_of_modelS ppref (by decide) s.kap s.nf (fun _ => tbRef) pol i.index x hr he hm.2
  exact ⟨i.index, x, _, hr, he, hm.1, hs.nf, ledger_hyps_met hs.nf hpol i.index x hR⟩

end Ledger

end OnBytes.Road.Hd.Top

#print axioms OnBytes.Road.Hd.Top.modelS_next_iff
#print axioms OnBytes.Road.Hd.Top.stream_bound
#print axioms OnBytes.Road.Hd.Top.modelS_of_head
#print axioms OnBytes.Road.Hd.Top.next_token_of_head
#print axioms OnBytes.Road.Hd.Top.next_token_of_alike
#print axioms OnBytes.Road.Hd.Top.next_token_of_ledger
#print axioms OnBytes.Road.Hd.Top.layersGive_of_cond
#print axioms OnBytes.Road.Hd.Top.next_token_of_rno
#print axioms OnBytes.Road.Hd.Top.next_token_of_parts
#print axioms OnBytes.Road.Hd.Top.hyps_met
#print axioms OnBytes.Road.Hd.Top.next_true_exists
#print axioms OnBytes.Road.Hd.Top.next_hyps_met
#print axioms OnBytes.Road.Hd.Top.lawful_exists
#print axioms OnBytes.Road.Hd.Top.rinfR_of_ledger
#print axioms OnBytes.Road.Hd.Top.ledger_hyps_met
#print axioms OnBytes.Road.Hd.Top.ledger_next_hyps_met
