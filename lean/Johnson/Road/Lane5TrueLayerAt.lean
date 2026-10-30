-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5TrueLayerAt.lean

A request that is true at an index with a layer whose weights are not all 0, at the table of scales
of the verifier's own record; and the three seams before the lookups, and the bundle, at it.

WHAT THE CASE IS, AND WHAT IT IS NOT. The index and the request are the library's made-up ones
(Inst/Model/SanityAtt.lean; Cm/RelTrue.lean uses them in the proof of "true_layer").
 (i) OF THE LAYERS' WEIGHTS ONLY W_v AND W_o OF LAYER 0 ARE NOT 0. The head of
   Inst/Model/SanityAtt.lean says of the weights wA: "token 0 is embedded as 2^20 in the channel 0,
   every other token as the zero row; layer 0 has no queries and keys, so attention is the mean over
   the positions so far; the value of a position is 64 in all channels if its token is 0; the output
   projection adds all 5,120 channels into the channel 2, which votes for the token 7". layA is
   zeroLayer with W_v and W_o set: W_q, W_k and the whole feed-forward part of layer 0 are zero, and
   so are the layers 1 to 47. W_v is one row (channel 0; 1,024 entries), W_o one column (channel 2;
   5,120 entries), every entry 4,095. A value's product has one term that is not 0 (2,047 times
   4,095: Av_eq); the output projection adds 5,120 equal terms. No weight is negative, there is no
   second value, and attention is the plain mean. The embedding and the output matrix are not 0.
 (ii) ALL SCORES ARE 0 (sc0, a theorem of that file): the scores' products are still products of 0
   with 0. Every softmax weight is 4,096 (wt_eq); the denominator at position i is 4,096 (i + 1)
   (den_eq).
 (iii) THE VALUE PRODUCT AND THE DIVISION WORK ON NUMBERS THAT ARE NOT 0: the value is 64 in the
   channels below 1,024 where the token is 0 (v_eq); the accumulator is 4,096 Bs z i (ac_eq), Bs the
   sum of 64 over the positions up to i whose token is 0. Here "acc_wA_pA": at wA and the prompt pA
   the accumulator of head 0, position 0, feature 0 in layer 0 is 262,144.
 (iv) THESE ARE FACTS ON THE FUNCTIONS Att.* OF THE LIBRARY's INTEGER PROGRAM
   (Inst/Model/Program.lean): no theorem here ties them to the cells of the trace Cm.trace, off
   which the matrices of the seams are read. The trace has no cell for an accumulator: it is formed
   inside a looked-up value from the cells of the softmax weights and the values. THAT ANY CELL OR
   LOOKED-UP VALUE OF THESE MATRICES DIFFERS FROM THOSE WITH LAYER 0 ZERO IS SHOWN BY NO THEOREM
   HERE. The theorems on the seams and on the bundle are the theorems for every true request, put in
   at this one: nothing of layA enters their proofs. From the other side: the matrices that meet the
   bundle at this request do not meet it once layer 0 is put to 0 in the weights' matrix (in one
   step from "under_of_public", Johnson/Road/Lane5TopPub.lean, and "false_layer_file", here;
   "ordsL_layer_file", here, meets it at the request's own matrix; no theorem joins them): the
   bundle's verdict turns on the weights' matrix; which group's clause turns is not shown.
 (v) GROUP 0 ALONE HOLDS LAYER 0: at the groups 1 to 11 all layers are zero. By a reading of the
   clauses: only "ForInG" at g = 0 (in "OrdsL": the key clause of group 0) takes W_v and W_o;
   "AttR0", attention's "InTables" and "HeadR0" take no weights; "LayerR0" takes the embedding
   alone; "ForInH" takes the output matrix.
 (vi) THE REQUEST HAS ONE COVERED POSITION, THE LAST, WHICH CHECKS THE ANNOUNCED TOKEN AGAINST ITS
   LOGITS, AND NO COUNTED ONE. It is "the next token after these 1,024 tokens": r = 1,023 and
   e = 1,024 (Instance.nextOf, Inst/Model/Program.lean); its set of counted positions is empty
   (`cnt_nextOf`, Inst/Model/ProgramRExact.lean). So the policy's two clauses on costs are empty
   sums and the policy decides nothing here: the theorems are stated at exact match, and by
   "RinfR_next" (Inst/Model/ProgramR.lean) such a request is true under every policy or under none.
   THE WEIGHTS ARE MADE UP: "They say nothing on the weights of a trained model" (the same head).
 (vii) THE PAIR IS THE LIBRARY's. Under the premises below X's table is the reference table
   "Cm.sRef" ("scales_at_ref", Johnson/Road/Lane5ScalesRef.lean): "true_layer_file" and
   "false_layer_file" are the library's "Cm.true_layer" (Cm/RelTrue.lean), with its indices, its
   request and the policy named, carried to X's table. At idxZ the integer program runs and answers
   the token 0 (model_wZ_pA): "not true" is another answer, not a failed range test.
No case is shown in which a layer's feed-forward weights, queries or keys are not 0.

Why. Three files show a statement "for every request that is true under its policy" at the record X
that publicOf returns (Johnson/Road/Lane5AttSeamTrueAt.lean, Johnson/Road/Lane5LayerSeamTrueAt.lean,
Johnson/Road/Ends/HeadWitTrue.lean), and Johnson/Road/Lane5TopLTrue.lean at letters. The requests
that are put in (there, in Johnson/Road/Lane5TrueGapAt.lean and Johnson/Road/Lane5ScalesRef.lean)
stand at indices all of whose 48 layers are zero.

Names.
* "idxA" := Cm.Idx.ofIndex ⟨SanityAtt.wA, SanityAtt.wA_wf⟩: the digit matrix that holds wA.
  "idxZ" := Cm.Idx.ofIndex ⟨SanityAtt.wZ, SanityAtt.wZ_wf⟩: wZ is wA with layer 0 zero.
* "reqA" := Instance.nextOf SanityAtt.pA ⟨7, _⟩: the prompt pA has token 0 at the positions 0 to
  1,022 and token 1 at the last; the answer is 7.

Main theorems.
* "idxA_layer0": layer 0 of idxA's weights is layA, and two of its entries are written out:
  W_v 0 0 = 4095, W_o 0 2 = 4095. "idxA_idxZ": idxA and idxZ have the same embedding, the same
  output matrix and the same layers 1 to 47.
Under publicOf's line, "Hd.PublicAt X.P" and "the scale file's words are scalesKF", at the table
"scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)" and the policy of exact match:
* **"true_layer_file"**: reqA is true at idxA. **"false_layer_file"**: reqA is not true at idxZ. So
  at X's own table the weights of layer 0 decide.
* "seam_layer_file" (with the test "attUsualK X"): attention's "AttR0" and "InTables" at the plan of
  every group g below 12, at the list read off that request's honest trace.
* "layerSeam_layer_file", "linkOK_layer_file" (with the test "recordOneB X g"): the layers'
  "L5.LayerR0" and "ForInG", and link 2 * g in order, at the matrices read off that trace. The
  second is a round trip: the proof of "layerSeam_of_true" starts from this link's order at the
  honest trace. It shows that the premises of "linkOK_of_one" can be met together at this request;
  it is no new fact on the link.
* "headForIn_layer_file", "headForIn_layer_blank" (with the test "Hd.headPubB X"): the head's
  "L5.HeadR0" and "ForInH"; the second at the written record Hd.blankRun X.
* "ordsL_layer_file": the whole bundle OrdsL.

Further limits. All those of the four files named above hold here too, but for their sentences that
no case is shown with a layer's weights not 0: the key vectors are terms of
this library; in these matrices the matrix that would hold a lookup's counts is 0; LayerR0 and
ForInG read no logit and no counted position; "attUsualK", "recordOneB" and "Hd.headPubB" are no
tests of the verifier: a configuration that it admits may fail them, and then nothing is said; that
publicOf returns and that the tests hold of any parameter file is a run's matter
(Johnson/Road/Lane5PublicRun.lean: publicOf's line and "Hd.PublicAt";
Johnson/Road/Lane5AttSeamRun.lean: "attUsualK"; Johnson/Road/Ends/GuardRec.lean: "recordOneB" in
twelve groups; Johnson/Road/FormsKeysRunK.lean: the scale words); no Lean code compares the text
linesKF and the words scalesKF with files; the runs are made with no layout file.

Not claimed: that a prover's committed cells are these matrices; that an honest prover's proof is
accepted (completeness of the protocol); anything on a proof or a verifier's verdict. It is a
statement on integers and tables alone.

-/
import Johnson.Road.Lane5LayerSeamTrueAt
import Johnson.Road.Ends.HeadWitTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Verify (publicOf layerShape)

/-- Cm.Idx.ofIndex ⟨SanityAtt.wA, SanityAtt.wA_wf⟩: the digit matrix that holds the library's
made-up weights wA: layer 0 has values and an output projection. -/
def idxA : Cm.Idx := Cm.Idx.ofIndex ⟨SanityAtt.wA, SanityAtt.wA_wf⟩

/-- Cm.Idx.ofIndex ⟨SanityAtt.wZ, SanityAtt.wZ_wf⟩: the same for wZ: wA with layer 0 zero. -/
def idxZ : Cm.Idx := Cm.Idx.ofIndex ⟨SanityAtt.wZ, SanityAtt.wZ_wf⟩

/-- Instance.nextOf SanityAtt.pA ⟨7, _⟩: "the next token after these 1,024 tokens" at the prompt pA,
with the answer 7. -/
def reqA : Instance ppref := Instance.nextOf SanityAtt.pA ⟨7, by decide⟩

/-- **Layer 0 of idxA's weights is not zero**: two of its entries. -/
theorem idxA_layer0 : idxA.weights.layer 0 = SanityAtt.layA ∧ SanityAtt.layA.Wv 0 0 = 4095 ∧
    SanityAtt.layA.Wo 0 2 = 4095 := by
  refine ⟨?_, rfl, rfl⟩
  unfold idxA
  rw [Cm.weights_ofIndex]
  rfl

/-- idxA and idxZ differ in layer 0 alone. -/
theorem idxA_idxZ : idxA.weights.Emb = idxZ.weights.Emb ∧ idxA.weights.H = idxZ.weights.H ∧
    ∀ L, L ≠ 0 → idxA.weights.layer L = idxZ.weights.layer L := by
  unfold idxA idxZ
  rw [Cm.weights_ofIndex, Cm.weights_ofIndex]
  exact ⟨rfl, rfl, fun _ hL => if_neg hL⟩

/-- **An accumulator of attention that is not 0**: at the weights wA and the prompt pA, in layer 0:
head 0, position 0, feature 0. On the function Att.ac of the library's integer program; X here is
that program's stream Inst.Model.X, not the verifier's record. -/
theorem acc_wA_pA :
    Att.ac ppref tbRef (SanityAtt.wA.layer 0) 0 (X ppref tbRef SanityAtt.wA SanityAtt.pA 0)
      (0 / ppref.ch) 0 (0 % ppref.ch) = 262144 := by
  rw [show X ppref tbRef SanityAtt.wA SanityAtt.pA 0 = SanityAtt.xs (SanityAtt.zz SanityAtt.pA) from
    SanityAtt.X0_eq SanityAtt.pA _]
  show Att.ac ppref tbRef SanityAtt.layA 0 (SanityAtt.xs (SanityAtt.zz SanityAtt.pA))
    (0 / ppref.ch) 0 (0 % ppref.ch) = 262144
  rw [SanityAtt.ac_eq (SanityAtt.zz SanityAtt.pA) 0 0 (by norm_num), SanityAtt.zz_pA]
  simp [SanityAtt.Bs, SanityAtt.bz]

/-- At the reference table and exact match: true at idxA. -/
theorem true_layer_ref : Policy.IsTrueUnder Cm.sRef AcceptancePolicy.exact idxA reqA :=
  (Policy.isTrueUnder_exact_iff Cm.sRef idxA reqA).2
    ((Cm.true_next ⟨SanityAtt.wA, SanityAtt.wA_wf⟩ SanityAtt.pA ⟨7, by decide⟩).2
      SanityAtt.model_wA_pA)

/-- At the reference table and exact match: not true at idxZ. -/
theorem false_layer_ref : ¬ Policy.IsTrueUnder Cm.sRef AcceptancePolicy.exact idxZ reqA := fun hT => by
  have h7 := (Cm.true_next ⟨SanityAtt.wZ, SanityAtt.wZ_wf⟩ SanityAtt.pA ⟨7, by decide⟩).1
    ((Policy.isTrueUnder_exact_iff Cm.sRef idxZ reqA).1 hT)
  exact absurd (modelIs_unique _ _ _ _ h7 SanityAtt.model_wZ_pA) (by decide)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **A true request at an index whose layer 0 is not zero, at the table of the verifier's own
record.** -/
theorem true_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact idxA
      reqA := by
  rw [scales_at_ref h A hW]
  exact true_layer_ref

/-- **With layer 0 zero the same request is not true there.** -/
theorem false_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    ¬ Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact idxZ
      reqA := by
  rw [scales_at_ref h A hW]
  exact false_layer_ref

/-- **Attention's seam at that request, at the record's own plan.** -/
theorem seam_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (U : attUsualK X = true) (hW : Model.fileWords KL = scalesKF.toArray) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      AttR0 Ag.S (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
          idxA reqA))) ∧
      (callsA Ag.S Ag.fs (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
          idxA reqA)))).InTables :=
  seam_of_true_file h A U hW AcceptancePolicy.exact_ok hg idxA reqA (true_layer_file h A hW)

/-- **The layers' seam at that request.** -/
theorem layerSeam_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) (hg : g < 12) :
    LayerR0 (layerShape X.P) X.layers.sc X.layers.y g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
          idxA reqA))) g)
      idxA.mat reqA ∧
    Alg.ForInG X.layers g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
          idxA reqA))) g)
      idxA.mat :=
  layerSeam_of_true_file h A t hW AcceptancePolicy.exact_ok hg idxA reqA (true_layer_file h A hW)

/-- **Link 2 g is in order at that request's matrices.** -/
theorem linkOK_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) (hg : g < 12) :
    LinkOK Cm.Seg.Hd.main
      (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
      idxA.mat reqA (2 * g)
      (libMZ X.layers.y g
        (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact)
          idxA reqA))) g)) :=
  linkOK_of_true_file h A t hW AcceptancePolicy.exact_ok hg idxA reqA (true_layer_file h A hW)

/-- **The head's seam at that request.** -/
theorem headForIn_layer_file (h : publicOf pol KL lay = .ok X) (t : Hd.headPubB X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {R0 : Model.Head.Run} (e1 : R0.h = X.hS)
    (e2 : R0.L = X.HLy) :
    HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) AcceptancePolicy.exact reqA (Hd.mhTrue X AcceptancePolicy.exact idxA reqA) ∧
      Hd.ForInH (Hd.runReq R0 reqA)
        (Hd.callsH (Hd.runReq R0 reqA) (Model.Verify.borderOf X.y) X.layers.wsLay
          (Hd.mhTrue X AcceptancePolicy.exact idxA reqA) idxA.mat).K := by
  have A : Hd.PublicAt X.P := by
    have t' := t
    simp only [Hd.headPubB, Bool.and_eq_true, decide_eq_true_eq] at t'
    exact t'.1.1.1.1.1
  exact Hd.headForIn_of_true h t hW AcceptancePolicy.exact_ok e1 e2 idxA reqA (true_layer_file h A hW)

/-- **The same at the written record.** -/
theorem headForIn_layer_blank (h : publicOf pol KL lay = .ok X) (t : Hd.headPubB X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) AcceptancePolicy.exact reqA (Hd.mhTrue X AcceptancePolicy.exact idxA reqA) ∧
      Hd.ForInH (Hd.runReq (Hd.blankRun X) reqA)
        (Hd.callsH (Hd.runReq (Hd.blankRun X) reqA) (Model.Verify.borderOf X.y) X.layers.wsLay
          (Hd.mhTrue X AcceptancePolicy.exact idxA reqA) idxA.mat).K :=
  headForIn_layer_file h t hW (R0 := Hd.blankRun X) rfl rfl

/-- **The whole bundle at that request.** -/
theorem ordsL_layer_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) AcceptancePolicy.exact (Hd.shapeA X)
      idxA.mat reqA
      (zTrue (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact idxA reqA)
      (zaTrue (Hd.shapeA X) (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) AcceptancePolicy.exact
        idxA reqA) :=
  have B := Hd.public_of_publicOf h A
  ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.2.2)
    (fun _ hg => (att_of_at' h A hg).2.1) (fun _ hg => (att_of_at' h A hg).2.2.1)
    (lawful_of_at h A hW) AcceptancePolicy.exact_ok idxA reqA (true_layer_file h A hW)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.idxA_layer0
#print axioms OnBytes.Road.L5.idxA_idxZ
#print axioms OnBytes.Road.L5.acc_wA_pA
#print axioms OnBytes.Road.L5.true_layer_ref
#print axioms OnBytes.Road.L5.false_layer_ref
#print axioms OnBytes.Road.L5.true_layer_file
#print axioms OnBytes.Road.L5.false_layer_file
#print axioms OnBytes.Road.L5.seam_layer_file
#print axioms OnBytes.Road.L5.layerSeam_layer_file
#print axioms OnBytes.Road.L5.linkOK_layer_file
#print axioms OnBytes.Road.L5.headForIn_layer_file
#print axioms OnBytes.Road.L5.headForIn_layer_blank
#print axioms OnBytes.Road.L5.ordsL_layer_file
