-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/EmbHead.lean: CONDITIONAL.

What is here. The field emb of the hypothesis `FootRest` (Law/W/FootAtStand.lean), in its own text:
in the first group, what the honest side sends as the value of the claim on the embedding is the
library's sum at the cells of the matrices that are unpacked from the data: at the state behind the
step of the member of the feed-forward layers' own rounds (sub-protocol K4), at the thread with the
library's own values (`lettersHead`, Honest/Thread/FirstHead.lean). `emb_at`
(Law/W/ItemRightOf.lean) has that text from fourteen hypotheses. Seven of them are paid here under h
and at a stand: the four on public numbers by the library's `emb_public_in_scope`
(Johnson/Goal/Meaning/EmbScope.lean), the sizes of two heard points by the library's
`emb_hear_sizes` (Johnson/Road/K4/EmbHear.lean), the number of position bits by `public_head`
(Law/W/PublicHead.lean). An eighth, the identity on the cells (`EmbCube`), comes OUT OF THE THREAD:
the open item `Item.constr m .idn` says it beside the norms' identities (the library's `EmbField`),
and `embCube_of_field` (Johnson/Road/K4/W/EmbOfField.lean) carries it over, with the tie on symbols
and `MatsAre` for the cells (Law/W/OneTie.lean) and two ties more. Each proof is a chain of calls.

  `embField_head`   the library's `EmbField` at the list that the library reads off the witness for
      the group, the index's matrix and the request as the library makes it, at every continuation
      of the challenges heard: out of the thread in front of the member.
  `emb_head`   **the field emb, behind the step from a stand.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN, OR
THAT ANY STEP OF THE MEMBER ACCEPTS: hT : Thr and Zs : `K4Stand` (Law/SlotsTrue.lean) are
hypotheses. tie (`K4SymsTieAt`): it ties two readers of one witness; `symsTie_head`
(Law/W/ReadersHead.lean) has it wherever the thread stands; it can hold as 0 = 0: both readers
answer 0, without a word, where they find no seat for an array. hA (`MatsAre`,
Johnson/Desc/First/Look/K3CallerLay.lean, at the list that the library reads off the witness for the
group): an equation of functions: it binds the list to 0 outside every size; `matsAre_head`
(Law/W/MatsAreHead.lean) has it at every witness. hi: the Script's cells hold an index i (`Cm.Idx`:
a digit matrix that meets the library's `WFW`: so a clause on the input). hW: THE EMBEDDING THAT THE
LIBRARY's `embR` READS OFF THE WEIGHTS OF THE HONEST SIDE's READER IS THE ONE THAT IT READS OFF THE
IMAGES OF THE INDEX's MATRIX: a tie on the reader `weights`, at the entries of the embedding's unit
alone: nothing is asked outside them; `hiW_of_index` (Law/W/IndexHiW.lean) has it from one
hypothesis on the weights. hTok: THE TOKENS THAT THE HONEST SIDE's READER READS ARE THE PROMPT OF
THE REQUEST AS THE LIBRARY MAKES IT OF THE PUBLIC INSTANCE AND THE WITNESS: a hypothesis on the
reader `tokens`; Law/W/TokPublic.lean brings it down to a sentence on the public instance alone, and
Law/W/TokOfBytes.lean shows that sentence of the lot's own reader where the request bytes decode.
env, claim, hu, hs: four returns of the honest side's functions (the claims' environment; the claim
on the embedding; its unit; the test on its shape): hypotheses here; `emb_returns_stand`
(Law/EmbReturns.lean) has them at a stand. Lh (`LaidK4`, Law/SeatedHead.lean) and hQ: on public
lists and numbers. The side library AtFullSide proves, with no hypothesis, that h has a member at
one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits
say what it is worth). Of h together with Lh, hQ, Zs, hT, hi, tie, hA, hW, hTok, env, claim, hu and
hs (`emb_head`), or with Lh, hT and hi (`embField_head`), no example is known to us. THE FIRST GROUP
ALONE (`emb_head`). THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`).
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. IT
IMPORTS A FILE UNDER Johnson/Goal/ BY NAME (Johnson/Goal/Meaning/EmbScope.lean) and calls its
`emb_public_in_scope`; `emb_head` rests besides on `Meaning.P34.pub34_all`, through `lam_head`
(Law/W/FullHead.lean) and `public_head`. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OneTie
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ItemRightOf
import Johnson.Road.K4.W.EmbOfField
import Johnson.Road.K4.EmbHear
import Johnson.Goal.Meaning.EmbScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own ClaimEnv)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road (sclOf cellsOf cellsAt pt)
open OnBytes.Road.Rows.Norms (NormField EmbField castM)
open OnBytes.Road.K4 (emb_hear_sizes)
open OnBytes.Road.K4.W (uEOf embCube_of_field mats_of_are syms_of_plain)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (embR xS)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (MatsAre)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ matsOfData oneDec)
open VerifiableInference.OnPublicFiles (headLink layMs)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS constrQAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hT and hi. **THE LIBRARY's `EmbField`, OUT OF THE THREAD.** i: an index
that the Script's cells hold. d: a continuation of the challenges heard. -/
theorem embField_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {i : Cm.Idx} (hi : Holds (Q.cells mm.st.input) i) (d : List Fmt.Drawn) :
    EmbField (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).layers.sc (P5J.At.X Zp).y g
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) i.mat
      (h.𝔇.put (h.𝔇.H.req (mm.st.input.x.pub, s))
        (h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).tok).val := by
  have e24 := P5J.headLink_in_scope h.scope h.reads h.pubOne
  have c0 := idn_item_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (atK4_of_laid Lh) hT d
  rw [Lh.seg] at c0
  have c' : constrQAt (headLink (P5J.At.X Zp)) h.𝔇.put
      (oneDec (fun _ _ => some (Q.cells mm.st.input)) h.𝔇.H) h.𝔇.headPart h.𝔇.digitsPart (2 * g)
      .idn (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ d)) := c0
  have hh : 2 * g ≠ headLink (P5J.At.X Zp) := by
    have := Lh.lt
    rw [e24]
    omega
  have q := partG_of_constr (Hh := oneDec (fun _ _ => some (Q.cells mm.st.input)) h.𝔇.H)
    (M := Q.cells mm.st.input) c' (by decide) hh rfl hi
  have q' : NormField (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).layers.sc (P5J.At.X Zp).y g
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) i.mat
      (h.𝔇.put (h.𝔇.H.req (mm.st.input.x.pub, s))
        (h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).tok).val ∧
      EmbField (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).layers.sc (P5J.At.X Zp).y g
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) i.mat
        (h.𝔇.put (h.𝔇.H.req (mm.st.input.x.pub, s))
          (h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).tok).val := q
  exact q'.2

/-- CONDITIONAL: on h, Lh, hQ, Zs, hT, hi, tie, hA, hW, hTok, env, claim, hu and hs. **THE FIELD
emb, BEHIND THE STEP FROM A STAND.** xl: a place of the lookup at which tie and hA hold. ce, cl, un:
what the honest side's functions return. -/
theorem emb_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl} {own : List (ℕ × ℕ)}
    {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {i : Cm.Idx} (hi : Holds (Q.cells mm.st.input) i)
    {xl : VerifiableInference.Desc.First.Look.Place} {names : Array (ℕ × String)}
    (tie : K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW names own rdOf c s mm)
    (hA : ∀ d, MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
      h.𝔇.l3.nc
      (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
        h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ d)))
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g))
    (hW : embR ppref kRef (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w) =
      embR ppref kRef fun a b => ((i.mat a b : ℤ) : Cb.Gl.E))
    (hTok : ∀ d q, q < 2 ^ DF.lT →
      (k4Wit Qp cells weights tokens (look Qp) mm.st.input).tokv.getD q 0 =
        Cm.Seg.tokX
          (h.𝔇.put (h.𝔇.H.req (mm.st.input.x.pub, s))
            (h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).tok).val q)
    {ce : ClaimEnv} {cl : WsClaim} {un : WsUnit}
    (env : claimEnvOf Qp
      (ptsE Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input) mm.st.heard ds) = some ce)
    (claim : ce.claimE
      (ptsE Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input) mm.st.heard ds).ZE
      (ptsE Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input) mm.st.heard ds).tkh Qp.P.V
      (k4Wit Qp cells weights tokens (look Qp) mm.st.input).tokv = some cl)
    (hu : Qp.P.wsLay.U[cl.ui]? = some un) (hs : wsClaimShape Qp.P.wsLay cl = .ok ())
    (ds' : List Fmt.Drawn) :
    o.v.g = 0 → Reading.gl.val (wEmb Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input)
       mm.st.heard ds) =
      ∑ kh ∈ Finset.range (o.v.y.h.d / o.v.y.S2),
        Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
          ∑ r ∈ Finset.range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
            Blocks.ext DF.lT
              (fun q => xS DF (cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
                  (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))))) 0
                (kh * 2 ^ o.v.y.ls + r) q)
              (uEOf Reading.gl o.v o.H) := by
  intro hg0
  obtain ⟨eY, eS, eg⟩ := pub_is Lh hQ
  obtain ⟨⟨eP, _, _, _, _⟩, _, _, _⟩ := pub_of Lh hQ
  have eQ : Qp.P = (P5J.At.X Zp).layers := eP.symm.trans Lh.P
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  have g0 : g = 0 := by rw [← eg, ← Fu.grp]; exact hg0
  subst g0
  obtain ⟨Ne, Zw, hl, hV⟩ := Meaning.Emb.emb_public_in_scope h.scope h.reads h.pubOne
  obtain ⟨_, _, elt⟩ := public_head h Lh.lt Lh.hp
  obtain ⟨a, _, _, ha, _, _, _, hhear, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  have sz := emb_hear_sizes (P := { Qp.P with tokv := s.tokv }) (by rw [eg]; rfl) hhear
  have hZ : o.H.ZE.size = o.v.y.ls + o.v.y.h.lt := by
    rw [Fu.lay, ← eY]
    exact sz.1
  have hk : o.H.tkh.size = o.v.y.lPd - o.v.y.ls := by
    rw [Fu.lay, ← eY]
    exact sz.2
  have hM : matsOfData x.2.hp.tl names
      (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))) =
      castM ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds')))).MG 0) := by
    rw [hdata, i1, i2, List.append_assoc]
    exact mats_of_are xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc _
      names _ (syms_of_plain xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _ names _
        (tie a ha (ds ++ ds'))) (hA (ds ++ ds'))
  have hJ := embCube_of_field
    (embField_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hi (ds ++ ds'))
    (sclOf (Verify.layerShape (P5J.At.X Zp).P) o.v.sc o.v.g o.v.y.Lam)
    (t := cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
      (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))))))
    (emb := embR ppref kRef (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w))
    (tok := fun q => (k4Wit Qp cells weights tokens (look Qp) mm.st.input).tokv.getD q 0)
    (d := o.v.y.h.d) (by rw [hM, Fu.lay]) hW (hTok (ds ++ ds'))
    (by rw [Fu.lay, Ne.d]; exact Nat.le_refl _)
  exact emb_at Zs hT (by rw [Fu.lay]; exact elt) env claim hu hs _ Zw (by rw [eQ]; exact hl)
    (by rw [eQ]; exact hV) (by rw [Fu.lay]; exact Ne) hZ hk hJ hg0

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.embField_head
#print axioms ProofFile.Honest.K4.W.emb_head
