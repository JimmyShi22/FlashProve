-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/B1Head.lean: CONDITIONAL.

What is here. THE LOOKUP's OWN SENTENCE, OUT OF THE THREAD: the sum over the lookup's eight calls of
the heard weight times alpha less the call's number times theta less the extension of the call's key
vector at the call's heard point, plus the public number for the padding trees, is what the lookup's
end form is worth. It is what the laws on the start of the batched sumcheck of the feed-forward
layers' own rounds (sub-protocol K4) ask of the lookup (the hypothesis hB1 of `join_stand`,
Law/W/JoinAtFoot.lean; up to three rewritings, made in Law/W/JoinB1Head.lean, the field b1 of
`JoinB1At`, Law/W/JoinLeftB1.lean). Here it is concluded at the thread with the library's own values
(`lettersHead`, Honest/Thread/FirstHead.lean), at a state with an accepted step of the member
(`K4Stand`, Law/SlotsTrue.lean), from what the thread itself holds: the forward row at the member
asks the item `Item.worth m 2 "keys"`, which is open there, and its sentence is the lookup's item on
the keys (`keys_lay_head`, Law/W/KeysHead.lean). THE SENTENCE IS SO MOVED, NOT SHOWN: see below. The
reading is changed for the data's own mask row at the mask places, as in Law/W/NuCutHead.lean, by
the cut tie on the mask row (`outKeys_congr`, Johnson/Road/K4/W/KeysCongr.lean: the item reads no
other mask place and no cell); the rounds for which what was heard stands, and the four sentences on
the lookup's points and weights, are the library's `K3Left` out of the public item `.left m`
(`left_of_promise`, Law/W/StandsHead.lean); that the state's two readers of what the lookup has
heard find one thing is `lookTie_head` (Law/W/LookTieHead.lean), called at a constant; the item is
read backwards by `part_of_outKeys` (Johnson/Road/K4/C/KeysBack.lean). The proofs are chains of
calls.

  `stand_foLater`   the ledger in front of the member is earlier than the one that its step leaves.
  `b1Cut_head`   the sentence at the data's mask row, from the cut tie, at free key vectors.
  `b1_thread_head`   **the same at the library's own reader and seats: the cut tie is not asked.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN, OR
THAT ANY STEP OF THE MEMBER ACCEPTS: hT and Zs are hypotheses; Zs holds a tie on the thread's Script
(its field mask). OF WHAT ANOTHER SUB-PROTOCOL OWES, TWO CLAUSES OF hT ARE SPENT. (1) THE SENTENCE
OF THE OPEN ITEM ON THE KEYS' WORTH: it is owed behind the member of the lookup on the calls, and no
file of K4's honest side ends in it: whoever shows it must show that the lookup's join is worth 0 at
the reading of the places that the lookup's caller makes off the witness (`layNu`) and at the
caller's key vectors off the witness, at every continuation of the challenges. (2) What the public
item `.left m` says beside its test: the library proves that a yes of the lookup's block leaves it
(`k3LeavesAtCalls`, Johnson/Top/H/K3CEnd.lean); that it stands in the thread is not shown here.
Beside these, clauses of the frame's own are spent: the form's public tests and what the thread says
of how the state was made (through `maskCut_head`, Law/W/ReadersHead.lean, and `lookTie_head`). hKv:
THAT THE KEY VECTORS OF THE LOOKUP's CALLER ARE THE LIBRARY's `keyVec` AT THE CELLS t, THE TABLES tb
AND THE WEIGHTS wts: a hypothesis here, at free letters. T8, h8: public facts on the plan's trees
and calls; `trees_head` (Law/W/JoinB1Head.lean) has both under h. Lh, hx: on public lists and
numbers. No example is known of all the hypotheses together; nothing here was evaluated. THE FULL
SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). The import closure holds what
the closures of Law/W/NuCutHead.lean, Law/W/KeysHead.lean, Law/W/LookTieHead.lean,
Johnson/Road/K4/W/KeysCongr.lean and Johnson/Road/K4/C/KeysBack.lean hold. WHAT THIS FILE's IMPORTS
REACH, by a program's walk from import to import that stops, unopened, at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose name begins
Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it stopped
at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge; it saw
46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and none of the three
names. What lies behind the 78 is not counted: all the numbers are floors. `b1_thread_head` RESTS,
through `maskCut_head`, ON TWO STATEMENTS OF FILES UNDER Johnson/Goal/, `Meaning.scope_plans` and
`OnBytes.Road.Hd.core_of_scope` (Law/W/ReadersHead.lean's head names the files). A LAW, NOT A PART:
no file that defines a part of the proof file's description may import this one. Nothing on
soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.NuCutHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.KeysHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LookTieHead
import Johnson.Road.K4.W.KeysCongr
import Johnson.Road.K4.C.KeysBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (pt TreesFit)
open OnBytes.Road.K4 (AtK4 eAll layAt_plan attAt_even tlAt_plan padFo HeardFits)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.W (outKeys_congr)
open OnBytes.Road.K4.C (part_of_outKeys)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Claim First.S)
open VerifiableInference.Desc.First.Look (layAt stepOf layLay)
/- the library's pubAt, under a name that no file of the honest side has -/
open VerifiableInference.Desc.First.Look renaming pubAt → pubLay
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ mgAll_more_base seatTab)
open VerifiableInference.OnPublicFiles (layMu layNu K3OutKeys laterFo_of_psc)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim aC keyVec LW)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The ledger in front of the member is earlier than the one that its step leaves.** General in
the thread. CONDITIONAL: on Zs and h0. -/
theorem stand_foLater {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
    {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    {F0 : Fork} (h0 : s.fork? = some F0) : _root_.Fo.Later F0 A.F := by
  obtain ⟨a, a₀, _, _, hhere, eF, _, hhear, _⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  have e0 : s.fork? = some a₀.F := by
    simp only [VerifiableInference.Desc.First.S.fork?, hhere]
  obtain rfl : a₀.F = F0 := Option.some.inj (e0.symm.trans h0)
  have hL := OnBytes.Road.K4.hear_foLater (P := { Q.P with tokv := s.tokv }) hhear
  rw [eF] at hL
  exact hL.1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, Zs, hT, hx, hCut, T8, h8 and hKv. **THE LOOKUP's OWN SENTENCE FROM
THE CUT TIE.** Zs: a state with an accepted step of the member. ds': a continuation of the
challenges behind it. F: any ledger later than the one that the step leaves. -/
theorem b1Cut_head [scl : Scl] {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {p : Par} {blk : Block TS ProofFile.Cl} {own : List (ℕ × ℕ)}
    {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (hCut : K4MaskCutTieAt h Q (m := m) (x := x) xl own rdOf c s mm) (ds' : List Fmt.Drawn)
    {Dd : Dim} (T8 : TreesFit (P5J.At.X Zp).y.fo Dd) (h8 : (P5J.At.X Zp).y.fo.NC = 8)
    (t : Inst.Model.FFSeg.Cell → Cb.Gl.E) (tb : Tables) (L0 : ℕ) (wts : ℕ → LW Cb.Gl.E)
    (hKv : ∀ q : Fin 8, Cb.Fo.forK Cb.Gl.E
        (layLay (pubLay (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) xl.fs xl.lm xl.F.next xl.ns
          x.2.hp.tl h.𝔇.l3.nr h.𝔇.l3.nc) ()
        (Cb.Fo.zext (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
          h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
          (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) q.val =
      keyVec Dd t tb L0 wts q)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) :
    ∀ F, OnBytes.PscRun.Later A'.F F →
      (∑ q : Fin 8, Reading.gl.val (o.H.fo.e.getD q.val zeroE) *
          (Reading.gl.val o.H.fo.alpha - (q.val : Cb.Gl.E) * Reading.gl.val o.H.fo.theta -
            Blocks.ext (aC Dd q) (keyVec Dd t tb L0 wts q)
              (pt Reading.gl (o.H.fo.zk.getD q.val #[])))) +
        Reading.gl.val (padFo o.H.fo) - o.H.fo.cEnd.value Reading.gl
          (F.worldOf Reading.gl
            (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))).mask entry) = 0 := by
  intro F hLF
  have N := nine_head h Lh
  have A := atK4_of_laid Lh
  obtain ⟨x₁, hx₁, _, e1, e2, e3, en⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at e1 e2 e3 en
  have hN : FoNums.nMasks xl.fs ≤ xl.ns := by
    rw [_root_.FoLedger.elems_eq, e1, en]
    exact (_root_.Fo.Pub2.public_elems N.Sx.pubOf).1 _ _ N.Sx.plan
  have h2 : m % 2 = 0 := by
    rw [N.Sx.g]
    omega
  have hW := keys_lay_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT (ds ++ ds') N.Sx.pc2
    (attAt_even h2) hx (tlAt_plan N.Sx.notHead N.Sx.step N.Sx.plan)
  obtain ⟨_, F1, g₁, rs, _, hn, L, hh, hF1⟩ := left_of_promise (Dm := h.𝔇)
    (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH A N.Sx
    (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  obtain ⟨g', hg1, hg2, _⟩ := lookTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT
    (look := fun _ _ => g₁) (Qp := Qp) fun g₂ h2' => by
      obtain rfl : g₁ = g₂ := Option.some.inj (hh.symm.trans h2')
      exact ⟨rfl, rfl, rfl⟩
  obtain rfl : g' = o.H.fo := Option.some.inj (hg2.symm.trans (stand_look Zs))
  obtain rfl : g₁ = o.H.fo := Option.some.inj (hh.symm.trans hg1)
  obtain ⟨a, _, _, ha, _, _, _, _, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  have hL0 : _root_.Fo.Later F1 F := (stand_foLater Zs hF1).trans (laterFo_of_psc hLF)
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  rw [hdata, i1, i2, List.append_assoc]
  -- the rounds for which what was heard stands
  have es : o.H.fo.shape = xl.fs := L.shape.trans e1.symm
  have hI := L.heardIs
  rw [hn] at hI
  have hI' : _root_.Fo.HeardIs Reading.gl o.H.fo F1
      (_root_.Fo.endsOf o.H.fo.shape xl.lm xl.F.next rs) := by
    rw [es, e1, e2, e3]
    exact hI
  -- the two readings, as in nuCut_head
  let νL : _root_.Fo.Pl → Cb.Gl.E :=
    layNu xl (pubLay (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad
      h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1)
      h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds')))
  let νD : _root_.Fo.Pl → Cb.Gl.E := fun p => match p with
    | .mask j =>
      (dataQ own a (rdOf (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))).mask j
    | q => νL q
  have hm : ∀ j, j < xl.F.next + FoNums.nMasks xl.fs → νL (.mask j) = νD (.mask j) :=
    fun j hj => (hCut a ha (ds ++ ds') j (by rw [e3] at hj; omega)).symm
  let KL : ℕ → ℕ → Cb.Gl.E := Cb.Fo.forK Cb.Gl.E
        (layLay (pubLay (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) xl.fs xl.lm xl.F.next xl.ns
          x.2.hp.tl h.𝔇.l3.nr h.𝔇.l3.nc) ()
        (Cb.Fo.zext (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
          h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
          (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds')))))
  have P : K3OutKeys xl.fs xl.lm xl.F.next νL KL Reading.gl o.H.fo F1 := hW o.H.fo F1 hF1 hg1
  have P' : K3OutKeys o.H.fo.shape xl.lm xl.F.next νD KL Reading.gl o.H.fo F1 := by
    rw [es]
    exact outKeys_congr xl.fs xl.lm xl.F.next hm KL Reading.gl o.H.fo F1 P
  have Hf : HeardFits o.H.fo :=
    ⟨by rw [L.shape]; exact L.zx, by rw [L.shape]; exact L.zy,
      fun q hq => by rw [L.shape] at hq ⊢; exact (L.zkRaw q hq).2, by rw [L.shape]; exact L.eRaw⟩
  exact part_of_outKeys Hf (by rw [L.shape]; exact T8) (by rw [L.shape]; exact h8) t tb L0 wts
    (Kv := KL) hKv (nu := νD) entry hI' hL0 P'

/-- CONDITIONAL: on h, Lh, Zs, hT, hx, T8, h8 and hKv. **THE LOOKUP's OWN SENTENCE, WITH THE
CUT TIE NOT ASKED**: at the library's own reader and seats. -/
theorem b1_thread_head [scl : Scl] {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {p : Par} {blk : Block TS ProofFile.Cl} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (ds' : List Fmt.Drawn)
    {Dd : Dim} (T8 : TreesFit (P5J.At.X Zp).y.fo Dd) (h8 : (P5J.At.X Zp).y.fo.NC = 8)
    (t : Inst.Model.FFSeg.Cell → Cb.Gl.E) (tb : Tables) (L0 : ℕ) (wts : ℕ → LW Cb.Gl.E)
    (hKv : ∀ q : Fin 8, Cb.Fo.forK Cb.Gl.E
        (layLay (pubLay (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) xl.fs xl.lm xl.F.next xl.ns
          x.2.hp.tl h.𝔇.l3.nr h.𝔇.l3.nc) ()
        (Cb.Fo.zext (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
          h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
          (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) q.val =
      keyVec Dd t tb L0 wts q)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) :
    ∀ F, OnBytes.PscRun.Later A'.F F →
      (∑ q : Fin 8, Reading.gl.val (o.H.fo.e.getD q.val zeroE) *
          (Reading.gl.val o.H.fo.alpha - (q.val : Cb.Gl.E) * Reading.gl.val o.H.fo.theta -
            Blocks.ext (aC Dd q) (keyVec Dd t tb L0 wts q)
              (pt Reading.gl (o.H.fo.zk.getD q.val #[])))) +
        Reading.gl.val (padFo o.H.fo) - o.H.fo.cEnd.value Reading.gl
          (F.worldOf Reading.gl
            (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
              (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))).mask entry) = 0 :=
  b1Cut_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh Zs hT hx
    (maskCut_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hx) ds' T8 h8 t tb L0 wts hKv
    entry

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.stand_foLater
#print axioms ProofFile.Honest.K4.W.b1Cut_head
#print axioms ProofFile.Honest.K4.W.b1_thread_head
