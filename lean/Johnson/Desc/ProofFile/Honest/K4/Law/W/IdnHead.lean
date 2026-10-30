-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IdnHead.lean: CONDITIONAL.

What is here. The field idn of the hypothesis `ItemRight` (Law/W/SlotsOfStand.lean): the seventeen
identities of each norm at the cells of the matrices that are unpacked from the data: OUT OF THE
THREAD in front of the member of the feed-forward layers' own rounds (sub-protocol K4), at the
thread with the library's own values laid in (`lettersHead`, Honest/Thread/FirstHead.lean), at every
continuation of the challenges heard. Two statements are joined: the item `Item.constr m .idn` is
open there and the thread holds its sentence (Law/W/OpenAtHead.lean); that sentence is the library's
`partG` at the group's list (Law/W/IdnHotAt.lean), which gives the identities (`idnHold_full`,
Johnson/Road/K4/W/IdnOfField.lean). One statement with its proof: calls.

  `k4_idn_mats`   **`IdnHold` at every continuation**, at matrices that are the images of the
      library's list, said outright (hM): Johnson/Road/K4/W/MatsOfSyms.lean has hM from an equation
      of symbols and the library's `MatsAre`.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT : Thr is a hypothesis. IT ENDS IN FRONT OF THE
MEMBER's STEP: at the challenges that the run has heard there, and at a free matrix; the field idn
stands behind the step: Law/W/FieldsAtStand.lean carries it there. hM: THE MATRICES ARE THE IMAGES
OF THE LIST THAT THE LIBRARY READS OFF THE WITNESS FOR THE GROUP: a hypothesis, and the heaviest; in
a later group the list's matrix of the stream that comes in is the group before's. hi: the Script's
cells hold an index. hi and hM speak of a run's coins and input and of no state: `indexIs_thr`
(Law/IndexIs.lean) has hi from one hypothesis under the thread's clause that the input is valid;
`matsAre_head` (Law/W/MatsAreHead.lean) has the caller's matrices as the images of that list at
every witness, and `mats_of_are` (Johnson/Road/K4/W/MatsOfSyms.lean) has hM at the matrices off the
data from that and an equation of symbols. Fu: `FullAt` (Law/W/FullHead.lean has it behind the step
from a stand). The side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth). Of h together with A, hT, hi, hg, hm, Fu and hM no example is known to us. THE
FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on
completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 19 modules under Johnson/Goal/ and at 4 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 23 is not counted: all the numbers are floors. They come with
h and with the files that it joins. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpenAtHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IdnHotAt
import Johnson.Road.K4.W.ListOfPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (Mats sclOf cellsOf cellsAt)
open OnBytes.Road.Rows.Norms (NormField EmbField castM)
open OnBytes.Road.K4 (AtK4)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.W (IdnHold FullAt idnHold_full)
open OnBytes.Maker (WholeD)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SAME AT MATRICES THAT ARE THE IMAGES OF THE LIBRARY's LIST.** Mm ds': the matrices at the
continuation ds'. No packing is asked: hM says outright that they are the images of the list that
the library reads off the witness for the group. CONDITIONAL: on h, A, hT, hi, hg, hm, Fu and hM. -/
theorem k4_idn_mats
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {i : Cm.Idx} (hi : Holds (Q.cells mm.st.input) i) {g : ℕ} (hg : g < 12) (hm : m = 2 * g)
    {hS : Layer.Shape} {Dm : Dim} {o : Own} (Fu : FullAt (P5J.At.X Zp) g hS Dm o)
    (Mm : List Fmt.Drawn → Mats Cb.Gl.E)
    (hM : ∀ ds', Mm ds' =
      castM ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ ds'))).MG g)) :
    ∀ ds', IdnHold (scl := sclOf hS o.v.sc o.v.g o.v.y.Lam) Dm
      (cellsOf Dm (cellsAt o.v.y (Mm ds'))) := by
  subst hm
  intro ds'
  obtain ⟨x, pI⟩ := part_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ c mm.st.input s
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
    (mm.st.heard ++ ds') hi hg (p := .idn) (by decide)
    (idn_item_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT ds')
  have pI' : NormField (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).layers.sc (P5J.At.X Zp).y g
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ ds'))).MG g) i.mat x ∧
      EmbField (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).layers.sc (P5J.At.X Zp).y g
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ ds'))).MG g) i.mat x := pI
  exact idnHold_full Fu pI'.1 (by rw [hM ds'])

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_idn_mats
