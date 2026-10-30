-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LayersOfIndex.lean: CONDITIONAL.

What is here. THE TIE ON THE LAYERS' MATRICES (K4LayersTieAt, Law/W/LayersTie.lean) FROM THE ONE
HYPOTHESIS ON THE WEIGHTS (K4IndexIs, Law/IndexIs.lean). Where the lookup's caller reads the stored
table by the library's own filling of its five parameters (k3StoredAt,
Johnson/Desc/First/Look/K3LettersAt.lean: the message is the witness's cells' entries; the reader
answers with a cell inside the cells' shape and with 0 outside), what it reads at row a and column
b is the witness's cell inside the shape and 0 outside (the library's wOfE_conduit,
Johnson/Desc/First/Look/K3CallsWeights.lean). A script's witness has the script's cells. So under
K4IndexIs both sides of the tie are cut out of one matrix, the images of the index's matrix: at
every layer, also behind the model's last. Under h the five parameters are that filling by
definition (MgData.l3, Johnson/Desc/Sound/MgAll.lean).

  `wOfE_index`           what the caller reads off a script's witness is the index's matrix's image.
  `layersTie_conduit`    the tie at the library's filling; general in the other parameters.
  `layersTie_of_index`   **the tie at the parameters that h names.**
  `layersTie_thr`        **the same where the thread stands, from one clause under Vd.**

Not shown here. K4IndexIs IS A HYPOTHESIS: no example is shown here; what an input must be for it
to hold stands in Law/IndexIs.lean's head. h: the library's hypothesis on the public files; no
example of h is shown here. THE FULL SIZE ALONE (the script's cells have the full size's shape),
and in the last two the format's second hash function alone. A LAW, NOT A PART: its imports reach modules
under Johnson/Goal/ through h: no file that defines a part of the proof file's description
may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.IndexIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LayersTie
import Johnson.Desc.First.Look.K3CallsWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First.Look (Sent sigListCalls wOfE)
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (layMu wOfE_conduit)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X' : Type}

/-- **What the caller reads off a script's witness is the image of the index's matrix**, at every
row and column. hd: any list of challenges. CONDITIONAL: on hH. -/
theorem wOfE_index
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (Ds : Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (sigListCalls Ds rad xl.link).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (c : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn)
    {i : Cm.Idx} (hH : Holds (Q.cells v) i) :
    wOfE (layMu xl tl Ds rad (oWc OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull))
        wOfC OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull) seatT arr msgWc
        (Q.wit c v hd)) =
      fun a b => ((i.mat a b : ℤ) : Cb.Gl.E) := by
  funext a b
  refine (wOfE_conduit (x := xl) (tl := tl) (D := Ds) (rad := rad) seatT arr (Q.wit c v hd)
    a b).trans ?_
  by_cases hh : a < OnBytes.Flat.numsFull.rows ∧ b < P5J.colsAt OnBytes.Flat.numsFull
  · rw [dif_pos hh]
    exact hH.1 ⟨a, hh.1⟩ ⟨b, hh.2⟩
  · rw [dif_neg hh, hH.2 a b hh]
    exact Int.cast_zero.symm

/-- **The tie at the library's filling of the caller's five parameters.** CONDITIONAL: on hI. -/
theorem layersTie_conduit
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {weights : W₀ → Weights} (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2)
    (Ds : Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (sigListCalls Ds rad xl.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (g : ℕ)
    (c : Coins Bk) {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    (hI : K4IndexIs Q weights mm.st.input) :
    K4LayersTieAt Q weights xl tl Ds rad
      (oWc OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) wOfC
      OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull) seatT arr msgWc g c mm := by
  obtain ⟨i, hH, he⟩ := hI
  intro d l
  have e2 : (fun r c' =>
      algebraMap Cb.Gl.F Cb.Gl.E ((weights mm.st.input.w₀).entry r c')) =
      fun a b => ((i.mat a b : ℤ) : Cb.Gl.E) := by
    funext a b
    exact he a b
  rw [wOfE_index Q xl tl Ds rad seatT arr c mm.st.input (mm.st.heard ++ d) hH, e2]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE TIE AT THE PARAMETERS THAT h NAMES.** CONDITIONAL: on hI. h is named for its parameters
alone. -/
theorem layersTie_of_index (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {weights : W₀ → Weights} (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2)
    (g : ℕ) (c : Coins Bk) {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    (hI : K4IndexIs Q weights mm.st.input) :
    K4LayersTieAt Q weights xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW g c mm :=
  layersTie_conduit xl tl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1)
    h.𝔇.l3.arr g c hI

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Ky X₀ : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE TIE WHERE THE THREAD STANDS, FROM ONE CLAUSE UNDER Vd.** CONDITIONAL: on hI and hT. -/
theorem layersTie_thr {weights : W₀ → Weights} (hI : Vd w₁ → K4IndexIs Q weights w₁) {k : ℕ}
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (g : ℕ) :
    K4LayersTieAt Q weights xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW g c mm :=
  layersTie_of_index h xl tl g c
    (indexIs_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hI hT)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.wOfE_index
#print axioms ProofFile.Honest.K4.W.layersTie_conduit
#print axioms ProofFile.Honest.K4.W.layersTie_of_index
#print axioms ProofFile.Honest.K4.W.layersTie_thr
