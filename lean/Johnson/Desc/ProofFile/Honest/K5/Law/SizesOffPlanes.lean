-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SizesOffPlanes.lean: SIZES THAT ARE THE FULL-SIZE EXAMPLE's OFF
THE PLANES GIVE THE SAME FILLING OF THE SEGMENTS' FIRST SENDINGS AS THE EXAMPLE's TYPED SIZES
(`Sz.ref`, Johnson/HonestTrace/Places.lean), AT EVERY ENTRY BUT THOSE OF A PLANE's ARRAY. General in
the sizes S, under ONE PUBLIC PREMISE: `planesAtRef S = Sz.ref`. THE PREMISE IS MET at `Sz.ref`, and
at the sizes at a public part (`Sz.ofPublic X`, Johnson/HonestTrace/SzOfPublic.lean) where the
verifier's own function returns X and 41 numbers of its parameter file are the reference's
(`Hd.PublicCore`, Johnson/Meaning/PublicCore.lean; in the goals' scope that holds by
`Hd.core_of_scope`). On public data and the readers' letters. IT PAYS NOTHING OF THE SCRIPT. One
definition, a helper; thirteen theorems.

What it is for. The frame's filling takes its sizes as one letter, chosen in front of the public
part. A law at `Sz.ref` speaks of it at that letter alone; as terms `Sz.ofPublic X` and `Sz.ref` are
never one (SizesApart.lean in this folder). With this file a law on the filling off the planes can
stand at every S that meets the premise.

Main names:
  `ask_but_planes`: **AT EVERY ENTRY BUT THOSE OF A PLANE's ARRAY the filling's call that asks first
    answers the same at S and at `Sz.ref`.** Its premise hP, on public data, says just that.
  ITS FIVE CASES: `ask_unseated`, `ask_where_none`, `ask_no_label` (at any two sizes: no size is
    read) · `ask_no_matrix` · `ask_off_planes`: a matrix's array off the planes. The sixth, a
    plane's array, is not said.
  `cellsVals_off_planes`: the values' size and element agree at the name of a matrix off the planes.
  `planesAtRef S`: THE HELPER: S with lmb, lmbA, lmbH, kT, NC set to `Sz.ref`'s.
  `planesAtRef_ref`, `planesAtRef_ofPublic`: THE TWO PAYERS OF THE PREMISE.
  `matAt_planesAtRef`, `arrayNo_planesAtRef`, `shape_planesAtRef`: at every S that setting turns
    neither `matAt`, nor `arrayNo`, nor the shape of a matrix that holds no planes.

How. The values (`cellsVals`, Johnson/Desc/ProofFile/Honest/K1/FirstData.lean) read of the sizes
`matAt`, whether `arrayNo` returns, and `shape`, no more; the filling (`laidData`,
Johnson/Desc/ProofFile/Honest/LaidData.lean) reads the sizes through the values alone. For
`planesAtRef_ofPublic`: the lines of the parameter file: `Hd.PublicCore.num`; the model's sizes:
`sizesOf_ppref` (Johnson/Top/SizesRef.lean); the length of the table of exponentials:
`Hd.eleven_of_core` (PublicCore.lean) with `L5.AttSized.u0` (Johnson/Road/Lane5AttAddr.lean).

Limits. NOTHING AT A PLANE's ARRAY (b, bA, bH): there the sizes' lmb, lmbA, lmbH, kT and NC are
read; the premise says nothing of S's own. The small example's sizes (`Sz.small`) do not meet the
premise (`planesAtRef_small_ne`). All is on the call that asks first: of `RowData.at_`, `lays`,
`entry` and `readyAt` nothing is stated. That hP holds at a given array is not proved here. That a
ground's W is such an X is not said here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.HonestTrace.SzOfPublic
import Johnson.Meaning.PublicCore
import Johnson.Top.SizesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.HonestTrace (Sz Seg MatName)
open ProofFile.Honest.K1 (labelNo cellsVals)

/-- **The helper**: S with the five fields that the planes' shapes alone read set to the full-size
example's. -/
def planesAtRef (S : Sz) : Sz :=
  { S with lmb := Sz.ref.lmb, lmbA := Sz.ref.lmbA, lmbH := Sz.ref.lmbH, kT := Sz.ref.kT,
           NC := Sz.ref.NC }

/-- That setting does not turn `matAt`. -/
theorem matAt_planesAtRef (S : Sz) (l mu : ℕ) : (planesAtRef S).matAt l mu = S.matAt l mu :=
  rfl

/-- Nor `arrayNo`. -/
theorem arrayNo_planesAtRef (S : Sz) (σ : Seg) (μ : MatName) :
    (planesAtRef S).arrayNo σ μ = S.arrayNo σ μ := rfl

/-- **Nor the shape of a matrix that holds no planes.** -/
theorem shape_planesAtRef (S : Sz) (σ : Seg) {μ : MatName} (hb : μ ≠ .b) (hbA : μ ≠ .bA)
    (hbH : μ ≠ .bH) : (planesAtRef S).shape σ μ = S.shape σ μ := by
  cases μ <;> first | rfl | exact absurd rfl hb | exact absurd rfl hbA | exact absurd rfl hbH

/-- **THE SIZES AT A PUBLIC PART, WITH THE PLANES' FIVE FIELDS SET, ARE THE FULL-SIZE EXAMPLE's.**
CONDITIONAL: hX: the verifier's own function returns X; C: the 41 numbers. -/
theorem planesAtRef_ofPublic {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok X)
    (C : OnBytes.Road.Hd.PublicCore X.P) : planesAtRef (Sz.ofPublic X) = Sz.ref := by
  have u : (OnBytes.Road.Hd.shapeA X 0).u0 = 2307 :=
    ((OnBytes.Road.Hd.eleven_of_core hX C (OnBytes.Road.Hd.npOf X.hS)).2.1 0 (by decide)).u0
  have e_lt : X.P.h.lt = 10 := C.num 1
  have e_L : X.P.h.L = 48 := C.num 2
  have e_ll : X.P.h.ll = 2 := C.num 3
  have e_d : X.P.h.d = 5120 := C.num 4
  have e_H : X.P.h.H = 40 := C.num 5
  have e_Gk : X.P.h.Gk = 8 := C.num 6
  have e_dh : X.P.h.dh = 128 := C.num 7
  have e_f : X.P.h.f = 16384 := C.num 8
  have e_fe : X.P.h.fe = 8192 := C.num 9
  have e_NE : X.P.h.NE = 128 := C.num 10
  have e_V : X.P.h.V = 202048 := C.num 11
  have e_la : X.P.h.la = 16 := C.num 12
  have e_lmaf : X.P.h.lmaf = 16 := C.num 13
  have e_NAf : X.P.h.NAf = 3 := C.num 14
  have e_lmad : X.P.h.lmad = 15 := C.num 15
  have e_NAd : X.P.h.NAd = 1 := C.num 16
  have e_lmar : X.P.h.lmar = 13 := C.num 17
  have e_lmq : X.P.h.lmq = 16 := C.num 18
  have e_lmx : X.P.h.lmx = 16 := C.num 19
  have e_lmhf : X.P.h.lmhf = 16 := C.num 20
  have e_NHf : X.P.h.NHf = 4 := C.num 21
  have e_lmhd : X.P.h.lmhd = 14 := C.num 22
  have e_lmhr : X.P.h.lmhr = 13 := C.num 23
  have e_lB : X.P.h.lB = 6 := C.num 34
  have e_lmS : X.P.h.lmS = 16 := C.num 37
  have e_lmh : X.P.h.lmh = 13 := C.num 38
  have e_lmo : X.P.h.lmo = 16 := C.num 39
  have e_NAs : X.P.h.NAs = 1 := C.num 40
  have eP : OnBytes.Flat.sizesOf X.P.h = Inst.Model.ppref :=
    VerifiableInference.OnPublicFiles.Flat.sizesOf_ppref (by rw [e_lt]; rfl) (by rw [e_V]; rfl)
      (by rw [e_L]; rfl) (by rw [e_d]; rfl) (by rw [e_H]; rfl) (by rw [e_Gk]; rfl)
      (by rw [e_dh]; rfl) (by rw [e_f]; rfl) (by rw [e_fe]; rfl) (by rw [e_NE]; rfl)
  unfold planesAtRef Sz.ofPublic Sz.ofHdr
  simp only [
    eP, u, e_lt, e_L, e_ll, e_Gk, e_dh, e_la, e_lmaf, e_NAf, e_lmad, e_NAd, e_lmar, e_lmq, e_lmx,
    e_lmhf, e_NHf, e_lmhd, e_lmhr, e_lB, e_lmS, e_lmh, e_lmo, e_NAs]
  rfl

/-- **The premise is met at the full-size example's sizes themselves.** -/
theorem planesAtRef_ref : planesAtRef Sz.ref = Sz.ref := rfl

/-- **The small example's sizes do not meet it**: they have lt = 6, the full-size example's 10, and
the helper leaves lt as it is. -/
theorem planesAtRef_small_ne : planesAtRef Sz.small ≠ Sz.ref := by
  intro e
  have k : (6 : ℕ) = 10 := congrArg Sz.lt e
  exact absurd k (by decide)

/-- **THE VALUES AGREE OFF THE PLANES.** CONDITIONAL: hSz: S is the full-size example's off the
planes; hn, hM: the name is that of matrix number mu of segment number l, which is μ in σ's list; μ
holds no planes. -/
theorem cellsVals_off_planes {S : Sz} (hSz : planesAtRef S = Sz.ref) {l mu : ℕ} {name : String}
    {σ : Seg} {μ : MatName}
    (hn : labelNo name = some mu) (hM : Sz.ref.matAt l mu = some (σ, μ)) (hb : μ ≠ .b)
    (hbA : μ ≠ .bA) (hbH : μ ≠ .bH) :
    (cellsVals S).size l name = (cellsVals Sz.ref).size l name ∧
      ∀ (R : Readers) (hd : List Fmt.Drawn) (i c : ℕ),
        (cellsVals S).val R hd l name i c = (cellsVals Sz.ref).val R hd l name i c := by
  have e := hSz
  have hM' : S.matAt l mu = some (σ, μ) := by
    rw [← matAt_planesAtRef, e]
    exact hM
  have hS : S.shape σ μ = Sz.ref.shape σ μ := by
    rw [← shape_planesAtRef _ σ hb hbA hbH, e]
  have hA : S.arrayNo σ μ = Sz.ref.arrayNo σ μ := by
    rw [← arrayNo_planesAtRef, e]
  constructor
  · simp [cellsVals, hn, hM', hM, hA, hS, Sz.packedShape, Sz.shapeNo]
  · intro R hd i c
    simp [cellsVals, hn, hM', hM, hS, OnBytes.HonestTrace.packedCells]

/-- **THE FILLING's CALL THAT ASKS FIRST ANSWERS THE SAME AT BOTH SIZES, OFF THE PLANES.**
CONDITIONAL: hSz: S is the full-size example's off the planes; hAd: the address's seat; hB: the way
back finds element (i, c) of the array A at (row, place); hn, hM: A's name is that of a matrix μ,
which holds no planes. -/
theorem ask_off_planes {S : Sz} (hSz : planesAtRef S = Sz.ref) (codes : OnBytes.Codes)
    (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    {Ad : MsgAddr} {l m row place mu i c : ℕ} {A : OnBytes.Params.ReqArray} {σ : Seg}
    {μ : MatName} (hAd : seat Ad = some (l, m))
    (hB : laidBack ly l m row place = some (A, i, c)) (hn : labelNo A.name = some mu)
    (hM : Sz.ref.matAt l mu = some (σ, μ)) (hb : μ ≠ .b) (hbA : μ ≠ .bA) (hbH : μ ≠ .bH)
    (R : Readers) (hd : List Fmt.Drawn) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData Sz.ref codes s ly seat heard).ask R hd Ad row place := by
  obtain ⟨hs, hv⟩ := cellsVals_off_planes hSz hn hM hb hbA hbH
  have hr : ∀ S : Sz, (cellsVals S).ready = fun _ _ => true := fun _ => rfl
  simp only [K1.firstData, RowData.ask, RowData.heardOk, RowData.at_, laidData, hAd, hB,
    Option.any_some, hs, hv, hr]

/-- **Where the way back finds no array the call reads no sizes.** At any two sizes. -/
theorem ask_where_none (S S' : Sz) (codes : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    {Ad : MsgAddr} {l m row place : ℕ} (hAd : seat Ad = some (l, m))
    (hB : laidBack ly l m row place = none) (R : Readers) (hd : List Fmt.Drawn) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData S' codes s ly seat heard).ask R hd Ad row place := by
  have hr : ∀ S : Sz, (cellsVals S).ready = fun _ _ => true := fun _ => rfl
  simp only [K1.firstData, RowData.ask, RowData.heardOk, RowData.at_, laidData, hAd, hB,
    Option.any_none, hr]

/-- **Nor at an address that is not seated.** At any two sizes. -/
theorem ask_unseated (S S' : Sz) (codes : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    {Ad : MsgAddr} (hAd : seat Ad = none) (R : Readers) (hd : List Fmt.Drawn) (row place : ℕ) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData S' codes s ly seat heard).ask R hd Ad row place := by
  have hr : ∀ S : Sz, (cellsVals S).ready = fun _ _ => true := fun _ => rfl
  simp only [K1.firstData, RowData.ask, RowData.heardOk, RowData.at_, laidData, hAd, hr]

/-- **Nor at an array whose name is no matrix's label.** At any two sizes. -/
theorem ask_no_label (S S' : Sz) (codes : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    {Ad : MsgAddr} {l m row place i c : ℕ} {A : OnBytes.Params.ReqArray}
    (hAd : seat Ad = some (l, m)) (hB : laidBack ly l m row place = some (A, i, c))
    (hn : labelNo A.name = none) (R : Readers) (hd : List Fmt.Drawn) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData S' codes s ly seat heard).ask R hd Ad row place := by
  have hs : (cellsVals S).size l A.name = (cellsVals S').size l A.name := by
    simp [cellsVals, hn]
  have hv : ∀ (R : Readers) (hd : List Fmt.Drawn) (i c : ℕ),
      (cellsVals S).val R hd l A.name i c = (cellsVals S').val R hd l A.name i c := by
    intro R hd i c
    simp [cellsVals, hn]
  have hr : ∀ S : Sz, (cellsVals S).ready = fun _ _ => true := fun _ => rfl
  simp only [K1.firstData, RowData.ask, RowData.heardOk, RowData.at_, laidData, hAd, hB,
    Option.any_some, hs, hv, hr]

/-- **At an array whose label's number has no matrix the two sizes' calls answer alike.**
CONDITIONAL: hSz, as above. -/
theorem ask_no_matrix {S : Sz} (hSz : planesAtRef S = Sz.ref) (codes : OnBytes.Codes)
    (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    {Ad : MsgAddr} {l m row place mu i c : ℕ} {A : OnBytes.Params.ReqArray}
    (hAd : seat Ad = some (l, m)) (hB : laidBack ly l m row place = some (A, i, c))
    (hn : labelNo A.name = some mu) (hM : Sz.ref.matAt l mu = none) (R : Readers)
    (hd : List Fmt.Drawn) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData Sz.ref codes s ly seat heard).ask R hd Ad row place := by
  have e := hSz
  have hM' : S.matAt l mu = none := by
    rw [← matAt_planesAtRef, e]
    exact hM
  have hs : (cellsVals S).size l A.name = (cellsVals Sz.ref).size l A.name := by
    simp [cellsVals, hn, hM', hM]
  have hv : ∀ (R : Readers) (hd : List Fmt.Drawn) (i c : ℕ),
      (cellsVals S).val R hd l A.name i c =
        (cellsVals Sz.ref).val R hd l A.name i c := by
    intro R hd i c
    simp [cellsVals, hn, hM', hM, OnBytes.HonestTrace.packedCells]
  have hr : ∀ S : Sz, (cellsVals S).ready = fun _ _ => true := fun _ => rfl
  simp only [K1.firstData, RowData.ask, RowData.heardOk, RowData.at_, laidData, hAd, hB,
    Option.any_some, hs, hv, hr]

/-- **AT EVERY ENTRY BUT THOSE OF A PLANE's ARRAY THE TWO FILLINGS' CALLS ANSWER ALIKE.**
CONDITIONAL: hSz: S is the full-size example's off the planes; hP, on public data: what the way back
finds at (Ad, row, place) is no plane's array. -/
theorem ask_but_planes {S : Sz} (hSz : planesAtRef S = Sz.ref) (codes : OnBytes.Codes)
    (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ)
    (Ad : MsgAddr) (row place : ℕ)
    (hP : ∀ (l m i c mu : ℕ) (A : OnBytes.Params.ReqArray) (σ : Seg) (μ : MatName),
      seat Ad = some (l, m) → laidBack ly l m row place = some (A, i, c) →
      labelNo A.name = some mu → Sz.ref.matAt l mu = some (σ, μ) → μ ≠ .b ∧ μ ≠ .bA ∧ μ ≠ .bH)
    (R : Readers) (hd : List Fmt.Drawn) :
    (K1.firstData S codes s ly seat heard).ask R hd Ad row place =
      (K1.firstData Sz.ref codes s ly seat heard).ask R hd Ad row place := by
  cases hAd : seat Ad with
  | none => exact ask_unseated _ _ codes s ly seat heard hAd R hd row place
  | some lm =>
    obtain ⟨l, m⟩ := lm
    cases hB : laidBack ly l m row place with
    | none => exact ask_where_none _ _ codes s ly seat heard hAd hB R hd
    | some w =>
      obtain ⟨A, i, c⟩ := w
      cases hn : labelNo A.name with
      | none => exact ask_no_label _ _ codes s ly seat heard hAd hB hn R hd
      | some mu =>
        cases hM : Sz.ref.matAt l mu with
        | none => exact ask_no_matrix hSz codes s ly seat heard hAd hB hn hM R hd
        | some x =>
          obtain ⟨σ, μ⟩ := x
          obtain ⟨h1, h2, h3⟩ := hP l m i c mu A σ μ hAd hB hn hM
          exact ask_off_planes hSz codes s ly seat heard hAd hB hn hM h1 h2 h3 R hd

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.matAt_planesAtRef
#print axioms ProofFile.Honest.K5.arrayNo_planesAtRef
#print axioms ProofFile.Honest.K5.shape_planesAtRef
#print axioms ProofFile.Honest.K5.planesAtRef_ofPublic
#print axioms ProofFile.Honest.K5.planesAtRef_ref
#print axioms ProofFile.Honest.K5.planesAtRef_small_ne
#print axioms ProofFile.Honest.K5.cellsVals_off_planes
#print axioms ProofFile.Honest.K5.ask_off_planes
#print axioms ProofFile.Honest.K5.ask_where_none
#print axioms ProofFile.Honest.K5.ask_unseated
#print axioms ProofFile.Honest.K5.ask_no_label
#print axioms ProofFile.Honest.K5.ask_no_matrix
#print axioms ProofFile.Honest.K5.ask_but_planes
