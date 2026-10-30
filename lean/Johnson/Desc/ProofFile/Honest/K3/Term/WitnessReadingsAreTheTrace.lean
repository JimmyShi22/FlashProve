-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT.
Johnson/Desc/ProofFile/Honest/K3/Term/WitnessReadingsAreTheTrace.lean: the honest side of the kind
"lookup" (K3): from the four named premises on the `Script` and the trace
(Honest/K3/Term/ScriptHoldsTheHonestValues.lean) to the lookup's own readings of the witness
`Script.wit Q k w heard`.

Why. The premises at one witness of the lookup's exchange (`AtDigits`, `AtAttention`, `AtLayers`,
Honest/K3/Law/Thread/ExchangeOuts.lean; `AtHead`, ExchangeHeadAll.lean) speak of the readings
`digNu`, `attNu`, `layNu`, `headNu`; the fillings' laws (`fills_layers` and its sisters,
ExchangeFillAt.lean) speak of the trace's readings. This file has the half "same cells" of the way
between them, the clause "zero", and the two named readings of the calls' riders.

  `fillsAtTurnsWhereBitsAreRead`            `FillsAt.turn` asking "same reading" only at the bits' places
  `digitsReadingIsZeroAtThePlaceZero`, `attentionReading…`, `layersReading…`, `headReading…`
                                            the clause "zero", at every witness
  `matricesCutToTheSizes`                   integer matrices, 0 outside the smallness test's sizes
  `matricesCutToTheSizesInside`, `matricesCutToTheSizesOfZeroOutside`
  `symbolsHaveTheTraceCellsBehindThem`      premises 1 + 2 give the library's `BaseAt`
  `attentionCellsAreTheTrace`               the library's `CellsAre`
  `attentionEntryIsTheTraceCell`            every cell's entry, at attention's reading
  `attentionReadingIsTheTraceCell`          `attNu … (.cell row column)`, inside the planes' matrix
  `layersMatricesAreTheTrace`               the library's `MatsAre` (layers and head: one reading)
  `layersReadingIsTheTraceCell`             `layNu … (.cell row column)`, inside the planes' matrix
  `headReadingIsTheTraceCell`               `headNu … (.cell row column)`, inside the planes' matrix
  `digitsReadingAtACellIsTheCountsArray`    `digNu … (.cell row column)` is an entry of BZ
  `digitsBitsAreReadOffTheWitness`          premise 3 gives the bits' clause of `FillsAt` at `digNu`
  `storedEntriesAreTheIndexWeights`         premise 4 gives the caller's entries of the weights
  `layersWeightsAreTheIndexWeights`         the library's `WeightsAre`

Limits. CONDITIONAL ON THE NAMED PREMISES, WHICH NO FILE SHOWS. General in the `Script`, the public
data, the letters, the place and the tail: nothing is evaluated at any size. Not here: the keys'
identities, the riders' cubes, the mask row, that a bit's place lies inside the planes' matrix.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeMg
import Johnson.Desc.First.Look.K3HeadGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls symAt szOf enOf zsOf MatsAre
  WeightsAre CellsAre LayPub digList wOfE matsOfE msgLay msgAtt lyW lyCell cellJ enCell finOf
  lay_mats_cast attCells_cast)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)
open VerifiableInference.OnPublicFiles (K3Letters attMs attMu attNu digMu digNu layMs layMu layNu headNu)
open OnBytes.HonestTrace (LaidBZ virtZ)
open Cb.Pv.Tail (BaseAt baseAt_of_packs uniq_gl)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Exchange (FillsAt)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-! ## 1 The narrower turn -/

/-- **The three sentences on a filling pass to a reading that agrees AT THE BITS' PLACES, and to key
vectors whose joint vector is the same at every index below 2 ^ s.shape.v.** `FillsAt.turn`
(Honest/K3/Law/Thread/ExchangeMg.lean) asks the two readings to agree at every cell whatever: outside
the planes' matrix the witness's reading is 0 and the trace's need not be. -/
theorem fillsAtTurnsWhereBitsAreRead {s : Site} {a : Ask} {L : LookIn} {kv : Nat → Nat → GE}
    {ν : _root_.Fo.Pl → GE} {theta : GE} {heard : List Fmt.Drawn}
    (h : FillsAt s a L kv ν theta heard) (kv' : Nat → Nat → GE) (ν' : _root_.Fo.Pl → GE)
    (sameJointKeys : ∀ x, x < 2 ^ s.shape.v → OnBytes.Ends.jointKey s.shape kv' theta x =
      OnBytes.Ends.jointKey s.shape kv theta x)
    (sameBits : ∀ u j, u < 2 ^ s.shape.d → j < 32 →
      ν' ((_root_.Fo.numsF s.shape s.p.lm s.p.first theta).bAt u j) =
        ν ((_root_.Fo.numsF s.shape s.p.lm s.p.first theta).bAt u j)) :
    FillsAt s a L kv' ν' theta heard :=
  ⟨h.reads, fun x hx => (h.keys x hx).trans (sameJointKeys x hx).symm,
    fun u j hu hj => (h.bits u j hu hj).trans (sameBits u j hu hj).symm⟩

/-! ## 2 The clause "zero": at every witness -/

section zero
variable {Cells Tok : Type} (x : PlaceL) (tl : HTailF2) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (arr : ℕ → ℕ → ℕ) (v : Wit Cells Tok MsgT)

theorem digitsReadingIsZeroAtThePlaceZero (seatT : Fin (digList x D rad).length → ℕ × ℕ) :
    digNu x tl D rad seatT arr v .zero = 0 := rfl

theorem attentionReadingIsZeroAtThePlaceZero (A : OnBytes.Attention.Shape)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) :
    attNu x A tl D rad seatT arr v .zero = 0 := rfl

theorem layersReadingIsZeroAtThePlaceZero (q : LayPub) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (msgW : Wit Cells Tok MsgT → oW.Msg) :
    layNu x q tl D rad oW wOf nr nc seatT arr msgW v .zero = 0 := rfl

theorem headReadingIsZeroAtThePlaceZero [Sizes] [Policy] [Request] (adr : HeadAdr)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (msgW : Wit Cells Tok MsgT → oW.Msg) :
    headNu adr x tl D rad oW wOf nr nc seatT arr msgW v .zero = 0 := rfl

end zero

/-! ## 3 Integer matrices, cut to the sizes -/

/-- Integer matrices (number in the link's list, row, column), with 0 outside the sizes of the
link's smallness test: the library's `zsOf` at the matrices' own entries. -/
def matricesCutToTheSizes (tl : HTailF2) (matrices : OnBytes.Road.Mats ℤ) : OnBytes.Road.Mats ℤ :=
  zsOf (szOf tl) fun matrix column row => matrices matrix.val row.val column.val

theorem matricesCutToTheSizesInside (tl : HTailF2) (matrices : OnBytes.Road.Mats ℤ)
    {matrix row column : ℕ} (matrixInside : matrix < (szOf tl).NM)
    (columnInside : column < (szOf tl).k matrix) (rowInside : row < (szOf tl).m matrix) :
    matricesCutToTheSizes tl matrices matrix row column = matrices matrix row column := by
  unfold matricesCutToTheSizes zsOf
  rw [dif_pos ⟨matrixInside, columnInside, rowInside⟩]

theorem matricesCutToTheSizesOfZeroOutside (tl : HTailF2) (matrices : OnBytes.Road.Mats ℤ)
    (zeroOutside : ∀ matrix row column, ¬ (matrix < (szOf tl).NM ∧
      column < (szOf tl).k matrix ∧ row < (szOf tl).m matrix) → matrices matrix row column = 0) :
    matricesCutToTheSizes tl matrices = matrices := by
  funext matrix row column
  unfold matricesCutToTheSizes zsOf
  by_cases h : matrix < (szOf tl).NM ∧ column < (szOf tl).k matrix ∧ row < (szOf tl).m matrix
  · rw [dif_pos h]
  · rw [dif_neg h, zeroOutside _ _ _ h]

/-! ## 4 The calls -/

section calls
variable {Bk : ProverCoinCounts} {W Cells Tok : Type} {Q : Script Bk W Cells Tok MsgT} {D : Sent}
  {Lk : K3Letters Cells Tok} {valid : W → Prop} {challengesHeard : Nat} {x : PlaceL}
  {tl : HTailF2} {traceMatrices : W → OnBytes.Road.Mats ℤ}

/-- **PREMISES 1 AND 2 GIVE THE LIBRARY's `BaseAt`**: behind the committed symbols that the calls'
callers read off the honest witness stand the trace's integers. -/
theorem symbolsHaveTheTraceCellsBehindThem
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length) :
    BaseAt (symAt D.codes (sigListCalls D Lk.rad x.link) (seatCalls D x.link) tl
        (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard)))
      (fun matrix column row => traceMatrices w matrix.val row.val column.val) :=
  baseAt_of_packs Cb.Gl.p (uniq_gl rfl rfl) (fun matrix column row => small w isValid matrix column row)
    (fun matrix column symbolRow => packed k w heard isValid enough matrix column symbolRow)

/-- **Attention: the library's named reading `CellsAre`**, at the trace's integers cut to the
sizes. -/
theorem attentionCellsAreTheTrace
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (A : OnBytes.Attention.Shape)
    (k : Coins Bk) {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length) :
    CellsAre x A tl D Lk.rad
      (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard))
      (matricesCutToTheSizes tl (traceMatrices w)) :=
  attCells_cast _ _ (symbolsHaveTheTraceCellsBehindThem packed small k isValid enough)

/-- **Attention: every cell's entry**, at every number, row and column. -/
theorem attentionEntryIsTheTraceCell
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length)
    (matrix row column : ℕ) :
    attMu x tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard)
        (enCell x.ns tl matrix row column) =
      ((matricesCutToTheSizes tl (traceMatrices w) matrix row column : ℤ) : Cb.Gl.E) := by
  have B := symbolsHaveTheTraceCellsBehindThem packed small k isValid enough
  show msgAtt D.codes (sigListCalls D Lk.rad x.link) (seatCalls D x.link) tl x.ns _
    (enCell x.ns tl matrix row column) = _
  unfold matricesCutToTheSizes enCell cellJ zsOf
  by_cases h : matrix < (szOf tl).NM ∧ column < (szOf tl).k matrix ∧ row < (szOf tl).m matrix
  · rw [dif_pos h, dif_pos h]
    exact B.2.2 ⟨⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩⟩
  · rw [dif_neg h, dif_neg h]
    exact Int.cast_zero.symm

/-- **"SAME CELLS" AT ATTENTION**: inside the planes' matrix (number A.cf.NAs + 2 of the link's
list) the reading of a cell's place is the trace's integer. -/
theorem attentionReadingIsTheTraceCell
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (A : OnBytes.Attention.Shape)
    (k : Coins Bk) {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length) {row column : ℕ}
    (matrixInside : A.cf.NAs + 2 < (szOf tl).NM)
    (columnInside : column < (szOf tl).k (A.cf.NAs + 2))
    (rowInside : row < (szOf tl).m (A.cf.NAs + 2)) :
    attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard)
        (.cell row column) =
      ((traceMatrices w (A.cf.NAs + 2) row column : ℤ) : Cb.Gl.E) := by
  rw [← matricesCutToTheSizesInside tl (traceMatrices w) matrixInside columnInside rowInside]
  exact attentionEntryIsTheTraceCell packed small k isValid enough _ _ _

/-- **Layers and head: the library's named reading `MatsAre`**, at the trace's integers cut to the
sizes. The head's caller reads the cells by the layers' reading. -/
theorem layersMatricesAreTheTrace
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length) :
    MatsAre x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard))
      (matricesCutToTheSizes tl (traceMatrices w)) :=
  lay_mats_cast _ _ (symbolsHaveTheTraceCellsBehindThem packed small k isValid enough)

/-- **"SAME CELLS" AT THE LAYERS**: inside the planes' matrix the reading of a cell's place is the
trace's integer. -/
theorem layersReadingIsTheTraceCell
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (q : LayPub) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length)
    {row column : ℕ} (matrixInside : (OnBytes.Model.Layer.matIx q.y).iB < (szOf tl).NM)
    (columnInside : column < (szOf tl).k (OnBytes.Model.Layer.matIx q.y).iB)
    (rowInside : row < (szOf tl).m (OnBytes.Model.Layer.matIx q.y).iB) :
    layNu x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc (fun j => Lk.seat x.link false j.1) Lk.arr
        Lk.msgW (Q.wit k w heard) (.cell row column) =
      ((traceMatrices w (OnBytes.Model.Layer.matIx q.y).iB row column : ℤ) : Cb.Gl.E) := by
  rw [← matricesCutToTheSizesInside tl (traceMatrices w) matrixInside columnInside rowInside]
  exact congrFun (congrFun (congrFun
    (layersMatricesAreTheTrace packed small k isValid enough) _) row) column

/-- **"SAME CELLS" AT THE HEAD**: inside the planes' matrix the reading of a cell's place is the
trace's integer. -/
theorem headReadingIsTheTraceCell [Sizes] [Policy] [Request]
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (adr : HeadAdr) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length)
    {row column : ℕ} (matrixInside : adr.iB < (szOf tl).NM)
    (columnInside : column < (szOf tl).k adr.iB) (rowInside : row < (szOf tl).m adr.iB) :
    headNu adr x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc (fun j => Lk.seat x.link false j.1) Lk.arr
        Lk.msgW (Q.wit k w heard) (.cell row column) =
      ((traceMatrices w adr.iB row column : ℤ) : Cb.Gl.E) := by
  rw [← matricesCutToTheSizesInside tl (traceMatrices w) matrixInside columnInside rowInside]
  exact congrFun (congrFun (congrFun
    (layersMatricesAreTheTrace packed small k isValid enough) _) row) column

end calls

/-! ## 5 The digits -/

/-- **At the digits the reading of a cell's place IS an entry of the array BZ**, read as the matrix
with one row a plane: at every witness. -/
theorem digitsReadingAtACellIsTheCountsArray {Cells Tok : Type} (x : PlaceL) (tl : HTailF2)
    (D : Sent) (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (v : Wit Cells Tok MsgT) (row column : ℕ) :
    digNu x tl D rad seatT arr v (.cell row column) =
      virtZ tl (fun arrayRow arrayColumn =>
        digMu x D rad seatT arr v (enOf x.arrays (tl.ix.BZ, arrayRow, arrayColumn))) row column :=
  rfl

/-- **PREMISE 3 GIVES THE BITS' CLAUSE OF `FillsAt` AT THE WITNESS's OWN READING**: the bits of the
digits' filling `lookZ` are what `digNu` reads at their places. `lookZ_bit`'s own proof
(Honest/K3/Law/MeetsNamed.lean). CONDITIONAL on `Fo.ZPlan.FromPieces tl` (public) too. -/
theorem digitsBitsAreReadOffTheWitness {Bk : ProverCoinCounts} {W Cells Tok : Type}
    {Q : Script Bk W Cells Tok MsgT} {D : Sent} {Lk : K3Letters Cells Tok} {valid : W → Prop}
    {challengesHeard : Nat} {x : PlaceL} {tl : HTailF2}
    {digitsOfTheTrace : W → List Fmt.Drawn → ℕ → ℕ → Cb.Gl.F}
    (fromPieces : Fo.ZPlan.FromPieces tl)
    (arrays : ScriptHoldsTheDigitArrays Q D Lk valid challengesHeard x tl digitsOfTheTrace)
    (k : Coins Bk) {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length) (theta : Cb.Gl.E) (firstSlot : ℕ) {u j : ℕ}
    (hu : u < 2 ^ tl.f9.d) (hj : j < 32) :
    (lookZ tl (digitsOfTheTrace w heard)).bit u j =
      digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr (Q.wit k w heard)
        ((_root_.Fo.numsF tl.f9 5 firstSlot theta).bAt u j) := by
  have own : LaidBZ tl (inExt (digitsOfTheTrace w heard)) (bzIn tl (digitsOfTheTrace w heard)) :=
    fun _ _ _ _ => rfl
  exact (OnBytes.HonestTrace.bz_plane own hu hj).trans
    (OnBytes.HonestTrace.Look.bAt_plane tl.f9 5 firstSlot theta
      (OnBytes.HonestTrace.hitsZ tl (inExt (digitsOfTheTrace w heard))) (le_refl 5)
      (Nat.le_add_left 5 _)
      (digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr (Q.wit k w heard))
      (fun r hr c hc => OnBytes.HonestTrace.virtZ_plane fromPieces
        (arrays.countsBits k w heard isValid enough) r hr c hc) rfl hu hj).symm

/-! ## 6 The weights -/

section weights
variable {Bk : ProverCoinCounts} {W Cells Tok : Type} {Q : Script Bk W Cells Tok MsgT}
  {Lk : K3Letters Cells Tok} {valid : W → Prop} {challengesHeard : Nat}
  {weightEntry : W → ℕ → ℕ → Cb.Gl.F}

/-- **PREMISE 4 GIVES THE CALLER's ENTRIES OF THE COMMITTED MATRIX**, at every row and column.
CONDITIONAL: `weightEntry w` is the cast of the integer matrix `indexMatrix`, which is 0 outside the
letters' `nr` rows and `nc` columns. `wOfE_stored`'s proof (Johnson/Desc/Kinds/Law/HeadWeightsMeet.lean),
general in the letters. -/
theorem storedEntriesAreTheIndexWeights
    (stored : ScriptCellsAreTheIndexWeights Q Lk valid challengesHeard weightEntry) (x : PlaceL)
    (tl : HTailF2) (D : Sent) (k : Coins Bk) {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length) (indexMatrix : Inst.Model.Mat)
    (isCast : ∀ row column, weightEntry w row column = ((indexMatrix row column : ℤ) : Cb.Gl.F))
    (zeroOutside : ∀ row column, ¬ (row < Lk.nr ∧ column < Lk.nc) → indexMatrix row column = 0)
    (row column : ℕ) :
    wOfE (msgLay x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard))) row column = ((indexMatrix row column : ℤ) : Cb.Gl.E) := by
  unfold wOfE lyW finOf
  by_cases ha : row < Lk.nr
  · by_cases hb : column < Lk.nc
    · rw [dif_pos ha, dif_pos hb]
      show Lk.wOf (Lk.msgW (Q.wit k w heard)) row column = _
      rw [stored k w heard isValid enough, isCast, map_intCast]
    · rw [dif_pos ha, dif_neg hb, zeroOutside row column (fun e => hb e.2)]
      simp [msgLay]
  · rw [dif_neg ha, zeroOutside row column (fun e => ha e.1)]
    simp [msgLay]

/-- **The library's named reading `WeightsAre`**, at every group. -/
theorem layersWeightsAreTheIndexWeights
    (stored : ScriptCellsAreTheIndexWeights Q Lk valid challengesHeard weightEntry) (x : PlaceL)
    (tl : HTailF2) (D : Sent) (group : ℕ) (k : Coins Bk) {w : W} {heard : List Fmt.Drawn}
    (isValid : valid w) (enough : challengesHeard ≤ heard.length) (indexMatrix : Inst.Model.Mat)
    (isCast : ∀ row column, weightEntry w row column = ((indexMatrix row column : ℤ) : Cb.Gl.F))
    (zeroOutside : ∀ row column, ¬ (row < Lk.nr ∧ column < Lk.nc) → indexMatrix row column = 0) :
    WeightsAre x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc group
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard)) indexMatrix := by
  have e : wOfE (msgLay x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard))) = fun a b => ((indexMatrix a b : ℤ) : Cb.Gl.E) := by
    funext a b
    exact storedEntriesAreTheIndexWeights stored x tl D k isValid enough indexMatrix isCast
      zeroOutside a b
  intro l
  rw [e]

end weights

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.fillsAtTurnsWhereBitsAreRead
#print axioms ProofFile.Honest.K3.Term.digitsReadingIsZeroAtThePlaceZero
#print axioms ProofFile.Honest.K3.Term.attentionReadingIsZeroAtThePlaceZero
#print axioms ProofFile.Honest.K3.Term.layersReadingIsZeroAtThePlaceZero
#print axioms ProofFile.Honest.K3.Term.headReadingIsZeroAtThePlaceZero
#print axioms ProofFile.Honest.K3.Term.matricesCutToTheSizes
#print axioms ProofFile.Honest.K3.Term.matricesCutToTheSizesInside
#print axioms ProofFile.Honest.K3.Term.matricesCutToTheSizesOfZeroOutside
#print axioms ProofFile.Honest.K3.Term.symbolsHaveTheTraceCellsBehindThem
#print axioms ProofFile.Honest.K3.Term.attentionCellsAreTheTrace
#print axioms ProofFile.Honest.K3.Term.attentionEntryIsTheTraceCell
#print axioms ProofFile.Honest.K3.Term.attentionReadingIsTheTraceCell
#print axioms ProofFile.Honest.K3.Term.layersMatricesAreTheTrace
#print axioms ProofFile.Honest.K3.Term.layersReadingIsTheTraceCell
#print axioms ProofFile.Honest.K3.Term.headReadingIsTheTraceCell
#print axioms ProofFile.Honest.K3.Term.digitsReadingAtACellIsTheCountsArray
#print axioms ProofFile.Honest.K3.Term.digitsBitsAreReadOffTheWitness
#print axioms ProofFile.Honest.K3.Term.storedEntriesAreTheIndexWeights
#print axioms ProofFile.Honest.K3.Term.layersWeightsAreTheIndexWeights
