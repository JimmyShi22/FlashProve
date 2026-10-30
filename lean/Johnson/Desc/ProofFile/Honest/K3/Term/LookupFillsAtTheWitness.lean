-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupFillsAtTheWitness.lean: the honest side of the kind
"lookup" (K3): THE PREMISES AT ONE WITNESS of the lookup's exchange, whole, at the `Script`'s witness
`Script.wit Q k w heard`, sort by sort.

Why. The bundles on a run (`DigitsRunAll` and its sister at the calls) ask, as their last clause, one
of `AtDigits`, `AtAttention`, `AtLayers` (Honest/K3/Law/Thread/ExchangeOuts.lean) or `AtHead`
(ExchangeHeadAll.lean) at the witness. This file ends in these four, to the letter.

  `readingsAgreeAtTheBitsPlaces`            two readings that agree at the planes' cells and at "zero"
                                            agree at every bit's place
  `lookupFillsAtTheWitnessAtTheDigits`      ends in `AtDigits`
  `lookupFillsAtTheWitnessAtAttention`      ends in `AtAttention`
  `lookupFillsAtTheWitnessAtLayers`         ends in `AtLayers`
  `lookupFillsAtTheWitnessAtTheHead`        ends in `AtHead`

OF THE FOUR FIELDS ONE AND A HALF ARE SHOWN HERE: zero, and the bits' half of fills. The keys' half of
fills, masks and cubes are HYPOTHESES.
Field by field. zero: shown (by definition). fills: from `library`, the filling's law at the
library's key vectors and reading (the end of `fills_digits`, `fills_attention`, `fills_layers`,
`fills_head`, ExchangeFillAt.lean), turned to the witness's own reading: the bits by the named
premises on the `Script` and the trace (Honest/K3/Term/ScriptHoldsTheHonestValues.lean) and the public
test `planesAtB`; the keys by `sameJointKeys`, A HYPOTHESIS. masks, cubes: HYPOTHESES, in the fields'
own forms.

Limits. CONDITIONAL on all that; no named premise is shown here. General in the `Script`, the
public data and the letters. The challenges that the row's reader is asked at
(`heardByTheRow`) and those at which the witness is read (`heard`) are two letters without a tie.
Nothing is evaluated at any size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.WitnessReadingsAreTheTrace
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOuts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.First.Look.K3CallerCellsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (nuFrom atNo bNo)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent szOf enOf mkOf attLay layLay LayPub attRider layRider
  planesAtB planesAtB_iff)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider)
open VerifiableInference.OnPublicFiles (K3Letters attMs attMu attNu digMu digNu layMs layMu layNu headNu)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Exchange (FillsAt AtDigits AtAttention AtLayers AtHead)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-! ## 1 The bits' places -/

/-- **Two readings that agree at the cells of the planes' matrix (2 ^ lm rows, NC 2 ^ (kT + 5 - lm)
columns) and at the place "zero" agree at the place of every bit.** On the packing's two
inequalities. -/
theorem readingsAgreeAtTheBitsPlaces (shape : OnBytes.Model.Forest.Shape) (lm firstSlot : ℕ)
    (theta : GE) (fiveAtMost : 5 ≤ lm) (atMostTheTable : lm ≤ shape.kT + 5)
    (ν ν' : _root_.Fo.Pl → GE)
    (sameCells : ∀ row, row < 2 ^ lm → ∀ column, column < shape.NC * 2 ^ (shape.kT + 5 - lm) →
      ν' (.cell row column) = ν (.cell row column))
    (sameZero : ν' .zero = ν .zero) {u j : ℕ} (hu : u < 2 ^ shape.d) (hj : j < 32) :
    ν' ((_root_.Fo.numsF shape lm firstSlot theta).bAt u j) =
      ν ((_root_.Fo.numsF shape lm firstSlot theta).bAt u j) := by
  have ht : u / 2 ^ shape.cK < 2 ^ shape.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  show ν' (match FoNums.cellOf shape u j with
    | some x => .cell (FoNums.cellRC shape lm x).1 (FoNums.cellRC shape lm x).2
    | none => .zero) = ν (match FoNums.cellOf shape u j with
    | some x => .cell (FoNums.cellRC shape lm x).1 (FoNums.cellRC shape lm x).2
    | none => .zero)
  unfold FoNums.cellOf
  by_cases hc : u % 2 ^ shape.cK < shape.NC
  · rw [if_pos hc]
    obtain ⟨i1, i2⟩ := VerifiableInference.Desc.First.Look.cellRC_below shape lm fiveAtMost
      atMostTheTable _ _ _ ht hc hj
    exact sameCells _ i1 _ i2
  · rw [if_neg hc]
    exact sameZero

section
variable {Bk : ProverCoinCounts} {W Cells Tok : Type} {Q : Script Bk W Cells Tok MsgT} {D : Sent}
  {Lk : K3Letters Cells Tok} {valid : W → Prop} {challengesHeard : Nat} {x : PlaceL}
  {tl : HTailF2}

/-! ## 2 The digits -/

/-- **THE PREMISES AT ONE WITNESS, AT THE DIGITS, at the `Script`'s witness.** `library`: the end of
`fills_digits`, at an array `digits`; `digitsAreTheScripts`: that array is the one of the named
premise at the challenges at which the witness is read. No turn of the reading is needed: the bits
are read off the witness itself. -/
theorem lookupFillsAtTheWitnessAtTheDigits
    {digitsOfTheTrace : W → List Fmt.Drawn → ℕ → ℕ → Cb.Gl.F}
    (arrays : ScriptHoldsTheDigitArrays Q D Lk valid challengesHeard x tl digitsOfTheTrace)
    (fromPieces : Fo.ZPlan.FromPieces tl) (s : Site) (a : Ask) (theta : GE)
    (heardByTheRow : List Fmt.Drawn) (mask : Nat → GE) (k : Coins Bk) {w : W}
    {heard : List Fmt.Drawn} (isValid : valid w) (enough : challengesHeard ≤ heard.length)
    (shapeIsTheTails : s.shape = tl.f9) (planesRowsAreThirtyTwo : s.p.lm = 5)
    {digits : ℕ → ℕ → Cb.Gl.F} {libraryKeys : Nat → Nat → GE} {libraryReading : _root_.Fo.Pl → GE}
    (library : FillsAt s a (lookZ tl digits) libraryKeys libraryReading theta heardByTheRow)
    (digitsAreTheScripts : digits = digitsOfTheTrace w heard)
    (sameJointKeys : ∀ n, n < 2 ^ s.shape.v →
      OnBytes.Ends.jointKey s.shape
        (Cb.Fo.forK Cb.Gl.E
          (OnBytes.DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (Cb.Fo.zext (digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr
            (Q.wit k w heard)))) theta n =
        OnBytes.Ends.jointKey s.shape libraryKeys theta n)
    (masks : ∀ j, j < s.p.first + s.at_.face.slots →
      digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr (Q.wit k w heard) (.mask j) =
        mask j) :
    AtDigits s D Lk x tl a theta heardByTheRow mask (Q.wit k w heard) := by
  refine ⟨rfl, ⟨lookZ tl digits, library.reads,
    fun n hn => (library.keys n hn).trans (sameJointKeys n hn).symm, fun u j hu hj => ?_⟩, masks⟩
  rw [shapeIsTheTails, planesRowsAreThirtyTwo, digitsAreTheScripts]
  exact digitsBitsAreReadOffTheWitness fromPieces arrays k isValid enough theta s.p.first
    (by rw [← shapeIsTheTails]; exact hu) hj

/-! ## 3 The calls -/

variable {traceMatrices : W → OnBytes.Road.Mats ℤ} {X : OnBytes.Model.Verify.Public}
  {cell : ℕ → String → ℕ → ℕ → Cb.Gl.F} {link : ℕ}

/-- **THE PREMISES AT ONE WITNESS, AT ATTENTION's CALLS, at the `Script`'s witness.** `library`: the
end of `fills_attention`. `planesNumber`, `planesInside`: on public data. `cellsAreTheIntegers`: the
trace's reader by labels answers, at the planes' cells, the casts of the named premises' integers. -/
theorem lookupFillsAtTheWitnessAtAttention
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (A : OnBytes.Attention.Shape) (s : Site)
    (a : Ask) (theta : GE) (heardByTheRow : List Fmt.Drawn) (mask : Nat → GE) (k : Coins Bk)
    {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length)
    {L : LookIn} {libraryKeys : Nat → Nat → GE} {libraryMask : Nat → GE}
    (library : FillsAt s a L libraryKeys (nuFrom X cell link libraryMask) theta heardByTheRow)
    (planesNumber : bNo X link = A.cf.NAs + 2)
    (planesInside : planesAtB tl s.shape s.p.lm (A.cf.NAs + 2) = true)
    (cellsAreTheIntegers : ∀ row, row < 2 ^ s.p.lm →
      ∀ column, column < s.shape.NC * 2 ^ (s.shape.kT + 5 - s.p.lm) →
        atNo X cell link (A.cf.NAs + 2) row column =
          ((traceMatrices w (A.cf.NAs + 2) row column : ℤ) : Cb.Gl.E))
    (sameJointKeys : ∀ n, n < 2 ^ s.shape.v →
      OnBytes.Ends.jointKey s.shape
        (Cb.Fo.forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) ()
          (Cb.Fo.zext (attMu x tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr
            (Q.wit k w heard)))) theta n =
        OnBytes.Ends.jointKey s.shape libraryKeys theta n)
    (masks : ∀ j, j < s.p.first + s.at_.face.slots →
      attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard)
        (.mask j) = mask j)
    (cubes : Cb.Rider.OnCubes (attRider x A tl D Lk.rad Iop.extNone Unit).g
      (attRider x A tl D Lk.rad Iop.extNone Unit).f ()
      (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard))) :
    AtAttention s D Lk x tl a theta heardByTheRow mask (Q.wit k w heard) A := by
  obtain ⟨h5, hlm, hN, hm, hk⟩ := planesAtB_iff.1 planesInside
  refine ⟨rfl, ⟨L, fillsAtTurnsWhereBitsAreRead library _ _ sameJointKeys fun u j hu hj =>
    readingsAgreeAtTheBitsPlaces s.shape s.p.lm s.p.first theta h5 hlm _ _
      (fun row hr column hc => ?_) ?_ hu hj⟩, masks, cubes⟩
  · rw [attentionReadingIsTheTraceCell packed small A k isValid enough hN
      (Nat.lt_of_lt_of_le hc hk) (Nat.lt_of_lt_of_le hr hm)]
    show _ = atNo X cell link (bNo X link) row column
    rw [planesNumber, cellsAreTheIntegers row hr column hc]
  · rfl

/-- **THE PREMISES AT ONE WITNESS, AT THE LAYERS' CALLS, at the `Script`'s witness.** `library`: the
end of `fills_layers`. The rest as at attention. -/
theorem lookupFillsAtTheWitnessAtLayers
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x tl traceMatrices)
    (small : TraceCellsAreSmall valid tl traceMatrices) (q : LayPub) (s : Site)
    (a : Ask) (theta : GE) (heardByTheRow : List Fmt.Drawn) (mask : Nat → GE) (k : Coins Bk)
    {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length)
    {L : LookIn} {libraryKeys : Nat → Nat → GE} {libraryMask : Nat → GE}
    (library : FillsAt s a L libraryKeys (nuFrom X cell link libraryMask) theta heardByTheRow)
    (planesNumber : bNo X link = (OnBytes.Model.Layer.matIx q.y).iB)
    (planesInside : planesAtB tl s.shape s.p.lm (OnBytes.Model.Layer.matIx q.y).iB = true)
    (cellsAreTheIntegers : ∀ row, row < 2 ^ s.p.lm →
      ∀ column, column < s.shape.NC * 2 ^ (s.shape.kT + 5 - s.p.lm) →
        atNo X cell link (OnBytes.Model.Layer.matIx q.y).iB row column =
          ((traceMatrices w (OnBytes.Model.Layer.matIx q.y).iB row column : ℤ) : Cb.Gl.E))
    (sameJointKeys : ∀ n, n < 2 ^ s.shape.v →
      OnBytes.Ends.jointKey s.shape
        (Cb.Fo.forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl Lk.nr Lk.nc) ()
          (Cb.Fo.zext (layMu x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
            (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW (Q.wit k w heard)))) theta n =
        OnBytes.Ends.jointKey s.shape libraryKeys theta n)
    (masks : ∀ j, j < s.p.first + s.at_.face.slots → layNu x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW (Q.wit k w heard) (.mask j) = mask j)
    (cubes : Cb.Rider.OnCubes
      (layRider x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).g
      (layRider x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).f ()
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard))) :
    AtLayers s D Lk x tl a theta heardByTheRow mask (Q.wit k w heard) q := by
  obtain ⟨h5, hlm, hN, hm, hk⟩ := planesAtB_iff.1 planesInside
  refine ⟨rfl, ⟨L, fillsAtTurnsWhereBitsAreRead library _ _ sameJointKeys fun u j hu hj =>
    readingsAgreeAtTheBitsPlaces s.shape s.p.lm s.p.first theta h5 hlm _ _
      (fun row hr column hc => ?_) ?_ hu hj⟩, masks, cubes⟩
  · rw [layersReadingIsTheTraceCell packed small q k isValid enough hN
      (Nat.lt_of_lt_of_le hc hk) (Nat.lt_of_lt_of_le hr hm)]
    show _ = atNo X cell link (bNo X link) row column
    rw [planesNumber, cellsAreTheIntegers row hr column hc]
  · rfl

end

/-- **THE PREMISES AT ONE WITNESS, AT THE HEAD's CALLS, at the `Script`'s witness.** `library`: the
end of `fills_head`. The tail is the public part's own, as `AtHead` has it. token: the reply's. The
rest as at attention. -/
theorem lookupFillsAtTheWitnessAtTheHead [Sizes] [Policy] [Request] {Bk : ProverCoinCounts}
    {W Cells Tok : Type} {Q : Script Bk W Cells Tok MsgT} {D : Sent} {Lk : K3Letters Cells Tok}
    {valid : W → Prop} {challengesHeard : Nat} {x : PlaceL} (Z : Pub)
    {traceMatrices : W → OnBytes.Road.Mats ℤ} {X : OnBytes.Model.Verify.Public}
    {cell : ℕ → String → ℕ → ℕ → Cb.Gl.F} {link : ℕ}
    (packed : ScriptHoldsThePackedTraceCells Q D Lk valid challengesHeard x Z.p.X.H.tl
      traceMatrices)
    (small : TraceCellsAreSmall valid Z.p.X.H.tl traceMatrices) (adr : HeadAdr) (s : Site)
    (a : Ask) (theta : GE) (heardByTheRow : List Fmt.Drawn) (mask : Nat → GE) (token : Nat)
    (k : Coins Bk) {w : W} {heard : List Fmt.Drawn} (isValid : valid w)
    (enough : challengesHeard ≤ heard.length)
    {L : LookIn} {libraryKeys : Nat → Nat → GE} {libraryMask : Nat → GE}
    (library : FillsAt s a L libraryKeys (nuFrom X cell link libraryMask) theta heardByTheRow)
    (planesNumber : bNo X link = adr.iB)
    (planesInside : planesAtB Z.p.X.H.tl s.shape s.p.lm adr.iB = true)
    (cellsAreTheIntegers : ∀ row, row < 2 ^ s.p.lm →
      ∀ column, column < s.shape.NC * 2 ^ (s.shape.kT + 5 - s.p.lm) →
        atNo X cell link adr.iB row column =
          ((traceMatrices w adr.iB row column : ℤ) : Cb.Gl.E))
    (sameJointKeys : ∀ n, n < 2 ^ s.shape.v →
      OnBytes.Ends.jointKey s.shape
        (Cb.Fo.forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns Z.p.X.H.tl Lk.nr Lk.nc) token
          (Cb.Fo.zext (layMu x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
            (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW (Q.wit k w heard)))) theta n =
        OnBytes.Ends.jointKey s.shape libraryKeys theta n)
    (masks : ∀ j, j < s.p.first + s.at_.face.slots →
      headNu adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW (Q.wit k w heard) (.mask j) = mask j)
    (cubes : Cb.Rider.OnCubes
      (headRider adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).g
      (headRider adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).f token
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW
        (Q.wit k w heard))) :
    AtHead Z s D Lk adr x a theta heardByTheRow mask token (Q.wit k w heard) := by
  obtain ⟨h5, hlm, hN, hm, hk⟩ := planesAtB_iff.1 planesInside
  refine ⟨rfl, ⟨L, fillsAtTurnsWhereBitsAreRead library _ _ sameJointKeys fun u j hu hj =>
    readingsAgreeAtTheBitsPlaces s.shape s.p.lm s.p.first theta h5 hlm _ _
      (fun row hr column hc => ?_) ?_ hu hj⟩, masks, cubes⟩
  · rw [headReadingIsTheTraceCell packed small adr k isValid enough hN
      (Nat.lt_of_lt_of_le hc hk) (Nat.lt_of_lt_of_le hr hm)]
    show _ = atNo X cell link (bNo X link) row column
    rw [planesNumber, cellsAreTheIntegers row hr column hc]
  · rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.readingsAgreeAtTheBitsPlaces
#print axioms ProofFile.Honest.K3.Term.lookupFillsAtTheWitnessAtTheDigits
#print axioms ProofFile.Honest.K3.Term.lookupFillsAtTheWitnessAtAttention
#print axioms ProofFile.Honest.K3.Term.lookupFillsAtTheWitnessAtLayers
#print axioms ProofFile.Honest.K3.Term.lookupFillsAtTheWitnessAtTheHead
