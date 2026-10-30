-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRowCap.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS ROW OF THE TABLE OF
JOINTS AT THE LEAST ERROR, AND THAT ERROR AGAINST THE CAP.

`k08_row` (Johnson/Desc/First/K8/LawRow.lean) holds at every error e that is at least the proved
block's count times the sampler's number. Here e is that product itself, and the piece's list of
errors is held against a share of the round's written verifier messages:
  `leastAt p s`: the proved block's count at the sizes s (the matrices that can be drawn, divided by
    2 ^ tau) times the sampler's number at the kind's declared round.
  `piece_err_below`: the piece's list of errors at `leastAt p s` is, round by round, a share of at
    most 2 ^ -tau (`Err.Below`, Iop/InteractiveOracleProof.lean). At every seat. `piece_err_cap`: at 128
    combinations: of at most 2 ^ -128.
  `k08_row_cap`: **THE ROW, AT AN ERROR OF AT MOST 2 ^ -128 A ROUND**, at 128 combinations.
Statements and proofs; nothing is counted anew: `hear_price_tau`
(Johnson/Desc/First/K8/LawParted.lean), `k08_row`.
Limits. Those of LawRow.lean: the row stands under letters. ONE REQUEST'S PRICE. There is no room:
`K08CountNoRoom` (Johnson/Desc/First/K8/LawCap.lean). That a place has 128 combinations is a
premise.

-/
import Johnson.Desc.First.K8.LawRow
import Johnson.Desc.First.K8.LawCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

/-- The proved block's count times the sampler's number. -/
def leastAt (p : Par) (s : Size) : ℕ :=
  (Fintype.card (Dr s) / 2 ^ s.tau) * (Run.bsRound .two (rdt p).entry (rdt p).kind).w

/-- The piece's list of errors at the least error is a share of at most 2 ^ -tau a round. -/
theorem piece_err_below {S Cl W : Type} {F : Frame} (seat : Seat S) (p : Par) (base : ℕ) {s : Size}
    (hf : Fits p s) :
    Err.Below (piece (Cl := Cl) (W := W) (F := F) seat p base (leastAt p s)).err
      ((2 : ℝ≥0∞)⁻¹ ^ s.tau) :=
  ⟨hear_price_tau hf, trivial⟩

/-- At 128 combinations: of at most 2 ^ -128. -/
theorem piece_err_cap {S Cl W : Type} {F : Frame} (seat : Seat S) (p : Par) (base : ℕ) {s : Size}
    (hf : Fits p s) (hτ : p.tau = 128) :
    Err.Below (piece (Cl := Cl) (W := W) (F := F) seat p base (leastAt p s)).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := piece_err_below (Cl := Cl) (W := W) (F := F) seat p base hf
  rwa [hf.tau.trans hτ] at h

/-- **The row, at an error of at most 2 ^ -128 a round.** -/
theorem k08_row_cap {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
    (entW : Wit Cells Tok MsgT → J → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
    (smpOf : S → (sigOf cs l).Smp)
    (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
      smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
    (Cl : Type) (F : Frame) (p : Par) (base : ℕ) (hseat : ∀ i, (seat' i).1 < base)
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0) (hτ : p.tau = 128) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).ior.red.KeepsW
      (fun a => (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onA a ∧ Extra a.1)
      (fun b => (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧
        TieAt (fun w a r c => Y.cellAt (entW w) a r c) a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧
        SmallAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w ∧
        DigitsAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).err ∧
    Err.Below (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)).err ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨k08_row Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base _ hseat hE hgt hu hP
      (Nat.le_refl _),
    piece_err_cap atS p base (fits_of_place hP) hτ⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.piece_err_below
#print axioms VerifiableInference.Desc.First.K8.piece_err_cap
#print axioms VerifiableInference.Desc.First.K8.k08_row_cap
