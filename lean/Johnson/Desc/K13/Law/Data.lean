-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Data.lean: the premise of `atM3_goodIn_dec` on the written rounds, as a test
with code; and the piece's errors as shares. Statements with their proofs.
Main names:
  `bears d e`, `declaredB P dZ d0 ds`: the test, to be run on the written rounds of a real plan.
  `declared_of`: where it says yes, the stretch is `Declared`.
  `pieceM3_below`: where the library's condition on the numbers holds (`Maps.Held`,
    OnBytes/Flat/CarrySMaps.lean: at each round the typed count is a share of at most c of the
    round's typed values, and c with the sampler's bias and the gain from the bits of work is at
    most a bound), each written error of the piece is a share of at most that bound of the round's
    written challenges.
Used of `verify-on-bytes`: nothing.

What is not claimed. That the test says yes at every plan: an evaluation at two stored sets' public
files, a small and a full-size one, said yes, and four controls said no; no theorem says it of a
plan. That `Maps.Held` holds at a real plan's numbers: tried nowhere.

-/
import Johnson.Desc.K13.Law.Tries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open scoped ENNReal

variable {Cl W : Type}

/-- A written round bears an entry, and its kind is neither a sealing nor one of seeds. -/
def bears (d : RDT) (e : Fmt.Entry) : Bool :=
  decide (d.entry = e) && decide (d.kind ≠ .sealed) && decide (d.kind ≠ .seeds)

/-- What it says. -/
theorem bears_iff {d : RDT} {e : Fmt.Entry} (h : bears d e = true) : d.entry = e ∧ PlainKind d := by
  simp only [bears, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The test on the stretch's written rounds.** -/
def declaredB (P : Where) (dZ d0 : RDT) (ds : List RDT) : Bool :=
  decide (P.lin.kCol = ds.length) && bears dZ (sigmaEntry P) && bears d0 (epsEntry P) &&
    ds.all fun d => bears d (roundEntry P)

/-- Where it says yes, the stretch bears the entries that the block declares. -/
theorem declared_of {P : Where} {dZ d0 : RDT} {ds : List RDT} (h : declaredB P dZ d0 ds = true) :
    Declared P dZ d0 ds := by
  simp only [declaredB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, bears_iff h.1.1.2, bears_iff h.1.2, fun d hd => bears_iff (h.2 d hd)⟩

/-- The piece's errors as shares of the written challenges. -/
theorem pieceM3_below (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) {εs : ℝ≥0∞}
    (hH : (mapsOf dZ d0 ds).Held εs (errK P.rows ds.length)) :
    Err.Below (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).err εs := by
  obtain ⟨nZ, aZ, hZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, h0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  refine Maps.below_err _ (mapsOf_ok hZ h0 fun d hd => ?_) _ hH
  obtain ⟨he, hk⟩ := hD.vars d hd
  exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
    (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2

end VerifiableInference.Desc.K13.Law
