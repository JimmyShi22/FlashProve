-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeySeatsLe.lean: A SEAT AT LARGER ERRORS. A piece's errors say, round by round,
how many values of the challenge may be bad. A law that is proved at some errors holds at every
larger list of errors. So a seat can be filled at a piece whose errors somebody else has named (a
cap, say), from a law whose own errors lie below them.

What is said.
  `Piece.withErr p e`: the piece p with the errors e in the place of its own.
  `good_of_le`: if p with smaller errors e is good between two rows, so is p.
  `seat_of_le`: the same of a seat.
  `seat_of_relLawLe`: A SEAT IS FILLED BY A PROVED TYPED BLOCK WHOSE WRITTEN COUNTS LIE BELOW THE
    PIECE'S ERRORS: `seat_of_relLawAt` (Johnson/Desc/Sound/KeySeatsAt.lean) with "the piece's
    errors are the written counts along the maps" weakened to "the written counts along the maps
    lie below the piece's errors".

Limits. Rules. That some law's counts lie below some cap is shown nowhere here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeySeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Err Reduction Doomed)

variable {S S₀ P Cl W : Type} {F : Frame}

/-- The piece with other errors. -/
def Piece.withErr (p : Piece (ckP .two) F S Cl W) (e : Err (uLT (ckP .two) p.ds)) :
    Piece (ckP .two) F S Cl W :=
  ⟨p.b, p.base, p.ds, p.back, p.ext, e⟩

/-- **Good at smaller errors is good.** -/
theorem good_of_le (p : Piece (ckP .two) F S Cl W) (e : Err (uLT (ckP .two) p.ds))
    (he : Err.le e p.err) (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (h : ((p.withErr e).bk on on' R R').Good) : (p.bk on on' R R').Good :=
  ⟨h.point, h.isLocal, fun a ha => Doomed.mono_err _ he (h.know a ha)⟩

/-- **A seat at larger errors.** -/
theorem seat_of_le (εs : ℝ≥0∞) (A : JointRow S F) (ps : List (Piece (ckP .two) F S Cl W))
    (rs : List (JointRow S F)) (i : ℕ)
    (h : ∀ p, ps[i]? = some p → Err.Below p.err εs ∧ ∃ e : Err (uLT (ckP .two) p.ds),
      Err.le e p.err ∧
      ((p.withErr e).bk (keyRowAt A rs i).on (keyRowAt A rs (i + 1)).on
        (fun a _ => (keyRowAt A rs i).rel a) (fun a _ => (keyRowAt A rs (i + 1)).rel a)).Good) :
    SeatGood εs A ps rs i := fun p hp => by
  obtain ⟨hε, e, he, hg⟩ := h p hp
  exact ⟨good_of_le p e he _ _ _ _ hg, hε⟩

/-- **A seat is filled by a proved typed block whose written counts lie below the piece's
errors.** -/
theorem seat_of_relLawLe (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F)) (i : ℕ)
    (b : Block S₀ Cl) {JA JB : JK} (k : BK JA JB) (rdA : (P × S₀) × F.E.Str → JA.X × JA.E.Str)
    (hk : k.Good) (hB : Nonempty JB.W)
    (h : ∀ p, ps[i]? = some p → p.b = liftP P (below b) ∧ ∃ M : Maps p.ds k.R.red.shape,
      M.OK ∧ viewWordsBelowPrime ⟨p.back, []⟩ = true ∧ Err.le (M.err k.err) p.err ∧ Err.Below p.err εs ∧
      ∀ q : P, RelLaw b p.base p.ds p.back k M (fun a => rdA ((q, a.1), a.2))
        ((keyRowAt A rs i).atP q) ((keyRowAt A rs (i + 1)).atP q)) : SeatGood εs A ps rs i :=
  seat_of_le εs A ps rs i fun p hp => by
    obtain ⟨hb, M, hM, hback, he, hε, hl⟩ := h p hp
    refine ⟨hε, M.err k.err, he, ?_⟩
    have e : liftP P (below b) = below (liftP P b) := (below_lift _ _ b).symm
    have hp' : p.withErr (M.err k.err) =
        ⟨below (liftP P b), p.base, p.ds, p.back, p.ext, M.err k.err⟩ := by
      unfold Piece.withErr
      rw [hb, e]
    rw [hp']
    exact goodOfRelAt (⟨below (liftP P b), p.base, p.ds, p.back, p.ext, M.err k.err⟩ :
        Piece (ckP .two) F (P × S₀) Cl W) k (fun _ => M.carry) rdA _ _ hk hB
      (relAt_of_relLaw (liftP P b) p.base p.ds p.back k M rdA _ _ p.ext hM hback
        (relLaw_liftAll b p.base p.ds p.back k M rdA _ _ hl))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.good_of_le
#print axioms VerifiableInference.Desc.Sound.seat_of_le
#print axioms VerifiableInference.Desc.Sound.seat_of_relLawLe
