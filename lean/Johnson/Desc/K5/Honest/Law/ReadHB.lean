-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadHB.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "the index's cells are bits" (`sHB`,
Johnson/Desc/K5/Honest/Index.lean), read in a field, is the library's sumcheck for the bits with 4
variables for a bit's number (Cb/Pv/Att/Bits.lean: `bitWt 4`, `bitCube 4`, `bitSum 4`): its weights,
its two hidden maps at ANY point, its sum over the cube; and it has what the masked sumcheck's
prover asks of a summand. A name for a piece of the summand's text, and statements with their
proofs.

Main names:
  `hbA`, `sHB_even`, `sHB_odd`, `sHB_terms`   a name for the first hidden map; the summand's maps
                  are it, and it minus 1
  `hbA_reads`     the first map reads as the multilinear extension of `bitCube 4`
  `sHB_reads`     `ProductReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the summand
  `sHB_total`     the sum over the cube reads as `bitSum 4`
  `sHB_tame`      `Summand.Tame` at 4 coefficients a variable and 3 in Y (degree at most 2)

`sHB_even`, `sHB_odd` and `sHB_terms` have no premise. Every other statement is conditional. The
premises, and who is meant to show each:
`Sized`, `Planned`: public, the caller's. `Drawn`: the round that draws many elements has been heard
with all its elements: the caller's. `BitPts`: the library's challenges p are the prover's, read, in
the fields o'', tk, tbg and tbi, which are all that the weight reads: it holds at `pubOf`
(Johnson/Desc/K5/Honest/Law/Cells.lean, Weights.lean). That a token has at most 16 bits: public, a
numeral of the plan's. No cell is asked to be a bit: that the sum is 0 is not this file's matter.
Limits. Nothing here says that a premise holds at any place.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Weights
import Johnson.Desc.K5.Honest.Law.ProductsLaw
import Cb.Pv.Att.Mean.Reads
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo geoOf eqTab wAtIndex wCells)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The hidden maps, under a name -/

/-- The first hidden map, pair b, at the point x: cell k of the index for k below lt. The text of
`sHB`. -/
def hbA (g : Geo) (w : K5In) (x : Array E) (b : ℕ) : E :=
  sumTo g.lt fun k => mulE ((eqTab (x.extract (g.lt + g.lgk) (g.lt + g.lgk + 4))).getD k zeroE)
    (under (eqTab (x.extract g.lt (g.lt + g.lgk))) fun hk =>
      under (eqTab (x.extract 0 g.lt)) fun i => w.ibit k b hk i)

theorem sHB_even (P : Pub5) (w : K5In) (c : Chal) (x : List E) (b : ℕ) :
    (sHB P w c).endAt x (2 * b) = hbA P.g w x.toArray b := by
  show (if 2 * b % 2 == 0 then hbA P.g w x.toArray (2 * b / 2)
    else subE (hbA P.g w x.toArray (2 * b / 2)) oneE) = _
  rw [Nat.mul_mod_right, Nat.mul_div_cancel_left b (by norm_num)]
  rfl

theorem sHB_odd (P : Pub5) (w : K5In) (c : Chal) (x : List E) (b : ℕ) :
    (sHB P w c).endAt x (2 * b + 1) = subE (hbA P.g w x.toArray b) oneE := by
  show (if (2 * b + 1) % 2 == 0 then hbA P.g w x.toArray ((2 * b + 1) / 2)
    else subE (hbA P.g w x.toArray ((2 * b + 1) / 2)) oneE) = _
  rw [show (2 * b + 1) % 2 = 1 by omega, show (2 * b + 1) / 2 = b by omega]
  rfl

theorem sHB_terms (P : Pub5) (w : K5In) (c : Chal) (x : List E) :
    (sHB P w c).terms x = pairsOf P.g.NP
      (wCells P.g { (heardAt P c fun _ => none) with cells := sumAt x.toArray }) := rfl

/-! ## The first map, read -/

variable {P : Pub5} (H : Sized P) (w : K5In)
include H

/-- **The first map reads as the multilinear extension of the library's map on the cube**, at any
point of the sumcheck's length. -/
theorem hbA_reads (hK : P.D.lT ≤ 2 ^ 4) {x : Array E} (hx : x.size = P.D.lT + P.D.lg + 4)
    (b : ℕ) :
    ρ.val (hbA P.g w x b) =
      Blocks.ext (P.D.lT + P.D.lg + 4) (Cb.Pv.Att.bitCube 4 P.D (tOf ρ w) b) (pt ρ x) := by
  obtain ⟨_, k2⟩ := read_eqTab_cut ρ x (a := P.D.lT + P.D.lg) (n := 4) (by omega)
  have z1 : (x.extract 0 P.D.lT).size = P.D.lT := by
    rw [size_extract_le x (by omega)]
    omega
  have z2 : (x.extract P.D.lT (P.D.lT + P.D.lg)).size = P.D.lg := by
    rw [size_extract_le x (by omega)]
    omega
  rw [Cb.Pv.Att.bitCube_ext P.D (tOf ρ w) 4 hK b (pt ρ x)]
  unfold hbA
  rw [H.lt, read_sumTo]
  refine sum_congr rfl fun k hk => ?_
  rw [ρ.mul]
  refine congrArg₂ (· * ·) (k2 k (lt_of_lt_of_le (mem_range.mp hk) hK)) ?_
  show ρ.val (under (eqTab (x.extract P.D.lT (P.D.lT + P.D.lg))) fun hk =>
    under (eqTab (x.extract 0 P.D.lT)) fun i => w.ibit k b hk i) = _
  rw [read_under_eq ρ z2 (v := sh (pt ρ x) P.D.lT) fun j hj =>
    pt_extract ρ x P.D.lT (P.D.lT + P.D.lg) j (by omega)]
  unfold rd2 eqT
  rw [Dim.T_eq]
  refine sum_congr rfl fun g _ => ?_
  rw [read_under_eq ρ z1 (v := pt ρ x) fun j hj => by
    rw [pt_extract ρ x 0 P.D.lT j (by omega), Nat.zero_add], mul_sum]
  exact sum_congr rfl fun i _ => by rw [read_ibit]; ring

/-! ## The summand -/

variable (Pl : Planned P) {c : Chal} (Dr : Drawn P c) (hK : P.D.lT ≤ 2 ^ 4) {p : Pub K}
  (I : BitPts ρ P c p)
include Pl Dr hK I

/-- **The summand's weights and maps read as the library's.** -/
theorem sHB_reads : ProductReads ρ (sHB P w c) P.D.nb (Cb.Pv.Att.bitWt 4 P.D p)
    (fun b => Blocks.ext (P.D.lT + P.D.lg + 4) (Cb.Pv.Att.bitCube 4 P.D (tOf ρ w) b))
    (fun b ξ => Blocks.ext (P.D.lT + P.D.lg + 4) (Cb.Pv.Att.bitCube 4 P.D (tOf ρ w) b) ξ - 1) := by
  have hs : ∀ x : List E, x.length = (sHB P w c).vars →
      x.toArray.size = P.D.lT + P.D.lg + 4 := fun x hx => by
    rw [List.size_toArray, hx]
    show P.g.lt + P.g.lgk + 4 = _
    rw [H.lt]
    rfl
  refine ⟨⟨_, sHB_terms P w c, fun x hx b hb => ?_⟩, fun x hx b _ => ?_, fun x hx b _ => ?_⟩
  · exact cells_reads ρ H Pl Dr I x.toArray (le_of_eq (hs x hx).symm) hb
  · rw [sHB_even]
    exact hbA_reads ρ H w hK (hs x hx) b
  · rw [sHB_odd, ρ.sub, ρ.one, hbA_reads ρ H w hK (hs x hx) b]

/-- **The sum over the cube reads as the library's sum of the sumcheck for the bits.** -/
theorem sHB_total : ρ.val (sHB P w c).total = Cb.Pv.Att.bitSum 4 P.D p (tOf ρ w) := by
  have hv : (sHB P w c).vars = P.D.lT + P.D.lg + 4 := by
    show P.g.lt + P.g.lgk + 4 = _
    rw [H.lt]
    rfl
  rw [(sHB_reads ρ H w Pl Dr hK I).total, hv]
  unfold Cb.Pv.Att.bitSum
  refine sum_congr rfl fun X hX => sum_congr rfl fun b _ => ?_
  rw [Blocks.ext_cubePt _ _ (mem_range.mp hX)]

omit I in
/-- **The summand has what the masked sumcheck's prover asks of it.** The statement names no
challenges of the library's, so those made of the prover's are laid, at a made-up point of the
lookup's. It stands where the round that draws many elements has been heard; of the summand at
earlier challenges nothing is said. -/
theorem sHB_tame : (sHB P w c).Tame ρ (List.replicate (sHB P w c).vars 4) 2 := by
  have hv : (sHB P w c).vars = P.D.lT + P.D.lg + 4 := by
    show P.g.lt + P.g.lgk + 4 = _
    rw [H.lt]
    rfl
  refine (sHB_reads ρ H w Pl Dr hK (bitPts_pubOf ρ P c fun _ => 0)).tame (fun b _ => ?_)
    (fun b _ => ?_) (fun b _ => ?_)
  · rw [hv]
    exact fun ξ => Cb.Pv.Att.bitWtExt P.D _ 4 b ξ
  · rw [hv]
    exact extOfCube_ext _ _
  · rw [hv]
    intro ξ
    rw [Blocks.ext_sub, Blocks.ext_const, extOfCube_ext _ _ ξ]

end H2K5.Honest

#print axioms H2K5.Honest.sHB_even
#print axioms H2K5.Honest.sHB_odd
#print axioms H2K5.Honest.sHB_terms
#print axioms H2K5.Honest.hbA_reads
#print axioms H2K5.Honest.sHB_reads
#print axioms H2K5.Honest.sHB_total
#print axioms H2K5.Honest.sHB_tame
