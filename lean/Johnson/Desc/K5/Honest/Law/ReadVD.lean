-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadVD.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "the value product on the diagonal" (`sVD`,
Johnson/Desc/K5/Honest/Products.lean), read in a field, is the library's step s12
(Inst/Model/Att/Sums.lean): its weights, its two hidden maps at ANY point, its sum over the cube;
and it has what the masked sumcheck's prover asks of a summand. Two names for pieces of the
summand's text, and statements with their proofs.

Main names:
  `vdA`, `vdB`, `sVD_eq`   names for the two hidden maps; the summand is their sum of products
  `eqT_tiles`     the equality weight of a token is that of its tile times that of its place
  `vdA_reads`, `vdB_reads`   the maps read as the library's `Aext`, `Bext` of step s12
  `sVD_reads`     `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the summand
  `sVD_total`     the sum over the cube reads as `sumPhi` of step s12
  `sVD_tame`      `Summand.Tame` at 4 coefficients a variable and 3 in Y (degree at most 2)

All but `pointD_at`, `eqT_tiles` are conditional. Premises, and who is meant to show each: `Sized`,
`Planned`, `PairsAre`: public, the caller's. `divIn P c = some Dv`: that the verifier's function of
the points returns: tests on lengths alone, the caller's. `DivPts`: the lookup's points, read, are
the library's: from `KeyPtsAre` and `UnitIs` by `divPts_of`
(Johnson/Desc/K5/Honest/Law/Weights.lean). The library's challenges p are any at which `DivPts`
holds: step s12 reads z and th alone.
Limits. Nothing here says that a premise holds at any place.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Weights
import Johnson.Desc.K5.Honest.Law.ProductsLaw
import Johnson.Desc.K5.Honest.Law.TilesKit
import Cb.Pv.Att.Mean.ReadsOn
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 DivP Heard geoOf eqTab ofNat tok lastCoords pointD
  wDivision wOn KeyPtsAre UnitIs)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The two hidden maps, under names -/

/-- The first hidden map, piece b, at the point r: the softmax weights. The text of `sVD`. -/
def vdA (g : Geo) (w : K5In) (d : DivP) (r : Array E) (b : ℕ) : E :=
  weightAt w true (pointD g { d with vpd := { d.vpd with r := r } })
    (pairOf g (d.pwW.getD b ⟨0, 0, zeroE⟩))

/-- The second: the batching element plus the values. ec: the table of equality weights of the
channel point. -/
def vdB (g : Geo) (w : K5In) (d : DivP) (ec r : Array E) (b : ℕ) : E :=
  addE d.gam (overHeads g r fun hk =>
    atTokens (tok g (eqTab (r.extract g.lgk (g.lgk + g.lnT))) (lastCoords r g.lB)) ec
      fun pos ch => w.v (d.pwW.getD b ⟨0, 0, zeroE⟩).lam hk pos ch)

/-- Where `divIn` returns, the summand is the sum of products of these two maps. -/
theorem sVD_eq (P : Pub5) (w : K5In) (c : Chal) {Dv : DivIn} (h : divIn P c = some Dv) :
    sVD P w c = ofProducts ((cut P.x).getD (iVD P.x) 3 - 3) P.g.NP
      (fun r => wOn P.g Dv.pw Dv.zW { Dv.h with on := sumAt r })
      (vdA P.g w Dv.d) (vdB P.g w Dv.d Dv.ec) := by
  unfold sVD
  simp only [h]
  rfl

/-- The point of the region on the diagonal, with r in the place of the sumcheck's challenges. -/
theorem pointD_at (g : Geo) (d : DivP) (r : Array E) :
    pointD g { d with vpd := { d.vpd with r := r } } =
      r.extract 0 (g.lgk + g.lnT) ++ d.zilo g ++ lastCoords r g.lB := rfl

/-- **The equality weight of a token** is that of its tile times that of its place in the tile. -/
theorem eqT_tiles (D : Dim) (v : ℕ → K) (i : ℕ) :
    eqT D v i = Blocks.eqN D.lB 0 (sh v (D.lP + 1)) (i % D.B) *
      Blocks.eqN (D.lP + 1) 0 v (i / D.B) := by
  have e : 2 ^ D.lB * (i / D.B) + i % D.B = i := Nat.div_add_mod i D.B
  have s := Blocks.eqN_split (D.lP + 1) D.lB v (i / D.B) (c := i % D.B) (Nat.mod_lt i D.B_pos)
  rw [e] at s
  show Blocks.eqN (D.lP + 1 + D.lB) 0 v i = _
  rw [s, Cb.Pv.Att.eqN_sh, mul_comm]

/-! ## The maps, read -/

variable {P : Pub5} (H : Sized P) (w : K5In)
include H

/-- **The first map reads as the library's**, at any point of the step's length. -/
theorem vdA_reads {d : DivP} (pr : PairsAre P.g d.pwW) (C : Calls) (p : Pub K)
    (nLo : (d.zilo P.g).size = P.D.lB) (hlo : ∀ k < P.D.lB, pt ρ (d.zilo P.g) k = yi' P.D C p.z k)
    {r : Array E} (hr : r.size = Step.s12.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (vdA P.g w d r b) = Aext P.D C p (tOf ρ w) .s12 b (pt ρ r) := by
  have hr' : r.size = P.D.lg + (P.D.lP + 1) + P.D.lB := hr
  unfold vdA
  rw [pr.pair hb, read_weightAt, pointD_at, H.lnT]
  have s1 : (r.extract 0 (P.g.lgk + (P.D.lP + 1))).size = P.D.lg + (P.D.lP + 1) :=
    size_extract_le r (by show P.D.lg + (P.D.lP + 1) ≤ r.size; omega)
  have s3 : (lastCoords r P.g.lB).size = P.D.lB :=
    last_size r (by show P.D.lB ≤ r.size; omega)
  have sz : (r.extract 0 (P.g.lgk + (P.D.lP + 1)) ++ d.zilo P.g ++ lastCoords r P.g.lB).size =
      P.D.lD := by
    rw [Array.size_append, Array.size_append, s1, nLo, s3]
    rfl
  rw [sz]
  refine (Cb.Pv.Att.aext12 P.D C p (tOf ρ w) b (pt ρ r) _ ?_ ?_ ?_).symm
  · intro k hk
    rw [pt_append, if_pos (by rw [Array.size_append, s1, nLo]; omega), pt_append,
      if_pos (by rw [s1]; exact hk),
      pt_extract ρ r 0 _ k (by show 0 + k < P.D.lg + (P.D.lP + 1); omega), Nat.zero_add]
  · intro k hk
    rw [pt_append, if_pos (by rw [Array.size_append, s1, nLo]; omega), pt_append,
      if_neg (by rw [s1]; omega), s1, Nat.add_sub_cancel_left]
    exact hlo k hk
  · intro k hk
    have e : r.size - P.g.lB + k = P.D.lg + (P.D.lP + 1) + k := by
      show r.size - P.D.lB + k = _
      omega
    rw [pt_append, if_neg (by rw [Array.size_append, s1, nLo]; omega), Array.size_append, s1,
      nLo, Nat.add_sub_cancel_left, pt_last ρ r (n := P.g.lB) (by show P.D.lB ≤ r.size; omega) hk,
      e]

/-- **The second map reads as the library's.** zc: the channel point, which agrees with the
library's. -/
theorem vdB_reads {d : DivP} (pr : PairsAre P.g d.pwW) (C : Calls) (p : Pub K)
    (hg : ρ.val d.gam = p.th) {zc : Array E} (hc : zc.size = P.D.ln)
    (hn : ∀ k < P.D.ln, pt ρ zc k = yn P.D C p.z k) {r : Array E}
    (hr : r.size = Step.s12.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (vdB P.g w d (eqTab zc) r b) = Bext P.D C p (tOf ρ w) .s12 b (pt ρ r) := by
  have hr' : r.size = P.D.lg + (P.D.lP + 1) + P.D.lB := hr
  obtain ⟨_, t2⟩ := read_eqTab_cut ρ r (a := P.D.lg) (n := P.D.lP + 1) (by omega)
  obtain ⟨k1, k2⟩ := tok_reads ρ H (hi := eqTab (r.extract P.g.lgk (P.g.lgk + (P.D.lP + 1))))
    (lo := lastCoords r P.g.lB) (wt := Blocks.eqN (P.D.lP + 1) 0 (sh (pt ρ r) P.D.lg))
    (v := sh (sh (pt ρ r) P.D.lg) (P.D.lP + 1))
    (fun I hI => t2 I (by rw [Cb.Pv.Att.nBlk_pow]; exact hI))
    (last_size r (by show P.D.lB ≤ r.size; omega))
    (fun j hj => by
      have e : r.size - P.g.lB + j = P.D.lg + (P.D.lP + 1 + j) := by
        show r.size - P.D.lB + j = _
        omega
      rw [pt_last ρ r (n := P.g.lB) (by show P.D.lB ≤ r.size; omega) hj, e]
      rfl)
  rw [Cb.Pv.Att.bext12]
  unfold vdB
  rw [ρ.add, hg, lam_of pr hb, H.lnT]
  congr 1
  exact read_rd3 ρ H (by omega) (fun _ _ => rfl) k1 (fun i hi => by rw [k2 i hi, eqT_tiles])
    hc hn (fun g _ i _ n _ => read_v ρ w _ g i n)

/-! ## The summand -/

variable (Pl : Planned P) {c : Chal} {Dv : DivIn} (h : divIn P c = some Dv) {C : Calls}
  {p : Pub K} (R : DivPts ρ P C p Dv) (pr : PairsAre P.g Dv.d.pwW)
include Pl h R pr

/-- **The summand's weights and maps read as the library's of step s12.** -/
theorem sVD_reads : StepReads ρ (sVD P w c) P.D C p (tOf ρ w) .s12 := by
  rw [sVD_eq P w c h]
  have hs : ∀ x : List E, x.length = (cut P.x).getD (iVD P.x) 3 - 3 →
      x.toArray.size = Step.s12.g P.D := fun x hx => by
    rw [List.size_toArray]
    exact hx.trans Pl.vVD
  refine ⟨Pl.vVD, ⟨fun x => wOn P.g Dv.pw Dv.zW { Dv.h with on := sumAt x.toArray },
    fun x => rfl, fun x hx b hb => ?_⟩, fun x hx b hb => ?_, fun x hx b hb => ?_⟩
  · have e : x.toArray.size = P.D.lg + (P.D.lP + 1) + P.D.lB := hs x hx
    exact on_reads ρ P.D C p P.g Dv.h R.look H.lt rfl H.lnT x.toArray
      (by omega) hb
  · rw [ofProducts_even]
    exact vdA_reads ρ H w pr C p R.nLo R.hlo (hs x hx) hb
  · rw [ofProducts_odd, R.ec]
    exact vdB_reads ρ H w pr C p R.gam R.nC R.hn (hs x hx) hb

/-- **The sum over the cube reads as the library's sum of step s12.** -/
theorem sVD_total : ρ.val (sVD P w c).total = sumPhi P.D C p (tOf ρ w) .s12 :=
  (sVD_reads ρ H w Pl h R pr).total

/-- **The summand has what the masked sumcheck's prover asks of it.** -/
theorem sVD_tame : (sVD P w c).Tame ρ (List.replicate (sVD P w c).vars 4) 2 :=
  (sVD_reads ρ H w Pl h R pr).tame fun b ξ => Cb.Pv.Att.wbExt12 P.D C _ b ξ

end H2K5.Honest

#print axioms H2K5.Honest.sVD_eq
#print axioms H2K5.Honest.pointD_at
#print axioms H2K5.Honest.eqT_tiles
#print axioms H2K5.Honest.vdA_reads
#print axioms H2K5.Honest.vdB_reads
#print axioms H2K5.Honest.sVD_reads
#print axioms H2K5.Honest.sVD_total
#print axioms H2K5.Honest.sVD_tame
