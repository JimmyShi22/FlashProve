-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadVM.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "the value product BELOW THE DIAGONAL" (`sVM`,
Johnson/Desc/K5/Honest/Products.lean), READ IN A FIELD, is the library's summand of step s11
(Inst/Model/Att/Sums.lean). Two names for pieces of the summand's text, and statements with their
proofs.

rho is any reading (OnBytes/Model/HideLaws.lean). The points are any points: no coordinate is asked
to be 0 or 1. The second hidden map weighs the tokens by sums over tile slots, in which the tile
slot that holds no tile has no share; the library's map is the batching element alone on the cube at
that tile slot, and is extended from the cube. The first hidden map reads the region's cells at
every entry, on both sides. That the two sides agree at every point is what this file shows.

Main names:
  `vmA`, `vmB`, `sVM_eq`       names for the two hidden maps; the summand is their sum of products
  `pointM_reads`              the point at which the softmax weights are read is the library's
  `vmA_reads`, `vmB_reads`     the two hidden maps at any point are the library's `Aext`, `Bext`
  `sVM_reads`                 `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the
                              summand
  `sVM_total`                 the sum over the cube reads as `sumPhi` of step s11
  `sVM_tame`                  `Summand.Tame` (Law/TermsLaw.lean) at 4 coefficients a variable
EVERY STATEMENT IS CONDITIONAL; each docstring says on what, and who is meant to show it.
By `aext11`, `bext11` (Cb/Pv/Att/Mean/ReadsTiles.lean) and `tiles_col`, `tok_psi`
(Johnson/Road/Rows/AttEnds14Tiles.lean), through Johnson/Desc/K5/Honest/Law/TilesKit.lean.

Limits. Nothing here says that a premise holds at any place. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Weights
import Johnson.Desc.K5.Honest.Law.ProductsLaw
import Johnson.Desc.K5.Honest.Law.TilesKit
import Johnson.Road.Rows.AttWb14

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 ScoreP DivP UnitG geoOf eqTab ofNat tok tileSums
  lastCoords scoreTiles scoreW pointM wBelow inner UnitPtsM UnitPtsD LookPts)
open Inst.Model.AttSeg
open Cb.Pv.Att (aext6b bext6b aext6d bext6d aext11 bext11 psiDiag ptBelow)
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The two hidden maps, under names -/

/-- The first hidden map of the value product below the diagonal, piece b, at the point r: the
softmax weight. The text of `sVM` (Johnson/Desc/K5/Honest/Products.lean). -/
def vmA (g : Geo) (w : K5In) (d : DivP) (r : Array E) (b : ℕ) : E :=
  weightAt w false (pointM g (belowAt g d r)) (pairOf g (d.pwW.getD b ⟨0, 0, zeroE⟩))

/-- The second: the batching element plus the values. ec: eq of the channel point, as a table. -/
def vmB (g : Geo) (w : K5In) (d : DivP) (ec : Array E) (r : Array E) (b : ℕ) : E :=
  addE (belowAt g d r).gam (overHeads g (belowAt g d r).vpm.r fun hk =>
    atTokens (tok g (belowAt g d r).wJv (lastCoords (belowAt g d r).vpm.r g.lB)) ec fun pos ch =>
      w.v (d.pwW.getD b ⟨0, 0, zeroE⟩).lam hk pos ch)

/-- Where `divIn` returns, the summand is the sum of products of these two maps. -/
theorem sVM_eq (P : Pub5) (w : K5In) (c : Chal) {Dv : DivIn} (hD : divIn P c = some Dv) :
    sVM P w c = ofProducts ((cut P.x).getD (iVM P.x) 3 - 3) P.g.NP
      (fun r => wBelow P.g Dv.pw Dv.zW { Dv.h with below := sumAt r }) (vmA P.g w Dv.d)
      (vmB P.g w Dv.d Dv.ec) := by
  unfold sVM
  simp only [hD]
  rfl

variable {P : Pub5} (C : Calls) (p : Pub K) (w : K5In)

/-! ## The point at which the softmax weights are read -/

/-- The verifier's point of the region below the diagonal, with r in the place of the sumcheck's
challenges, has the region's number of coordinates and reads as the library's point. CONDITIONAL on:
the shape's numbers (public); the point of the query's place in its tile has its length and reads as
the library's (the caller's); r has the step's number of coordinates. -/
theorem pointM_reads (H : Sized P) {d : DivP} (nLo : (d.zilo P.g).size = P.D.lB)
    (hlo : ∀ k < P.D.lB, pt ρ (d.zilo P.g) k = yi' P.D C p.z k) {r : Array E}
    (hr : r.size = Step.s11.g P.D) :
    (pointM P.g (belowAt P.g d r)).size = P.D.lM ∧
      ∀ t < P.D.lM, pt ρ (pointM P.g (belowAt P.g d r)) t = ptBelow P.D C p (pt ρ r) t := by
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  have hr' : r.size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := hr
  have e : pointM P.g (belowAt P.g d r) = r.extract 0 (P.D.lg + 2 * P.g.lnT - 1) ++
      d.zilo P.g ++ lastCoords r P.D.lB := rfl
  rw [hl] at e
  have s1 : (r.extract 0 (P.D.lg + 2 * (P.D.lP + 1) - 1)).size =
      P.D.lg + P.D.lP + (P.D.lP + 1) := by
    rw [size_extract_le r (by omega)]
    omega
  have s3 : (lastCoords r P.D.lB).size = P.D.lB := last_size r (by omega)
  refine ⟨by rw [e, Array.size_append, Array.size_append, s1, nLo, s3]; rfl, fun t ht => ?_⟩
  have ht' : t < P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB := ht
  rw [e, pt_append, pt_append, Array.size_append, s1, nLo]
  unfold ptBelow cat
  by_cases h1 : t < P.D.lg + P.D.lP + (P.D.lP + 1)
  · rw [if_pos (by omega), if_pos h1, if_pos h1, pt_extract ρ r 0 _ t (by omega), Nat.zero_add]
  · by_cases h2 : t < P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos (by omega), hlo _ (by omega)]
    · rw [if_neg h2, if_neg h1, if_neg (by omega), pt_last ρ r (by omega) (by omega)]
      show pt ρ r _ = pt ρ r _
      congr 1
      omega

/-! ## The two hidden maps, read -/

/-- **The first hidden map of the value product below the diagonal, at ANY point r, reads as the
library's extension of its first map of step s11.** Both read the cells of every entry of the
region, also of the entries at the tile slot that holds no tile: what stands there is the cells'
matter; the step's weight is 0 there. CONDITIONAL on: the shape's numbers and "piece b is pair b"
(public); the point of the query's place in its tile reads as the library's (the caller's); r has
the step's number of coordinates. -/
theorem vmA_reads (H : Sized P) {d : DivP} (pr : PairsAre P.g d.pwW)
    (nLo : (d.zilo P.g).size = P.D.lB) (hlo : ∀ k < P.D.lB, pt ρ (d.zilo P.g) k = yi' P.D C p.z k)
    {r : Array E} (hr : r.size = Step.s11.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (vmA P.g w d r b) = Aext P.D C p (tOf ρ w) .s11 b (pt ρ r) := by
  obtain ⟨hs, hp⟩ := pointM_reads ρ C p H nLo hlo hr
  unfold vmA
  rw [pr.pair hb, read_weightAt, aext11, hs]
  exact Blocks.ext_congr_point hp _

/-- **The second hidden map of the value product below the diagonal, at ANY point r, reads as the
library's extension of its second map of step s11**, which is the batching element alone at the tile
slot that holds no tile. zc: the channel point. CONDITIONAL on: the shape's numbers and "piece b is
pair b" (public); the batching element and the channel point read as the library's (the caller's); r
has the step's number of coordinates. -/
theorem vmB_reads (H : Sized P) {d : DivP} (pr : PairsAre P.g d.pwW) (hg : ρ.val d.gam = p.th)
    {zc : Array E} (hc : zc.size = P.D.ln) (hn : ∀ k < P.D.ln, pt ρ zc k = yn P.D C p.z k)
    {r : Array E} (hr : r.size = Step.s11.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (vmB P.g w d (eqTab zc) r b) = Bext P.D C p (tOf ρ w) .s11 b (pt ρ r) := by
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  have hr' : r.size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := hr
  have ht := tok_reads ρ H (lo := lastCoords r P.g.lB)
    (v := sh (pt ρ r) (P.D.lg + P.D.lP + (P.D.lP + 1)))
    (fun I hI => tiles_snd ρ H (r := r) (a := P.g.lgk) (b := P.g.lgk + (P.g.lnT - 1))
      (c := P.g.lgk + (P.g.lnT - 1) + P.g.lnT) rfl rfl
      (by show P.D.lg + P.D.lP + P.g.lnT = _; rw [hl])
      (by show P.D.lg + P.D.lP + P.g.lnT ≤ r.size; omega) hI)
    (last_size r (by show P.D.lB ≤ r.size; omega))
    (fun j hj => by
      show pt ρ (lastCoords r P.D.lB) j = _
      rw [pt_last ρ r (by omega) hj]
      show pt ρ r (r.size - P.D.lB + j) = pt ρ r (P.D.lg + P.D.lP + (P.D.lP + 1) + j)
      congr 1
      omega)
  unfold vmB
  rw [ρ.add, lam_of pr hb, bext11]
  refine congrArg₂ HAdd.hAdd hg ?_
  exact read_rd3 ρ H (by show P.D.lg ≤ r.size; omega) (fun _ _ => rfl) ht.1 ht.2 hc hn
    fun g _ i _ n _ => read_v ρ w _ _ _ _

/-! ## The summand -/

variable {C p}

/-- **The summand's weights and maps read as the library's of step s11.** CONDITIONAL on: the
shape's and the plan's numbers and "piece b is pair b" (public); the verifier's function of the
points returns (tests on lengths alone: the caller's); the lookup's points and the batching element,
read, are the library's (`DivPts`, Law/Weights.lean, which follows there from what the lookup hands
on). -/
theorem sVM_reads (H : Sized P) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) :
    StepReads ρ (sVM P w c) P.D C p (tOf ρ w) .s11 := by
  rw [sVM_eq P w c h]
  have hs : ∀ x : List E, x.length = (cut P.x).getD (iVM P.x) 3 - 3 →
      x.toArray.size = Step.s11.g P.D := fun x hx => by
    rw [List.size_toArray]
    exact hx.trans Pl.vVM
  refine ⟨Pl.vVM, ⟨fun x => wBelow P.g Dv.pw Dv.zW { Dv.h with below := sumAt x.toArray },
    fun x => rfl, fun x hx b hb => ?_⟩, fun x hx b hb => ?_, fun x hx b hb => ?_⟩
  · have e : x.toArray.size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := hs x hx
    exact below_reads ρ H C p Dv.h R.look x.toArray (by omega) hb
  · rw [ofProducts_even]
    exact vmA_reads ρ C p w H pr R.nLo R.hlo (hs x hx) hb
  · rw [ofProducts_odd, R.ec]
    exact vmB_reads ρ C p w H pr R.gam R.nC R.hn (hs x hx) hb

/-- **The sum over the cube reads as the library's sum of step s11.** CONDITIONAL as `sVM_reads`. -/
theorem sVM_total (H : Sized P) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) :
    ρ.val (sVM P w c).total = sumPhi P.D C p (tOf ρ w) .s11 :=
  (sVM_reads ρ w H Pl h R pr).total

/-- **The summand has what the masked sumcheck's prover asks of it**: 4 coefficients a variable,
degree 2 in the further variable. CONDITIONAL as `sVM_reads`. -/
theorem sVM_tame (H : Sized P) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) :
    (sVM P w c).Tame ρ (List.replicate (sVM P w c).vars 4) 2 :=
  (sVM_reads ρ w H Pl h R pr).tame fun b ξ => OnBytes.Road.Rows.wbExt11 P.D C p b ξ

end H2K5.Honest

#print axioms H2K5.Honest.sVM_eq
#print axioms H2K5.Honest.pointM_reads
#print axioms H2K5.Honest.vmA_reads
#print axioms H2K5.Honest.vmB_reads
#print axioms H2K5.Honest.sVM_reads
#print axioms H2K5.Honest.sVM_total
#print axioms H2K5.Honest.sVM_tame
