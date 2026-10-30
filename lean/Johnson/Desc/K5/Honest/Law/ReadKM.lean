-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadKM.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand of a softmax-table unit BELOW THE DIAGONAL (`sK`,
Johnson/Desc/K5/Honest/Products.lean), READ IN A FIELD, is the library's summand of step s6b
(Inst/Model/Att/Sums.lean). Statements with their proofs.

rho is any reading (OnBytes/Model/HideLaws.lean). The points are any points: no coordinate is asked
to be 0 or 1. The two hidden maps weigh the tokens by sums over tile slots, in which the tile slot
that holds no tile has no share; the library's maps are 0 on the cube at that tile slot, and are
extended from the cube. That the two agree at every point is what this file shows.

Main names:
  `scoreTiles_below`          the verifier's tile weights, written out
  `unitA_below`, `unitB_below`  the two hidden maps at any point are the library's `Aext`, `Bext`
  `sKM_reads`                 `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the
                              summand
  `sKM_total`                 the sum over the cube reads as `sumPhi` of step s6b
  `sKM_tame`                  `Summand.Tame` (Law/TermsLaw.lean) at 4 coefficients a variable
EVERY STATEMENT IS CONDITIONAL; each docstring says on what, and who is meant to show it.
By `aext6b`, `bext6b` (Cb/Pv/Att/Mean/ReadsTiles.lean) and `tiles_row`, `tiles_col`, `tok_psi`
(Johnson/Road/Rows/AttEnds14Tiles.lean), through Johnson/Desc/K5/Honest/Law/TilesKit.lean.

Limits. A PLAN IN WHICH THE LAYERS OF THE GROUP HAVE MORE THAN ONE SHIFT IS NOT REACHED: there a
softmax-table unit has the pieces of some layers alone, while the library's step sums over all
pairs, and the premise that the unit has a piece for each pair fails. The premises are drawn from
what the lookup hands on in Law/UnitPts.lean. Nothing here says that a premise holds at any place.
No property is claimed by a definition.
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

/-! ## The tile weights of a unit below the diagonal -/

/-- The verifier's tile weights of a unit below the diagonal, with r in the place of its sumcheck's
challenges, written out. -/
theorem scoreTiles_below (g : Geo) (k : ScoreP) (r : Array E) (h : k.below = true) :
    scoreTiles g { k with sc := { k.sc with r := r } } =
      tileSums g (eqTab (r.extract g.lgk (g.lgk + g.lnT - 1)))
        (eqTab (r.extract (g.lgk + g.lnT - 1) (g.lgk + 2 * g.lnT - 1))) := by
  unfold scoreTiles
  dsimp only
  rw [if_pos h]

variable {P : Pub5} (C : Calls) (p : Pub K) (w : K5In)

/-! ## The two hidden maps -/

/-- **The first hidden map of a unit below the diagonal, at ANY point r, reads as the library's
extension of its first map of step s6b**, which is 0 at the tile slot that holds no tile.
CONDITIONAL on: the shape's numbers (public); the unit's named points are the library's and piece b
is pair b (`UnitReads`: the caller's); r has the step's number of coordinates. -/
theorem unitA_below (H : Sized P) {k : ScoreP} (U : UnitReads ρ P C p.z k) (hbel : k.below = true)
    {r : Array E} (hr : r.size = Step.s6b.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (unitA P.g w k r b) = Aext P.D C p (tOf ρ w) .s6b b (pt ρ r) := by
  have hn := H.Z.lnT
  have hr' : r.size = P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.ldh := hr
  have ht := tok_reads ρ H (lo := k.zi)
    (fun I hI => tiles_fst ρ H (r := r) (a := P.g.lgk) (b := P.g.lgk + P.g.lnT - 1)
      (c := P.g.lgk + 2 * P.g.lnT - 1) rfl
      (by show P.S.cf.lgk + P.S.lnT - 1 = P.S.cf.lgk + (P.S.lnT - 1); omega)
      (by show P.S.cf.lgk + 2 * P.S.lnT - 1 = P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1); omega)
      (by show P.S.cf.lgk + 2 * P.S.lnT - 1 ≤ r.size; omega) hI) U.si U.i
  unfold unitA
  rw [U.pairs.pair hb, aext6b, scoreTiles_below P.g k r hbel]
  refine read_rd3 ρ H (by show P.S.cf.lgk ≤ r.size; omega) (fun _ _ => rfl) ht.1 ht.2
    (last_size r (by show P.S.cf.ldh ≤ r.size; omega)) (fun j hj => ?_)
    fun g _ i _ n _ => read_q ρ w _ _ _ _
  have hj' : j < P.S.cf.ldh := hj
  show pt ρ (lastCoords r P.S.cf.ldh) j = _
  rw [pt_last ρ r (by omega) hj']
  show pt ρ r (r.size - P.S.cf.ldh + j) =
    pt ρ r (P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + j)
  congr 1
  omega

/-- **The second hidden map of a unit below the diagonal, at ANY point r, reads as the library's
extension of its second map of step s6b.** CONDITIONAL as `unitA_below`. -/
theorem unitB_below (H : Sized P) {k : ScoreP} (U : UnitReads ρ P C p.z k) (hbel : k.below = true)
    {r : Array E} (hr : r.size = Step.s6b.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (unitB P.g w k r b) = Bext P.D C p (tOf ρ w) .s6b b (pt ρ r) := by
  have hn := H.Z.lnT
  have hr' : r.size = P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.ldh := hr
  have ht := tok_reads ρ H (lo := k.zj)
    (fun I hI => tiles_snd ρ H (r := r) (a := P.g.lgk) (b := P.g.lgk + P.g.lnT - 1)
      (c := P.g.lgk + 2 * P.g.lnT - 1) rfl
      (by show P.S.cf.lgk + P.S.lnT - 1 = P.S.cf.lgk + (P.S.lnT - 1); omega)
      (by show P.S.cf.lgk + 2 * P.S.lnT - 1 = P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1); omega)
      (by show P.S.cf.lgk + 2 * P.S.lnT - 1 ≤ r.size; omega) hI) U.sj U.j
  unfold unitB
  rw [lam_of U.pairs hb, bext6b, scoreTiles_below P.g k r hbel]
  refine read_rd3 ρ H (by show P.S.cf.lgk ≤ r.size; omega) (fun _ _ => rfl) ht.1 ht.2
    (last_size r (by show P.S.cf.ldh ≤ r.size; omega)) (fun j hj => ?_)
    fun g _ i _ n _ => read_kx ρ w _ _ _ _
  have hj' : j < P.S.cf.ldh := hj
  show pt ρ (lastCoords r P.S.cf.ldh) j = _
  rw [pt_last ρ r (by omega) hj']
  show pt ρ r (r.size - P.S.cf.ldh + j) =
    pt ρ r (P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + j)
  congr 1
  omega

/-! ## The summand -/

variable {C p}

/-- **The summand's weights and maps read as the library's of step s6b.** CONDITIONAL on: the
shape's numbers (public); the place has the unit, below the diagonal, at the library's numbers, and
the verifier's function of the points returns (`UnitPlace`: the caller's); the unit's named points
and its call's key point, read, are the library's (`UnitReads`, `UnitPtsM`: they hang on what the
lookup hands on). -/
theorem sKM_reads (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6b (P.g.lgk + (P.g.lnT - 1) + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = true) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsM ρ P.D C p.z u (c.zk.getD u.call #[])) :
    StepReads ρ (sK P w c i) P.D C p (tOf ρ w) .s6b := by
  rw [sK_eq P w c A.unit A.pts]
  have hs : ∀ x : List E, x.length = (cut P.x).getD i 3 - 3 →
      x.toArray.size = Step.s6b.g P.D := fun x hx => by
    rw [List.size_toArray]
    exact hx.trans A.vars
  refine ⟨A.vars, ⟨fun x => (scoreW P.g u (c.zk.getD u.call #[]) x.toArray).getD #[],
    fun x => by rw [ofProducts_terms, A.np], fun x hx b hb => ?_⟩, fun x hx b hb => ?_,
    fun x hx b hb => ?_⟩
  · have e : x.toArray.size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.ln := hs x hx
    exact unitM_reads ρ P.D C p hbel lp rfl H.lnT A.size x.toArray (by omega) hb
  · rw [ofProducts_even]
    exact unitA_below ρ C p w H U (A.flag.trans hbel) (hs x hx) hb
  · rw [ofProducts_odd]
    exact unitB_below ρ C p w H U (A.flag.trans hbel) (hs x hx) hb

/-- **The sum over the cube reads as the library's sum of step s6b.** CONDITIONAL as `sKM_reads`. -/
theorem sKM_total (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6b (P.g.lgk + (P.g.lnT - 1) + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = true) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsM ρ P.D C p.z u (c.zk.getD u.call #[])) :
    ρ.val (sK P w c i).total = sumPhi P.D C p (tOf ρ w) .s6b :=
  (sKM_reads ρ w H A hbel U lp).total

/-- **The summand has what the masked sumcheck's prover asks of it**: 4 coefficients a variable,
degree 2 in the further variable. CONDITIONAL as `sKM_reads`. -/
theorem sKM_tame (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6b (P.g.lgk + (P.g.lnT - 1) + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = true) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsM ρ P.D C p.z u (c.zk.getD u.call #[])) :
    (sK P w c i).Tame ρ (List.replicate (sK P w c i).vars 4) 2 :=
  (sKM_reads ρ w H A hbel U lp).tame fun b ξ => OnBytes.Road.Rows.wbExt6b P.D C p b ξ

end H2K5.Honest

#print axioms H2K5.Honest.scoreTiles_below
#print axioms H2K5.Honest.unitA_below
#print axioms H2K5.Honest.unitB_below
#print axioms H2K5.Honest.sKM_reads
#print axioms H2K5.Honest.sKM_total
#print axioms H2K5.Honest.sKM_tame
