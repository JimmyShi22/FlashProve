-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadKD.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand of a softmax-table unit ON THE DIAGONAL (`sK`,
Johnson/Desc/K5/Honest/Products.lean), READ IN A FIELD, is the library's summand of step s6d
(Inst/Model/Att/Sums.lean). Statements with their proofs.

rho is any reading (OnBytes/Model/HideLaws.lean). The points are any points: no coordinate is asked
to be 0 or 1.

Main names:
  `scoreTiles_on`, `tile_on`   the verifier's tile weights, written out, and read
  `unitA_on`, `unitB_on`       the two hidden maps at any point are the library's `Aext`, `Bext`
  `sKD_reads`                 `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the
                              summand
  `sKD_total`                 the sum over the cube reads as `sumPhi` of step s6d
  `sKD_tame`                  `Summand.Tame` (Law/TermsLaw.lean) at 4 coefficients a variable
EVERY STATEMENT IS CONDITIONAL; the docstrings of the five on the maps and the summand say on what,
and who is meant to show it.
By `aext6d`, `bext6d` (Cb/Pv/Att/Mean/ReadsTiles.lean) and `tok_psi`
(Johnson/Road/Rows/AttEnds14Tiles.lean), through Johnson/Desc/K5/Honest/Law/TilesKit.lean.

Limits. A PLAN IN WHICH THE LAYERS OF THE GROUP HAVE MORE THAN ONE SHIFT IS NOT REACHED: there a
softmax-table unit has the pieces of some layers alone, while the library's step sums over all
pairs, and the premise that the unit has a piece for each pair fails. The premises are drawn from
what the lookup hands on in Law/UnitPts.lean. The library cuts the two points of a place in a tile
from the list below the diagonal; the premise `UnitReads` asks that this unit's own cuts read as
these. Nothing here says that a premise holds at any place. No property is claimed by a definition.
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

/-! ## The tile weights of a unit on the diagonal -/

/-- The verifier's tile weights of a unit on the diagonal, with r in the place of its sumcheck's
challenges, written out. -/
theorem scoreTiles_on (g : Geo) (k : ScoreP) (r : Array E) (h : k.below = false) :
    scoreTiles g { k with sc := { k.sc with r := r } } =
      (eqTab (r.extract g.lgk (g.lgk + g.lnT)), eqTab (r.extract g.lgk (g.lgk + g.lnT))) := by
  unfold scoreTiles
  dsimp only
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

variable {P : Pub5}

/-- The equality weights of the tile's coordinates of a point r. -/
theorem tile_on (H : Sized P) {r : Array E} (hr : P.D.lg + (P.D.lP + 1) ≤ r.size) {I : ℕ}
    (hI : I < P.D.nBlk) :
    ρ.val ((eqTab (r.extract P.g.lgk (P.g.lgk + P.g.lnT))).getD I zeroE) =
      Blocks.eqN (P.D.lP + 1) 0 (sh (pt ρ r) P.D.lg) I := by
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  rw [hl]
  refine read_eqTab ρ ?_ (fun j hj => pt_extract ρ r _ _ j (Nat.add_lt_add_left hj _)) ?_
  · show (r.extract P.D.lg (P.D.lg + (P.D.lP + 1))).size = _
    rw [size_extract_le r hr]
    exact Nat.add_sub_cancel_left _ _
  · rw [Cb.Pv.Att.nBlk_pow]
    exact hI

variable (C : Calls) (p : Pub K) (w : K5In)

/-! ## The two hidden maps -/

/-- **The first hidden map of a unit on the diagonal, at ANY point r, reads as the library's
extension of its first map of step s6d.** CONDITIONAL on: the shape's numbers (public); the unit's
named points are the library's and piece b is pair b (`UnitReads`: the caller's); r has the step's
number of coordinates. -/
theorem unitA_on (H : Sized P) {k : ScoreP} (U : UnitReads ρ P C p.z k) (hbel : k.below = false)
    {r : Array E} (hr : r.size = Step.s6d.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (unitA P.g w k r b) = Aext P.D C p (tOf ρ w) .s6d b (pt ρ r) := by
  have hr' : r.size = P.D.lg + (P.D.lP + 1) + P.D.ln := hr
  have ht := tok_reads ρ H (lo := k.zi) (fun I hI => tile_on ρ H (r := r) (by omega) hI) U.si U.i
  unfold unitA
  rw [U.pairs.pair hb, aext6d, scoreTiles_on P.g k r hbel]
  refine read_rd3 ρ H (by omega) (fun _ _ => rfl) ht.1 ht.2
    (last_size r (by show P.D.ln ≤ r.size; omega)) (fun j hj => ?_)
    fun g _ i _ n _ => read_q ρ w _ _ _ _
  show pt ρ (lastCoords r P.D.ln) j = _
  rw [pt_last ρ r (by omega) hj]
  show pt ρ r (r.size - P.D.ln + j) = pt ρ r (P.D.lg + (P.D.lP + 1) + j)
  congr 1
  omega

/-- **The second hidden map of a unit on the diagonal, at ANY point r, reads as the library's
extension of its second map of step s6d.** CONDITIONAL as `unitA_on`. -/
theorem unitB_on (H : Sized P) {k : ScoreP} (U : UnitReads ρ P C p.z k) (hbel : k.below = false)
    {r : Array E} (hr : r.size = Step.s6d.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (unitB P.g w k r b) = Bext P.D C p (tOf ρ w) .s6d b (pt ρ r) := by
  have hr' : r.size = P.D.lg + (P.D.lP + 1) + P.D.ln := hr
  have ht := tok_reads ρ H (lo := k.zj) (fun I hI => tile_on ρ H (r := r) (by omega) hI) U.sj U.j
  unfold unitB
  rw [lam_of U.pairs hb, bext6d, scoreTiles_on P.g k r hbel]
  refine read_rd3 ρ H (by omega) (fun _ _ => rfl) ht.1 ht.2
    (last_size r (by show P.D.ln ≤ r.size; omega)) (fun j hj => ?_)
    fun g _ i _ n _ => read_kx ρ w _ _ _ _
  show pt ρ (lastCoords r P.D.ln) j = _
  rw [pt_last ρ r (by omega) hj]
  show pt ρ r (r.size - P.D.ln + j) = pt ρ r (P.D.lg + (P.D.lP + 1) + j)
  congr 1
  omega

/-! ## The summand -/

variable {C p}

/-- **The summand's weights and maps read as the library's of step s6d.** CONDITIONAL on: the
shape's numbers (public); the place has the unit, on the diagonal, at the library's numbers, and the
verifier's function of the points returns (`UnitPlace`: the caller's); the unit's named points and
its call's key point, read, are the library's (`UnitReads`, `UnitPtsD`: they hang on what the lookup
hands on). -/
theorem sKD_reads (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6d (P.g.lgk + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = false) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsD ρ P.D C p.z u (c.zk.getD u.call #[])) :
    StepReads ρ (sK P w c i) P.D C p (tOf ρ w) .s6d := by
  rw [sK_eq P w c A.unit A.pts]
  have hs : ∀ x : List E, x.length = (cut P.x).getD i 3 - 3 →
      x.toArray.size = Step.s6d.g P.D := fun x hx => by
    rw [List.size_toArray]
    exact hx.trans A.vars
  refine ⟨A.vars, ⟨fun x => (scoreW P.g u (c.zk.getD u.call #[]) x.toArray).getD #[],
    fun x => by rw [ofProducts_terms, A.np], fun x hx b hb => ?_⟩, fun x hx b hb => ?_,
    fun x hx b hb => ?_⟩
  · have e : x.toArray.size = P.D.lg + (P.D.lP + 1) + P.D.ln := hs x hx
    exact unitD_reads ρ P.D C p hbel lp rfl H.lnT A.size x.toArray (by omega) hb
  · rw [ofProducts_even]
    exact unitA_on ρ C p w H U (A.flag.trans hbel) (hs x hx) hb
  · rw [ofProducts_odd]
    exact unitB_on ρ C p w H U (A.flag.trans hbel) (hs x hx) hb

/-- **The sum over the cube reads as the library's sum of step s6d.** CONDITIONAL as `sKD_reads`. -/
theorem sKD_total (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6d (P.g.lgk + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = false) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsD ρ P.D C p.z u (c.zk.getD u.call #[])) :
    ρ.val (sK P w c i).total = sumPhi P.D C p (tOf ρ w) .s6d :=
  (sKD_reads ρ w H A hbel U lp).total

/-- **The summand has what the masked sumcheck's prover asks of it**: 4 coefficients a variable,
degree 2 in the further variable. CONDITIONAL as `sKD_reads`. -/
theorem sKD_tame (H : Sized P) {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (A : UnitPlace P c i u k .s6d (P.g.lgk + P.g.lnT + 2 * P.g.lB))
    (hbel : u.below = false) (U : UnitReads ρ P C p.z k)
    (lp : UnitPtsD ρ P.D C p.z u (c.zk.getD u.call #[])) :
    (sK P w c i).Tame ρ (List.replicate (sK P w c i).vars 4) 2 :=
  (sKD_reads ρ w H A hbel U lp).tame fun b ξ => OnBytes.Road.Rows.wbExt6d P.D C p b ξ

end H2K5.Honest

#print axioms H2K5.Honest.scoreTiles_on
#print axioms H2K5.Honest.tile_on
#print axioms H2K5.Honest.unitA_on
#print axioms H2K5.Honest.unitB_on
#print axioms H2K5.Honest.sKD_reads
#print axioms H2K5.Honest.sKD_total
#print axioms H2K5.Honest.sKD_tame
