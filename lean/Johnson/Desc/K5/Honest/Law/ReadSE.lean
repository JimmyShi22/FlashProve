-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadSE.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "denominator times output" (`sSE`,
Johnson/Desc/K5/Honest/Products.lean), read in a field, is the library's step s8
(Inst/Model/Att/Sums.lean): its weights, its two hidden maps at ANY point, its sum over the cube;
and it has what the masked sumcheck's prover asks of a summand. Two names for pieces of the
summand's text, and statements with their proofs.

Main names:
  `seA`, `seB`, `sSE_eq`   names for the two hidden maps; the summand is their sum of products
  `seA_reads`, `seB_reads`   the maps read as the library's `Aext`, `Bext` of step s8
  `sSE_reads`     `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the summand
  `sSE_total`     the sum over the cube reads as `sumPhi` of step s8
  `sSE_tame`      `Summand.Tame` at 4 coefficients a variable

Every statement is conditional. The premises, and who is meant to show each: `Sized`, `Planned`,
`PairsAre`: public, the caller's. `divIn P c = some Dv`: that the verifier's function of the points
returns: tests on lengths alone, the caller's. `DivPts`: the lookup's points, read, are the
library's: from `KeyPtsAre`, `UnitIs` and hth (the batching element heard, read, is p's `th`) by
`divPts_of` (Johnson/Desc/K5/Honest/Law/Weights.lean). `DivPts` has that clause (`gam`) though step
s8 does not read `th`; the element is drawn in the part BEHIND this sumcheck, and an unheard one
reads 0: at challenges that end in front of that part the clause says th = 0. The library's
challenges p are any at which `DivPts` holds: step s8 reads the field z alone.
Limits. Nothing here says that a premise holds at any place.
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
open VerifiableInference.Desc.First.Att.P (Geo W1 DivP Heard geoOf eqTab ofNat tok lastCoords pointD
  wDivision wOn KeyPtsAre UnitIs)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The two hidden maps, under names -/

/-- The first hidden map, piece b, at the point r: the denominators. The text of `sSE`. -/
def seA (g : Geo) (w : K5In) (pw : Array W1) (r : Array E) (b : ℕ) : E :=
  overHeads g r fun hk => underN (eqTab (r.extract g.lgk (g.lgk + g.lt))) fun i =>
    w.zd (pairOf g (pw.getD b ⟨0, 0, zeroE⟩)) hk i

/-- The second: the outputs. ec: the table of equality weights of the channel point. -/
def seB (g : Geo) (w : K5In) (pw : Array W1) (ec r : Array E) (b : ℕ) : E :=
  overHeads g r fun hk => atTokens (eqTab (r.extract g.lgk (g.lgk + g.lt))) ec fun i ch =>
    w.o (pairOf g (pw.getD b ⟨0, 0, zeroE⟩)) hk i ch

/-- Where `divIn` returns, the summand is the sum of products of these two maps. -/
theorem sSE_eq (P : Pub5) (w : K5In) (c : Chal) {Dv : DivIn} (h : divIn P c = some Dv) :
    sSE P w c = ofProducts ((cut P.x).getD (iSE P.x) 3 - 3) P.g.NP
      (fun r => wDivision P.g Dv.pw Dv.zW { Dv.h with division := sumAt r })
      (seA P.g w Dv.d.pwW) (seB P.g w Dv.d.pwW Dv.ec) := by
  unfold sSE
  simp only [h]
  rfl

/-! ## The maps, read -/

variable {P : Pub5} (H : Sized P) (w : K5In)
include H

/-- **The first map reads as the library's**, at any point of the step's length. -/
theorem seA_reads {pw : Array W1} (pr : PairsAre P.g pw) (C : Calls) (p : Pub K) {r : Array E}
    (hr : r.size = Step.s8.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (seA P.g w pw r b) = Aext P.D C p (tOf ρ w) .s8 b (pt ρ r) := by
  have hr' : P.D.lg + P.D.lT ≤ r.size := le_of_eq hr.symm
  obtain ⟨t1, t2⟩ := read_eqTab_cut ρ r hr'
  rw [Cb.Pv.Att.aext8]
  unfold seA
  rw [pr.pair hb, H.lt]
  exact read_rd2 ρ H (by omega) (fun _ _ => rfl) (by rw [Dim.T_eq]; exact t1)
    (fun i hi => t2 i (by rw [← Dim.T_eq]; exact hi)) (fun g _ i _ => read_zd ρ w b g i)

/-- **The second map reads as the library's.** zc: the channel point, which agrees with the
library's. -/
theorem seB_reads {pw : Array W1} (pr : PairsAre P.g pw) (C : Calls) (p : Pub K) {zc : Array E}
    (hc : zc.size = P.D.ln) (hn : ∀ k < P.D.ln, pt ρ zc k = yn P.D C p.z k) {r : Array E}
    (hr : r.size = Step.s8.g P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (seB P.g w pw (eqTab zc) r b) = Bext P.D C p (tOf ρ w) .s8 b (pt ρ r) := by
  have hr' : P.D.lg + P.D.lT ≤ r.size := le_of_eq hr.symm
  obtain ⟨t1, t2⟩ := read_eqTab_cut ρ r hr'
  rw [Cb.Pv.Att.bext8]
  unfold seB
  rw [pr.pair hb, H.lt]
  exact read_rd3 ρ H (by omega) (fun _ _ => rfl) (by rw [Dim.T_eq]; exact t1)
    (fun i hi => t2 i (by rw [← Dim.T_eq]; exact hi)) hc hn
    (fun g _ i _ n _ => read_o ρ w b g i n)

/-! ## The summand -/

variable (Pl : Planned P) {c : Chal} {Dv : DivIn} (h : divIn P c = some Dv) {C : Calls}
  {p : Pub K} (R : DivPts ρ P C p Dv) (pr : PairsAre P.g Dv.d.pwW)
include Pl h R pr

/-- **The summand's weights and maps read as the library's of step s8.** Conditional: H, Pl, h, R,
pr (laid as variables above). -/
theorem sSE_reads : StepReads ρ (sSE P w c) P.D C p (tOf ρ w) .s8 := by
  rw [sSE_eq P w c h]
  have hs : ∀ x : List E, x.length = (cut P.x).getD (iSE P.x) 3 - 3 →
      x.toArray.size = Step.s8.g P.D := fun x hx => by
    rw [List.size_toArray]
    exact hx.trans Pl.vSE
  refine ⟨Pl.vSE, ⟨fun x => wDivision P.g Dv.pw Dv.zW { Dv.h with division := sumAt x.toArray },
    fun x => rfl, fun x hx b hb => ?_⟩, fun x hx b hb => ?_, fun x hx b hb => ?_⟩
  · exact division_reads ρ P.D C p P.g Dv.h R.look H.lt rfl x.toArray
      (le_of_eq (hs x hx).symm) hb
  · rw [ofProducts_even]
    exact seA_reads ρ H w pr C _ (hs x hx) hb
  · rw [ofProducts_odd, R.ec]
    exact seB_reads ρ H w pr C p R.nC R.hn (hs x hx) hb

/-- **The sum over the cube reads as the library's sum of step s8.** Conditional: H, Pl, h, R, pr
(laid as variables above). -/
theorem sSE_total : ρ.val (sSE P w c).total = sumPhi P.D C p (tOf ρ w) .s8 :=
  (sSE_reads ρ H w Pl h R pr).total

/-- **The summand has what the masked sumcheck's prover asks of it**, at 4 coefficients a variable
and 3 in Y. Conditional: H, Pl, h, R, pr (laid as variables above). -/
theorem sSE_tame : (sSE P w c).Tame ρ (List.replicate (sSE P w c).vars 4) 2 :=
  (sSE_reads ρ H w Pl h R pr).tame fun b ξ => OnBytes.Road.Rows.wbExt8 P.D C _ b ξ

end H2K5.Honest

#print axioms H2K5.Honest.sSE_eq
#print axioms H2K5.Honest.seA_reads
#print axioms H2K5.Honest.seB_reads
#print axioms H2K5.Honest.sSE_reads
#print axioms H2K5.Honest.sSE_total
#print axioms H2K5.Honest.sSE_tame
