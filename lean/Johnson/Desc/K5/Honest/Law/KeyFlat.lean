-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeyFlat.lean: IN ITS SECOND HALF CONDITIONAL: the honest prover's side of
an attention segment's own rounds: what the verifier computes, at the end of the masked sumcheck
"the key at the index", of the values that are shown for the end values, READ IN A FIELD, is the
prover's summand's formula on these values; and on honest values it is the prover's polynomial in
the further variable Y at that variable's challenge. Statements with their proofs. The Greek letter
ρ is any reading (OnBytes/Model/HideLaws.lean); the name rho in Latin letters is an array.

The verifier's side. The row that this sumcheck leaves is made of the plain function keyFlat
(OnBytes/Tie/Pv/Att/Flat.lean) on what lies under the end values' numbers: leftKey_spec
(Johnson/Desc/First/Att/K5LeftAll.lean). Its arguments there are two cuts of the challenges of the
score at the index, three cuts of this sumcheck's own challenges, and the batching powers: the same
five cuts stand here, of an array rho and of a list rs.

Main names:
  read_keyTermFlat   one pair's term
  keyFlat_formula    keyFlat on ANY values sh reads as the summand's formula (Summand.formula,
                     Johnson/Desc/K5/Honest/Law/TermsLaw.lean) on these values, read: unconditional
  keyFlat_formula_of   the same with values e in the field that sh reads as, below the number of end
                     values
  key_s0_is_cf       **on what an honest sender shows it is the polynomial in Y at beta**

keyFlat_formula_of and key_s0_is_cf are CONDITIONAL: on what sh reads as, number by number. For
key_s0_is_cf: each shown value reads as the end value plus beta times its mask entry. That is the
law of the masked sumcheck's honest part; whoever calls the statement shows it.
Limits. Nothing ties rho, rs or om' to what a verifier has heard. Nothing is said of a row's value.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.ReadSD

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Tie.Pv.Att (keyFlat keyTermFlat)
open VerifiableInference.Desc.First.Att.P (Geo)
open VerifiableInference.Desc.Part.MaskedSum (valueAt)
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-- One pair's term, read. -/
theorem read_keyTermFlat (lt Lam HA : ℕ) (sh : ℕ → E) (pj : Array E) (o : E) (b : ℕ) :
    ρ.val (keyTermFlat lt Lam HA sh pj o b) = ρ.val o * ρ.val (sh (b / HA)) *
      ((List.range lt).map fun k => ρ.val (sh (Lam + b * lt + k)) *
        (ρ.val (pj.getD (lt - 1 - k) zeroE) + ρ.val (pj.getD (lt - 1 - k) zeroE) - 1) +
          (1 - ρ.val (pj.getD (lt - 1 - k) zeroE))).prod := by
  unfold keyTermFlat
  rw [read_foldl_mul ρ (fun k => addE (mulE (sh (Lam + b * lt + k))
      (subE (addE (pj.getD (lt - 1 - k) zeroE) (pj.getD (lt - 1 - k) zeroE)) oneE))
      (subE oneE (pj.getD (lt - 1 - k) zeroE))), ρ.mul]
  refine congrArg _ (congrArg List.prod (List.map_congr_left fun k _ => ?_))
  rw [ρ.add, ρ.mul, ρ.sub, ρ.add, ρ.sub, ρ.one]

variable (g : Geo) (w : K5In) (rho om' : Array E)

/-- **The verifier's plain function of the key's row, on ANY values sh in the end values' place,
reads as the summand's formula on these values, read.** Unconditional. -/
theorem keyFlat_formula (rs : List E) (sh : ℕ → E) :
    ρ.val (keyFlat g.lt g.Lam g.HA g.NP (rho.extract 0 g.lt) (rho.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract 0 g.lt) (rs.toArray.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)) om' sh) =
      (sdOf g w rho om').formula ρ rs fun n => ρ.val (sh n) := by
  unfold keyFlat Summand.formula
  rw [ρ.mul, read_foldl_add ρ (fun b => keyTermFlat g.lt g.Lam g.HA sh
    (rs.toArray.extract 0 g.lt) (om'.getD b zeroE) b), ρ.zero, zero_add, ← List.sum_map_mul_left]
  show _ = (((List.range g.NP).map fun b => (⟨sdCoef g rho om' rs.toArray b,
    ⟨oneE, b / g.HA, zeroE⟩ :: (List.range g.lt).map (sdBit g rs.toArray b)⟩ : Term)).map _).sum
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  show _ = ρ.val (sdCoef g rho om' rs.toArray b) *
    ((⟨oneE, b / g.HA, zeroE⟩ :: (List.range g.lt).map (sdBit g rs.toArray b)).map
      fun f : Factor => ρ.val f.a * ρ.val (sh f.n) + ρ.val f.b).prod
  rw [read_keyTermFlat, List.map_cons, List.prod_cons, List.map_map]
  have e : ((List.range g.lt).map ((fun f : Factor => ρ.val f.a * ρ.val (sh f.n) + ρ.val f.b) ∘
      sdBit g rs.toArray b)) = (List.range g.lt).map fun k =>
        ρ.val (sh (g.Lam + b * g.lt + k)) *
        (ρ.val ((rs.toArray.extract 0 g.lt).getD (g.lt - 1 - k) zeroE) +
          ρ.val ((rs.toArray.extract 0 g.lt).getD (g.lt - 1 - k) zeroE) - 1) +
          (1 - ρ.val ((rs.toArray.extract 0 g.lt).getD (g.lt - 1 - k) zeroE)) := by
    refine List.map_congr_left fun k _ => ?_
    show ρ.val (subE (addE _ _) oneE) * ρ.val (sh (g.Lam + b * g.lt + k)) +
      ρ.val (subE oneE _) = _
    rw [ρ.sub, ρ.add, ρ.sub, ρ.one, mul_comm]
  rw [e]
  show _ = ρ.val (mulE (mulE _ _) (om'.getD b zeroE)) *
    ((ρ.val oneE * ρ.val (sh (b / g.HA)) + ρ.val zeroE) * _)
  rw [ρ.mul (mulE _ _) (om'.getD b zeroE), ρ.one, ρ.zero, one_mul, add_zero]
  show ρ.val (mulE (OnBytes.Attention.eqPts _ _) (OnBytes.Attention.eqPts _ _)) * _ =
    ρ.val (mulE (OnBytes.Attention.eqPts _ _) (OnBytes.Attention.eqPts _ _)) * _ * _
  ring

/-- The same with values e in the field, CONDITIONAL on: below the number of end values, sh reads as
e. -/
theorem keyFlat_formula_of (rs : List E) (sh : ℕ → E) (e : ℕ → K)
    (hs : ∀ n < g.Lam + g.NP * g.lt, ρ.val (sh n) = e n) :
    ρ.val (keyFlat g.lt g.Lam g.HA g.NP (rho.extract 0 g.lt) (rho.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract 0 g.lt) (rs.toArray.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)) om' sh) =
      (sdOf g w rho om').formula ρ rs e := by
  rw [keyFlat_formula ρ g w]
  exact Summand.formula_congr ρ _ rs _ _ fun t ht f hf => hs f.n (sd_below g w rho om' rs t ht f hf)

/-- **On the shown end values it is the polynomial in Y at beta.** CONDITIONAL on: what is shown
under each end value's number reads as the end value plus beta times its mask entry. -/
theorem key_s0_is_cf (rs m : List E) (beta : E) (sh : ℕ → E)
    (hs : ∀ n < (sdOf g w rho om').ends, ρ.val (sh n) =
      ρ.val ((sdOf g w rho om').endAt rs n) + ρ.val beta * ρ.val (m.getD n zeroE)) :
    ρ.val (keyFlat g.lt g.Lam g.HA g.NP (rho.extract 0 g.lt) (rho.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract 0 g.lt) (rs.toArray.extract g.lt (g.lt + g.lgk))
      (rs.toArray.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)) om' sh) =
      ρ.val (valueAt ((sdOf g w rho om').inY rs m) beta) := by
  rw [Summand.inY_at]
  exact keyFlat_formula_of ρ g w rho om' rs sh _ hs

end H2K5.Honest

#print axioms H2K5.Honest.read_keyTermFlat
#print axioms H2K5.Honest.keyFlat_formula
#print axioms H2K5.Honest.keyFlat_formula_of
#print axioms H2K5.Honest.key_s0_is_cf
