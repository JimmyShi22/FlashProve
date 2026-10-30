-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TameSD.lean: the honest prover's side of an attention segment's own
rounds: the summand "the key at the index" has what the masked sumcheck's prover asks of a summand
(Summand.Tame, Johnson/Desc/K5/Honest/Law/TermsLaw.lean), AT THE SHAPE's NUMBERS OF COEFFICIENTS
(sdDs), WHICH ARE THE VERIFIER'S WHERE THE PLANNER's NUMBERS ARE THE SHAPE's (shape_sSD: conditional
on Planned). Statements with their proofs. rho: any reading (OnBytes/Model/HideLaws.lean).

What is at stake. The verifier's list of stages (Johnson/Desc/First/Att/K5AttentionKind.lean, script) gives this
sumcheck 3 coefficients at each of the lt variables of the key's token j, lt + 3 at each of the lgk
variables of the head hk, lt + 2 at each of the lt variables of the query's token i, and lt + 2 in
the further variable Y. The prover's function makes lt + 3 coefficients at every variable, and the
sender keeps the verifier's number. So at j and at i coefficients are dropped. Here it is shown that
what is dropped reads 0: in a variable of j only the keys' map and one bit's factor move; in a
variable of i the coefficient and the lt bits' factors move, the keys' map does not.

Main names:
  sdDs            the numbers of coefficients, variable by variable, in the shape's numbers
  SD.ds_length .. SD.ds_i   that list by number
  uniform_sdOf    the terms' skeleton does not depend on the point
  sd_coef_fn, sd_fac_fn   each coefficient and each factor's value reads as a function of the read
                  point that is of degree at most 1 in every coordinate; which coordinates it does
                  not read
  tame_sdOf       **the summand on plain letters is tame**
  tame_sSD        **the prover's summand is tame**
  shape_sSD       the row's part at this sumcheck's number has these numbers of coefficients and the
                  summand's number of end values
  named_sSD       every factor of the prover's summand names one of its end values

The two main statements are UNCONDITIONAL: they hold at any sizes, cells and challenges. shape_sSD
is CONDITIONAL on Planned (Johnson/Desc/K5/Honest/Law/Weights.lean): the planner's numbers, in which
the verifier's list of stages is typed, are the shape's, in which the summand is typed. It calls the
row written out (Johnson/Desc/K5/Honest/Law/Named.lean).
Limits. Nothing says that the summand is the verifier's, nor what its sum is (for that:
Johnson/Desc/K5/Honest/Law/ReadSD.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.ReadSD
import Johnson.Desc.K5.Honest.Law.Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo)
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-- **The numbers of coefficients** at the variables of j, of hk, of i, in the shape's numbers. -/
def sdDs (g : Geo) : List ℕ :=
  List.replicate g.lt 3 ++ List.replicate g.lgk (g.lt + 3) ++ List.replicate g.lt (g.lt + 2)

namespace SD
variable (g : Geo) {v : ℕ}

theorem ds_length : (sdDs g).length = 2 * g.lt + g.lgk := by
  unfold sdDs
  rw [List.length_append, List.length_append, List.length_replicate, List.length_replicate,
    List.length_replicate]
  omega

theorem ds_j (h : v < g.lt) : (sdDs g).getD v 0 = 3 := by
  unfold sdDs
  rw [List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_left (by rw [List.length_replicate]; exact h), List.getElem?_replicate,
    if_pos h]
  rfl

theorem ds_g (h1 : g.lt ≤ v) (h2 : v < g.lt + g.lgk) : (sdDs g).getD v 0 = g.lt + 3 := by
  unfold sdDs
  rw [List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by rw [List.length_replicate]; exact h1), List.length_replicate,
    List.getElem?_append_left (by rw [List.length_replicate]; omega), List.getElem?_replicate,
    if_pos (by omega)]
  rfl

theorem ds_i (h1 : g.lt + g.lgk ≤ v) (h2 : v < 2 * g.lt + g.lgk) :
    (sdDs g).getD v 0 = g.lt + 2 := by
  have hl : (List.replicate g.lt 3 ++ List.replicate g.lgk (g.lt + 3)).length = g.lt + g.lgk := by
    rw [List.length_append, List.length_replicate, List.length_replicate]
  unfold sdDs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; exact h1), hl,
    List.getElem?_replicate, if_pos (by omega)]
  rfl

/-- The numbers below n that are c: at most one. -/
theorem sum_one_le (n c : ℕ) : ∑ j ∈ range n, (if j = c then 1 else 0) ≤ 1 := by
  rw [sum_ite_eq']
  split <;> omega

/-- The numbers below n + 1 that are not 0. -/
theorem sum_not_zero (n : ℕ) : ∑ j ∈ range (n + 1), (if j = 0 then 0 else 1) = n := by
  rw [sum_range_succ']
  simp

end SD

section Text
variable (g : Geo) (w : K5In) (rho om' : Array E)

/-- **The terms' skeleton does not depend on the point.** -/
theorem uniform_sdOf : (sdOf g w rho om').Uniform := by
  intro x y _ _
  show ((List.range g.NP).map _).map _ = ((List.range g.NP).map _).map _
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  have e : ∀ z : Array E, ((List.range g.lt).map (sdBit g z b)).map (·.n) =
      (List.range g.lt).map fun k => g.Lam + b * g.lt + k := fun z => by
    rw [List.map_map]
    exact List.map_congr_left fun k _ => rfl
  show (b / g.HA) :: ((List.range g.lt).map (sdBit g x.toArray b)).map (·.n) =
    (b / g.HA) :: ((List.range g.lt).map (sdBit g y.toArray b)).map (·.n)
  rw [e, e]

/-- A term has lt + 1 factors. -/
theorem sd_factors (x : List E) : ∀ t ∈ (sdOf g w rho om').terms x, t.fs.length ≤ g.lt + 1 := by
  intro t ht
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 ht
  show (_ :: (List.range g.lt).map _).length ≤ _
  rw [List.length_cons, List.length_map, List.length_range]

theorem sd_factors_at (x : List E) (t : ℕ) :
    ((sdOf g w rho om').termAt x t).fs.length = if t < g.NP then g.lt + 1 else 0 := by
  by_cases h : t < g.NP
  · rw [sd_termAt g w rho om' x h, if_pos h]
    show (_ :: (List.range g.lt).map _).length = _
    rw [List.length_cons, List.length_map, List.length_range]
  · rw [sd_termAt_beyond g w rho om' x h, if_neg h]
    rfl

/-- **A coefficient reads as a function of the read point** that is of degree at most 1 in every
coordinate and does not read the coordinates of j. -/
theorem sd_coef_fn (t : ℕ) : ∃ F : (ℕ → K) → K,
    (∀ x : List E, x.length = (sdOf g w rho om').vars →
      ρ.val ((sdOf g w rho om').coefAt t x) = F (ptL ρ x)) ∧
    (∀ v, Deg.Aff v F) ∧ ∀ v, v < g.lt → Deg.Free v F := by
  by_cases h : t < g.NP
  · refine ⟨coF g.lt g.lgk (rho.extract 0 g.lt).size (rho.extract g.lt (g.lt + g.lgk)).size
        (pt ρ (rho.extract 0 g.lt)) (pt ρ (rho.extract g.lt (g.lt + g.lgk)))
        (ρ.val (om'.getD t zeroE)), fun x _ => ?_,
      fun v => aff_coF g.lt g.lgk _ (size_rg_le g rho) _ _ _,
      fun v hv => free_coF g.lt g.lgk _ _ _ _ _ hv⟩
    unfold Summand.coefAt
    rw [sd_termAt g w rho om' x h, ptL_eq ρ x]
    exact read_sdCoef ρ g rho om' t
  · refine ⟨fun _ => 0, fun x _ => ?_, fun v => (Deg.free_const 0).aff,
      fun v _ => Deg.free_const 0⟩
    unfold Summand.coefAt
    rw [sd_termAt_beyond g w rho om' x h]
    exact ρ.zero

/-- **A factor's value reads as a function of the read point** that is of degree at most 1 in every
coordinate. The first factor does not read the coordinates of i. Of the coordinates of j, number v
is read by the first factor and by factor number lt - v alone. -/
theorem sd_fac_fn (t j : ℕ) : ∃ F : (ℕ → K) → K,
    (∀ x : List E, x.length = (sdOf g w rho om').vars →
      ρ.val ((sdOf g w rho om').facAt t j x) = F (ptL ρ x)) ∧
    (∀ v, Deg.Aff v F) ∧ (j = 0 → ∀ v, g.lt + g.lgk ≤ v → Deg.Free v F) ∧
    ∀ v, v < g.lt → j ≠ 0 → j ≠ g.lt - v → Deg.Free v F := by
  have zero : (∀ x : List E, ρ.val ((sdOf g w rho om').facAt t j x) = 0) →
      ∃ F : (ℕ → K) → K,
        (∀ x : List E, x.length = (sdOf g w rho om').vars →
          ρ.val ((sdOf g w rho om').facAt t j x) = F (ptL ρ x)) ∧
        (∀ v, Deg.Aff v F) ∧ (j = 0 → ∀ v, g.lt + g.lgk ≤ v → Deg.Free v F) ∧
        ∀ v, v < g.lt → j ≠ 0 → j ≠ g.lt - v → Deg.Free v F := fun h0 =>
    ⟨fun _ => 0, fun x _ => h0 x, fun v => (Deg.free_const 0).aff,
      fun _ v _ => Deg.free_const 0, fun v _ _ _ => Deg.free_const 0⟩
  by_cases h : t < g.NP
  · cases j with
    | zero =>
      refine ⟨kcF g.lt g.lgk fun n => ρ.val ((kcTab g w rho (t / g.HA)).getD n zeroE),
        fun x hx => ?_, fun v => aff_kcF g.lt g.lgk _,
        fun _ v hv => free_kcF g.lt g.lgk _ hv, fun v _ h0 _ => absurd rfl h0⟩
      unfold Summand.facAt
      rw [sd_termAt g w rho om' x h]
      exact read_fac_kc ρ g w rho om' hx h
    | succ k =>
      by_cases hk : k < g.lt
      · refine ⟨bitF g.lt g.lgk k fun hk i => ρ.val (w.ibit k t hk i), fun x hx => ?_,
          fun v => aff_bitF g.lt g.lgk hk _,
          fun h0 => absurd h0 (Nat.succ_ne_zero k),
          fun v hv _ hne => free_bitF g.lt g.lgk k _ hv (by omega)⟩
        unfold Summand.facAt
        rw [sd_termAt g w rho om' x h]
        show ρ.val ((sdOf g w rho om').factorAt x
          (((List.range g.lt).map (sdBit g x.toArray t)).getD k _)) = _
        rw [SD.getD_map_range, if_pos hk]
        exact read_fac_bit ρ g w rho om' hx t hk
      · refine zero fun x => ?_
        unfold Summand.facAt
        rw [sd_termAt g w rho om' x h]
        show ρ.val ((sdOf g w rho om').factorAt x
          (((List.range g.lt).map (sdBit g x.toArray t)).getD k _)) = _
        rw [SD.getD_map_range, if_neg hk]
        exact read_noFactor ρ _ x
  · refine zero fun x => ?_
    unfold Summand.facAt
    rw [sd_termAt_beyond g w rho om' x h]
    exact read_noFactor ρ _ x

/-- **The summand "the key at the index" is tame at the shape's numbers of coefficients (sdDs)**: 3
at a variable of j, lt + 3 at a variable of hk, lt + 2 at a variable of i, lt + 2 in Y.
Unconditional: whatever the sizes, the cells and the two arrays of public letters are. It leans on
one definition: the number of pairs is the number of layers times the number of query heads to a
head (Geo.NP, Johnson/Desc/First/Att/Geo.lean), so a pair's first factor names a layer's keys, which
do not move with i, and never a cell of the index. -/
theorem tame_sdOf : (sdOf g w rho om').Tame ρ (sdDs g) (g.lt + 1) where
  vars := SD.ds_length g
  uniform := uniform_sdOf g w rho om'
  coef := fun v t => by
    obtain ⟨F, hr, ha, _⟩ := sd_coef_fn ρ g w rho om' t
    exact affine_of_reads ρ hr (ha v)
  fact := fun v t j => by
    obtain ⟨F, hr, ha, _⟩ := sd_fac_fn ρ g w rho om' t j
    exact affine_of_reads ρ hr (ha v)
  cut := fun rs hrs j hj => by
    have hrs' : rs.length < 2 * g.lt + g.lgk := hrs
    by_cases h1 : rs.length < g.lt
    · -- a variable of j: the keys' map and one bit's factor move
      rw [SD.ds_j g h1] at hj
      refine (sdOf g w rho om').cut_of_still ρ (uniform_sdOf g w rho om') rs hrs 3 (fun _ => 0)
        (fun _ i => (if i = 0 then 1 else 0) + (if i = g.lt - rs.length then 1 else 0))
        (fun t _ => ?_) (fun t i e => ?_) (fun x _ t => ?_) j hj
      · obtain ⟨F, hr, _, hf⟩ := sd_coef_fn ρ g w rho om' t
        exact still_of_reads ρ hr (hf _ h1)
      · obtain ⟨F, hr, _, _, hf⟩ := sd_fac_fn ρ g w rho om' t i
        have e0 : i ≠ 0 := fun h => by simp [h] at e
        have e1 : i ≠ g.lt - rs.length := fun h => by simp [h] at e
        exact still_of_reads ρ hr (hf _ h1 e0 e1)
      · show 0 + ∑ i ∈ range ((sdOf g w rho om').termAt x t).fs.length,
          ((if i = 0 then 1 else 0) + (if i = g.lt - rs.length then 1 else 0)) < 3
        rw [sum_add_distrib]
        have a := SD.sum_one_le ((sdOf g w rho om').termAt x t).fs.length 0
        have b := SD.sum_one_le ((sdOf g w rho om').termAt x t).fs.length (g.lt - rs.length)
        omega
    · by_cases h2 : rs.length < g.lt + g.lgk
      · -- a variable of hk: nothing is dropped
        rw [SD.ds_g g (by omega) h2] at hj
        exact read_beyond ρ _ j (Nat.le_trans
          ((sdOf g w rho om').length_round_le (g.lt + 1) (sd_factors g w rho om') rs) hj)
      · -- a variable of i: the keys' map does not move
        rw [SD.ds_i g (by omega) hrs'] at hj
        refine (sdOf g w rho om').cut_of_still ρ (uniform_sdOf g w rho om') rs hrs (g.lt + 2)
          (fun _ => 1) (fun _ i => if i = 0 then 0 else 1)
          (fun t e => absurd e Nat.one_ne_zero) (fun t i e => ?_) (fun x _ t => ?_) j hj
        · obtain ⟨F, hr, _, hf, _⟩ := sd_fac_fn ρ g w rho om' t i
          have e0 : i = 0 := by
            by_contra h
            simp [h] at e
          exact still_of_reads ρ hr (hf e0 _ (by omega))
        · show 1 + ∑ i ∈ range ((sdOf g w rho om').termAt x t).fs.length,
            (if i = 0 then 0 else 1) < g.lt + 2
          rw [sd_factors_at]
          by_cases ht : t < g.NP
          · rw [if_pos ht, SD.sum_not_zero]
            omega
          · rw [if_neg ht, range_zero, sum_empty]
            omega
  cutY := fun rs m _ j hj =>
    read_beyond ρ _ j (Nat.le_trans
      ((sdOf g w rho om').length_inY_le (g.lt + 1) rs m (sd_factors g w rho om' rs)) hj)

end Text

/-- **The prover's summand "the key at the index" is tame at the shape's numbers of coefficients
(sdDs).** Unconditional. That these are the verifier's: `shape_sSD`, conditional. -/
theorem tame_sSD (P : Pub5) (w : K5In) (c : Chal) :
    (sSD P w c).Tame ρ (sdDs P.g) (P.g.lt + 1) := by
  rw [sSD_eq]
  exact tame_sdOf ρ P.g w _ _

/-- **The row's part at this sumcheck's number has the summand's numbers**: no scalar in front, the
numbers of coefficients sdDs, lt + 2 coefficients in Y, and as many end values as the summand has.
CONDITIONAL on: the planner's numbers are the shape's (Planned): public, with code, the caller's. -/
theorem shape_sSD {P : Pub5} (Pl : Planned P) (w : K5In) (c : Chal) :
    (shapes P.x)[iSD P.x]? =
      some (.sum ⟨0, (sdDs P.g).map .plain, some ⟨P.g.lt + 1, (sSD P w c).ends⟩⟩) := by
  rw [shape_iSD]
  unfold keyVars
  rw [Pl.lt, Pl.lgk, Pl.Lam, Pl.pairs]
  rfl

/-- Every factor of the prover's summand names one of its end values. -/
theorem named_sSD (P : Pub5) (w : K5In) (c : Chal) :
    (sSD P w c).Named (P.g.Lam + P.g.NP * P.g.lt) := by
  rw [sSD_eq]
  exact named_sdOf P.g w _ _

end H2K5.Honest

#print axioms H2K5.Honest.SD.ds_length
#print axioms H2K5.Honest.SD.ds_j
#print axioms H2K5.Honest.SD.ds_g
#print axioms H2K5.Honest.SD.ds_i
#print axioms H2K5.Honest.SD.sum_one_le
#print axioms H2K5.Honest.SD.sum_not_zero
#print axioms H2K5.Honest.uniform_sdOf
#print axioms H2K5.Honest.sd_factors
#print axioms H2K5.Honest.sd_factors_at
#print axioms H2K5.Honest.sd_coef_fn
#print axioms H2K5.Honest.sd_fac_fn
#print axioms H2K5.Honest.tame_sdOf
#print axioms H2K5.Honest.tame_sSD
#print axioms H2K5.Honest.shape_sSD
#print axioms H2K5.Honest.named_sSD
