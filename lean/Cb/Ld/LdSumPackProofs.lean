-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumPackProofs.lean: proofs of all `Spec` statements of Cb/Ld/LdSumPack.lean, on packing a
polynomial's coefficients into a table. Nothing is assumed beyond the hypotheses of the statements
and whatever the arguments hold as proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: the sumcheck of Cb/Ld/LdSum.lean has the packing as a parameter (`SumPar.pk`, `SumPar.Qw`) with
the condition `SumPar.PackOK`; here the packings of Cb/Ld/LdSumPack.lean are proved to meet it
(`PackLaw`, `ld_pack_ok_iff`).
The main statement is `ld_pack_law`: for all h, g, m, the table `pkC h g m W` of the coefficients W
of the polynomial `hU` (Cb/Ld/LdHide.lean) in h + g variables and the weights `QwC h g m` meet
`PackLaw h g (m + 1)` (m + 1: the largest degree of a round polynomial): the polynomial at a point γ
is the sum, over the columns, of the weight at γ times the table folded at the first h coordinates
of γ. The other statements are told in Cb/Ld/LdSumPack.lean.
A column of the second summand of `PCol` is leading (`pLead`) if it is that of the first coefficient
of the variable h + 1, or that of the constant if g = 0.

Notation (where no file is named: Cb/Ld/LdSumPack.lean):
  `h`, `g`, `m`: natural numbers; the polynomial has h + g variables;
  `PackLaw`: the law of a packing, for tables with rows on the cube of the first h variables and
    columns J;
  `PCol h g m`: the columns: (i, p - 2) for the first h variables; the coefficients of the last g
    variables; the constant;
  `pkC`: the table; `QwC`: the public weights;
  `pMon i β`: the monomial X_i .. X_h at a corner of the cube;
  `hIx`, `hCst`: the name of the coefficient of X_l^(p+1) .., and of the constant;
  `HIdx`: the names of the coefficients; `hU`: the hiding polynomial, as a function of a point
    (both: Cb/Ld/LdHide.lean);
  `sPt`: a point as a function of the variable (Cb/Ld/LdSum.lean);
  `foldV γ v`: the fold of a vector with rows on the cube (Cb/Ld/LdRel.lean).
-/
import Cb.Ld.LdSumPack
import Cb.Ld.LdHideProofs

set_option autoImplicit false

namespace Cb
open Prob

section
variable {E : Type} [Field E]

/-! ## The polynomial, written out -/

theorem hPsi_plain {n : ℕ} (hn : 1 ≤ n) :
    ∀ (k : ℕ) (γ : HPt (sVars E n k)), hPsi (sVars E n k) γ = ∏ j, sPt n k γ j
  | 0, _ => by
      rw [Fin.prod_univ_zero]
      rfl
  | k + 1, γ => by
      show hev (HVar.plain E n).psi γ.1 * hPsi (sVars E n k) γ.2 = _
      rw [plain_psi E n γ.1 hn, hPsi_plain hn k γ.2, Fin.prod_univ_succ]
      rfl

theorem tail_zero {k : ℕ} (z : Fin (k + 1) → E) :
    (∏ j : Fin (k + 1), if (0 : Fin (k + 1)) < j then z j else 1) = ∏ j : Fin k, z j.succ := by
  rw [Fin.prod_univ_succ]
  simp [Fin.succ_pos]

theorem tail_succ {k : ℕ} (z : Fin (k + 1) → E) (l : Fin k) :
    (∏ j : Fin (k + 1), if l.succ < j then z j else 1) =
      ∏ j : Fin k, if l < j then z j.succ else 1 := by
  rw [Fin.prod_univ_succ]
  simp [Fin.succ_lt_succ_iff]

end

theorem ld_pack_formula (E : Type) [Field E] : Spec.ld_pack_formula E := by
  intro n k hn
  induction k with
  | zero =>
      intro W γ
      rw [Fin.sum_univ_zero, zero_add]
      rfl
  | succ k ih =>
      intro W γ
      have h1 : hU (sVars E n (k + 1)) W γ =
          hPsi (sVars E n k) γ.2 • hev (Fin.cons 0 fun t => W (.inl t) : Fin (n + 1) → E) γ.1 +
            hU (sVars E n k) (fun i => W (.inr i)) γ.2 := rfl
      rw [h1, ih, hPsi_plain hn, hev_cons0, Fin.sum_univ_succ, tail_zero, ← add_assoc]
      congr 1
      congr 1
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        show (∏ j, sPt n k γ.2 j) * (γ.1 ^ (p.val + 1) * W (.inl p)) =
          W (.inl p) * (γ.1 ^ (p.val + 1) * ∏ j : Fin k, sPt n k γ.2 j)
        ring
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [tail_succ]
        rfl

/-! ## Sums over the cube -/

section
variable {E : Type} [Field E]

/-- a sum over the cube of a product with one factor for each variable -/
theorem sum_cube_prod {h : ℕ} (F : Fin h → Bool → E) :
    ∑ β : Fin h → Bool, ∏ j, F j (β j) = ∏ j, (F j true + F j false) := by
  have h1 := Finset.prod_univ_sum (fun _ : Fin h => (Finset.univ : Finset Bool)) F
  rw [Fintype.piFinset_univ] at h1
  rw [← h1]
  exact Finset.prod_congr rfl fun j _ => Fintype.sum_bool _

/-- Folding evaluates a tabulated monomial. -/
theorem fold_pMon {h : ℕ} (z : Fin h → E) (i : Fin h) :
    ∑ β, Alg.eqk z β * pMon i β = ∏ j, if i ≤ j then z j else 1 := by
  have h1 : ∀ β : Fin h → Bool, Alg.eqk z β * pMon i β =
      ∏ j, (fun (j : Fin h) (b : Bool) =>
          (if b then z j else 1 - z j) * (if i ≤ j then (if b then 1 else 0) else 1))
        j (β j) := fun β => by
    unfold Alg.eqk pMon
    rw [← Finset.prod_mul_distrib]
  refine (Finset.sum_congr rfl fun β _ => h1 β).trans
    ((sum_cube_prod (fun (j : Fin h) (b : Bool) =>
      (if b then z j else 1 - z j) * (if i ≤ j then (if b then 1 else 0) else 1))).trans ?_)
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : i ≤ j
  · simp [hij]
  · simp [hij]

/-- X_i .. X_h = X_i · (X_(i+1) .. X_h) -/
theorem mon_split {h : ℕ} (z : Fin h → E) (i : Fin h) :
    (∏ j, if i ≤ j then z j else 1) = z i * ∏ j, if i < j then z j else 1 := by
  have h1 : ∀ j : Fin h, (if i ≤ j then z j else 1) =
      (if j = i then z i else 1) * (if i < j then z j else 1) := fun j => by
    rcases lt_trichotomy i j with hl | hl | hl
    · rw [if_pos hl.le, if_neg hl.ne', if_pos hl, one_mul]
    · subst hl
      rw [if_pos le_rfl, if_pos rfl, if_neg (lt_irrefl _), mul_one]
    · rw [if_neg (not_le.mpr hl), if_neg hl.ne, if_neg (not_lt.mpr hl.le), one_mul]
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i fun _ => z i, if_pos (Finset.mem_univ i)]

theorem tail_cast {h g : ℕ} (z : Fin (h + g) → E) (i : Fin h) :
    (∏ j : Fin (h + g), if Fin.castAdd g i < j then z j else 1) =
      (∏ j : Fin h, if i < j then z (Fin.castAdd g j) else 1) *
        ∏ t : Fin g, z (Fin.natAdd h t) := by
  rw [Fin.prod_univ_add]
  congr 1
  refine Finset.prod_congr rfl fun t _ => if_pos ?_
  rw [Fin.lt_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem tail_nat {h g : ℕ} (z : Fin (h + g) → E) (t : Fin g) :
    (∏ j : Fin (h + g), if Fin.natAdd h t < j then z j else 1) =
      ∏ t' : Fin g, if t < t' then z (Fin.natAdd h t') else 1 := by
  rw [Fin.prod_univ_add]
  have h1 : (∏ j : Fin h, if Fin.natAdd h t < Fin.castAdd g j then z (Fin.castAdd g j) else 1) = 1 := Finset.prod_eq_one fun j _ => if_neg (by
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega)
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun t' _ => ?_
  have h2 : Fin.natAdd h t < Fin.natAdd h t' ↔ t < t' := by
    rw [Fin.lt_def, Fin.lt_def]
    simp only [Fin.val_natAdd]
    omega
  simp only [h2]

/-- the weights of the columns of the last g variables and of the constant, from the last g
coordinates -/
def wLate {g m : ℕ} (zl : Fin g → E) : (Fin g × Fin (m + 1)) ⊕ Unit → E
  | .inl tp => zl tp.1 ^ (tp.2.val + 1) * ∏ t : Fin g, if tp.1 < t then zl t else 1
  | .inr _ => 1

/-- The weights (`wLate`) of the leading columns (`pLead`) sum to the product of the last g
coordinates, X_(h+1) .. X_k; by `pLead` exactly one column is leading. -/
theorem lead_sum {m : ℕ} :
    ∀ {g : ℕ} (zl : Fin g → E) (Λ : E),
      ∑ s, wLate (m := m) zl s * (if pLead g m s then Λ else 0) = (∏ t, zl t) * Λ
  | 0, zl, Λ => by
      rw [Fintype.sum_sum_type, Fin.prod_univ_zero]
      simp [wLate, pLead]
  | g + 1, zl, Λ => by
      rw [Fintype.sum_sum_type]
      have h1 : ∑ u : Unit,
            wLate (m := m) zl (.inr u) * (if pLead (g + 1) m (.inr u) then Λ else 0) = 0 := by
        simp [pLead]
      rw [h1, add_zero, Fintype.sum_eq_single ((0 : Fin (g + 1)), (0 : Fin (m + 1)))]
      · have h2 : pLead (g + 1) m (.inl ((0 : Fin (g + 1)), (0 : Fin (m + 1)))) = true := by
          simp [pLead]
        rw [h2, if_pos rfl]
        show (zl 0 ^ (0 + 1) * ∏ t : Fin (g + 1), if (0 : Fin (g + 1)) < t then zl t else 1) * Λ = _
        rw [tail_zero, Fin.prod_univ_succ, zero_add, pow_one]
      · intro tp htp
        have h2 : pLead (g + 1) m (.inl tp) = false := by
          unfold pLead
          rw [decide_eq_false_iff_not]
          exact fun hc => htp (Prod.ext (Fin.ext hc.1) (Fin.ext hc.2))
        rw [h2]
        simp

/-! ## The folded table -/

theorem fold_inl (h g m : ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E)
    (z' : Fin h → E) (iq : Fin h × Fin m) :
    foldV z' (pkC h g m W) (.inl iq) =
      W (hIx E (m + 1) (h + g) (Fin.castAdd g iq.1) iq.2.succ) *
        ∏ j, if iq.1 ≤ j then z' j else 1 := by
  rw [← fold_pMon, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  show Alg.eqk z' β * (W (hIx E (m + 1) (h + g) (Fin.castAdd g iq.1) iq.2.succ) * pMon iq.1 β) = _
  ring

/-- the coefficient that a column of the second summand of `PCol` (the last g variables, the
constant) holds in every row -/
def pBase (h g m : ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E) : (Fin g × Fin (m + 1)) ⊕ Unit → E
  | .inl tp => W (hIx E (m + 1) (h + g) (Fin.natAdd h tp.1) tp.2)
  | .inr _ => W (hCst E (m + 1) (h + g))

theorem fold_inr (h g m : ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E)
    (z' : Fin h → E) (s : (Fin g × Fin (m + 1)) ⊕ Unit) :
    foldV z' (pkC h g m W) (.inr s) =
      pBase h g m W s +
        if pLead g m s then
          ∑ i : Fin h,
            W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * ∏ j, (if i ≤ j then z' j else 1)
        else 0 := by
  have h1 : ∀ β : Fin h → Bool, pkC h g m W (β, .inr s) =
      pBase h g m W s +
        if pLead g m s then ∑ i : Fin h, W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * pMon i β
        else 0 := fun β => by
    rcases s with tp | u <;> rfl
  unfold foldV
  rw [Finset.sum_congr rfl fun β _ => by rw [h1 β, mul_add], Finset.sum_add_distrib,
    ← Finset.sum_mul, Alg.sum_eqk, one_mul]
  congr 1
  by_cases hl : pLead g m s = true
  · simp only [hl, if_true]
    rw [Finset.sum_congr rfl fun β _ => Finset.mul_sum _ _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← fold_pMon, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  · simp [hl]

end

/-! ## The law -/

theorem ld_pack_law (E : Type) [Field E] : Spec.ld_pack_law E := by
  intro h g m W γ
  rw [ld_pack_formula E (m + 1) (h + g) (Nat.succ_le_succ (Nat.zero_le m)) W γ]
  generalize sPt (m + 1) (h + g) γ = z
  have hw : ∀ s, QwC h g m z (.inr s) = wLate (fun t => z (Fin.natAdd h t)) s := fun s => by
    rcases s with tp | u <;> rfl
  have hu : ∑ u : Unit,
        wLate (m := m) (fun t => z (Fin.natAdd h t)) (.inr u) * pBase h g m W (.inr u) =
      W (hCst E (m + 1) (h + g)) := by
    rw [Fintype.sum_unique]
    exact one_mul _
  -- the right-hand side
  have hR : ∑ j : PCol h g m, QwC h g m z j * foldV (fun i => z (Fin.castAdd g i)) (pkC h g m W) j =
      (∑ i : Fin h, ∑ q : Fin m, QwC h g m z (.inl (i, q)) *
          (W (hIx E (m + 1) (h + g) (Fin.castAdd g i) q.succ) *
            ∏ j : Fin h, if i ≤ j then z (Fin.castAdd g j) else 1)) +
        ((∑ t : Fin g, ∑ p : Fin (m + 1),
              wLate (fun t => z (Fin.natAdd h t)) (.inl (t, p)) * pBase h g m W (.inl (t, p)) +
            W (hCst E (m + 1) (h + g))) +
          (∏ t : Fin g, z (Fin.natAdd h t)) *
            ∑ i : Fin h, W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * ∏ j : Fin h, if i ≤ j then
              z (Fin.castAdd g j)
            else 1) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by rw [fold_inl]
    · have h1 : ∀ s,
        QwC h g m z (.inr s) * foldV (fun i => z (Fin.castAdd g i)) (pkC h g m W) (.inr s)
          = wLate (fun t => z (Fin.natAdd h t)) s * pBase h g m W s +
              wLate (fun t => z (Fin.natAdd h t)) s *
                (if pLead g m s then
                    ∑ i : Fin h, W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) *
                      ∏ j : Fin h, (if i ≤ j then z (Fin.castAdd g j) else 1)
                  else 0) := fun s => by
        rw [fold_inr, hw s, mul_add]
      rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_add_distrib, lead_sum,
        Fintype.sum_sum_type, Fintype.sum_prod_type, hu]
  -- the left-hand side
  have hc : ∀ i : Fin h, ∑ p : Fin (m + 1), W (hIx E (m + 1) (h + g) (Fin.castAdd g i) p) *
        (z (Fin.castAdd g i) ^ (p.val + 1) *
          ∏ j : Fin (h + g), if Fin.castAdd g i < j then z j else 1) =
      (∏ t : Fin g, z (Fin.natAdd h t)) *
          (W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) *
            ∏ j : Fin h, if i ≤ j then z (Fin.castAdd g j) else 1) +
        ∑ q : Fin m, QwC h g m z (.inl (i, q)) *
          (W (hIx E (m + 1) (h + g) (Fin.castAdd g i) q.succ) *
            ∏ j : Fin h, if i ≤ j then z (Fin.castAdd g j) else 1) := fun i => by
    rw [Fin.sum_univ_succ, tail_cast, mon_split (fun j => z (Fin.castAdd g j)) i]
    congr 1
    · simp only [Fin.val_zero, zero_add, pow_one]
      ring
    · refine Finset.sum_congr rfl fun q _ => ?_
      show _ = (z (Fin.castAdd g i) ^ (q.val + 1) * ∏ t : Fin g, z (Fin.natAdd h t)) * _
      rw [Fin.val_succ, pow_succ (z (Fin.castAdd g i)) (q.val + 1)]
      ring
  have hn : ∀ t : Fin g, ∑ p : Fin (m + 1), W (hIx E (m + 1) (h + g) (Fin.natAdd h t) p) *
        (z (Fin.natAdd h t) ^ (p.val + 1) *
          ∏ j : Fin (h + g), if Fin.natAdd h t < j then z j else 1) =
      ∑ p : Fin (m + 1), wLate (fun t => z (Fin.natAdd h t)) (.inl (t, p)) *
        pBase h g m W (.inl (t, p)) := fun t => by
    rw [tail_nat]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  rw [hR, Fin.sum_univ_add, Finset.sum_congr rfl fun i _ => hc i,
    Finset.sum_congr rfl fun t _ => hn t, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ## `SumPar.PackOK`, the number of columns, padding, the plain packing -/

theorem ld_pack_ok_iff (E : Type) [Field E] : Spec.ld_pack_ok_iff E := fun _ _ => Iff.rfl

theorem ld_pack_card : Spec.ld_pack_card := by
  intro h g m
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  ring

section
variable {E : Type} [Field E] {Cl J : Type} [Fintype Cl] [DecidableEq J]

theorem placeV_at {plc : Cl → J} (hp : Function.Injective plc) (v : Cl → E) (c : Cl) :
    placeV plc v (plc c) = v c := by
  classical
  unfold placeV
  simp only [hp.eq_iff]
  rw [Finset.sum_ite_eq' Finset.univ c v, if_pos (Finset.mem_univ c)]

theorem placeV_sum [Fintype J] (plc : Cl → J) (a : Cl → E) (B : J → E) :
    ∑ j, placeV plc a j * B j = ∑ c, a c * B (plc c) := by
  unfold placeV
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (plc c) fun j => a c * B j, if_pos (Finset.mem_univ _)]

theorem foldV_place {h : ℕ} {Ix : Type} (plc : Cl → J) (pk : (Ix → E) → (Fin h → Bool) × Cl → E)
    (W : Ix → E) (z' : Fin h → E) (j : J) :
    foldV z' (pkAt plc pk W) j = placeV plc (foldV z' (pk W)) j := by
  unfold foldV pkAt placeV
  rw [Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : plc c = j
  · simp only [hc, if_true]
  · simp only [hc, if_false, mul_zero, Finset.sum_const_zero]

end

theorem ld_pack_place (E : Type) [Field E] : Spec.ld_pack_place E := by
  intro h g n Cl J _ _ _ plc pk Qw hp hl W γ
  rw [hl W γ]
  unfold QwAt
  rw [placeV_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [foldV_place, placeV_at hp]

section
variable {E : Type} [Field E]

theorem sUn_sPt (n : ℕ) : ∀ (k : ℕ) (γ : HPt (sVars E n k)), sUn n k (sPt n k γ) = γ
  | 0, _ => rfl
  | k + 1, γ => by
      show (γ.1, sUn n k (Fin.tail (Fin.cons γ.1 (sPt n k γ.2) : Fin (k + 1) → E))) = γ
      rw [Fin.tail_cons, sUn_sPt n k γ.2]
      rfl

end

theorem ld_pack0 (E : Type) [Field E] : Spec.ld_pack0 E := by
  intro g n W γ
  rw [hide_form E E _ W γ]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : foldV (fun i : Fin 0 => sPt n (0 + g) γ (Fin.castAdd g i)) (pk0 g n W) j = W j := by
    unfold foldV
    rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)]
    simp [Alg.eqk, pk0]
  rw [h1]
  unfold Qw0
  rw [sUn_sPt]
  rfl

/-! ## Linear and injective -/

section
variable {E : Type} [Field E]

theorem pkC_inr (h g m : ℕ) (W : HIdx (sVars E (m + 1) (h + g)) → E)
    (β : Fin h → Bool) (s : (Fin g × Fin (m + 1)) ⊕ Unit) :
    pkC h g m W (β, .inr s) =
      pBase h g m W s +
        if pLead g m s then ∑ i : Fin h, W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * pMon i β
        else 0 := by
  rcases s with tp | u <;> rfl

theorem pBase_lin (h g m : ℕ) (W W' : HIdx (sVars E (m + 1) (h + g)) → E)
    (c : E) (s : (Fin g × Fin (m + 1)) ⊕ Unit) :
    pBase h g m (W + c • W') s = pBase h g m W s + c * pBase h g m W' s := by
  rcases s with tp | u <;> rfl

end

theorem ld_pack_lin (E : Type) [Field E] : Spec.ld_pack_lin E := by
  intro h g m W W' c
  funext a
  obtain ⟨β, iq | s⟩ := a
  · show (W _ + c * W' _) * pMon iq.1 β = W _ * pMon iq.1 β + c * (W' _ * pMon iq.1 β)
    ring
  · show pkC h g m (W + c • W') (β, .inr s) = pkC h g m W (β, .inr s) + c * pkC h g m W' (β, .inr s)
    rw [pkC_inr, pkC_inr, pkC_inr, pBase_lin]
    by_cases hl : pLead g m s = true
    · simp only [hl, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_add, Finset.mul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [hl, Bool.false_eq_true, if_false, add_zero]

section
variable {E : Type} [Field E]

/-- every coefficient has a name -/
theorem hIx_surj (n : ℕ) :
    ∀ (k : ℕ) (a : HIdx (sVars E n k)), (∃ l p, a = hIx E n k l p) ∨ a = hCst E n k
  | 0, _ => Or.inr rfl
  | _ + 1, .inl p => Or.inl ⟨0, p, rfl⟩
  | k + 1, .inr a =>
    (hIx_surj n k a).elim (fun ⟨l, p, h⟩ => Or.inl ⟨l.succ, p, congrArg Sum.inr h⟩)
      fun h => Or.inr (congrArg Sum.inr h)

theorem exists_lead (m : ℕ) : ∀ g : ℕ, ∃ s, pLead g m s = true
  | 0 => ⟨.inr (), by simp [pLead]⟩
  | g + 1 => ⟨.inl (0, 0), by simp [pLead]⟩

/-- the monomial X_i .. X_h at the corner β with β_j = 1 if and only if a ≤ j -/
theorem pMon_from {h : ℕ} (i : Fin h) (a : ℕ) :
    pMon (E := E) i (fun j => decide (a ≤ j.val)) = if a ≤ i.val then 1 else 0 := by
  unfold pMon
  by_cases ha : a ≤ i.val
  · rw [if_pos ha]
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hij : i ≤ j
    · have : a ≤ j.val := ha.trans hij
      simp [hij, this]
    · simp [hij]
  · rw [if_neg ha]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [ha]

end

theorem ld_pack_names (E : Type) [Field E] : Spec.ld_pack_names E := by
  intro n k
  refine (Fintype.bijective_iff_surjective_and_card _).2 ⟨fun a => ?_, ?_⟩
  · rcases hIx_surj n k a with ⟨l, p, h⟩ | h
    · exact ⟨.inl (l, p), h.symm⟩
    · exact ⟨.inr (), h.symm⟩
  · rw [plain_card E k n]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]

theorem ld_pack_inj (E : Type) [Field E] : Spec.ld_pack_inj E := by
  intro h g m W W' hEq
  -- columns of the second summand of `PCol`, at the corner with β_j = 1 iff a ≤ j (a = h: 0 .. 0)
  have hrow : ∀ (a : ℕ) (s : (Fin g × Fin (m + 1)) ⊕ Unit), pBase h g m W s +
        (if pLead g m s then
            ∑ i : Fin h,
              W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * (if a ≤ i.val then 1 else 0)
          else 0) =
      pBase h g m W' s +
        (if pLead g m s then
            ∑ i : Fin h,
              W' (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * (if a ≤ i.val then 1 else 0)
          else 0) := fun a s => by
    have h1 := congrFun hEq (fun j => decide (a ≤ j.val), .inr s)
    rw [pkC_inr, pkC_inr] at h1
    simpa only [pMon_from] using h1
  have hbase : ∀ s, pBase h g m W s = pBase h g m W' s := fun s => by
    have h1 := hrow h s
    have hz : ∀ V : HIdx (sVars E (m + 1) (h + g)) → E, ∑ i : Fin h,
          V (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * (if h ≤ i.val then (1 : E) else 0) =
        0 := fun V =>
      Finset.sum_eq_zero fun i _ => by rw [if_neg (not_le.mpr i.2), mul_zero]
    rw [hz W, hz W'] at h1
    simpa using h1
  obtain ⟨sL, hsL⟩ := exists_lead m g
  have hsum : ∀ a : ℕ, ∑ i : Fin h,
        W (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) * (if a ≤ i.val then (1 : E) else 0) =
      ∑ i : Fin h, W' (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) *
        (if a ≤ i.val then (1 : E) else 0) := fun a => by
    have h1 := hrow a sL
    rw [hbase sL, hsL] at h1
    simpa using h1
  have hone : ∀ (V : HIdx (sVars E (m + 1) (h + g)) → E) (i : Fin h),
      V (hIx E (m + 1) (h + g) (Fin.castAdd g i) 0) =
        ∑ i' : Fin h, V (hIx E (m + 1) (h + g) (Fin.castAdd g i') 0) *
            (if i.val ≤ i'.val then (1 : E) else 0) -
          ∑ i' : Fin h, V (hIx E (m + 1) (h + g) (Fin.castAdd g i') 0) *
            (if i.val + 1 ≤ i'.val then (1 : E) else 0) := fun V i => by
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single i]
    · simp
    · intro i' hne
      have hv : i'.val ≠ i.val := fun hc => hne (Fin.ext hc)
      by_cases h1 : i.val ≤ i'.val
      · have h2 : i.val + 1 ≤ i'.val := by omega
        simp [h1, h2]
      · have h2 : ¬ i.val + 1 ≤ i'.val := by omega
        simp [h1, h2]
  funext a
  rcases hIx_surj (m + 1) (h + g) a with ⟨l, p, rfl⟩ | rfl
  · refine Fin.addCases (fun i => ?_) (fun t => ?_) l
    · refine Fin.cases ?_ (fun q => ?_) p
      · rw [hone W i, hone W' i, hsum, hsum]
      · have h1 := congrFun hEq (fun j => decide (0 ≤ j.val), .inl (i, q))
        have h2 : ∀ V : HIdx (sVars E (m + 1) (h + g)) → E,
            pkC h g m V (fun j => decide (0 ≤ j.val), .inl (i, q)) =
              V (hIx E (m + 1) (h + g) (Fin.castAdd g i) q.succ) *
                pMon i (fun j => decide (0 ≤ j.val)) := fun _ => rfl
        rw [h2, h2, pMon_from, if_pos (Nat.zero_le _), mul_one, mul_one] at h1
        exact h1
    · exact hbase (.inl (t, p))
  · exact hbase (.inr ())

/-! ## The degrees of the weights -/

section
variable {E : Type} [Field E]
open Polynomial

theorem deg_pow {ι : Type} [DecidableEq ι] (a : ι) (r : ℕ) :
    Alg.DegLE (fun v => if v = a then r else 0) (fun z : ι → E => z a ^ r) := fun z i => by
  by_cases hi : i = a
  · subst hi
    exact ⟨X ^ r, (natDegree_X_pow_le r).trans (le_of_eq (if_pos rfl).symm), fun t => by simp⟩
  · exact ⟨C (z a ^ r), by simp, fun t => by simp [Function.update_of_ne (fun e => hi e.symm)]⟩

/-- a product of some of the last g coordinates -/
theorem deg_late {h g : ℕ} (c : Fin g → Prop) [DecidablePred c] :
    Alg.DegLE (fun v : Fin (h + g) => ∑ t : Fin g, if c t ∧ v = Fin.natAdd h t then 1 else 0)
      (fun z : Fin (h + g) → E => ∏ t : Fin g, if c t then z (Fin.natAdd h t) else 1) := by
  refine Alg.DegLE.prod Finset.univ (d := fun t v => if c t ∧ v = Fin.natAdd h t then 1 else 0)
    (g := fun t z => if c t then z (Fin.natAdd h t) else 1) fun t _ => ?_
  by_cases hc : c t
  · simp only [hc, true_and, if_true]
    simpa only [pow_one] using deg_pow (E := E) (Fin.natAdd h t) 1
  · simp only [hc, false_and, if_false]
    exact Alg.DegLE.const _ 1

theorem late_le_one {h g : ℕ} (c : Fin g → Prop) [DecidablePred c] (v : Fin (h + g)) :
    (∑ t : Fin g, if c t ∧ v = Fin.natAdd h t then 1 else 0) ≤ 1 := by
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_one.2 fun t ht t' ht' => ?_
  have h1 := (Finset.mem_filter.1 ht).2.2
  have h2 := (Finset.mem_filter.1 ht').2.2
  have h3 : (Fin.natAdd h t).val = (Fin.natAdd h t').val := congrArg Fin.val (h1.symm.trans h2)
  simp only [Fin.val_natAdd] at h3
  exact Fin.ext (by omega)

theorem late_eq_zero {h g : ℕ} (c : Fin g → Prop) [DecidablePred c]
    (v : Fin (h + g)) (hv : ∀ t, c t → v ≠ Fin.natAdd h t) :
    (∑ t : Fin g, if c t ∧ v = Fin.natAdd h t then 1 else 0) = 0 :=
  Finset.sum_eq_zero fun t _ => if_neg fun hc => hv t hc.1 hc.2

end

theorem ld_pack_deg (E : Type) [Field E] : Spec.ld_pack_deg E := by
  intro h g m c
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have h1 := (deg_pow (E := E) (Fin.castAdd g i) (q.val + 1)).mul
      (deg_late (E := E) (h := h) (g := g) fun _ => True)
    simp only [if_true] at h1
    refine h1.mono fun v => ?_
    by_cases hv : v.val < h
    · rw [if_pos hv, late_eq_zero _ v fun t _ hc => by
        have := congrArg Fin.val hc
        simp only [Fin.val_natAdd] at this
        omega]
      have := q.2
      split_ifs <;> omega
    · rw [if_neg hv, if_neg fun hc => hv (by rw [hc]; exact i.2)]
      have := late_le_one (h := h) (fun _ : Fin g => True) v
      omega
  · have h1 := (deg_pow (E := E) (Fin.natAdd h t) (p.val + 1)).mul
      (deg_late (E := E) (h := h) (g := g) fun t' => t < t')
    refine h1.mono fun v => ?_
    by_cases hv : v.val < h
    · rw [if_pos hv, late_eq_zero _ v fun t' _ hc => by
        have := congrArg Fin.val hc
        simp only [Fin.val_natAdd] at this
        omega, if_neg fun hc => by
        have := congrArg Fin.val hc
        simp only [Fin.val_natAdd] at this
        omega]
      omega
    · rw [if_neg hv]
      by_cases hvt : v = Fin.natAdd h t
      · rw [if_pos hvt, late_eq_zero _ v fun t' ht' hc => by
          have := congrArg Fin.val (hvt.symm.trans hc)
          simp only [Fin.val_natAdd] at this
          exact absurd (Fin.ext (by omega) : t = t') ht'.ne]
        have := p.2
        omega
      · rw [if_neg hvt]
        have := late_le_one (h := h) (fun t' : Fin g => t < t') v
        omega
  · exact Alg.DegLE.const _ 1

theorem ld_pack_deg_place (E : Type) [Field E] : Spec.ld_pack_deg_place E := by
  intro ι Cl J _ _ _ plc Qw d hq j
  unfold QwAt placeV
  refine Alg.DegLE.sum Finset.univ fun c _ => ?_
  by_cases hc : plc c = j
  · simp only [hc, if_true]
    exact hq c
  · simp only [hc, if_false]
    exact Alg.DegLE.const d 0

end Cb
