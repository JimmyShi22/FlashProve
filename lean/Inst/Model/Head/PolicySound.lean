-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicySound.lean: the head's integer relations (`HRel`,
Inst/Model/Head/PolicyDefs.lean) imply the acceptance policy, if V ≥ 2.

Integers only: no field, no cell (a cell is one committed integer of a proof), no protocol. (The
relation on a request under a policy is in Inst/Model/ProgramR.lean.)
The argument, at the step table (sh = 8, F = 24, BIG = 2^37, Pub = 0:
Inst/Model/Head/PolicyDefs.lean): the middle digit (Lemma (L)), the cost, the bounds, the last
position.
  `cost_le_hidden`           the key lemma: under `HRel`, 2 ≤ V, at a counted position cost = gap +
                             2^8 ≤ c + 2^37 b
  `polOK_of_HRel`            `HRel` → 2 ≤ V → `PolOK`: (a), (b), (c) ((c) has the premise r < e in
                             its own definition: Inst/Model/ProgramR.lean)
What is used of `HRel`:
  (Z), (B2), (B4) as they are;
  of (B3) only that its right side is at most cap (the factor [NB > 0] is not used);
  of the six hidden numbers only that they are not negative at counted positions (nothing is asked
    of them elsewhere; no upper range: `Hid.Bytes` is not used);
  of the digits K0 ≥ 0, K1 ≥ 0, K2 ≥ 0 (no upper range; the weight 2^23 of K0 could be any number
    that is not negative);
  of the table EX[0] = 2^24 and EX ≥ 1;
  (HE) at counted positions only;
  (B1) at counted positions and, if e = T, at T − 1.
That b is a bit is neither asked nor used. So the upper ranges, 2^23 and `Hid.Bytes` matter in other
files, not in this one:
  Policy/Rel/LedgerHeadNoWrap.lean proves the top digit's upper range and 2^23 from a congruence:
    `top_digit`, under `HCong`, `Fit`;
  the ranges of the middle and the low digit and `Hid.Bytes` are hypotheses there (`HCong`);
  `Hid.Bytes` is proved from the lookup of single bytes in the same file: `hid_full`, under `RFz p`.

Notation:
  margin: `marg` (Inst/Model/Head/PolicyDefs.lean): the margin at position t and token v.
  gap: `gapOf` (Inst/Model/ProgramR.lean): the logit gap of the token w: max_(v < V) (l[v] − l[w] +
    [v < w]); cost: `costOf`: the cost of a counted position, at the step table.
  covered: r ≤ t < e (`rhoR`, Inst/Model/Head/PolicyDefs.lean); counted: `Instance.cnt`
    (Inst/Model/ProgramR.lean): covered, and below T − 1: their checked token is a token of the
    request; checked token: `Instance.w`.
Limits. This file does not say ("the programs" are the implementation, outside lean/):
  (1) That integers with `HRel` exist for every request within the policy: that is the honest rule's
  part (Inst/Model/Head/PolicyHonest.lean).
  (2) That anything which a verifier tests gives `HRel`. Policy/Rel/LedgerHeadNoWrap.lean goes from
      congruences modulo p to `HRel`, and from the field relation of the head, in its integer form,
      to those congruences; that a protocol gives the field relation is not said in that file or in
      this one. For the programs, the step from their claims
      to the relations over the integers has only a written proof, which is
      not machine-checked and has not been independently reviewed.
  (3) Anything on probabilities or on an exponential table. A protocol text of the implementation
      (not in this repository) defines the cost as the greater of gap + 2^sh and nll (minus the
      scaled logarithm of the softmax probability); `costOf` is gap + 2^8. That the two agree at the
      step table is argued there over the real numbers (it needs sT = sh − 4 and ln V < 16): no Lean
      file has it. So (a), (b) for that cost follow from this file only together with that argument.
  (4) That the public parameters have sh = 8 and the step table: they are constants here, while the
      implementation's verifier also admits sh = 7 and exponential tables.
2 ≤ V is needed (the following example is not proved in this library): at V = 1 the one token may
have middle digit 0 (the sum is then exactly 2^24), so c = b = 0 is admitted where the cost is 2^8:
with C = 1, θ = 0, cap = 0, one counted position, u = z = zs = 0, k = 1, all digits 0 and ex = 2^24,
`HRel` holds and (a) fails. (docs/format/FORMAT.md, section 13.8, has 2 ≤ V among the verifier's
tests, under the name shape-V; this is said from that page alone, not from the verifier's source.)
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicyDefs
import Inst.Model.TablesSanity

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model

/-- How (HE) is obtained from a lookup: the looked-up value K1 + 2^16 ex is a row of FE, and K1 is a
16-bit digit. -/
theorem key_split {K1 ex : ℤ} {u : ℕ} (h0 : 0 ≤ K1) (h1 : K1 < 2 ^ 16)
    (hu : u < 2 ^ 16) (e : K1 + 2 ^ 16 * ex = FE.row u) : K1 = u ∧ ex = EX K1.toNat := by
  have e' : K1 + 2 ^ 16 * ex = (u : ℤ) + 2 ^ 16 * EX u := e
  have hu' : (u : ℤ) < 2 ^ 16 := by exact_mod_cast hu
  have hK : K1 = u := by omega
  refine ⟨hK, ?_⟩
  rw [hK, Int.toNat_natCast]
  omega

/-- one term 2^24 among V ≥ 2 terms that are all at least 1 -/
theorem sum_ex_gt {V : ℕ} (hV : 2 ≤ V) (f : ℕ → ℤ) (h1 : ∀ v < V, 1 ≤ f v) {v0 : ℕ}
    (hv0 : v0 < V) (e : f v0 = 2 ^ 24) :
    2 ^ 24 < ∑ v ∈ Finset.range V, f v := by
  have hm : v0 ∈ Finset.range V := Finset.mem_range.2 hv0
  rw [← Finset.add_sum_erase _ f hm, e]
  have hc : ((Finset.range V).erase v0).card = V - 1 := by
    rw [Finset.card_erase_of_mem hm, Finset.card_range]
  have hs : (((Finset.range V).erase v0).card : ℤ) ≤ ∑ v ∈ (Finset.range V).erase v0, f v := by
    have := Finset.card_nsmul_le_sum ((Finset.range V).erase v0) f 1
      (fun v hv => h1 v (Finset.mem_range.1 (Finset.mem_of_mem_erase hv)))
    simpa using this
  rw [hc] at hs
  have : (1 : ℤ) ≤ ((V - 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 1 ≤ V - 1)
  omega

section
variable {P : Params} {lg : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x : Instance P} {h : Hid} {d : Dig}

theorem cnt_covered {t : ℕ} (ht : t ∈ x.cnt) : x.r ≤ t ∧ t < x.e := by
  have := Finset.mem_Ico.1 ht
  omega

/-- Lemma (L), under `HRel`, 2 ≤ V: at a counted position the middle digit of every margin with
v < V is at least 1. -/
theorem K1_pos (H : HRel lg pol x h d) (hV : 2 ≤ P.V) {t : ℕ} (ht : t ∈ x.cnt)
    {v : ℕ} (hv : v < P.V) : 1 ≤ d.K1 v t := by
  obtain ⟨hr, he⟩ := cnt_covered ht
  by_contra hlt
  have h0 : d.K1 v t = 0 := by have := (H.B1 t hr he v hv).2.2.1.1; omega
  have hex : d.ex v t = 2 ^ 24 := by rw [H.HE t hr he v hv, h0]; exact TablesSanity.tab9.1
  have hs : 2 ^ 24 < ∑ v ∈ Finset.range P.V, d.ex v t := sum_ex_gt hV (fun v => d.ex v t) (fun v' hv' => by
    show 1 ≤ d.ex v' t
    rw [H.HE t hr he v' hv']; exact (TablesSanity.tab9.2 _).1) hv hex
  have hz := H.Z t ht
  have hzs := (H.nonneg t ht).2.2.2.2.2
  omega

/-- The key lemma, under `HRel`, 2 ≤ V: at a counted position the hidden number c + 2^37 b is at
least the cost. -/
theorem cost_le_hidden (H : HRel lg pol x h d) (hV : 2 ≤ P.V) {t : ℕ} (ht : t ∈ x.cnt) :
    costOf lg x t ≤ h.c t + 2 ^ 37 * h.b t := by
  obtain ⟨hr, he⟩ := cnt_covered ht
  obtain ⟨j, hj, e⟩ :=
    (maxTo_spec (fun v => lg t v - lg t (x.w t) + if v < x.w t then 1 else 0) (P.V - 1)).2
  have hjV : j < P.V := by omega
  obtain ⟨hB, ⟨hK0, _⟩, _, ⟨hK2, _⟩⟩ := H.B1 t hr he j hjV
  have hK1 := K1_pos H hV ht hjV
  have hg : gapOf P.V (lg t) (x.w t) = lg t j - lg t (x.w t) + if j < x.w t then 1 else 0 := e.symm
  unfold costOf
  rw [hg]
  unfold marg rhoC at hB
  rw [if_pos ht] at hB
  split at hB <;> omega

theorem c_le_C (H : HRel lg pol x h d) {t : ℕ} (ht : t ∈ x.cnt) : h.c t ≤ pol.C := by
  have := H.B4 t ht
  have := (H.nonneg t ht).2.2.2.1
  omega

/-- under `HRel`, 2 ≤ V: a counted position above the clip has b ≥ 1 -/
theorem b_pos_of_above (H : HRel lg pol x h d) (hV : 2 ≤ P.V) {t : ℕ}
    (ht : t ∈ x.cnt) (ha : (pol.C : ℤ) < costOf lg x t) : 1 ≤ h.b t := by
  have h1 := cost_le_hidden H hV ht
  have h2 := c_le_C H ht
  omega

/-- under `HRel`, 2 ≤ V: at a counted position the clipped cost is at most c + C b -/
theorem min_cost_le (H : HRel lg pol x h d) (hV : 2 ≤ P.V) {t : ℕ} (ht : t ∈ x.cnt) :
    min (costOf lg x t) pol.C ≤ h.c t + pol.C * h.b t := by
  have hc := (H.nonneg t ht).1
  have hb := (H.nonneg t ht).2.1
  rcases eq_or_lt_of_le hb with h0 | h1
  · have h1 := cost_le_hidden H hV ht
    rw [← h0] at h1 ⊢
    exact le_trans (min_le_left _ _) (by omega)
  · have hC : (pol.C : ℤ) ≤ pol.C * h.b t :=
      le_mul_of_one_le_right (Int.natCast_nonneg _) (by omega)
    exact le_trans (min_le_right _ _) (by omega)

/-- If 2 ≤ V, the relations of the head imply the policy. -/
theorem polOK_of_HRel (H : HRel lg pol x h d) (hV : 2 ≤ P.V) : PolOK lg pol x where
  a := by
    rw [← H.B2]
    refine Finset.sum_le_sum fun t ht => ?_
    have := min_cost_le H hV ht
    have := (H.nonneg t ht).2.2.1
    omega
  b := by
    have h1 : ((x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t).card : ℤ) ≤
        ∑ t ∈ x.cnt, (h.b t + h.z t) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_le_sum fun t ht => ?_
      have hb := (H.nonneg t ht).2.1
      have hz := (H.nonneg t ht).2.2.2.2.1
      split
      · rename_i ha
        have := b_pos_of_above H hV ht ha
        omega
      · omega
    rw [H.B3] at h1
    have h2 : (if 0 < x.NB then (pol.cap : ℤ) else 0) ≤ pol.cap := by split <;> simp
    exact_mod_cast le_trans h1 h2
  c := by
    intro hre heT
    have hT : x.r ≤ P.T - 1 ∧ P.T - 1 < x.e := by omega
    have hn : P.T - 1 ∉ x.cnt := by
      intro hm
      have := Finset.mem_Ico.1 hm
      omega
    have hw : x.w (P.T - 1) = x.y.val := by
      unfold Instance.w Instance.tok
      rw [dif_neg (by omega)]
    refine le_antisymm ?_ (gapOf_nonneg _ _ x.y.isLt)
    obtain ⟨j, hj, e⟩ := (maxTo_spec
      (fun v => lg (P.T - 1) v - lg (P.T - 1) x.y.val + if v < x.y.val then 1 else 0) (P.V - 1)).2
    have hjV : j < P.V := by have := x.y.isLt; omega
    obtain ⟨hB, ⟨hK0, _⟩, ⟨hK1, _⟩, ⟨hK2, _⟩⟩ := H.B1 (P.T - 1) hT.1 hT.2 j hjV
    have hg : gapOf P.V (lg (P.T - 1)) x.y.val =
      lg (P.T - 1) j - lg (P.T - 1) x.y.val + if j < x.y.val then 1 else 0 := e.symm
    rw [hg]
    unfold marg rhoC at hB
    rw [if_neg hn, hw] at hB
    split at hB <;> omega

end

/-- with "the program runs", `Head3` and 2 ≤ V, `HRel` gives the relation `RinfR` -/
theorem RinfR_of_HRel {P : Params} {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    {pol : AcceptancePolicy} {i : Index P} {x : Instance P} {h : Hid} {d : Dig}
    (hrun : RunsK P κ nf tbs i.val x.prompt) (h3 : Head3 x) (hV : 2 ≤ P.V)
    (H : HRel (lgK P κ nf tbs i.val x.prompt) pol x h d) :
    RinfR P κ nf tbs pol i x := ⟨hrun, h3, polOK_of_HRel H hV⟩

end Inst.Model.Head.Policy
