-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ProgramBridge.lean.
WHAT IT DOES NOT SHOW. Nothing on a proof file or a verifier: it begins at the two relations on
cells. THE REQUEST's FORM HAS A CLAUSE THAT NEITHER LEMMA GIVES: "y = 0 where e < T": that is asked
where y is heard (the next token's block): here it is a premise. The library's cost has 2^8: the
premise sh = 8 (the tests on the plan allow 7 too). The sizes, the request and the policy of the
kind's classes are tied to the library's records by a premise each (SameRequest).
WHAT IT IS. FROM THE HEAD's TWO LEMMAS' CONCLUSIONS (HeadLaw.lean: Says; HeadNormLaw.lean: SaysN) TO
THE WORDS OF THE LIBRARY's INTEGER PROGRAM (Inst/Model/ProgramR.lean): the final normalization goes
on at every position (NORM.OK), the request has its form (Head3), and the policy's three clauses
hold (PolOK) of the logits dot (NORM.out (stream)) (the output matrix).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormProof
import Inst.Model.ProgramR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open Inst.Model (NormPar Params Instance AcceptancePolicy PolOK Head3 gapOf costOf maxTo dot)

variable [Sizes] [Policy] [Request] [Token]

/-- The kind's public letters are the library's records'. -/
structure SameRequest (P : Params) (x : Instance P) : Prop where
  hT : T = P.T
  hV : V = P.V
  hd : d = P.d
  hsh : sh = 8
  htok : ∀ i (h : i < P.T), tok i = (x.prompt ⟨i, h⟩).val
  hr : r = x.r
  he : e = x.e
  hy : y = x.y.val

variable {P : Params} {x : Instance P}

theorem win_eq (R : SameRequest P x) (t : Nat) : win t = x.w t := by
  unfold win Instance.w Instance.tok
  rw [R.hT]
  by_cases h : t + 1 < P.T
  · rw [if_pos h, dif_pos h, R.htok _ h]
  · rw [if_neg h, dif_neg h, R.hy]

theorem foldlMax_eq (g : Nat → Int) (n : Nat) :
    (List.range (n + 1)).foldl (fun m v => max m (g v)) 0 = max 0 (maxTo g n) := by
  induction n with
  | zero => simp [maxTo]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, maxTo]
    rw [max_assoc]

/-- The kind's gap is the library's. -/
theorem gap_eq (R : SameRequest P x) (c : Cells) (t : Nat) (l : Nat → Int)
    (hl : ∀ v, logit c t v = l v) : gap c t = gapOf P.V l (x.w t) := by
  have hw : x.w t < P.V := x.w_lt t
  obtain ⟨n, hn⟩ : ∃ n, P.V = n + 1 := ⟨P.V - 1, by omega⟩
  unfold gap
  rw [R.hV, hn, foldlMax_eq, win_eq R]
  have h0 := Inst.Model.gapOf_nonneg P.V l hw
  unfold gapOf at h0 ⊢
  rw [hn] at h0
  simp only [Nat.add_sub_cancel] at h0 ⊢
  simp only [hl]
  exact max_eq_right h0

theorem costed_iff (R : SameRequest P x) (t : Nat) : costed t = true ↔ t ∈ x.cnt := by
  unfold costed checked Instance.cnt
  rw [R.hr, R.he, R.hT, Finset.mem_Ico]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem cnt_subset (R : SameRequest P x) : x.cnt ⊆ Finset.range T := by
  intro t ht
  have h := (Finset.mem_Ico.mp ht).2
  rw [Finset.mem_range, R.hT]
  omega

theorem sum_costed (R : SameRequest P x) (f : Nat → Int) :
    ((Finset.range T).sum fun t => if costed t = true then f t else 0) = x.cnt.sum f := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  rw [Finset.mem_filter, costed_iff R]
  exact ⟨fun h => h.2, fun h => ⟨cnt_subset R h, h⟩⟩

/-- **The policy's three clauses, in the library's words.** lg: any logits that are the cells' at
the positions below T. -/
theorem polOK_of_says (R : SameRequest P x) {c : Cells} (S : Says c) (lg : Nat → Nat → Int)
    (hlg : ∀ t, t < T → ∀ v, logit c t v = lg t v) : PolOK lg ⟨C, theta, cap⟩ x := by
  have hcost : ∀ t, t ∈ x.cnt → cost c t = costOf lg x t := fun t ht => by
    unfold cost costOf
    rw [gap_eq R c t (lg t) (hlg t (Finset.mem_range.mp (cnt_subset R ht))), R.hsh]
  have hRC : RC = x.NB := by
    unfold RC Instance.NB
    rw [R.he, R.hT, R.hr]
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩
  · have h := S.a
    rw [sumZ_eq, sum_costed R, hRC] at h
    have e : x.cnt.sum (fun t => min (cost c t) (C : Int)) =
        x.cnt.sum fun t => min (costOf lg x t) (C : Int) :=
      Finset.sum_congr rfl fun t ht => by rw [hcost t ht]
    rw [e] at h
    exact h
  · have h := S.b
    have e1 := filter_length_eq T fun t => costed t && decide ((C : Int) < cost c t)
    have e2 : ((Finset.range T).sum fun t =>
        if (costed t && decide ((C : Int) < cost c t)) = true then (1 : Int) else 0) =
        ((x.cnt.filter fun t => ((C : Nat) : Int) < costOf lg x t).card : Int) := by
      rw [Finset.card_filter]
      push_cast
      rw [← sum_costed R]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases hc : costed t = true
      · rw [if_pos hc, ← hcost t ((costed_iff R t).mp hc)]
        simp [hc]
      · rw [if_neg hc]
        simp [hc]
    have : ((x.cnt.filter fun t => ((C : Nat) : Int) < costOf lg x t).card : Int) ≤
        (cap : Int) := by
      rw [← e2, ← e1]
      exact_mod_cast h
    exact_mod_cast this
  · have hT0 : 0 < P.T := by
      have := x.e_le
      omega
    have h := S.c (by rw [R.he, R.hT]; exact h2)
    rw [gap_eq R c (T - 1) (lg (T - 1)) (hlg _ (by rw [R.hT]; omega))] at h
    have hw : x.w (T - 1) = x.y.val := by
      unfold Instance.w Instance.tok
      rw [R.hT, dif_neg (by omega)]
    rw [hw, R.hT] at h
    exact h

/-- **All that the library's relation asks of a head, from the two relations on cells.** -/
theorem program_of_cells (R : SameRequest P x) (sT : Nat) (tab : Nat → Nat) (c : NCells)
    (hplan : planOk sT = true) (hreq : Request.ok = true) (htab : TableOk tab)
    (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) (hy0 : e < T → y = 0)
    (h : CellRelH c.toCells tab) (hN : CellRelN c) :
    (∀ pos, pos < P.T → Inst.Model.NORM.OK npOf P.d (str c pos)) ∧ Head3 x ∧
      PolOK (fun pos v => dot P.d (Inst.Model.NORM.out npOf P.d (str c pos)) fun j => c.Wh j v)
        ⟨C, theta, cap⟩ x := by
  have hy : y < V := by
    rw [R.hy, R.hV]
    exact x.y.isLt
  obtain ⟨S, _⟩ := lemma1_whole sT tab c hplan hreq hy htab hW h hN
  refine ⟨fun pos hp => ?_, ?_, polOK_of_says R S _ fun t ht v => ?_⟩
  · rw [← R.hd]
    exact (lemma1N_program sT c hplan hN (by rw [R.hT]; exact hp)).1
  · unfold Request.ok at hreq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hreq
    refine ⟨by rw [← R.hr, ← R.he]; exact hreq.1.1, x.e_le, fun h1 => ?_⟩
    rw [← R.hy]
    exact hy0 (by rw [R.he, R.hT]; exact h1)
  · unfold logit dot
    rw [sumZ_eq, ← R.hd]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(lemma1N_program sT c hplan hN ht).2 k (Finset.mem_range.mp hk)]

end VerifiableInference.Desc.Kinds.Head.Law
