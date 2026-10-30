-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Proof.lean: THE HEAD's TWO LAWS, for reads that are true at every index (`k06CoreAll`,
`k06OutAll`, `k06BackAll`; from them Clamp.lean has `K06OutStatement` and `K06BackStatement` of K06Statement.lean).
From the glue (K06Glue.lean), Lemma 2b's core in the world of the sent reads
(Lemma2b.lean: coreW) and Lemma 1 (Values.lean: lemma1_strong).
-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Glue
import Johnson.Desc.Kinds.Law.Filled6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE okE addE mulE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- The value of logitForms' second form in a world in which the reads' entries are true. -/
theorem actForm_valueW [FinalNorm.In] [In] [Heard] [Reads] (c : Cells) (W : World K)
    (he : ∀ r i, vW W (entry r i) = rd (readAt c r.of i)) :
    vW W ((logits.end_ 0).var - sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k)
      = vW W (logits.end_ 0).var - (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
          rd (eq rH t) * rd (eq rs k) * fA c t k := by
  have hs : ((Finset.range d).sum fun k =>
      vW W (eq rs k • FinalNorm.actAt (entry .actAtLogits) k))
      = (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
          rd (eq rH t) * rd (eq rs k) * fA c t k := ?_
  · rw [vW_sub, vW_sumTo, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vW_smulE]
  unfold FinalNorm.actAt
  rw [vW_add, vW_smulN, he, he]
  show rd (eq rs k) * (rd (readAt c (.act, .short (eq rH)) k)
    + _ * rd (readAt c (.act, .short (eq rH)) (d + k))) = _
  rw [rd_readAt_short, rd_readAt_short, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold fA act
  push_cast
  ring

/-! ## mean and count from the true reads alone (Closed.lean's proofs, re-typed by a program) -/

section Reads
variable [FinalNorm.In] [In] [Heard] [Reads] {W : World K} {c : Cells}

/-- A number, summed plainly over the positions with a cost. -/
theorem vW_summedE (he : ∀ r i, vW W (entry r i) = rd (readAt c r.of i)) (n : Number) :
    vW W (summed n) = (Finset.range T).sum fun t =>
      if costed t = true then ((numZ c n t : Int) : K) else 0 := by
  unfold summed
  rw [vW_sumTo]
  have h1 : ∀ l, vW W ((256 : Nat) ^ l • (entry Read.rowCount (NR + n.digits.1 + l) + off1 * RC))
      = (Finset.range T).sum fun t => if costed t = true then
          ((256 : K) ^ l * (((c.cell .row (NR + n.digits.1 + l) t : Int) : K) + 128)) else 0 := by
    intro l
    rw [vW_smulN, vW_addN, he]
    show _ * (rd (readAt c (.row, .short fun t => if costed t then 1 else 0) _) + _) = _
    rw [rd_readAt_short]
    push_cast
    rw [RC_eq, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold off1
    by_cases hc : costed t = true
    · simp only [hc, if_true, rd_one]; push_cast; ring
    · simp only [hc, if_false, rd_zero, Bool.false_eq_true]; ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : costed t = true
  · simp only [hc, if_true]
    unfold numZ
    push_cast
    rfl
  · simp [hc]

theorem vW_meanE (he : ∀ r i, vW W (entry r i) = rd (readAt c r.of i)) : vW W mean = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t
    else 0) - (theta : Int) * (RC : Int) : Int) : K) := by
  unfold mean
  rw [vW_subN, vW_add, vW_add, vW_smulN, vW_summedE he, vW_summedE he, vW_summedE he, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem vW_countE (he : ∀ r i, vW W (entry r i) = rd (readAt c r.of i)) : vW W count = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .over t + numZ c .slackCap t else 0)
      - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) := by
  unfold count
  rw [vW_sub, vW_add, vW_natCast, vW_summedE he, vW_summedE he, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

end Reads

/-- Lemma 2a's three equations, without its premise on zl's length (which its proof does not spend).
-/
theorem corners (c : Cells) (p : Pt) (hreq : Request.ok = true) (hy : y < V)
    (hzt : p.zt.size = lt) :
    rd (clipAt c p) = (Finset.range T).sum (fun t => rd (eq p.zt t) * rd (clipAt c (corner 0 t))) ∧
    rd (tableAt c p) = (Finset.range T).sum (fun t => rd (eq p.zt t) * rd (tableAt c (corner 0 t))) ∧
    ∀ k, rd (keyAt c p k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      rd (p.ew k x) * rd (eq p.zt t) * rd (keyAt c (corner x t) k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rd_clipAt]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_clipAt, sum_costed_delta (Finset.mem_range.mp ht)]
    split <;> simp
  · rw [rd_tableAt]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_tableAt, sum_costed_delta (Finset.mem_range.mp ht)]
    split <;> simp
  · intro k
    rw [rd_keyAt c p hzt hreq hy k]
    refine Finset.sum_congr rfl fun x hx => ?_
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [rd_keyAt_corner c hreq hy k (Finset.mem_range.mp hx) (Finset.mem_range.mp ht)]

/-- Lemma 2b at the letters that came in and at the sent reads, judged at any ledger later than the
one behind the sumcheck; for reads that are true at every index; the rule is Lemma 2b's. -/
theorem k06CoreAll [FinalNorm.In] [In] (c : Cells) (mask : Nat → E) (F0 : Fork)
    (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0)
    (hzt : (FinalNorm.zt).size = lt) (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork)
    (ent : Nat → Nat → Nat → E) [Reads] (hcan : Canonical t)
    (hsum : sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []))
    (hL : OnBytes.PscRun.Later F1 G) :
    letI : Heard := { logits := S }
    TrueReadsAll c G mask ent → WeightTrue c G mask ent →
    (∀ f, f ∈ logitForms → atWorld G mask ent f = 0) → NoBad (badP c mask F0) t →
    (2 ^ lPd : E) * atWorld G mask ent logits.claimed.var = trueSum c := by
  letI : Heard := { logits := S }
  intro hreads hwt hlog hnb
  have he : ∀ r i, vW (worldE G mask ent) (entry r i) = rd (readAt c r.of i) :=
    fun r i => by rw [← rd_atWorld, hreads r i]
  have g1 : vW (worldE G mask ent) (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0 := by
    have h1 := congrArg rd (hlog (logits.left ((logits.end_ 0).shown * (logits.end_ 1).shown))
      (List.Mem.head _))
    rw [rd_atWorld, rd_zero] at h1
    exact h1
  have g2 : vW (worldE G mask ent) (S.end_ 0).var = (Finset.range T).sum fun t =>
      (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fA c t k := by
    have h1 := congrArg rd (hlog ((logits.end_ 0).var
      - sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k)
      (List.Mem.tail _ (List.Mem.head _)))
    rw [rd_atWorld, rd_zero, actForm_valueW c _ he] at h1
    exact sub_eq_zero.mp h1
  have g3 : vW (worldE G mask ent) (S.end_ 1).var = (Finset.range T).sum fun t =>
      (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fU c t k := by
    have h1 := congrArg rd hwt
    rw [rd_atWorld, weights_eq c hreq hy] at h1
    exact h1
  have h2b := coreW c mask F0 hWL hzt (worldE G mask ent)
    (fun j h1 h2 => hidden_later mask hL (filled_range hWL hsum j h1 h2)) hcan hsum g1 g2 g3 hnb
  apply eq_of_rd (okE_mulE _ _) (by unfold trueSum; exact okE_sumTo _ _)
  have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
  have hm : rd (mulE (2 ^ lPd) (atWorld G mask ent logits.claimed.var))
      = rd ((2 : E) ^ lPd) * rd (atWorld G mask ent logits.claimed.var) := Reading.gl.mul _ _
  rw [hm, rd_pow, hr2, rd_atWorld]
  exact h2b

/-- Out, to the lookup, likewise. -/
theorem k06OutAll [FinalNorm.In] [In] (c : Cells) (mask : Nat → E) (F0 : Fork)
    (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0) (hw : WeightsOk)
    (hzt : (FinalNorm.zt).size = lt) (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork)
    (ent : Nat → Nat → Nat → E) [Reads] (hcan : Canonical t)
    (hsum : sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []))
    (hL : OnBytes.PscRun.Later F1 G) :
    letI : Heard := { logits := S }
    TrueReadsAll c G mask ent → WeightTrue c G mask ent →
    (∀ f, f ∈ logitForms → atWorld G mask ent f = 0) → NoBad (badP c mask F0) t →
    (∀ k, atWorld G mask ent (key k) =
      sumTo (len k) fun x => sumTo T fun t => In.ew k x * eq FinalNorm.zt t * keyAt c (corner x t) k) ∧
    atWorld G mask ent clip = (sumTo T fun t => eq FinalNorm.zt t * clipAt c (corner 0 t)) ∧
    atWorld G mask ent table = (sumTo T fun t => eq FinalNorm.zt t * tableAt c (corner 0 t)) := by
  letI : Heard := { logits := S }
  intro hreads hwt hlog hnb
  have hcl := k06CoreAll c mask F0 hreq hy hWL hzt F1 t S G ent hcan hsum hL hreads hwt hlog hnb
  obtain ⟨hkey, hclip, htable, _, _⟩ := k06GlueAll c G mask ent hreq hy hw hzt hreads hcl
  obtain ⟨c1, c2, c3⟩ := corners c ptOf hreq hy hzt
  refine ⟨fun k => ?_, ?_, ?_⟩
  · rw [hkey k]
    apply eq_of_rd (okE_keyAt c ptOf k) (okE_sumTo _ _)
    rw [c3 k, rd_sumTo]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_mul, rd_mul, hw.ew k x (Finset.mem_range.mp hx)]
    rfl
  · rw [hclip]
    apply eq_of_rd (okE_clipAt c ptOf) (okE_sumTo _ _)
    rw [c1, rd_sumTo]
    exact Finset.sum_congr rfl fun t _ => by rw [rd_mul]; rfl
  · rw [htable]
    apply eq_of_rd (okE_tableAt c ptOf) (okE_sumTo _ _)
    rw [c2, rd_sumTo]
    exact Finset.sum_congr rfl fun t _ => by rw [rd_mul]; rfl

/-- Back, from the lookup, for reads that are true at every index. -/
theorem k06BackAll (sT : Nat) (tab : Nat → Nat) (c : Cells) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : y < V) (htab : TableOk tab)
    (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hA : ∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047)
    (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) [FinalNorm.In] [In] [Heard] [Reads]
    (hsmall : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) (hreads : TrueReadsAll c F mask ent)
    (hmean : atWorld F mask ent mean = 0) (hcount : atWorld F mask ent count = 0)
    (hkeys : CornerKeys c tab) (hguests : CornerGuests c) : CellRel c tab ∧ Says c := by
  have he : ∀ r i, vW (worldE F mask ent) (entry r i) = rd (readAt c r.of i) :=
    fun r i => by rw [← rd_atWorld, hreads r i]
  have hm : okE (meanAt c) = true := okE_addMul _ _ _
  have hc : okE (countAt c) = true := okE_addMul _ _ _
  have s1 : meanAt c = 0 := by
    apply zero_of_rd hm
    have h1 := congrArg rd hmean
    rw [rd_atWorld, rd_zero, vW_meanE he] at h1
    rw [rd_mean]; exact h1
  have s2 : countAt c = 0 := by
    apply zero_of_rd hc
    have h1 := congrArg rd hcount
    rw [rd_atWorld, rd_zero, vW_countE he] at h1
    rw [rd_count]; exact h1
  have hrel : CellRel c tab :=
    { small := hsmall, bytes := hkeys.bytes, top := hkeys.top, mid := hkeys.mid, low := hkeys.low
      rowA := hkeys.rowA, rowB := hkeys.rowB, lines := hguests, sums := ⟨s1, s2⟩ }
  exact ⟨hrel, lemma1_strong hplan hreq hy htab hW hA hrel⟩

end VerifiableInference.Desc.Kinds.Head.Law

