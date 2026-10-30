-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Place.lean: the two placements. Lists, numbers and permutations only; no protocol and
no hashing.

The prover of Compile/Batch/Star.lean puts request number a of the whole batch into slot σ a, for a
sampled permutation σ of the slots (uniform if `WP.perm` has `Enum.OK`, Iop/Wire.lean). The lifetime
experiment of Compile/Batch/SpecLifeStar.lean is told the adversary's own instances only
(`LifeOutB`: a batch on copy j with the adversary's own requests xs) and puts own instance number a'
into slot σ' a'. With τ a fixed permutation that carries a' to the number, in the whole batch, of
the a'-th own request, σ' = σ τ is uniform if σ is, and the two placements put the own instances
into the same slots.
  `ownIdx b`           the numbers of the own requests of a batch, in their order
  `getElem?_slotList`, `idxOf_slotList`     the list of the slots of the first k places
  `IsTau`, `exists_tau`   the permutation τ
-/
import Compile.Batch.RealB
import Compile.Batch.Life

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (ownPf)
open Compile.BatchLife (slotList slotsOf ownAt)

namespace Place

/-! ## The slots of the first k places -/

section SlotList

variable {N : ℕ}

theorem filter_lt_range (k : ℕ) :
    ∀ N : ℕ, (List.range N).filter (fun a => decide (a < k)) = List.range (min k N)
  | 0 => by simp
  | N + 1 => by
      rw [List.range_succ, List.filter_append, filter_lt_range k N]
      by_cases h : N < k
      · have e : min k (N + 1) = min k N + 1 := by omega
        have e' : min k N = N := by omega
        rw [e, List.range_succ, e']
        simp [h]
      · have e : min k (N + 1) = min k N := by omega
        rw [e]
        simp [h]

theorem slotList_eq (σ : Equiv.Perm (Fin N)) (k : ℕ) :
    slotList σ k = ((List.finRange N).filter fun a => decide (a.val < k)).map σ := by
  unfold slotList
  induction List.finRange N with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a.val < k
    · simp [h, ih]
    · simp [h, ih]

theorem map_val_filter (k : ℕ) :
    (((List.finRange N).filter fun a => decide (a.val < k)).map Fin.val) =
      List.range (min k N) := by
  have h : ((List.finRange N).filter fun a => decide (a.val < k)) =
      (List.finRange N).filter ((fun a : ℕ => decide (a < k)) ∘ Fin.val) := rfl
  rw [h, ← List.filter_map, List.map_coe_finRange_eq_range, filter_lt_range]

theorem getElem?_slotList (σ : Equiv.Perm (Fin N)) {k a : ℕ} (hk : a < k) (hN : a < N) :
    (slotList σ k)[a]? = some (σ ⟨a, hN⟩) := by
  rw [slotList_eq, List.getElem?_map]
  have h1 : ((((List.finRange N).filter fun a => decide (a.val < k)).map Fin.val))[a]? =
      some a := by
    rw [map_val_filter, List.getElem?_range (by omega)]
  rw [List.getElem?_map] at h1
  cases hx : ((List.finRange N).filter fun a => decide (a.val < k))[a]? with
  | none => rw [hx] at h1; cases h1
  | some x =>
    rw [hx] at h1
    have hv : x.val = a := Option.some.inj h1
    have : x = ⟨a, hN⟩ := Fin.ext hv
    rw [this]
    rfl

theorem length_slotList (σ : Equiv.Perm (Fin N)) (k : ℕ) : (slotList σ k).length = min k N := by
  rw [slotList_eq, List.length_map, ← List.length_map (f := Fin.val),
    map_val_filter, List.length_range]

theorem nodup_slotList (σ : Equiv.Perm (Fin N)) (k : ℕ) : (slotList σ k).Nodup := by
  rw [slotList_eq]
  exact ((List.nodup_finRange N).filter _).map σ.injective

theorem idxOf_slotList (σ : Equiv.Perm (Fin N)) {k a : ℕ} (hk : a < k) (hN : a < N) :
    (slotList σ k).idxOf (σ ⟨a, hN⟩) = a := by
  have hl : a < (slotList σ k).length := by rw [length_slotList]; omega
  have hg : (slotList σ k)[a] = σ ⟨a, hN⟩ := by
    have := getElem?_slotList σ hk hN
    rw [List.getElem?_eq_getElem hl] at this
    exact Option.some.inj this
  rw [← hg]
  exact (nodup_slotList σ k).idxOf_getElem a hl

end SlotList

/-! ## The numbers of the own requests -/

section OwnIdx

variable {X : Type}

/-- the numbers of the own requests of a batch, in their order -/
def ownIdx : ZKCP.Gen.Batch X Unit → List ℕ
  | [] => []
  | s :: b => (if s.2.2 then [0] else []) ++ (ownIdx b).map (· + 1)

theorem ownX_cons (s : X × Unit × Bool) (b : ZKCP.Gen.Batch X Unit) :
    ZKCP.Gen.Batch.ownX (s :: b) = (if s.2.2 then [s.1] else []) ++ ZKCP.Gen.Batch.ownX b := by
  cases h : s.2.2 <;> simp [ZKCP.Gen.Batch.ownX, h]

theorem reqs_cons (s : X × Unit × Bool) (b : ZKCP.Gen.Batch X Unit) :
    reqs (s :: b) = s.1 :: reqs b := by
  simp [reqs, ZKCP.Gen.Batch.pairs]

theorem length_reqs' (b : ZKCP.Gen.Batch X Unit) : (reqs b).length = b.length := by
  simp [reqs, ZKCP.Gen.Batch.pairs]

theorem length_ownIdx : ∀ b : ZKCP.Gen.Batch X Unit, (ownIdx b).length = b.ownX.length
  | [] => rfl
  | s :: b => by
      rw [ownIdx, ownX_cons, List.length_append, List.length_append,
        List.length_map, length_ownIdx b]
      cases s.2.2 <;> rfl

theorem mem_ownIdx : ∀ (b : ZKCP.Gen.Batch X Unit) (a : ℕ), a ∈ ownIdx b ↔ ownFlag b a = true
  | [], a => by simp [ownIdx, ownFlag]
  | s :: b, 0 => by
      rw [ownIdx, RealB.ownFlag_zero]
      cases s.2.2 <;> simp
  | s :: b, a + 1 => by
      rw [ownIdx, RealB.ownFlag_succ, ← mem_ownIdx b a]
      cases s.2.2 <;> simp

theorem lt_of_ownFlag {b : ZKCP.Gen.Batch X Unit} {a : ℕ} (h : ownFlag b a = true) :
    a < b.length := by
  by_contra hn
  unfold ownFlag at h
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem nodup_ownIdx : ∀ b : ZKCP.Gen.Batch X Unit, (ownIdx b).Nodup
  | [] => List.nodup_nil
  | s :: b => by
      rw [ownIdx]
      have h1 : ((ownIdx b).map (· + 1)).Nodup := (nodup_ownIdx b).map fun _ _ h => Nat.succ.inj h
      cases s.2.2
      · simpa using h1
      · simp only [if_true, List.singleton_append, List.nodup_cons]
        exact ⟨by simp, h1⟩

/-- The own instances are the instances at these numbers. -/
theorem ownX_eq : ∀ b : ZKCP.Gen.Batch X Unit, b.ownX = (ownIdx b).filterMap fun a => (reqs b)[a]?
  | [] => rfl
  | s :: b => by
      rw [ownIdx, ownX_cons, List.filterMap_append, List.filterMap_map, ownX_eq b, reqs_cons]
      congr 1
      cases s.2.2 <;> simp

/-- The own proofs are the proofs at these numbers. -/
theorem ownPf_eq {Pf : Type} :
    ∀ (b : ZKCP.Gen.Batch X Unit) (l : List Pf), ownPf b l = (ownIdx b).filterMap fun a => l[a]?
  | [], _ => by simp [ownPf, ownIdx]
  | s :: b, [] => by simp [ownPf]
  | s :: b, π :: l => by
      rw [RealB.ownPf_cons, ownIdx, List.filterMap_append, List.filterMap_map, ownPf_eq b l]
      congr 1
      cases s.2.2 <;> simp

end OwnIdx

/-! ## The permutation τ -/

section Tau

variable {X : Type} {N : ℕ}

theorem getElem?_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome = true) → ∀ i : ℕ, (l.filterMap f)[i]? = (l[i]?).bind f
  | [], _, i => by simp
  | a :: l, h, i => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
      rw [List.filterMap_cons_some hy]
      cases i with
      | zero => simp [hy]
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact getElem?_filterMap_of_isSome f l (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

/-- own instance number a' is the instance of request number (ownIdx b)[a'] -/
theorem ownX_getElem? (b : ZKCP.Gen.Batch X Unit) (a' : ℕ) :
    b.ownX[a']? = ((ownIdx b)[a']?).bind fun a => (reqs b)[a]? := by
  conv_lhs => rw [ownX_eq b]
  refine getElem?_filterMap_of_isSome _ _ (fun a ha => ?_) a'
  have h1 := lt_of_ownFlag ((mem_ownIdx b a).1 ha)
  rw [List.getElem?_eq_getElem (by rw [length_reqs']; exact h1)]
  rfl

/-- τ carries the place a' to the number, in the whole batch, of the a'-th own request -/
def IsTau (b : ZKCP.Gen.Batch X Unit) (τ : Equiv.Perm (Fin N)) : Prop :=
  ∀ (a' : ℕ) (hN : a' < N), a' < b.ownX.length → (ownIdx b)[a']? = some (τ ⟨a', hN⟩).val

theorem length_ownX_le_length (b : ZKCP.Gen.Batch X Unit) : b.ownX.length ≤ b.length := by
  simp only [ZKCP.Gen.Batch.ownX, List.length_map]
  exact List.length_filter_le _ _

theorem exists_tau (b : ZKCP.Gen.Batch X Unit) (hb : b.length ≤ N) :
    ∃ τ : Equiv.Perm (Fin N), IsTau b τ := by
  have hm : b.ownX.length ≤ N := (length_ownX_le_length b).trans hb
  have hlt : ∀ a' : Fin b.ownX.length, a'.val < (ownIdx b).length :=
    fun a' => by rw [length_ownIdx]; exact a'.isLt
  let g : Fin b.ownX.length → Fin N := fun a' =>
    ⟨(ownIdx b)[a'.val]'(hlt a'),
      (lt_of_ownFlag ((mem_ownIdx b _).1 (List.getElem_mem (hlt a')))).trans_le hb⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : (ownIdx b)[x.val]'(hlt x) = (ownIdx b)[y.val]'(hlt y) := congrArg Fin.val hxy
    exact Fin.ext ((nodup_ownIdx b).getElem_inj_iff.1 h1)
  obtain ⟨τ, hτ⟩ := BatchLife.exists_perm_comp (Fin.castLE hm) g (Fin.castLE_injective hm) hg
  refine ⟨τ, fun a' hN ha => ?_⟩
  have h2 := hτ ⟨a', ha⟩
  have h3 : (Fin.castLE hm ⟨a', ha⟩ : Fin N) = ⟨a', hN⟩ := rfl
  rw [h3] at h2
  rw [h2, List.getElem?_eq_getElem (hlt ⟨a', ha⟩)]

variable {b : ZKCP.Gen.Batch X Unit} {τ : Equiv.Perm (Fin N)}

/-- For τ with `IsTau b τ`: the requests that τ reaches from the first places (those below the
number of own instances) are the own requests. -/
theorem IsTau.ownFlag_iff (h : IsTau b τ) (c : Fin N) :
    ownFlag b c.val = true ↔ (τ.symm c).val < b.ownX.length := by
  constructor
  · intro hc
    obtain ⟨a', ha', he⟩ := List.getElem_of_mem ((mem_ownIdx b c.val).2 hc)
    have hm : a' < b.ownX.length := by rw [← length_ownIdx]; exact ha'
    by_cases hN : a' < N
    · have h1 := h a' hN hm
      rw [List.getElem?_eq_getElem ha', he] at h1
      have h2 : τ ⟨a', hN⟩ = c := Fin.ext (Option.some.inj h1).symm
      rw [← h2, Equiv.symm_apply_apply]
      exact hm
    · -- more own requests than slots: every place is below the number of own requests
      exact (τ.symm c).isLt.trans_le (by omega)
  · intro hc
    have h1 := h (τ.symm c).val (τ.symm c).isLt hc
    rw [Fin.eta, Equiv.apply_symm_apply] at h1
    exact (mem_ownIdx b c.val).1 (List.mem_of_getElem? h1)

/-- for τ with `IsTau b τ` and a' below the number of own instances: own instance number a' is, in
the whole batch, at the number τ a' -/
theorem IsTau.ownX_at (h : IsTau b τ) (a' : Fin N) (ha : a'.val < b.ownX.length) :
    b.ownX[a'.val]? = (reqs b)[(τ a').val]? := by
  rw [ownX_getElem?, h a'.val a'.isLt ha]
  rfl

theorem symm_mul (σ τ : Equiv.Perm (Fin N)) (s : Fin N) : (σ * τ).symm s = τ.symm (σ.symm s) := rfl

end Tau

end Place

end Compile.Batch
