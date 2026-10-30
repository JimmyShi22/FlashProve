-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Values.lean: the head's example: publicOfO at the stored full-size files: its
first step, over named values.
  yBase · foW · kbmW · pubW · yFull: terms, no literals. `values_W`: the six equations.
  **`polLayout_W` : Verify.polLayout VerifierAndGoals.storedPublicFiles.pol = .ok (PW, yFull).**
  `noFill_W` | `noAsk_W` | `planeCols_W` | `pub_W`: the twins and the two later steps return
    yBase | foW | kbmW | pubW. `withY_eq` | `withFo_eq`: a closed fact by Lean's kernel at the
    twins speaks of yBase | foW.
  `h_W` | `hFull_W` | `dq_W` | `lPd_W`: yBase.h = hW · yFull.h = hW · yBase.dq = 5120 ·
    yBase.lPd = 13; each of the last two by one closed test, with a control that comes out false.
The twins baseNoFill | shapeNoAsk | callAskNoTab come through Johnson/AtFull/Public/Twins.lean;
shape_eq | ask_eq from Johnson/Unfolds/ShapeEq.lean. This file still holds, in its own namespace,
the texts of the laws that also stand in Johnson/Unfolds/Tabs | Count | PubAsk | Used.

Limits. The recursion limit is raised in this file (maxRecDepth 1000000). The values of most fields
are not spelled out; of the counts of padding keys a bound alone is shown. Nothing on soundness.

-/
import Johnson.AtFull.Public.Twins
import Johnson.Goal.Meaning.PadScope
import Johnson.Meaning.GateLut
import Johnson.Desc.Sound.RuleAtKitProofs
import Johnson.Road.FormsKeysPub
import Johnson.Road.FormsKeysRun
import Johnson.Road.FormsKeysCap
import Johnson.Goal.Meaning.ScalesReturn
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial.Values
open OnBytes OnBytes.Model OnBytes.Model.Layer
open Johnson.Unfolds (shape_eq ask_eq)

/-- The check: tensorsFill's two tests, with "the runs rise already" in the sort's place. -/
def fillB (ten : List (String × TenAt)) (feat S2 : Nat) : Bool :=
  !(ten.any fun t => t.2.J == 0 || t.2.J % S2 != 0) &&
    decide ((tensorRuns ten).Pairwise fun a b => decide (a.1 ≤ b.1) = true) &&
    (runsEnd (tensorRuns ten) 0 == some feat)

/-- The library's law fill_ok (Johnson/Road/FormsKeysRun.lean), its three premises in one test. -/
theorem fill_of_check {ten : List (String × TenAt)} {feat S2 : Nat} (arr : String)
    (h : fillB ten feat S2 = true) : tensorsFill ten feat S2 arr = .ok () := by
  unfold fillB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact OnBytes.Road.fill_ok ten feat S2 arr h1 (h2.imp fun hab => decide_eq_true hab) h3

theorem base_eq (h : Layer.Shape) (pc : List (List String))
    (h1 : tensorsFill [("x", (⟨0, h.xl, 1, h.d⟩ : TenAt))] (h.xl * h.d) (2 ^ (h.la - h.lt))
      "stream" = .ok ())
    (h2 : tensorsFill (((layTensors (tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2)
        (h.H * h.dh + h.Gk * h.dh) (h.H * h.dh) (h.Gk * h.dh)) #[0, 0, 0, 0]).1.filter
          fun t => t.mat == 3).map fun t => (t.name, t.place))
      ((layTensors (tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2) (h.H * h.dh + h.Gk * h.dh)
        (h.H * h.dh) (h.Gk * h.dh)) #[0, 0, 0, 0]).2.getD 3 0) (2 ^ (h.la - h.lt)) "qa" = .ok ()) :
    layoutBase h pc = baseNoFill h pc := by
  unfold layoutBase baseNoFill
  simp only [h1, h2]
  rfl

/-- A number below 2 ^ 42, as a word, is below the prime. -/
theorem word_ok {n : Nat} (h : n < 2 ^ 42) : okF n.toUInt64 = true := by
  refine VerifiableInference.Desc.Sound.okF_of_lt _ ?_
  have e : n.toUInt64.toNat = n % 2 ^ 64 := by simp [Nat.toUInt64]
  rw [e, Nat.mod_eq_of_lt (by omega)]
  have : Fmt.Fld.two.p = 18446744069414584321 := by decide
  omega

/-- A table made of a rule over the first n numbers: its size; its words. -/
theorem table_ok (f : Nat → Nat) (n : Nat) (h : ∀ t, t < n → f t < 2 ^ 42) :
    ((Array.range n).map fun t => (f t).toUInt64).size = n ∧
      ∀ x ∈ ((Array.range n).map fun t => (f t).toUInt64).toList, okF x = true := by
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact word_ok (h t ht)

theorem getD_le {a : Array Nat} {B : Nat} (h : ∀ v ∈ a.toList, v ≤ B) (t : Nat) :
    a.getD t 0 ≤ B := by
  by_cases ht : t < a.size
  · have e : a.getD t 0 = a[t] := by simp [Array.getD, ht]
    rw [e]
    exact h _ (Array.getElem_mem_toList ht)
  · have e : a.getD t 0 = 0 := by simp [Array.getD, ht]
    rw [e]
    exact Nat.zero_le _

/-- A word of table SILU is at most 4096 + smax. -/
theorem siluWord_le (eg smax : Nat) (X : Array Nat) (t : Nat) :
    siluWord eg smax X t ≤ 4096 + smax := by
  unfold siluWord
  dsimp only
  split
  · omega
  · have := Nat.min_le_right (roundHalfUp 64 (roundD
      ((if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
        else min (t - 32768) (64 * 2 ^ eg - 1)) *
        (onePlusExp X (if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
          else min (t - 32768) (64 * 2 ^ eg - 1)) (decide (t < 32768))).2)
      (2 ^ eg * (onePlusExp X (if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
          else min (t - 32768) (64 * 2 ^ eg - 1)) (decide (t < 32768))).1))) smax
    omega

section
variable {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}

theorem fc_ok (hy : layoutBase h pc = .ok y) :
    y.tauFC.size = 65536 ∧ ∀ x ∈ y.tauFC.toList, okF x = true := by
  rw [OnBytes.Road.Hd.tauFC_of_base hy]
  exact table_ok rowFC 65536 fun t ht =>
    Nat.lt_trans (OnBytes.Road.Hd.rowFC_lt ht) (by decide)

theorem fl_ok (hy : layoutBase h pc = .ok y) (hs : h.smax ≤ 4095) :
    y.tauFL.size = 65536 ∧ ∀ x ∈ y.tauFL.toList, okF x = true := by
  rw [(Meaning.P34.tables_of_base hy).1]
  refine table_ok (fun t => t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28) 65536
    fun t ht => ?_
  have b : (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 ≤ 4096 + h.smax := by
    refine getD_le (fun v hv => ?_) t
    unfold gateTables at hv
    simp only [Array.toList_map, List.mem_map] at hv
    obtain ⟨u, _, rfl⟩ := hv
    exact siluWord_le _ _ _ _
  show t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28 < 2 ^ 42
  have : (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28 ≤ 8191 * 2 ^ 28 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem fs_ok (hy : layoutBase h pc = .ok y) (h1 : h.eg = 8) (h2 : h.smax = 4095)
    (h3 : h.p3 = true) (h4 : h.gcl = true) :
    y.tauFS.size = 65536 ∧ ∀ x ∈ y.tauFS.toList, okF x = true := by
  rw [(Meaning.P34.tables_of_base hy).2, h1, h2, h3, h4, if_pos rfl]
  exact table_ok (rowFS true (gateTables 8 4095 true true).2) 65536 fun t ht =>
    Nat.lt_trans (Meaning.Gate.rowFS_eq ht).2 (by decide)

end

/-- A table is whole and below the prime. -/
def TabOk (t : Array F) : Prop := t.size = 65536 ∧ ∀ x ∈ t.toList, okF x = true

theorem rec_ok (y : Layer.Lay) (q : Nat) (cd : CallD) (hC : TabOk y.tauFC) (hL : TabOk y.tauFL)
    (hS : TabOk y.tauFS) :
    (∀ t, (y.callRecord q cd).tau = some t → t.size = 2 ^ (y.callRecord q cd).k) ∧
      ∀ x ∈ ((y.callRecord q cd).tau.getD #[]).toList, okF x = true := by
  show (∀ t, y.tauOf cd.kind = some t → t.size = 2 ^ (if cd.kind == "R8" then 8 else 16)) ∧
    ∀ x ∈ ((y.tauOf cd.kind).getD #[]).toList, okF x = true
  generalize cd.kind = k
  unfold Lay.tauOf
  by_cases h1 : k = "FC"
  · subst h1
    refine ⟨fun t ht => ?_, fun x hx => hC.2 x hx⟩
    obtain rfl : y.tauFC = t := Option.some.inj ht
    exact hC.1
  · have e1 : (k == "FC") = false := by simpa using h1
    rw [e1]
    by_cases h2 : k = "FL"
    · subst h2
      refine ⟨fun t ht => ?_, fun x hx => hL.2 x hx⟩
      obtain rfl : y.tauFL = t := Option.some.inj ht
      exact hL.1
    · have e2 : (k == "FL") = false := by simpa using h2
      rw [e2]
      by_cases h3 : k = "FS"
      · subst h3
        refine ⟨fun t ht => ?_, fun x hx => hS.2 x hx⟩
        obtain rfl : y.tauFS = t := Option.some.inj ht
        exact hS.1
      · have e3 : (k == "FS") = false := by simpa using h3
        rw [e3]
        exact ⟨fun t ht => (nomatch ht), fun x hx => absurd hx (by simp)⟩

/-- Every record of the list that layoutLook makes is the record of a call. -/
theorem mem_records (y : Layer.Lay) {c : Call}
    (hc : c ∈ (y.calls.mapIdx fun q cd => y.callRecord q cd).toList) :
    ∃ q cd, c = y.callRecord q cd := by
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hc
  obtain ⟨i, hi, e⟩ := hc
  exact ⟨i, _, e.symm⟩

theorem foldlM_returns {α β : Type} (f : β → α → Except String β) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, ∃ b', f b x = .ok b') → ∃ b', l.foldlM f b = .ok b'
  | [], b, _ => ⟨b, rfl⟩
  | a :: l, b, h => by
    obtain ⟨b1, e⟩ := h a (List.mem_cons_self ..) b
    obtain ⟨b2, e2⟩ := foldlM_returns f l b1 fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b2, ?_⟩
    rw [List.foldlM_cons, e]
    exact e2

theorem pubOfCall_returns (y : Lay) (fo : Forest.Shape) (q : Nat) (cd : CallD) (pub : Array Nat)
    (hfit : y.Lam * cd.J ≤ 2 ^ (fo.dT - y.h.lt) * 2 ^ fo.iota.getD q 0) :
    ∃ pub', y.pubOfCall fo q cd pub = .ok pub' := by
  unfold Lay.pubOfCall
  refine foldlM_returns _ _ _ fun x hx b => ?_
  have hx' : x < y.Lam * cd.J := List.mem_range.1 hx
  have z : x / 2 ^ (fo.dT - y.h.lt) / 2 ^ fo.iota.getD q 0 = 0 := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx' hfit)
  by_cases hp : cd.padding (x / cd.J) (x % cd.J) = true
  · refine ⟨b.modify (fo.first.getD q 0 + x / 2 ^ (fo.dT - y.h.lt)) (· + y.T), ?_⟩
    simp only [hp, if_true, z]
    rfl
  · refine ⟨b, ?_⟩
    simp only [hp]
    rfl

theorem pubAll_returns (y : Lay) (fo : Forest.Shape) (pub : Array Nat)
    (hfit : ∀ x ∈ y.calls.toList.zipIdx,
      y.Lam * x.1.J ≤ 2 ^ (fo.dT - y.h.lt) * 2 ^ fo.iota.getD x.2 0) :
    ∃ pub', (y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub) pub =
      .ok pub' :=
  foldlM_returns _ _ _ fun x hx b => pubOfCall_returns y fo x.2 x.1 b (hfit x hx)

section
theorem sum_zero {α : Type} (f : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
      sum_zero f l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem in_block {n M t : Nat} (hM : 0 < M) (h : n / M = t) : t * M ≤ n ∧ n < t * M + M := by
  subst h
  refine ⟨Nat.div_mul_le_self n M, ?_⟩
  have := Nat.lt_mul_div_succ n hM
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
  exact this

theorem block_le (Q : Nat → Bool) (T M t : Nat) (hM : 0 < M) : ∀ n,
    ((List.range n).map fun x => if Q x = true ∧ x / M = t then T else 0).sum ≤
      (min n (t * M + M) - min n (t * M)) * T
  | 0 => by simp
  | n + 1 => by
    have ih := block_le Q T M t hM n
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : Q n = true ∧ n / M = t
    · rw [if_pos hc]
      obtain ⟨h1, h2⟩ := in_block hM hc.2
      generalize t * M = a at *
      have e : min (n + 1) (a + M) - min (n + 1) a = (min n (a + M) - min n a) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      omega
    · rw [if_neg hc, Nat.add_zero]
      generalize t * M = a at *
      exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))

theorem block_lt (Q : Nat → Bool) (T M t x₀ : Nat) (hM : 0 < M) (h0 : Q x₀ = false)
    (ht : x₀ / M = t) : ∀ n,
    ((List.range n).map fun x => if Q x = true ∧ x / M = t then T else 0).sum +
        (if x₀ < n then T else 0) ≤ (min n (t * M + M) - min n (t * M)) * T
  | 0 => by simp
  | n + 1 => by
    have ih := block_lt Q T M t x₀ hM h0 ht n
    obtain ⟨w1, w2⟩ := in_block hM ht
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hc : Q n = true ∧ n / M = t
    · rw [if_pos hc]
      have hne : x₀ ≠ n := fun e => by rw [e, hc.1] at h0; exact absurd h0 (by decide)
      obtain ⟨h1, h2⟩ := in_block hM hc.2
      generalize t * M = a at *
      have e : min (n + 1) (a + M) - min (n + 1) a = (min n (a + M) - min n a) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      by_cases hx : x₀ < n
      · rw [if_pos hx] at ih
        rw [if_pos (by omega)]
        omega
      · rw [if_neg hx] at ih
        rw [if_neg (by omega)]
        omega
    · rw [if_neg hc, Nat.add_zero]
      generalize t * M = a at *
      by_cases hx : x₀ < n
      · rw [if_pos hx] at ih
        rw [if_pos (by omega)]
        exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))
      · rw [if_neg hx] at ih
        by_cases hx' : x₀ < n + 1
        · rw [if_pos hx']
          have en : x₀ = n := by omega
          subst en
          have e : min (x₀ + 1) (a + M) - min (x₀ + 1) a = (min x₀ (a + M) - min x₀ a) + 1 := by
            omega
          rw [e, Nat.add_mul, Nat.one_mul]
          omega
        · rw [if_neg hx']
          exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))

section
variable (y : Layer.Lay) (first dT : Nat) (cd : CallD)

theorem pubOf_in (t : Nat) : OnBytes.Road.pubOf y first dT cd (first + t) =
    ((List.range (y.Lam * cd.J)).map fun x =>
      if (cd.padding (x / cd.J) (x % cd.J)) = true ∧ x / 2 ^ (dT - y.h.lt) = t then y.T else 0).sum
          := by
  unfold OnBytes.Road.pubOf
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Nat.add_left_cancel_iff]

theorem pubOf_out {A θ : Nat} (hfit : y.Lam * cd.J ≤ 2 ^ (dT - y.h.lt) * A)
    (hθ : θ < first ∨ first + A ≤ θ) : OnBytes.Road.pubOf y first dT cd θ = 0 := by
  unfold OnBytes.Road.pubOf
  refine sum_zero _ _ fun x hx => ?_
  have hx' : x < y.Lam * cd.J := List.mem_range.1 hx
  have hd : x / 2 ^ (dT - y.h.lt) < A :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hx' hfit)
  rw [if_neg]
  rintro ⟨_, e⟩
  generalize x / 2 ^ (dT - y.h.lt) = d at hd e
  omega

theorem pubOf_le (t : Nat) :
    OnBytes.Road.pubOf y first dT cd (first + t) ≤ 2 ^ (dT - y.h.lt) * y.T := by
  rw [pubOf_in]
  refine Nat.le_trans (block_le (fun x => cd.padding (x / cd.J) (x % cd.J)) y.T
    (2 ^ (dT - y.h.lt)) t (Nat.two_pow_pos _) _) (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ (dT - y.h.lt) = M
  generalize t * M = a
  omega

theorem pubOf_lt {x₀ : Nat} (hx : x₀ < y.Lam * cd.J)
    (h0 : cd.padding (x₀ / cd.J) (x₀ % cd.J) = false) :
    OnBytes.Road.pubOf y first dT cd (first + x₀ / 2 ^ (dT - y.h.lt)) + y.T ≤
      2 ^ (dT - y.h.lt) * y.T := by
  rw [pubOf_in]
  have k := block_lt (fun x => cd.padding (x / cd.J) (x % cd.J)) y.T (2 ^ (dT - y.h.lt))
    (x₀ / 2 ^ (dT - y.h.lt)) x₀ (Nat.two_pow_pos _) h0 rfl (y.Lam * cd.J)
  rw [if_pos hx] at k
  refine Nat.le_trans k (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ (dT - y.h.lt) = M
  generalize x₀ / M * M = a
  omega

end

/-- The bound on what one call adds at one tree. -/
def bdOf (y : Layer.Lay) (fo : Forest.Shape) (x : CallD × Nat) (θ : Nat) : Nat :=
  if fo.first.getD x.2 0 ≤ θ ∧ θ < fo.first.getD x.2 0 + 2 ^ fo.iota.getD x.2 0 then
    (if θ = fo.first.getD x.2 0 + 1 / (2 ^ (fo.dT - y.h.lt) / x.1.J) then
      2 ^ (fo.dT - y.h.lt) * y.T - y.T else 2 ^ (fo.dT - y.h.lt) * y.T)
  else 0

/-- The bound on a tree's count. -/
def vOf (y : Layer.Lay) (fo : Forest.Shape) (θ : Nat) : Nat :=
  (y.calls.toList.zipIdx.map fun x => bdOf y fo x θ).sum

/-- Four closed conditions on a call. -/
def callB (y : Layer.Lay) (fo : Forest.Shape) (x : CallD × Nat) : Bool :=
  decide (y.Lam * x.1.J ≤ 2 ^ (fo.dT - y.h.lt) * 2 ^ fo.iota.getD x.2 0) &&
    decide (2 ^ (fo.dT - y.h.lt) = x.1.J * (2 ^ (fo.dT - y.h.lt) / x.1.J)) &&
    decide (2 ≤ y.Lam) && decide (0 < x.1.J)

theorem bd_le (y : Layer.Lay) (fo : Forest.Shape) (x : CallD × Nat) (θ : Nat)
    (hB : callB y fo x = true) (hw : ∃ p, p < x.1.J ∧ x.1.padding 1 p = false) :
    OnBytes.Road.pubOf y (fo.first.getD x.2 0) fo.dT x.1 θ ≤ bdOf y fo x θ := by
  unfold callB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hB
  unfold bdOf
  by_cases hin : fo.first.getD x.2 0 ≤ θ ∧ θ < fo.first.getD x.2 0 + 2 ^ fo.iota.getD x.2 0
  · rw [if_pos hin]
    obtain ⟨t, rfl⟩ : ∃ t, θ = fo.first.getD x.2 0 + t := ⟨θ - fo.first.getD x.2 0, by omega⟩
    by_cases ht : fo.first.getD x.2 0 + t =
        fo.first.getD x.2 0 + 1 / (2 ^ (fo.dT - y.h.lt) / x.1.J)
    · rw [if_pos ht, ht]
      obtain ⟨p, hp, h0⟩ := hw
      have hx : x.1.J + p < y.Lam * x.1.J := by
        have : 2 * x.1.J ≤ y.Lam * x.1.J := Nat.mul_le_mul_right _ c3
        omega
      have d1 : (x.1.J + p) / x.1.J = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      have d2 : (x.1.J + p) % x.1.J = p := by
        rw [Nat.add_mod_left]
        exact Nat.mod_eq_of_lt hp
      have d3 : (x.1.J + p) / 2 ^ (fo.dT - y.h.lt) = 1 / (2 ^ (fo.dT - y.h.lt) / x.1.J) := by
        generalize 2 ^ (fo.dT - y.h.lt) / x.1.J = r at c2 ⊢
        rw [c2, ← Nat.div_div_eq_div_mul, d1]
      have k := pubOf_lt y (fo.first.getD x.2 0) fo.dT x.1 hx (by rw [d1, d2]; exact h0)
      rw [d3] at k
      exact Nat.le_sub_of_add_le k
    · rw [if_neg ht]
      exact pubOf_le y _ _ _ t
  · rw [if_neg hin, pubOf_out y _ _ _ c1 (by omega)]

theorem sum_le {α : Type} (f g : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (sum_le f g l fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **The counts that the loops return lie under the bound.** -/
theorem pub_le (y : Layer.Lay) (fo : Forest.Shape) (pub : Array Nat)
    (hf : (y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub)
      (Forest.noPub fo) = .ok pub)
    (hall : ∀ x ∈ y.calls.toList.zipIdx, callB y fo x = true ∧
      ∃ p, p < x.1.J ∧ x.1.padding 1 p = false) :
    pub.size = fo.NT ∧ ∀ θ, pub.getD θ 0 ≤ vOf y fo θ := by
  have h0 : (Forest.noPub fo).size = fo.NT := by simp [Forest.noPub]
  obtain ⟨s, f⟩ := OnBytes.Road.loop_adds (fun (x : CallD × Nat) pub => y.pubOfCall fo x.2 x.1 pub)
    (fun x θ => OnBytes.Road.pubOf y (fo.first.getD x.2 0) fo.dT x.1 θ) fo.NT
    (fun x pub pub' hs h => OnBytes.Road.pubOfCall_adds y fo x.2 x.1 fo.NT pub pub' hs h)
    (y.calls.toList.zipIdx) (Forest.noPub fo) pub h0 hf
  refine ⟨s, fun θ => ?_⟩
  by_cases hθ : θ < fo.NT
  · have z : (Forest.noPub fo).getD θ 0 = 0 := by simp [Forest.noPub, Array.getD]
    rw [f θ hθ, z, Nat.zero_add]
    exact sum_le _ _ _ fun x hx => bd_le y fo x θ (hall x hx).1 (hall x hx).2
  · have z : pub.getD θ 0 = 0 := by simp [Array.getD, s, hθ]
    rw [z]
    exact Nat.zero_le _

end

/-- pubAsk's tests on the counts, at a bound. -/
def askB (h : Forest.Shape) (V : Nat → Nat) : Bool :=
  ((List.range h.NT).all fun θ => decide (V θ ≤ 2 ^ h.dT)) &&
    (List.range h.NC).all fun c =>
      decide ((List.range (2 ^ h.iota.getD c 0)).foldl
        (fun s b => s + V (h.first.getD c 0 + b)) 0 < 2 ^ (h.dT + h.iota.getD c 0))

theorem foldl_le (f g : Nat → Nat) (hfg : ∀ b, f b ≤ g b) : ∀ (l : List Nat) (s s' : Nat), s ≤ s' →
    l.foldl (fun s b => s + f b) s ≤ l.foldl (fun s b => s + g b) s'
  | [], _, _, h => h
  | a :: l, s, s', h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_le f g hfg l _ _ (Nat.add_le_add h (hfg a))

theorem loop_ok (h : Forest.Shape) (pub : Array Nat) : ∀ (l : List Nat),
    (∀ c ∈ l, (List.range (2 ^ h.iota.getD c 0)).foldl
      (fun s b => s + pub.getD (h.first.getD c 0 + b) 0) 0 < 2 ^ (h.dT + h.iota.getD c 0)) →
    (forIn l PUnit.unit fun c _ => (
      if (List.range (2 ^ h.iota.getD c 0)).foldl
          (fun s b => s + pub.getD (h.first.getD c 0 + b) 0) 0 ≥ 2 ^ (h.dT + h.iota.getD c 0) then
              do
        throw "forest-only-padding"
        pure (ForInStep.yield PUnit.unit)
      else do
        pure PUnit.unit
        pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))) = .ok PUnit.unit
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.forIn_cons]
    have ha := hl a (List.mem_cons_self ..)
    simp only [ge_iff_le, Nat.not_le.2 ha, if_false]
    exact loop_ok h pub l fun c hc => hl c (List.mem_cons_of_mem _ hc)

/-- **Where the counts lie under a bound that meets the tests, the tests on the counts return.** -/
theorem pubAsk_of (h : Forest.Shape) (pub : Array Nat) (V : Nat → Nat) (h1 : pub.size = h.NT)
    (h2 : h.calls.size = h.NC) (hV : ∀ θ, pub.getD θ 0 ≤ V θ) (hB : askB h V = true) :
    Forest.pubAsk h pub = .ok () := by
  unfold askB at hB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hB
  obtain ⟨b1, b2⟩ := hB
  have e1 : (pub.size != h.NT || h.calls.size != h.NC) = false := by simp [h1, h2]
  have e2 : (pub.any fun x => decide (x > 2 ^ h.dT)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    rw [Array.any_eq_true] at hh
    obtain ⟨i, hi, hx⟩ := hh
    have e : pub.getD i 0 = pub[i] := by simp [Array.getD, hi]
    have k1 := hV i
    have k2 := b1 i (by omega)
    rw [e] at k1
    have := of_decide_eq_true hx
    omega
  have e3 := loop_ok h pub (List.range h.NC) fun c hc =>
    Nat.lt_of_le_of_lt (foldl_le _ _ (fun b => hV (h.first.getD c 0 + b)) _ 0 0 (Nat.le_refl 0))
      (b2 c (List.mem_range.1 hc))
  unfold Forest.pubAsk
  simp only [e1, e2, Bool.false_eq_true, if_false]
  exact Eq.trans (congrArg (fun z => z >>= fun _ => (pure PUnit.unit : Except String PUnit)) e3) rfl

section
open OnBytes.Road
theorem markOf_ne (g : Seg) : markOf g ≠ 0 := by
  unfold markOf
  split <;> decide

/-- A mark, once written, is never 0 again. -/
theorem marks_stay (j : Nat) : ∀ (segs : List Seg) (u : Array Nat), u.getD j 0 ≠ 0 →
    (segs.foldl markUsed u).getD j 0 ≠ 0
  | [], _, h => h
  | g :: segs, u, h => by
    rw [List.foldl_cons]
    refine marks_stay j segs _ ?_
    obtain ⟨a1, a2, a3⟩ := markUsed_get u g j
    by_cases hj : j ∈ g.pos.toList
    · by_cases hs : j < u.size
      · rw [a2 hj hs]
        exact markOf_ne g
      · exfalso
        apply h
        simp [Array.getD, hs]
    · rw [a3 hj]
      exact h

/-- A column of a segment of the list, inside the array, bears a mark. -/
theorem marks_made (j : Nat) : ∀ (segs : List Seg) (u : Array Nat), j < u.size →
    (∃ s ∈ segs, j ∈ s.pos.toList) → (segs.foldl markUsed u).getD j 0 ≠ 0
  | [], _, _, ⟨_, hs, _⟩ => absurd hs List.not_mem_nil
  | g :: segs, u, hj, ⟨s, hs, hp⟩ => by
    rw [List.foldl_cons]
    obtain ⟨a1, a2, a3⟩ := markUsed_get u g j
    rcases List.mem_cons.1 hs with e | hs'
    · subst e
      exact marks_stay j segs _ (by rw [a2 hp hj]; exact markOf_ne s)
    · exact marks_made j segs _ (by rw [a1]; exact hj) ⟨s, hs', hp⟩

/-- **The placing rule leaves a column that is no padding on an odd layer.** -/
theorem place_used (name kind : String) (asks : List SegAsk) (fl : Nat)
    (h : ∃ a ∈ asks, 0 < a.2.1 ∧ a.2.1 < 2 ^ (topBit + 1)) :
    ∃ p, p < (place name kind asks fl).J ∧ (place name kind asks fl).padding 1 p = false := by
  obtain ⟨a, ha, h0, h1⟩ := h
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem ha
  have hn : (asks.map (·.2.1)).getD i 0 = a.2.1 := by
    simp [List.getD, hi, e]
  obtain ⟨c1, c2⟩ := columnsOf_onBlocks (asks.map (·.2.1)) i 0 (topBit + 1) (by simp)
    (by rw [hn]; exact h1)
  rw [hn] at c1 c2
  have hcol := place_columns name kind asks fl i hi
  rw [hn] at hcol
  have hseg : (place name kind asks fl).segs.getD i default ∈ (place name kind asks fl).segs := by
    have hl : i < (place name kind asks fl).segs.length := by
      show i < (asks.zipIdx.map _).length
      simp [hi]
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hlt : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 <
      2 ^ (place name kind asks fl).lJ := by
    rw [hcol]
    refine Nat.lt_of_lt_of_le (c2.inside 0 (by rw [c1]; exact h0)) ?_
    show _ ≤ 2 ^ max (ceilLog2 _) fl
    exact Nat.le_trans (le_two_pow_ceilLog2 _)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hsz : 0 < ((place name kind asks fl).segs.getD i default).pos.size := by
    rw [hcol, c1]
    exact h0
  have hmem : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 ∈
      ((place name kind asks fl).segs.getD i default).pos.toList := by
    have e : ((place name kind asks fl).segs.getD i default).pos.getD 0 0 =
        ((place name kind asks fl).segs.getD i default).pos[0] := by
      unfold Array.getD
      rw [dif_pos hsz]
      rfl
    rw [e]
    exact Array.getElem_mem_toList hsz
  have hu : (place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 ≠ 0 :=
    marks_made _ (place name kind asks fl).segs
      (Array.replicate (2 ^ (place name kind asks fl).lJ) 0)
      (by rw [Array.size_replicate]; exact hlt) ⟨_, hseg, hmem⟩
  refine ⟨((place name kind asks fl).segs.getD i default).pos.getD 0 0, hlt, ?_⟩
  show ((place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 == 0 ||
    ((place name kind asks fl).used.getD
      (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 == 2 && 1 % 2 == 0)) = false
  generalize (place name kind asks fl).used.getD
    (((place name kind asks fl).segs.getD i default).pos.getD 0 0) 0 = u at hu ⊢
  have e0 : (u == 0) = false := by simpa using hu
  rw [e0]
  simp

end

/-! ## The closed facts, and the join -/

/-- The layers' shape at the scan's WRITTEN value at the stored free numbers. -/
def hW : Layer.Shape :=
  Verify.layerShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines)

/-- layoutLook's own first line. -/
abbrev clOf (y : Layer.Lay) : Array Call := y.calls.mapIdx fun q cd => y.callRecord q cd

/-- A test at the first half's value and the forest's numbers, made without the two sorting calls
  and
without the tests on the calls' tables. -/
def withFo (f : Layer.Lay → Forest.Shape → Bool) : Bool :=
  match baseNoFill hW VerifierAndGoals.Lines.callsRef with
  | .ok y => (match Forest.shapeNoAsk (clOf y) y.h.lidb with
    | .ok fo => f y fo
    | .error _ => false)
  | .error _ => false

theorem withFo_true {f : Layer.Lay → Forest.Shape → Bool} (h : withFo f = true) :
    ∃ y fo, baseNoFill hW VerifierAndGoals.Lines.callsRef = .ok y ∧
      Forest.shapeNoAsk (clOf y) y.h.lidb = .ok fo ∧ f y fo = true := by
  unfold withFo at h
  split at h
  · rename_i y hy
    split at h
    · rename_i fo hfo
      exact ⟨y, fo, hy, hfo, h⟩
    · cases h
  · cases h

theorem ok_unit {x : Except String PUnit} (h : x.toOption.isSome = true) : x = .ok () := by
  cases x with
  | error e => cases h
  | ok a => rfl

theorem ok_some {α : Type} {x : Except String α} (h : x.toOption.isSome = true) :
    ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

theorem bind_ok {α β : Type} {x : Except String α} {a : α} (h : x = .ok a)
    (f : α → Except String β) : (x >>= f) = f a := by
  rw [h]
  rfl

theorem refuse_ok {b : Bool} (n : String) (h : b = false) : refuseIf b n = .ok () := by
  subst h
  rfl

theorem fst_mem {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat), x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => absurd h (by simp)
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h'
    · subst e
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem l (k + 1) x h')

/-- All that is asked of Lean's kernel behind the first half: numbers and short lists. -/
def bigTest (y : Layer.Lay) (fo : Forest.Shape) : Bool :=
  ((y.calls.zip (clOf y)).forM fun x => y.callHeld x.1 x.2).toOption.isSome &&
  ((clOf y).toList.all fun c => (Forest.callAskNoTab c).toOption.isSome) &&
  !decide (fo.dT < y.h.la) &&
  (Forest.planeCols fo y.h.lmb).toOption.isSome &&
  (((clOf y).zip fo.iota).forM fun x => refuseIf (x.1.iota != x.2) "shape-call").toOption.isSome &&
  !((List.range 8).any fun q => decide (q ≥ y.calls.size) && y.h.iota.getD q 0 != 0) &&
  (y.calls.toList.zipIdx.all fun x => callB y fo x &&
    x.1.segs.any fun s => decide (0 < s.n) && decide (s.n < 2 ^ (topBit + 1))) &&
  askB fo (vOf y fo) &&
  (fo.calls.size == fo.NC)

theorem shapeW : hW.p3 = true ∧ hW.gcl = true ∧ hW.eg = 8 ∧ hW.smax = 4095 := by decide +kernel

theorem streamW : fillB [("x", (⟨0, hW.xl, 1, hW.d⟩ : TenAt))] (hW.xl * hW.d)
    (2 ^ (hW.la - hW.lt)) = true := by decide +kernel

theorem qaW : fillB (((layTensors (tensorAsks hW (2 ^ hW.ll) (2 ^ hW.ll / 2)
      (hW.H * hW.dh + hW.Gk * hW.dh) (hW.H * hW.dh) (hW.Gk * hW.dh)) #[0, 0, 0, 0]).1.filter
        fun t => t.mat == 3).map fun t => (t.name, t.place))
    ((layTensors (tensorAsks hW (2 ^ hW.ll) (2 ^ hW.ll / 2) (hW.H * hW.dh + hW.Gk * hW.dh)
      (hW.H * hW.dh) (hW.Gk * hW.dh)) #[0, 0, 0, 0]).2.getD 3 0) (2 ^ (hW.la - hW.lt)) = true := by
  decide +kernel

theorem allW : withFo bigTest = true := by decide +kernel

/-- **THE LAYERS' LAYOUT RETURNS AT THE SCAN's WRITTEN VALUE**, and what it returns: the first
  half's
value with the calls' records, the forest's numbers with the counts of padding keys, and the planes'
columns laid in. -/
theorem layout_returns : ∃ (y : Layer.Lay) (fo : Forest.Shape) (pub : Array Nat) (kbm : Nat),
    layoutBase hW VerifierAndGoals.Lines.callsRef = .ok y ∧
    Forest.shape (clOf y) y.h.lidb = .ok fo ∧
    Forest.planeCols fo y.h.lmb = .ok kbm ∧
    (y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub) (Forest.noPub fo) =
      .ok pub ∧
    Layer.layout hW VerifierAndGoals.Lines.callsRef =
      .ok { y with cl := clOf y, fo := { fo with pub := pub }, kbm := kbm } := by
  obtain ⟨y, fo, hy0, hfo, hT⟩ := withFo_true allW
  unfold bigTest at hT
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true,
    beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩ := hT
  obtain ⟨s1, s2, s3, s4⟩ := shapeW
  have hb : layoutBase hW VerifierAndGoals.Lines.callsRef = .ok y :=
    (base_eq hW VerifierAndGoals.Lines.callsRef (fill_of_check _ streamW) (fill_of_check _ qaW)).trans hy0
  have A := OnBytes.Road.admitted_of_base hb s1
  have hC := fc_ok hb
  have hL := fl_ok hb (Nat.le_of_eq s4)
  have hS := fs_ok hb s3 s4 s1 s2
  have asks : ∀ c ∈ (clOf y).toList, Forest.callAsk c = .ok () := by
    intro c hc
    have k := t2 c hc
    obtain ⟨q, cd, rfl⟩ := mem_records y hc
    rw [ask_eq _ (rec_ok y q cd hC hL hS).1 (rec_ok y q cd hC hL hS).2]
    exact ok_unit k
  have f2 : Forest.shape (clOf y) y.h.lidb = .ok fo := (shape_eq _ _ asks).trans hfo
  obtain ⟨kbm, f4⟩ := ok_some t4
  have hall : ∀ x ∈ y.calls.toList.zipIdx, callB y fo x = true ∧
      ∃ p, p < x.1.J ∧ x.1.padding 1 p = false := by
    intro x hx
    obtain ⟨k1, k0⟩ := t7 x hx
    obtain ⟨s, hs, k2⟩ := List.any_eq_true.1 k0
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at k2
    refine ⟨k1, ?_⟩
    obtain ⟨cl, taken, _, _, hc⟩ := A.calls
    have hm : x.1 ∈ y.calls.toList := fst_mem _ _ _ hx
    rw [hc] at hm
    obtain ⟨c, _, e⟩ := List.mem_map.1 hm
    rw [← e] at hs ⊢
    obtain ⟨a, ha, _, e2, _⟩ := OnBytes.Road.place_segs _ _ _ _ s hs
    exact place_used _ _ _ _ ⟨a, ha, by rw [← e2]; exact k2.1, by rw [← e2]; exact k2.2⟩
  obtain ⟨pub, f6⟩ := pubAll_returns y fo (Forest.noPub fo) fun x hx => by
    have k := (hall x hx).1
    unfold callB at k
    simp only [Bool.and_eq_true, decide_eq_true_eq] at k
    exact k.1.1.1
  obtain ⟨p1, p2⟩ := pub_le y fo pub f6 hall
  have f7 : Forest.pubAsk fo pub = .ok () := pubAsk_of fo pub (vOf y fo) p1 t9 p2 t8
  refine ⟨y, fo, pub, kbm, hb, f2, f4, f6, ?_⟩
  unfold Layer.layout
  rw [bind_ok hb]
  unfold layoutLook
  dsimp only
  rw [bind_ok (ok_unit t1), bind_ok f2, bind_ok (refuse_ok _ (decide_eq_false t3)), bind_ok f4,
    bind_ok (ok_unit t5), bind_ok f6, bind_ok f7, bind_ok (refuse_ok _ t6)]
  rfl

/-! ## polLayout at the stored full-size parameter file's own bytes -/

/-- The strict scan's WRITTEN value at the stored free numbers. -/
def PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- **The strict scan of the stored parameter file returns the written value.** (The text of
scan_zFull in Johnson/AtFull/Public/Scales.lean, repeated here.) -/
theorem scan_zFull : polScan VerifierAndGoals.storedPublicFiles.pol = .ok PW := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨P, hP, -⟩ := Meaning.Ret.shape_of_read hZ hR
  rw [hP]
  rw [VerifierAndGoals.pol_zFull] at hP
  exact congrArg Except.ok (VerifierAndGoals.Lines.scan_closed hP)

theorem beforeW : (polBeforeLayout PW).toOption.isSome = true := by decide +kernel
theorem tablesW : (polTablesAdmitted PW).toOption.isSome = true := by decide +kernel
theorem behindW : (polBehindLayout PW).toOption.isSome = true := by decide +kernel

/-- Every record that layoutLook makes has multiplicities of 32 bits: by its text. -/
theorem planes_ok (y : Layer.Lay) : Verify.planesHeld (clOf y) = .ok () := by
  unfold Verify.planesHeld
  refine refuse_ok _ ?_
  rw [Bool.eq_false_iff]
  intro hh
  rw [Array.any_eq_true'] at hh
  obtain ⟨c, hc, hn⟩ := hh
  obtain ⟨q, cd, rfl⟩ := mem_records y (Array.mem_toList_iff.mpr hc)
  have hn' : ((5 : Nat) != 5) = true := hn
  exact absurd hn' (by decide)

/-- **THE SCAN AND THE LAYERS' LAYOUT, WITH THE TESTS ROUND THEM, RETURN AT THE STORED FULL-SIZE
  PARAMETER
FILE's OWN BYTES**, and what they return. -/
theorem polLayout_zFull : ∃ (y : Layer.Lay) (fo : Forest.Shape) (pub : Array Nat) (kbm : Nat),
    layoutBase hW VerifierAndGoals.Lines.callsRef = .ok y ∧
    Forest.shape (clOf y) y.h.lidb = .ok fo ∧
    Forest.planeCols fo y.h.lmb = .ok kbm ∧
    (y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub) (Forest.noPub fo) =
      .ok pub ∧
    Verify.polLayout VerifierAndGoals.storedPublicFiles.pol =
      .ok (PW, { y with cl := clOf y, fo := { fo with pub := pub }, kbm := kbm }) := by
  obtain ⟨y, fo, pub, kbm, h1, h2, h3, h4, h5⟩ := layout_returns
  refine ⟨y, fo, pub, kbm, h1, h2, h3, h4, ?_⟩
  have h5' : Layer.layout (Verify.layerShape PW) PW.polCalls =
      .ok { y with cl := clOf y, fo := { fo with pub := pub }, kbm := kbm } := h5
  unfold Verify.polLayout
  rw [bind_ok scan_zFull, bind_ok (ok_unit beforeW), bind_ok h5', bind_ok (ok_unit behindW)]
  dsimp only
  rw [bind_ok (planes_ok y), bind_ok (ok_unit tablesW)]
  rfl

/-! ## The values by name -/

/-- The value of a computation that returns. -/
def valOf {α : Type} (x : Except String α) (h : x.toOption.isSome = true) : α := x.toOption.get h

theorem valOf_eq {α : Type} {x : Except String α} {a : α} (e : x = .ok a)
    (h : x.toOption.isSome = true) : valOf x h = a := by
  subst e
  rfl

theorem base_some : (layoutBase hW VerifierAndGoals.Lines.callsRef).toOption.isSome = true := by
  obtain ⟨y, _, _, _, h1, _⟩ := layout_returns
  rw [h1]
  rfl

/-- The first half's value. -/
def yBase : Layer.Lay := valOf (layoutBase hW VerifierAndGoals.Lines.callsRef) base_some

/-- The forest's numbers. -/
def foW : Forest.Shape := (Forest.shape (clOf yBase) yBase.h.lidb).toOption.getD default

/-- The planes' columns. -/
def kbmW : Nat := (Forest.planeCols foW yBase.h.lmb).toOption.getD 0

/-- The counts of padding keys. -/
def pubW : Array Nat := ((yBase.calls.toList.zipIdx).foldlM
  (fun pub x => yBase.pubOfCall foW x.2 x.1 pub) (Forest.noPub foW)).toOption.getD #[]

/-- The layers' layout at the stored full-size parameter file. -/
def yFull : Layer.Lay := { yBase with cl := clOf yBase, fo := { foW with pub := pubW }, kbm := kbmW
    }

/-- **All six at once.** -/
theorem values_W : layoutBase hW VerifierAndGoals.Lines.callsRef = .ok yBase ∧
    Forest.shape (clOf yBase) yBase.h.lidb = .ok foW ∧
    Forest.planeCols foW yBase.h.lmb = .ok kbmW ∧
    (yBase.calls.toList.zipIdx).foldlM (fun pub x => yBase.pubOfCall foW x.2 x.1 pub)
      (Forest.noPub foW) = .ok pubW ∧
    Layer.layout hW VerifierAndGoals.Lines.callsRef = .ok yFull ∧
    Verify.polLayout VerifierAndGoals.storedPublicFiles.pol = .ok (PW, yFull) := by
  obtain ⟨y, fo, pub, kbm, h1, h2, h3, h4, h5⟩ := polLayout_zFull
  obtain ⟨y', fo', pub', kbm', g1, g2, g3, g4, g5⟩ := layout_returns
  have e1 : yBase = y := valOf_eq h1 base_some
  subst e1
  have e2 : foW = fo := by
    unfold foW
    rw [h2]
    rfl
  subst e2
  have e3 : kbmW = kbm := by
    unfold kbmW
    rw [h3]
    rfl
  subst e3
  have e4 : pubW = pub := by
    unfold pubW
    rw [h4]
    rfl
  subst e4
  obtain rfl : yBase = y' := Except.ok.inj (h1.symm.trans g1)
  obtain rfl : foW = fo' := Except.ok.inj (h2.symm.trans g2)
  obtain rfl : kbmW = kbm' := Except.ok.inj (h3.symm.trans g3)
  obtain rfl : pubW = pub' := Except.ok.inj (h4.symm.trans g4)
  exact ⟨h1, h2, h3, h4, g5, h5⟩

theorem base_W : layoutBase hW VerifierAndGoals.Lines.callsRef = .ok yBase := values_W.1
theorem shape_W : Forest.shape (clOf yBase) yBase.h.lidb = .ok foW := values_W.2.1
theorem layout_W : Layer.layout hW VerifierAndGoals.Lines.callsRef = .ok yFull := values_W.2.2.2.2.1
theorem polLayout_W : Verify.polLayout VerifierAndGoals.storedPublicFiles.pol = .ok (PW, yFull) := values_W.2.2.2.2.2

/-- A test at the first half's value, made without the two sorting calls. -/
def withY (f : Layer.Lay → Bool) : Bool :=
  match baseNoFill hW VerifierAndGoals.Lines.callsRef with
  | .ok y => f y
  | .error _ => false

theorem noFill_W : baseNoFill hW VerifierAndGoals.Lines.callsRef = .ok yBase :=
  (base_eq hW VerifierAndGoals.Lines.callsRef (fill_of_check _ streamW) (fill_of_check _ qaW)).symm.trans
    base_W

/-- **A closed fact at the twin speaks of yBase.** -/
theorem withY_eq (f : Layer.Lay → Bool) : withY f = f yBase := by
  unfold withY
  rw [noFill_W]

theorem noAsk_W : Forest.shapeNoAsk (clOf yBase) yBase.h.lidb = .ok foW := by
  obtain ⟨y, fo, hy0, hfo, _⟩ := withFo_true allW
  obtain rfl : yBase = y := Except.ok.inj (noFill_W.symm.trans hy0)
  have hC := fc_ok base_W
  obtain ⟨s1, s2, s3, s4⟩ := shapeW
  have hL := fl_ok base_W (Nat.le_of_eq s4)
  have hS := fs_ok base_W s3 s4 s1 s2
  have hT := (withFo_true allW)
  obtain ⟨y', fo', hy', hfo', hT'⟩ := hT
  obtain rfl : yBase = y' := Except.ok.inj (noFill_W.symm.trans hy')
  unfold bigTest at hT'
  simp only [Bool.and_eq_true, List.all_eq_true] at hT'
  have t2 := hT'.1.1.1.1.1.1.1.2
  have asks : ∀ c ∈ (clOf yBase).toList, Forest.callAsk c = .ok () := by
    intro c hc
    have k := t2 c hc
    obtain ⟨q, cd, rfl⟩ := mem_records yBase hc
    rw [ask_eq _ (rec_ok yBase q cd hC hL hS).1 (rec_ok yBase q cd hC hL hS).2]
    exact ok_unit k
  exact (shape_eq _ _ asks).symm.trans shape_W

/-- **A closed fact at the twins speaks of yBase and foW.** -/
theorem withFo_eq (f : Layer.Lay → Forest.Shape → Bool) : withFo f = f yBase foW := by
  unfold withFo
  rw [noFill_W]
  dsimp only
  rw [noAsk_W]

theorem planeCols_W : Forest.planeCols foW yBase.h.lmb = .ok kbmW := values_W.2.2.1
theorem pub_W : (yBase.calls.toList.zipIdx).foldlM (fun pub x => yBase.pubOfCall foW x.2 x.1 pub)
    (Forest.noPub foW) = .ok pubW := values_W.2.2.2.1

/-! ## Small facts on the first half's value, for the ledger's premises -/

/-- The first half keeps the shape: the library's base_shape (Johnson/Road/FormsKeysCap.lean). -/
theorem h_W : yBase.h = hW := OnBytes.Road.base_shape base_W

/-- yFull's shape is yBase's: the "with" touches cl, fo and kbm alone. -/
theorem hFull_W : yFull.h = hW := h_W

theorem dqB : withY (fun y => y.dq == 5120) = true := by decide +kernel
theorem dqB_no : withY (fun y => y.dq == 5121) = false := by decide +kernel
theorem lPdB : withY (fun y => y.lPd == 13) = true := by decide +kernel
theorem lPdB_no : withY (fun y => y.lPd == 14) = false := by decide +kernel

theorem dq_W : yBase.dq = 5120 := eq_of_beq ((withY_eq _).symm.trans dqB)
theorem lPd_W : yBase.lPd = 13 := eq_of_beq ((withY_eq _).symm.trans lPdB)

end OnBytes.Road.K4.Trial.Values

#print axioms OnBytes.Road.K4.Trial.Values.shapeW
#print axioms OnBytes.Road.K4.Trial.Values.streamW
#print axioms OnBytes.Road.K4.Trial.Values.qaW
#print axioms OnBytes.Road.K4.Trial.Values.allW
#print axioms OnBytes.Road.K4.Trial.Values.layout_returns
#print axioms OnBytes.Road.K4.Trial.Values.scan_zFull
#print axioms OnBytes.Road.K4.Trial.Values.planes_ok
#print axioms OnBytes.Road.K4.Trial.Values.polLayout_zFull
#print axioms OnBytes.Road.K4.Trial.Values.values_W
#print axioms OnBytes.Road.K4.Trial.Values.polLayout_W
#print axioms OnBytes.Road.K4.Trial.Values.withY_eq
#print axioms OnBytes.Road.K4.Trial.Values.withFo_eq
#print axioms OnBytes.Road.K4.Trial.Values.planeCols_W
#print axioms OnBytes.Road.K4.Trial.Values.pub_W
#print axioms OnBytes.Road.K4.Trial.Values.noFill_W
#print axioms OnBytes.Road.K4.Trial.Values.noAsk_W
#print axioms OnBytes.Road.K4.Trial.Values.h_W
#print axioms OnBytes.Road.K4.Trial.Values.hFull_W
#print axioms OnBytes.Road.K4.Trial.Values.dq_W
#print axioms OnBytes.Road.K4.Trial.Values.lPd_W
#print axioms OnBytes.Road.K4.Trial.Values.dqB_no
#print axioms OnBytes.Road.K4.Trial.Values.lPdB_no
