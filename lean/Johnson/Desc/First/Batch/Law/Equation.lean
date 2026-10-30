-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Equation.lean
(kind K9's soundness lemma): THEOREMS: (T2), the one equation is the ledger's
value.
  equation_total   if K9.equation returns an equation, its left side on any data D (eqValue) is the
                   ledger's value (Fork.total) in the world of D (worldAt).
  t2               (T2) of Law/Statements.lean holds of K9.equation.
Beneath it:
  slotsIn_total    the slots put in: CARRIED from the library's settleSteps (HideLaws.lean), through
                   slotFold: where K9's fold returns, Fork.settleStep's fold returns the same.
  weightAt_product a product form's weight at index i is entry i of the form written out.
  weightAt_pick    pickIndex bits i has the weight 1 at i and 0 at every other index below 2^bits.
  rowTerms_val, allTerms_val   what the terms of a virtual row, and of all listed arrays, add up to.
  trees_val        the ledger's value on the arrays is that sum: here the tests K9.weights-sizes,
                   K9.row-form-values, K9.array-laid, K9.arrays-there and K9.no-weight-outside work.
It stops at K9.Equation: terms on named arrays, coefficients on the mask row, a constant. Nothing on
the row that K9.asRow makes of it. Nothing where the text refuses. No count, no probability.

-/
import Johnson.Desc.First.Batch.Law.LayAgrees
import Johnson.Desc.First.Batch.Law.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Tools for a text in Except String -/

theorem ok_bind {α β : Type} {x : Ans α} {f : α → Ans β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : K9.need n b = .ok u) : b = true := by
  unfold K9.need at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- A fold of steps that may refuse under a name. If each step adds g a to a value, the whole fold
adds the sum. -/
theorem foldlM_addsE {α σ : Type} (f : σ → α → Ans σ) (val : σ → K) (g : α → K)
    (H : ∀ s a s', f s a = .ok s' → val s' = val s + g a) :
    ∀ (l : List α) (s s' : σ), l.foldlM f s = .ok s' → val s' = val s + (l.map g).sum
  | [], s, s', h => by
    rw [List.foldlM_nil] at h
    have hs : s = s' := Except.ok.inj h
    subst hs
    simp
  | a :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h2⟩ := ok_bind h
    rw [foldlM_addsE f val g H l t s' h2, H s a t ht, List.map_cons, List.sum_cons]
    ring

/-! ## Tools for sums -/

theorem sumFrom_plain {α : Type} (g : α → K) :
    ∀ (l : List α) (s : Nat), sumFrom (fun _ x => g x) s l = (l.map g).sum
  | [], _ => by simp [sumFrom]
  | x :: l, s => by simp [sumFrom, sumFrom_plain g l (s + 1)]

theorem sumFrom_congr {α : Type} (g g' : Nat → α → K) :
    ∀ (l : List α) (s : Nat), (∀ k x, l[k]? = some x → g (s + k) x = g' (s + k) x) →
      sumFrom g s l = sumFrom g' s l
  | [], _, _ => rfl
  | x :: l, s, H => by
    simp only [sumFrom]
    have h0 : g s x = g' s x := by simpa using H 0 x (by simp)
    rw [h0, sumFrom_congr g g' l (s + 1) (fun k y hy => by
      have h1 := H (k + 1) y (by simpa using hy)
      rwa [show s + (k + 1) = s + 1 + k by omega] at h1)]

theorem sumFrom_range {α : Type} (g : Nat → α → K) (d : α) :
    ∀ (l : List α) (s : Nat),
      sumFrom g s l = ∑ k ∈ Finset.range l.length, g (s + k) (l.getD k d)
  | [], _ => by simp [sumFrom]
  | x :: l, s => by
    simp only [sumFrom, List.length_cons]
    rw [Finset.sum_range_succ', sumFrom_range g d l (s + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show s + 1 + k = s + (k + 1) by omega]

theorem sum_map_range (g : ℕ → K) :
    ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range g n,
      Finset.sum_range_succ]
    simp

theorem foldl_push_list {α β : Type} (f : α → β) :
    ∀ (l : List α) (a : Array β),
      (l.foldl (fun t i => t.push (f i)) a).toList = a.toList ++ l.map f
  | [], a => by simp
  | x :: l, a => by simp

theorem toList_getD {α : Type} (a : Array α) (t : Nat) (d : α) :
    a.toList.getD t d = a.getD t d := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem getElem?_of_lt {α : Type} (a : Array α) (t : Nat) (d : α) (h : t < a.size) :
    a.toList[t]? = some (a.getD t d) := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_map_of {α β : Type} (f : α → β) (a : Array α) (t : Nat) (x : α) (d : β)
    (h : a.toList[t]? = some x) : (a.map f).getD t d = f x := by
  have h' : a[t]? = some x := by simpa using h
  simp [Array.getD_eq_getD_getElem?, h']

theorem allFrom_spec (p : Nat → Bool) : ∀ (count i : Nat), allFrom p count i = true →
    ∀ j, i ≤ j → j < i + count → p j = true := by
  intro count
  induction count with
  | zero => intro i _ j h1 h2; omega
  | succ n ih =>
    intro i h j h1 h2
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases e : j = i
    · subst e; exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

theorem le_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  show n ≤ 2 ^ ceilLog2 n
  unfold ceilLog2
  split
  · rename_i h
    exact Nat.le_trans h Nat.one_le_two_pow
  · rename_i h
    have h2 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    omega

/-! ## The slots put in -/

/-- One step of K9.slotsIn, under a name. -/
def slotStep (F : Fork) (x : Nat × Array E × E) (l : E) : Ans (Nat × Array E × E) := do
  if isZeroE l then pure (x.1 + 1, x.2.1, x.2.2)
  else
    K9.need "K9.slot-with-coefficient-filled" (F.gotF.getD x.1 false)
    pure (x.1 + 1, x.2.1.set! x.1 (subE zeroE (mulE l (F.mf.getD x.1 zeroE))),
      addE x.2.2 (mulE l (F.vp.getD x.1 zeroE)))

/-- Where K9's step returns, the library's Fork.settleStep returns the same. -/
theorem slotStep_settle (F : Fork) (x z : Nat × Array E × E) (l : E)
    (h : slotStep F x l = .ok z) : Fork.settleStep F x l = some z := by
  obtain ⟨j, m, c⟩ := x
  unfold slotStep at h
  by_cases hz : isZeroE l = true
  · rw [if_pos hz] at h
    simp only [Fork.settleStep, if_pos hz]
    exact congrArg some (Except.ok.inj h)
  · rw [if_neg hz] at h
    obtain ⟨u, hu, h2⟩ := ok_bind h
    have hg : F.gotF.getD j false = true := need_ok hu
    simp only [Fork.settleStep, if_neg hz, if_pos hg]
    exact congrArg some (Except.ok.inj h2)

theorem slotFold (F : Fork) : ∀ (l : List E) (x z : Nat × Array E × E),
    l.foldlM (slotStep F) x = .ok z → l.foldlM (Fork.settleStep F) x = some z
  | [], x, z, h => by
    rw [List.foldlM_nil] at h ⊢
    exact congrArg some (Except.ok.inj h)
  | a :: l, x, z, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨y, hy, h2⟩ := ok_bind h
    rw [slotStep_settle F x y a hy]
    exact slotFold F l y z h2

/-- **The slots put in.** sum_j m[j] mask[j] + c = sum_j LS[j] (vp[j] - mf[j] mask[j]) + c0. -/
theorem slotsIn_total (F : Fork) (mask : Nat → K) (entry : Nat → Nat → Nat → K) (mc : Array E × E)
    (hLS : F.LS.size = F.ns) (h : slotsIn F = .ok mc) :
    maskValue ρ mask mc.1 + ρ.val mc.2 =
      slotsValue ρ (F.worldOf ρ mask entry) F.LS + ρ.val F.c0 := by
  have h' : (F.LS.foldlM (slotStep F) (0, Array.replicate F.ns zeroE, F.c0) >>=
      fun x => (pure x.2 : Ans (Array E × E))) = .ok mc := h
  obtain ⟨x, hx, h2⟩ := ok_bind h'
  have hm : x.2 = mc := Except.ok.inj h2
  rw [← Array.foldlM_toList] at hx
  have e := settleSteps ρ F mask F.LS.toList 0 _ _ x (slotFold F _ _ _ hx) (fun i _ h3 => by
    have : i < F.ns := by simpa [hLS] using h3
    simp [this])
  rw [hm] at e
  rw [e]
  simp only [maskValue, Array.toList_replicate, sumFrom_zeros, slotsValue, Fork.worldOf]
  ring

/-! ## Weights on an index -/

/-- One step of productWritten, under a name. -/
def pwStep (w : IndexWeights) (all : Array E) (t : Nat) : Array E :=
  all.map (fun x => mulE x (w.lo.getD t zeroE)) ++ all.map (fun x => mulE x (w.hi.getD t zeroE))

theorem pw_spec (w : IndexWeights) : ∀ n : Nat,
    ((List.range n).foldl (pwStep w) #[oneE]).size = 2 ^ n ∧
    ∀ i, i < 2 ^ n → ∃ x, ((List.range n).foldl (pwStep w) #[oneE])[i]? = some x ∧
      ρ.val x = ∏ t ∈ Finset.range n,
        if i.testBit t then ρ.val (w.hi.getD t zeroE) else ρ.val (w.lo.getD t zeroE)
  | 0 => by
    refine ⟨by simp, fun i hi => ⟨oneE, ?_, by simp [ρ.one]⟩⟩
    have h0 : i = 0 := by simpa using hi
    subst h0
    simp
  | n + 1 => by
    obtain ⟨hs, hv⟩ := pw_spec w n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (pwStep w) #[oneE] = A at hs hv ⊢
    refine ⟨?_, ?_⟩
    · simp only [pwStep, Array.size_append, Array.size_map, hs, pow_succ]
      omega
    · intro i hi
      by_cases hlt : i < 2 ^ n
      · obtain ⟨x, hx, hxv⟩ := hv i hlt
        have hb : i < A.size := by rw [hs]; exact hlt
        have hxe : A[i] = x := by
          rw [Array.getElem?_eq_getElem hb] at hx
          exact Option.some.inj hx
        refine ⟨mulE x (w.lo.getD n zeroE), ?_, ?_⟩
        · simp [pwStep, Array.getElem?_append, hs, hlt, hxe]
        · rw [ρ.mul, hxv, Finset.prod_range_succ, Nat.testBit_lt_two_pow hlt]
          simp
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ n + j := ⟨i - 2 ^ n, by omega⟩
        have hj : j < 2 ^ n := by rw [pow_succ] at hi; omega
        obtain ⟨x, hx, hxv⟩ := hv j hj
        refine ⟨mulE x (w.hi.getD n zeroE), ?_, ?_⟩
        · simp [pwStep, Array.getElem?_append, hs, hx]
        · rw [ρ.mul, hxv, Finset.prod_range_succ, Nat.testBit_two_pow_add_eq,
            Nat.testBit_lt_two_pow hj]
          simp only [Bool.not_false, if_true]
          congr 1
          apply Finset.prod_congr rfl
          intro t ht
          rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)]

/-- A product form's weight at index i is entry i of the form written out. -/
theorem weightAt_product (w : IndexWeights) (hv : w.values = none) (i : Nat)
    (hi : i < 2 ^ w.lo.size) : weightAt ρ w i = ρ.val ((productWritten w).getD i zeroE) := by
  obtain ⟨x, hx, hxv⟩ := (pw_spec ρ w w.lo.size).2 i hi
  have hx' : (productWritten w)[i]? = some x := hx
  unfold weightAt
  rw [hv, Array.getD_eq_getD_getElem?, hx']
  exact hxv.symm

/-- pickIndex bits i: the weight 1 at i, and 0 at every other index below 2^bits. -/
theorem weightAt_pick (bits i j : Nat) (hi : i < 2 ^ bits) (hj : j < 2 ^ bits) :
    weightAt ρ (pickIndex bits i) j = if j = i then 1 else 0 := by
  have hv : (pickIndex bits i).values = none := rfl
  have hlo : (pickIndex bits i).lo.size = bits := by simp [pickIndex]
  have glo : ∀ t, t < bits →
      (pickIndex bits i).lo.getD t zeroE = if i.testBit t then zeroE else oneE := by
    intro t ht
    simp [pickIndex, Array.getD_eq_getD_getElem?, ht]
  have ghi : ∀ t, t < bits →
      (pickIndex bits i).hi.getD t zeroE = if i.testBit t then oneE else zeroE := by
    intro t ht
    simp [pickIndex, Array.getD_eq_getD_getElem?, ht]
  unfold weightAt
  rw [hv]
  show (∏ t ∈ Finset.range (pickIndex bits i).lo.size, _) = _
  rw [hlo]
  by_cases e : j = i
  · subst e
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro t ht
    rw [glo t (Finset.mem_range.mp ht), ghi t (Finset.mem_range.mp ht)]
    cases hb : j.testBit t <;> simp [ρ.one]
  · rw [if_neg e]
    obtain ⟨t, ht⟩ : ∃ t, j.testBit t ≠ i.testBit t := by
      by_contra hcon
      exact e (Nat.eq_of_testBit_eq fun t => by
        by_contra hne
        exact hcon ⟨t, hne⟩)
    have htb : t < bits := by
      by_contra hge
      have hge' : bits ≤ t := Nat.le_of_not_lt hge
      have hp : 2 ^ bits ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hge'
      exact ht (by rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj hp),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi hp)])
    apply Finset.prod_eq_zero (Finset.mem_range.mpr htb)
    rw [glo t htb, ghi t htb]
    cases hb : j.testBit t <;> cases hc : i.testBit t <;> simp_all [ρ.zero]

/-- What K9.rowWeights returns has, at each row of the array, the written-out weight coef. -/
theorem rowWeights_at (X : HTree) (r : HRow) (w : IndexWeights) (h : K9.rowWeights X r = .ok w)
    (i : Nat) (hi : i < X.R) : weightAt ρ w i = ρ.val (r.coef.getD i zeroE) := by
  unfold K9.rowWeights at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, h2, h⟩ := ok_bind h
  have e : rowProduct X r = w := Except.ok.inj h
  have h2' := need_ok h2
  rw [everyBelow_eq] at h2'
  have h3 := allFrom_spec _ _ _ h2' i (Nat.zero_le i) (by omega)
  have h4 : (productWritten (rowProduct X r)).getD i zeroE = r.coef.getD i zeroE := eq_of_beq h3
  have hsz : (rowProduct X r).lo.size = clog2 X.R := by simp [rowProduct]
  rw [← e, ← h4]
  exact weightAt_product ρ (rowProduct X r) rfl i
    (by rw [hsz]; exact Nat.lt_of_lt_of_le hi (le_pow_clog2 X.R))

/-! ## The terms -/

/-- The sum of the values of terms. -/
def termsVal (dims : Nat → String → Nat × Nat) (D : Bound K) (ts : Array ReqTerm) : K :=
  (ts.toList.map (termValue ρ dims D)).sum

/-- A virtual row's weights L applied to the row's entries, an entry being the weights coef applied
to a column of the array. -/
def hrowVal (D : Bound K) (born : Nat) (array : String) (X : HTree) (r : HRow) : K :=
  sumFrom (fun c v => ρ.val v *
    ∑ i ∈ Finset.range X.R, ρ.val (r.coef.getD i zeroE) * D.cell born array i c) r.L0 r.L.toList

theorem hrowVal_eq (D : Bound K) (born : Nat) (array : String) (X : HTree) (r : HRow)
    (h0 : r.L0 = 0) (hK : r.L.size = X.K) :
    hrowVal ρ D born array X r = ∑ i ∈ Finset.range X.R, ∑ c ∈ Finset.range X.K,
      ρ.val (r.coef.getD i zeroE) * ρ.val (r.L.getD c zeroE) * D.cell born array i c := by
  unfold hrowVal
  rw [h0, sumFrom_range _ zeroE, Array.length_toList, hK, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Nat.zero_add, toList_getD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **The terms of one virtual row.** -/
theorem rowTerms_val (dims : Nat → String → Nat × Nat) (D : Bound K) (born : Nat) (array : String)
    (X : HTree) (acc acc' : Array ReqTerm) (r : HRow) (hd : dims born array = (X.R, X.K))
    (h : rowTerms born array X acc r = .ok acc') :
    termsVal ρ dims D acc' = termsVal ρ dims D acc + hrowVal ρ D born array X r := by
  unfold rowTerms at h
  obtain ⟨_, hsz, h⟩ := ok_bind h
  have hsz' := need_ok hsz
  simp only [Bool.and_eq_true, beq_iff_eq] at hsz'
  rw [hrowVal_eq ρ D born array X r hsz'.2 hsz'.1.2]
  by_cases hf : r.rowForm = true
  · simp only [if_pos hf] at h
    obtain ⟨w, hw, h⟩ := ok_bind h
    have e := Except.ok.inj h
    rw [← e]
    simp only [termsVal, Array.toList_push, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    simp only [termValue, hd]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro c _
    rw [rowWeights_at ρ X r w hw i (Finset.mem_range.mp hi)]
    simp [weightAt, ρ.one]
  · simp only [if_neg hf] at h
    have e := Except.ok.inj h
    rw [← e]
    unfold termsVal
    rw [foldl_push_list, List.map_append, List.sum_append, List.map_map, sum_map_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < 2 ^ clog2 X.R :=
      Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (le_pow_clog2 X.R)
    simp only [Function.comp, termValue, hd]
    rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro c _
      rw [weightAt_pick ρ _ i i hi2 hi2, if_pos rfl]
      simp [weightAt]
    · intro j hj hne
      apply Finset.sum_eq_zero
      intro c _
      rw [weightAt_pick ρ _ i j hi2
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) (le_pow_clog2 X.R)), if_neg hne]
      simp
    · intro hni
      exact absurd hi hni

theorem dims_of_laidAs (c : ChainCheck) (born : Nat) (name : String) (R C : Nat)
    (h : laidAs c born name R C = true) : dimsOf c born name = (R, C) := by
  unfold laidAs at h
  unfold dimsOf
  cases hfind : (c.rows.layout.link.getD born []).find? fun A => A.name == name with
  | none => rw [hfind] at h; simp at h
  | some A =>
    rw [hfind] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]

/-- **The terms on all listed arrays.** -/
theorem allTerms_val (D : Bound K) (L : LinkCtx) (F : Fork) (terms : Array ReqTerm)
    (h : allTerms L F = .ok terms) :
    termsVal ρ (dimsOf L.check) D terms = ∑ ti ∈ Finset.range L.list.nt.size,
      ((F.trees.getD ti {}).rows.toList.map
        (hrowVal ρ D (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
          (F.trees.getD ti {}))).sum := by
  unfold allTerms at h
  have e := foldlM_addsE _ (termsVal ρ (dimsOf L.check) D)
    (fun ti => ((F.trees.getD ti {}).rows.toList.map
        (hrowVal ρ D (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
          (F.trees.getD ti {}))).sum)
    (fun s ti s' hs => by
      beta_reduce
      rcases hba : L.arrayOf.getD ti (0, "") with ⟨born, array⟩
      rw [hba] at hs
      obtain ⟨_, hl, hs⟩ := ok_bind hs
      have hd := dims_of_laidAs _ _ _ _ _ (need_ok hl)
      rw [← Array.foldlM_toList] at hs
      exact foldlM_addsE _ _ _
        (fun a r a' hr => rowTerms_val ρ _ D born array _ a a' r hd hr) _ _ _ hs)
    _ _ _ h
  rw [e, sum_map_range]
  simp [termsVal]

/-! ## The ledger's value on the arrays -/

/-- The value of a listed array in the world of D. -/
theorem tree_val (D : Bound K) (L : LinkCtx) (F : Fork) (t : Nat) (X : HTree)
    (hX : F.trees.toList[t]? = some X) :
    HTree.value ρ (worldAt ρ L F D) t X =
      (X.rows.toList.map
        (hrowVal ρ D (L.arrayOf.getD t (0, "")).1 (L.arrayOf.getD t (0, "")).2 X)).sum := by
  unfold HTree.value
  rw [← sumFrom_plain]
  apply sumFrom_congr
  intro r R hR
  have f1 : (treesFrame F.trees).getD t default = X.frame := getD_map_of _ _ _ _ _ hX
  have f2 : X.frame.2.getD r default = R.frame := getD_map_of _ _ _ _ _ hR
  simp only [HRow.value, hrowVal, worldAt, Fork.worldOf, entryAt, Nat.zero_add, f1, f2]
  rfl

/-- **The ledger's value on the arrays is the sum over the listed arrays.** -/
theorem trees_val (D : Bound K) (L : LinkCtx) (F : Fork) (n : Nat) (hn : n ≤ F.trees.size)
    (hOut : ((F.trees.extract n F.trees.size).all fun X =>
      X.rows.all fun r => r.L.all isZeroE) = true) :
    treesValue ρ (worldAt ρ L F D) F.trees = ∑ ti ∈ Finset.range n,
      ((F.trees.getD ti {}).rows.toList.map
        (hrowVal ρ D (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
          (F.trees.getD ti {}))).sum := by
  unfold treesValue
  rw [sumFrom_range _ ({} : HTree), Array.length_toList]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hn)]
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' : t < F.trees.size := Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) hn
    rw [Nat.zero_add, toList_getD]
    exact tree_val ρ D L F t _ (getElem?_of_lt _ _ _ ht')
  · intro t ht hnt
    have ht' : t < F.trees.size := Finset.mem_range.mp ht
    have hge : n ≤ t := Nat.le_of_not_lt (fun hlt => hnt (Finset.mem_range.mpr hlt))
    rw [Nat.zero_add, toList_getD]
    simp only [Array.all_eq_true_iff_forall_mem] at hOut
    have hmem : F.trees.getD t {} ∈ F.trees.extract n F.trees.size := by
      rw [← Array.mem_toList_iff, Array.toList_extract, List.mem_iff_getElem?]
      refine ⟨t - n, ?_⟩
      simp only [List.extract_eq_take_drop, List.getElem?_take, List.getElem?_drop]
      rw [if_pos (by omega), show n + (t - n) = t by omega]
      exact getElem?_of_lt _ _ _ ht'
    unfold HTree.value
    apply sumFrom_eq_zero
    intro r R hR
    unfold HRow.value
    apply sumFrom_eq_zero
    intro i v hv
    rw [isZeroE_eq (hOut _ hmem R (Array.mem_toList_iff.mp hR) v (Array.mem_toList_iff.mp hv)),
      ρ.zero, zero_mul]

/-! ## The one equation -/

/-- **(T2), the law.** -/
theorem equation_total (D : Bound K) (L : LinkCtx) (F G : Fork) (q : Equation)
    (h : equation L F = .ok (q, G)) :
    eqValue ρ (dimsOf L.check) D q = F.total ρ (worldAt ρ L F D) := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, hOut, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, hThere, h⟩ := ok_bind h
  obtain ⟨terms, hT, h⟩ := ok_bind h
  obtain ⟨_, hSz, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨mc, hS, h⟩ := ok_bind h
  have e := Except.ok.inj h
  have eq1 : q = { terms := terms, onMasks := mc.1, constant := mc.2 } :=
    (congrArg Prod.fst e).symm
  have hSz' := need_ok hSz
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hSz'
  have hThere' : L.list.nt.size ≤ F.trees.size := by simpa using need_ok hThere
  have a := allTerms_val ρ D L _ terms hT
  have b := trees_val ρ D L F L.list.nt.size hThere' (need_ok hOut)
  have c := slotsIn_total ρ _ D.mask (entryAt ρ L.arrayOf (treesFrame F.trees) D) mc
    hSz'.1.1.2 hS
  rw [eq1]
  show termsVal ρ (dimsOf L.check) D terms + maskValue ρ D.mask mc.1 + ρ.val mc.2 = _
  rw [Fork.total, add_assoc, add_assoc, b, a]
  congr 1

/-- Where K9.equation returns, the ledger has one coefficient for each slot (K9.slots-sizes). -/
theorem equation_sized (L : LinkCtx) (F G : Fork) (q : Equation)
    (h : equation L F = .ok (q, G)) : F.LS.size = F.ns := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, hSz, h⟩ := ok_bind h
  have hSz' := need_ok hSz
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hSz'
  exact hSz'.1.1.2

/-- **(T2) holds of K9.equation.** -/
theorem t2 : T2 equation :=
  ⟨fun _ _ ρ D L F G q h => equation_total ρ D L F G q h, fun c =>
    ⟨{ check := c, list := { link := true }, handed := true },
      { planClaimsF := 1, nClaim := 1, kapMapF := #[true] },
      ({ terms := #[], onMasks := #[], constant := zeroE },
        { planClaimsF := 1, nClaim := 1, kapMapF := #[true], doorShutF := true }), rfl, by
      simp [equation, K9.need, allTerms, slotsIn, bind, Except.bind, pure, Except.pure]⟩⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_total
#print axioms VerifiableInference.Desc.K9L.equation_sized
#print axioms VerifiableInference.Desc.K9L.t2
