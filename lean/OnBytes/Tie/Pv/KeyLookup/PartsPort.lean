-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/PartsPort.lean: the program's own test on the public inputs of a lookup
gives the conditions of Cb/Pv/KeyLookup/Letters.lean, and its public factor and count target, read
in the field, are that record's.

S is any value of the program's Lkp.Public (OnBytes/Iop/Lkp.lean), pubOf S the record made of it
(OnBytes/Tie/Pv/KeyLookup/PubOf.lean). readE reads the program's elements of three words in the
field Cb.Gl.E (OnBytes/Slice/ProgField.lean).

Main names.
  oneRow S          a test: every run of padding holds the first run's row, and every block of tree
                    numbers has a function, so that no tree holds padding alone. The record has one
                    row of padding for a lookup; the program's type allows a row for each run.
  pubOf_allKeys     (pubOf S).allKeys = S.allKeys.
  paddingList_eq, paddingCount_eq   under oneRow the program's list of padding is (length, padRow)
                    run by run, and its count of padding is (pubOf S).padCount.
  read_factor       without a condition: the program's public factor, read, is padFac
                    (Cb/Pv/Lookup/Alg/PadAlg.lean) at the program's rows, read, and the program's
                    list with each pair turned round.
  read_factor_one   under oneRow it is (alpha - the padding's row)^padCount, as Dat.fac has it.
  read_pin          under S.ok and oneRow the target of the counts' row, read, is the number allKeys
                    - padCount in the field, as Dat.Num has it.
  meets_of_common   if two runs have a place in common, the program's test Padding.meets says so.
  adm_of_ok         S.ok and 1 ≤ S.d give (pubOf S).Adm Cb.Gl.p, all clauses. 1 ≤ d is no clause of
                    Lkp.Public.ok; the caller's test Wf.lookupOk (OnBytes/Key/Ranges.lean) has it.
  oneRow_lookupOf, adm_lookupOf   at what the caller of a key file's lookups makes (Wf.lookupOf):
                    oneRow holds always; (Wf.lookupOf id m l).ok and Wf.lookupOk give Adm.

Conditions: the program's own public tests, and oneRow where said: public numbers and shapes alone.

Not claimed. That a lookup of a key file passes S.ok (the program tests it in every run). Anything
on shifts, tree numbers or written-out tables, which Adm does not read. What the rows of the table
are. At Wf.lookupOf, OnBytes/Slice/BlkTableRead.lean and OnBytes/Slice/BlkPadCount.lean have the
factor, the count target and the count of padding in their own terms; these are not stated again.

-/
import OnBytes.Slice.BlkPadCount
import Cb.Pv.KeyLookup.PartsAt
import OnBytes.Tie.Pv.KeyLookup.PubOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Cb.Lkp OnBytes OnBytes.Slice

/-- Every run of padding holds one and the same row; no tree holds padding alone. -/
def oneRow (S : Lkp.Public) : Bool :=
  (S.padding.all fun p => p.row == (pubOf S).padRow) && S.keys.all (·.function.isSome)

theorem oneRow_row {S : Lkp.Public} (h : oneRow S = true) :
    ∀ p ∈ S.padding, p.row = (pubOf S).padRow := fun p hp =>
  beq_iff_eq.1 (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1 p hp)

theorem oneRow_keys {S : Lkp.Public} (h : oneRow S = true) :
    S.keys.filter (·.function.isNone) = [] := by
  rw [List.filter_eq_nil_iff]
  intro b hb hn
  have h1 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 b hb
  cases hf : b.function <;> simp [hf] at h1 hn

/-! ### numbers -/

theorem pubOf_allKeys (S : Lkp.Public) : (pubOf S).allKeys = S.allKeys := rfl

theorem paddingList_eq {S : Lkp.Public} (h : oneRow S = true) :
    Lkp.paddingList S = (pubOf S).runs.map fun r => (r.length, (pubOf S).padRow) := by
  unfold Lkp.paddingList
  rw [oneRow_keys h, List.map_nil, List.append_nil]
  show _ = (S.padding.map runOf).map fun r => (r.length, (pubOf S).padRow)
  rw [List.map_map]
  exact List.map_congr_left fun p hp => by rw [oneRow_row h p hp]; rfl

theorem paddingCount_eq {S : Lkp.Public} (h : oneRow S = true) :
    Lkp.paddingCount S = (pubOf S).padCount := by
  unfold Lkp.paddingCount Pub.padCount
  rw [paddingList_eq h, List.map_map]
  rfl

/-! ### the public factor and the pin's target, read in the field -/

private theorem read_factorLoop (row : ℕ → E) (α : E) : ∀ (l : List (ℕ × ℕ)) (a : E),
    readE (l.foldl (fun a p => mulE a (powE (subE α (row p.2)) p.1)) a) =
      readE a * padFac (fun u => readE (row u)) (l.map Prod.swap) (readE α)
  | [], a => by simp [padFac]
  | p :: l, a => by
    rw [List.foldl_cons, read_factorLoop row α l, readE_mul, readE_pow, readE_sub, List.map_cons,
      padFac_cons, mul_assoc]
    rfl

/-- The program's public factor, read, is `padFac`. -/
theorem read_factor (S : Lkp.Public) (θ α : E) :
    readE (Lkp.factorOf S θ α) =
      padFac (fun u => readE (Lkp.rowAt S θ u)) ((Lkp.paddingList S).map Prod.swap) (readE α) := by
  unfold Lkp.factorOf
  rw [read_factorLoop (Lkp.rowAt S θ) α, readE_one, one_mul]

private theorem padFac_const {F : Type} [Field F] (t : ℕ → F) (r : ℕ) (al : F) : ∀ l : List ℕ,
    padFac t (l.map fun c => (r, c)) al = (al - t r) ^ l.sum
  | [] => by simp [padFac]
  | c :: l => by
    rw [List.map_cons, padFac_cons, padFac_const t r al l, List.sum_cons, pow_add]

/-- With one row of padding the factor is (alpha - that row)^(places of padding). -/
theorem read_factor_one {S : Lkp.Public} (h : oneRow S = true) (θ α : E) :
    readE (Lkp.factorOf S θ α) =
      (readE α - readE (Lkp.rowAt S θ (pubOf S).padRow)) ^ (pubOf S).padCount := by
  rw [read_factor, paddingList_eq h, List.map_map]
  have e : (pubOf S).runs.map (Prod.swap ∘ fun r => (r.length, (pubOf S).padRow)) =
      ((pubOf S).runs.map (·.length)).map fun c => ((pubOf S).padRow, c) := by
    rw [List.map_map]
    rfl
  rw [e, padFac_const]
  rfl

/-! ### the program's tests on the public inputs -/

private theorem allPairs_pairwise {α : Type} (p : α → α → Bool) :
    ∀ l : List α, Lkp.allPairs p l = true → l.Pairwise fun a b => p a b = true
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [Lkp.allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (allPairs_pairwise p l h.2)

/-- The heart of the program's test on two runs, the finer one first. -/
private theorem meets_core (f c : Lkp.Padding) (hle : f.logStep ≤ c.logStep)
    (k x y : ℕ) (hx : x < f.length) (hy : y < c.length) (hkf : k = f.first + x * 2 ^ f.logStep)
    (hkc : k = c.first + y * 2 ^ c.logStep) :
    f.first % 2 ^ f.logStep = c.first % 2 ^ f.logStep ∧
    (if f.first ≤ c.first then 0
      else (f.first - c.first + 2 ^ c.logStep - 1) / 2 ^ c.logStep) < c.length ∧
    c.first + (if f.first ≤ c.first then 0
      else (f.first - c.first + 2 ^ c.logStep - 1) / 2 ^ c.logStep) * 2 ^ c.logStep ≤
      f.first + (f.length - 1) * 2 ^ f.logStep := by
  have hpc : 0 < 2 ^ c.logStep := by positivity
  have h1 : k % 2 ^ f.logStep = f.first % 2 ^ f.logStep := by
    rw [hkf, Nat.add_mul_mod_self_right]
  have h2 : k % 2 ^ f.logStep = c.first % 2 ^ f.logStep := by
    have e : 2 ^ c.logStep = 2 ^ (c.logStep - f.logStep) * 2 ^ f.logStep := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hkc, e, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  have hs : (if f.first ≤ c.first then 0
      else (f.first - c.first + 2 ^ c.logStep - 1) / 2 ^ c.logStep) ≤ y := by
    split
    · exact Nat.zero_le _
    · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpc).2 ?_)
      have e : (y + 1) * 2 ^ c.logStep = y * 2 ^ c.logStep + 2 ^ c.logStep := by ring
      have h3 : 0 ≤ x * 2 ^ f.logStep := Nat.zero_le _
      rw [e]
      omega
  refine ⟨h1.symm.trans h2, lt_of_le_of_lt hs hy, ?_⟩
  have h4 := Nat.mul_le_mul_right (2 ^ c.logStep) hs
  have h5 : x * 2 ^ f.logStep ≤ (f.length - 1) * 2 ^ f.logStep :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Two runs with a place in common: the program's test says that they meet. -/
theorem meets_of_common (a b : Lkp.Padding) (i k : ℕ) (ha : (runOf a).holds i k = true)
    (hb : (runOf b).holds i k = true) : a.meets b = true := by
  obtain ⟨ha1, x, hx, hkx⟩ := ((runOf a).holds_iff i k).1 ha
  obtain ⟨hb1, y, hy, hky⟩ := ((runOf b).holds_iff i k).1 hb
  have hpa : a.part = i := ha1
  have hpb : b.part = i := hb1
  by_cases hle : a.logStep ≤ b.logStep
  · obtain ⟨h1, h2, h3⟩ := meets_core a b hle k x y hx hy hkx hky
    simp only [Lkp.Padding.meets, hle, ↓reduceIte]
    rw [if_neg (by simp [hpa, hpb, h1])]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := meets_core b a (by omega) k y x hy hx hky hkx
    simp only [Lkp.Padding.meets, hle, ↓reduceIte]
    rw [if_neg (by simp [hpa, hpb, h1])]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h2, h3⟩

theorem padIn_eq (S : Lkp.Public) (i : ℕ) :
    (pubOf S).padIn i = Lkp.paddedBy S fun p => p.part == i := by
  unfold Pub.padIn Lkp.paddedBy
  show (((S.padding.map runOf).filter fun r => r.part == i).map (·.length)).sum = _
  rw [List.filter_map, List.map_map]
  rfl

private theorem headD_eq_getD (l : List ℕ) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

/-- What the program's test on the sizes gives. -/
private theorem sizes_of {S : Lkp.Public} (h : S.sizesOK = true) :
    S.parts ≠ [] ∧ S.live < 2 ^ S.mu ∧ 2 ≤ S.planes ∧ (∀ x ∈ S.parts, 1 ≤ x ∧ x < S.planes) ∧
      S.allKeys < 2 ^ S.planes ∧ S.d + S.planes < 64 := by
  simp only [Lkp.Public.sizesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c2⟩, _⟩, _⟩, c5⟩, c6⟩, _⟩, c8⟩, c9⟩, _⟩, c11⟩, _⟩, _⟩ := h
  refine ⟨fun he => ?_, c5, c6, fun x hx => ?_, c9, c11⟩
  · rw [he] at c2
    simp at c2
  · have := List.all_eq_true.1 c8 x hx
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

/-- What the program's test on the runs of padding gives. -/
private theorem padding_of {S : Lkp.Public} (h : S.paddingOK = true) :
    (∀ p ∈ S.padding, p.part < S.parts.length ∧ 1 ≤ p.length ∧
      p.first + (p.length - 1) * 2 ^ p.logStep < 2 ^ S.parts.getD p.part 0 ∧ p.row < 2 ^ S.d) ∧
    S.padding.Pairwise fun a b => (!a.meets b) = true := by
  simp only [Lkp.Public.paddingOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, c2⟩, _⟩, c4⟩ := h
  refine ⟨fun p hp => ?_, allPairs_pairwise _ _ c4⟩
  have := List.all_eq_true.1 c2 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨d1, d2⟩, _⟩, _⟩, _⟩, d6⟩, d7⟩, _⟩, _⟩ := this
  exact ⟨d1, d2, d6, d7⟩

/-- The program's own test gives the record's conditions. -/
theorem adm_of_ok {S : Lkp.Public} (hok : S.ok = true) (hd : 1 ≤ S.d) :
    (pubOf S).Adm Cb.Gl.p := by
  simp only [Lkp.Public.ok, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨hs, _⟩, _⟩, hp⟩, hn⟩, ho⟩ := hok
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sizes_of hs
  obtain ⟨p1, p2⟩ := padding_of hp
  have hin : ∀ r ∈ (pubOf S).runs, r.part < (pubOf S).m ∧ 1 ≤ r.length ∧
      r.first + (r.length - 1) * 2 ^ r.logStep < 2 ^ (pubOf S).v r.part := by
    intro r hr
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hr
    exact ⟨(p1 p hp').1, (p1 p hp').2.1, (p1 p hp').2.2.1⟩
  have hnot : ∀ i < (pubOf S).m, (pubOf S).padIn i < 2 ^ (pubOf S).v i := by
    intro i hi
    simp only [Lkp.Public.onlyPadding, Bool.or_eq_false_iff] at hn
    have h2 := List.any_eq_false.1 hn.1.2 i (List.mem_range.2 hi)
    rw [padIn_eq]
    exact Nat.lt_of_not_le fun hc => h2 (decide_eq_true hc)
  have hroom : (pubOf S).pl ≤ 2 ^ (pubOf S).mu := by
    show S.planes ≤ 2 ^ S.mu
    unfold Lkp.Public.planes
    split
    · exact le_rfl
    · exact le_of_lt s2
  have hbits : ∀ i < (pubOf S).m, 1 ≤ (pubOf S).v i ∧ (pubOf S).v i < (pubOf S).pl := by
    intro i hi
    have hi' : i < S.parts.length := hi
    have e : (pubOf S).v i = S.parts[i] := List.getD_eq_getElem _ _ hi'
    rw [e]
    exact s4 _ (List.getElem_mem hi')
  have hchar : 2 ^ (pubOf S).d * (2 ^ (pubOf S).pl - 1) < Cb.Gl.p := by
    show 2 ^ S.d * (2 ^ S.planes - 1) < Cb.Gl.p
    have e1 : 2 ^ S.d * (2 ^ S.planes - 1) ≤ 2 ^ S.d * 2 ^ S.planes :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have e2 : 2 ^ S.d * 2 ^ S.planes ≤ 2 ^ 63 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact lt_of_le_of_lt (e1.trans e2) (by decide)
  have hrow : (pubOf S).padRow < 2 ^ (pubOf S).d := by
    show (S.padding.head?.map (·.row)).getD 0 < 2 ^ S.d
    cases hpad : S.padding with
    | nil => exact Nat.two_pow_pos _
    | cons q qs => exact (p1 q (by rw [hpad]; exact List.mem_cons_self)).2.2.2
  have hapart : (pubOf S).runs.Pairwise
      fun a b => ∀ i k, ¬ (a.holds i k = true ∧ b.holds i k = true) := by
    show (S.padding.map runOf).Pairwise _
    rw [List.pairwise_map]
    refine p2.imp ?_
    intro a b hab i k hc
    rw [meets_of_common a b i k hc.1 hc.2] at hab
    simp at hab
  have hpads : (pubOf S).padCount ≤ (pubOf S).allKeys :=
    (pubOf S).padCount_le_of (fun r hr => (hin r hr).1) hnot
  have horder : (∀ j ∈ (pubOf S).order, j + 1 < (pubOf S).least) ∧ (pubOf S).order.Nodup := by
    simp only [Lkp.Public.orderOK, Bool.and_eq_true] at ho
    refine ⟨fun j hj => ?_, ?_⟩
    · have h3 := of_decide_eq_true (List.all_eq_true.1 ho.1 j hj)
      have e : (pubOf S).least = S.parts.foldl min S.firstBits := by
        unfold Pub.least Lkp.Public.firstBits
        rw [headD_eq_getD]
        rfl
      rw [e]
      omega
    · exact (allPairs_pairwise _ _ ho.2).imp fun hab => bne_iff_ne.1 hab
  exact
    { some := List.length_pos_iff.2 s1
      planes := s3
      room := hroom
      bits := hbits
      keys := s5
      pads := hpads
      char := hchar
      tabs := hd
      row := hrow
      inPart := hin
      apart := hapart
      notAll := hnot
      order := horder }

/-- The pin's target, read, is the number of keys that are not padding. -/
theorem read_pin {S : Lkp.Public} (hok : S.ok = true) (h1 : oneRow S = true) :
    readE (Lkp.natE (S.allKeys - Lkp.paddingCount S)) =
      (((pubOf S).allKeys - (pubOf S).padCount : ℕ) : GE) := by
  simp only [Lkp.Public.ok, Bool.and_eq_true] at hok
  have hs := sizes_of hok.1.1.1.1.1
  have h2 : S.allKeys < 2 ^ S.planes := hs.2.2.2.2.1
  have h3 : S.planes < 64 := by
    have := hs.2.2.2.2.2
    omega
  have h4 : 2 ^ S.planes ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (le_of_lt h3)
  rw [Leaves.read_natE _ (by omega), paddingCount_eq h1]
  rfl

/-! ### at what the caller of a key file's lookups makes -/

theorem oneRow_lookupOf (id : ℕ) (m : Wf.Matrix) (l : Params.WfLookup) :
    oneRow (Wf.lookupOf id m l) = true := by
  unfold oneRow
  rw [Bool.and_eq_true_iff]
  refine ⟨List.all_eq_true.2 fun p hp => beq_iff_eq.2 ?_, rfl⟩
  have hr := Planes.padding_row id m l
  show p.row = (((Wf.lookupOf id m l).padding.head?).map (·.row)).getD 0
  cases hpad : (Wf.lookupOf id m l).padding with
  | nil => rw [hpad] at hp; cases hp
  | cons q qs =>
    show p.row = q.row
    rw [hr p hp, hr q (by rw [hpad]; exact List.mem_cons_self)]

theorem adm_lookupOf (id : ℕ) (m : Wf.Matrix) (l : Params.WfLookup)
    (hok : (Wf.lookupOf id m l).ok = true) (hl : Wf.lookupOk Wf.fBits l = true) :
    (pubOf (Wf.lookupOf id m l)).Adm Cb.Gl.p := by
  refine adm_of_ok hok ?_
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact hl.1.1.1.1.1.1.1.1.2

end Lk6

#print axioms Lk6.paddingCount_eq
#print axioms Lk6.read_factor
#print axioms Lk6.read_factor_one
#print axioms Lk6.meets_of_common
#print axioms Lk6.adm_of_ok
#print axioms Lk6.read_pin
#print axioms Lk6.oneRow_lookupOf
#print axioms Lk6.adm_lookupOf
