-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkCsStretch.lean: what coefficients on a stretch of the rest add to a row of the
program's code switch, in the field, at any places that increase along the stretch.

The program's code switch (OnBytes/Iop/Cs.lean) lays a vector of coefficients on a stretch of "the
rest": entry number i of the stretch stands in a table of the new oracle message at the index
`places.get (first + i)`. It cuts the stretch into pieces whose entries are equally spaced
(`switchPieces`) and adds one run of coefficients for each piece (`switchAddRestE`,
`switchAddRestF`). OnBytes/Slice/BlkCsRows.lean reads the result where the entries lie side by side:
then there is one piece. Here the places are any that increase along the stretch: rows filled row
index first, with the places of a pad stepped over. Definitions, statements and proofs.
Main names:
  `sum_hit`: of the terms first + step j = J of a run, at most one holds.
  `pieceAt c p J`: what the piece p gives on the index J, for coefficients c on the stretch.
    `runAt_piece`: a run on a piece gives that.
  `OpenOK`, `OptOK`, `openVal`, `Inv`: the state of the loop of `switchPieces` after n entries.
    `close_val`, `inv_step`, `inv_loop`: the loop keeps it.
  `stretchAt places first count c J`: the sum of c i over the i below count with
    `places.get (first + i) = J`.
  `switchPieces_sum`: every piece has a step other than 0, and together the pieces give `stretchAt`.
  `coefAt_rest`: the general law, for any coefficients on the pieces that read as c.
  `coefAt_restE_at`, `coefAt_restF_at`: the row's coefficient (`coefAt`) behind `switchAddRestE`,
    `switchAddRestF` is the one before, plus `stretchAt` on the table that takes the rest.
Limits: that the places of a switch increase is a premise. Nothing on which index a place is.
Nothing on the run of the block. Nothing on soundness.

-/
import OnBytes.Slice.BlkCsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice
open Finset

/-! ## One run -/

/-- At most one term of a run's sum hits the index J. -/
theorem sum_hit (first step len J : ℕ) (hs : 0 < step) (f : ℕ → GE) :
    (∑ j ∈ range len, if first + step * j = J then f j else 0) =
      if first ≤ J ∧ (J - first) % step = 0 ∧ (J - first) / step < len then
        f ((J - first) / step) else 0 := by
  by_cases h : first ≤ J ∧ (J - first) % step = 0 ∧ (J - first) / step < len
  · rw [if_pos h]
    obtain ⟨h1, h2, h3⟩ := h
    rw [Finset.sum_eq_single ((J - first) / step)]
    · have : first + step * ((J - first) / step) = J := by
        have := Nat.div_add_mod (J - first) step
        omega
      rw [if_pos this]
    · intro j _ hj
      rw [if_neg]
      intro e
      apply hj
      subst e
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hs]
    · intro hn
      exact absurd (Finset.mem_range.2 h3) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg]
    intro e
    apply h
    subst e
    rw [Nat.add_sub_cancel_left, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hs]
    exact ⟨Nat.le_add_right _ _, rfl, Finset.mem_range.1 hj⟩

/-- What a piece gives on the index J, for coefficients c on the stretch. -/
def pieceAt (c : ℕ → GE) (p : SwitchPiece) (J : ℕ) : GE :=
  ∑ j ∈ range (p.stop - p.start), if p.first + p.step * j = J then c (p.start + j) else 0

/-- A run on a piece. K: the run's coefficients. -/
theorem runAt_piece (c : ℕ → GE) (p : SwitchPiece) (K : Coeffs) (hs : 0 < p.step)
    (hK : K.size ≤ p.stop - p.start)
    (h1 : ∀ j, j < K.size → readE (K.get j) = c (p.start + j))
    (h0 : ∀ j, K.size ≤ j → j < p.stop - p.start → c (p.start + j) = 0)
    (g : ℕ) (part : Part) (o : ℕ) (part' : Part) (J : ℕ) :
    runAt ⟨g, part, p.first, p.step, K⟩ o part' J =
      if g == o && part == part' then pieceAt c p J else 0 := by
  unfold pieceAt
  rw [sum_hit p.first p.step _ J hs fun j => c (p.start + j)]
  unfold runAt runHits
  by_cases hg : (g == o && part == part') = true
  · simp only [hg, Bool.true_and, if_true]
    by_cases a1 : p.first ≤ J
    · by_cases a2 : (J - p.first) % p.step = 0
      · by_cases a3 : (J - p.first) / p.step < K.size
        · simp [a1, a2, a3, hs, h1 _ a3, lt_of_lt_of_le a3 hK]
        · by_cases a4 : (J - p.first) / p.step < p.stop - p.start
          · simp [a1, a2, a3, hs, a4, h0 _ (Nat.le_of_not_lt a3) a4]
          · simp [a1, a2, a3, hs, a4]
      · simp [a1, a2, hs]
    · simp [a1]
  · simp [hg]

/-! ## The loop of `switchPieces` -/

section Loop
variable (P : ℕ → ℕ) (c : ℕ → GE)

/-- What is asked of the open piece after n entries. -/
structure OpenOK (n : ℕ) (o : OpenPiece) : Prop where
  lt : o.start < n
  first : o.first = P o.start
  last : o.last = P (n - 1)
  law : ∀ i, o.start ≤ i → i < n → P i = o.first + o.step.getD 1 * (i - o.start)
  pos : 0 < o.step.getD 1
  one : o.step = none → n = o.start + 1

/-- The same of "no piece is open". -/
def OptOK (n : ℕ) : Option OpenPiece → Prop
  | none => n = 0
  | some o => OpenOK P n o

/-- What the open piece's entries give on the index J. -/
def openVal (J n : ℕ) : Option OpenPiece → GE
  | none => 0
  | some o => ∑ i ∈ Ico o.start n, if P i = J then c i else 0

/-- The open piece, closed, gives what its entries give. -/
theorem close_val {n : ℕ} {o : OpenPiece} (h : OpenOK P n o) (J : ℕ) :
    pieceAt c (o.close n) J = openVal P c J n (some o) := by
  show (∑ j ∈ range (n - o.start),
    if o.first + o.step.getD 1 * j = J then c (o.start + j) else 0) =
      ∑ i ∈ Ico o.start n, if P i = J then c i else 0
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [h.law (o.start + j) (Nat.le_add_right _ _) (by omega), Nat.add_sub_cancel_left]

/-- The state of the loop after n entries. -/
structure Inv (n : ℕ) (s : List SwitchPiece × Option OpenPiece) : Prop where
  pos : ∀ p ∈ s.1, 0 < p.step
  ok : OptOK P n s.2
  val : ∀ J, (s.1.map fun p => pieceAt c p J).sum + openVal P c J n s.2 =
    ∑ i ∈ range n, if P i = J then c i else 0

end Loop

/-- One step of the loop keeps the state. -/
theorem inv_step (places : SwitchPlaces) (first : ℕ) (c : ℕ → GE) (n : ℕ)
    (hm : ∀ i j, i < j → j ≤ n → places.get (first + i) < places.get (first + j))
    (s : List SwitchPiece × Option OpenPiece)
    (h : Inv (fun i => places.get (first + i)) c n s) :
    Inv (fun i => places.get (first + i)) c (n + 1) (pieceStep places first s n) := by
  obtain ⟨L, oo⟩ := s
  have hfresh : OpenOK (fun i => places.get (first + i)) (n + 1)
      ⟨n, places.get (first + n), none, places.get (first + n)⟩ :=
    ⟨Nat.lt_succ_self n, rfl, rfl, fun i h1 h2 => by
      have : i = n := by
        have h1' : n ≤ i := h1
        omega
      subst this
      simp, Nat.one_pos, fun _ => rfl⟩
  have hone : ∀ J, openVal (fun i => places.get (first + i)) c J (n + 1)
      (some ⟨n, places.get (first + n), none, places.get (first + n)⟩) =
      if places.get (first + n) = J then c n else 0 := fun J => by
    show (∑ i ∈ Ico n (n + 1), if places.get (first + i) = J then c i else 0) = _
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
  have hgrow : ∀ (o o' : OpenPiece) (J : ℕ), o'.start = o.start → o.start < n + 1 →
      openVal (fun i => places.get (first + i)) c J (n + 1) (some o') =
      openVal (fun i => places.get (first + i)) c J n (some o) +
        if places.get (first + n) = J then c n else 0 := fun o o' J e hl => by
    show (∑ i ∈ Ico o'.start (n + 1), if places.get (first + i) = J then c i else 0) =
      (∑ i ∈ Ico o.start n, if places.get (first + i) = J then c i else 0) + _
    rw [e, Finset.sum_Ico_succ_top (by omega)]
  rcases oo with _ | ⟨st, fi, sp, la⟩
  · -- no piece is open
    have h0 : n = 0 := h.ok
    refine ⟨h.pos, hfresh, fun J => ?_⟩
    show (L.map fun p => pieceAt c p J).sum + openVal _ c J (n + 1) (some _) = _
    rw [hone, Finset.sum_range_succ, ← h.val J]
    simp only [openVal, add_zero]
  · have ho : OpenOK (fun i => places.get (first + i)) n ⟨st, fi, sp, la⟩ := h.ok
    rcases sp with _ | d
    · -- one entry so far
      have hn : n = st + 1 := ho.one rfl
      have hfi : fi = places.get (first + st) := ho.first
      have hlt : fi < places.get (first + n) := by
        rw [hfi]
        exact hm st n (by omega) le_rfl
      refine ⟨h.pos, ⟨by show st < n + 1; omega, hfi, rfl, fun i h1 h2 => ?_, ?_, ?_⟩,
        fun J => ?_⟩
      · have h1' : st ≤ i := h1
        show places.get (first + i) = fi + (places.get (first + n) - fi) * (i - st)
        rcases Nat.lt_or_ge i n with hi | hi
        · have : i = st := by omega
          subst this
          simp [hfi]
        · have : i = n := by omega
          subst this
          have : i - st = 1 := by omega
          rw [this]
          omega
      · show 0 < places.get (first + n) - fi
        omega
      · intro e
        exact absurd e (by simp)
      · show (L.map fun p => pieceAt c p J).sum + openVal _ c J (n + 1) (some _) = _
        rw [hgrow ⟨st, fi, none, la⟩
          ⟨st, fi, some (places.get (first + n) - fi), places.get (first + n)⟩ J rfl
          (by show st < n + 1; omega), ← add_assoc, h.val J, Finset.sum_range_succ]
    · have hd : 0 < d := ho.pos
      have hla : la = places.get (first + (n - 1)) := ho.last
      have hst : st < n := ho.lt
      by_cases hp : places.get (first + n) = la + d
      · -- the piece goes on
        have e : pieceStep places first (L, some ⟨st, fi, some d, la⟩) n =
            (L, some ⟨st, fi, some d, places.get (first + n)⟩) := by
          unfold pieceStep
          simp [hp]
        rw [e]
        refine ⟨h.pos, ⟨by show st < n + 1; omega, ho.first, rfl, fun i h1 h2 => ?_, hd, ?_⟩,
          fun J => ?_⟩
        · have h1' : st ≤ i := h1
          show places.get (first + i) = fi + d * (i - st)
          rcases Nat.lt_or_ge i n with hi | hi
          · exact ho.law i h1 hi
          · have : i = n := by omega
            subst this
            have l1 : places.get (first + (i - 1)) = fi + d * (i - 1 - st) :=
              ho.law (i - 1) (by show st ≤ i - 1; omega) (by omega)
            rw [hp, hla, l1]
            have : i - st = (i - 1 - st) + 1 := by omega
            rw [this, Nat.mul_succ]
            omega
        · intro e
          exact absurd e (by simp)
        · show (L.map fun p => pieceAt c p J).sum + openVal _ c J (n + 1) (some _) = _
          rw [hgrow ⟨st, fi, some d, la⟩ ⟨st, fi, some d, places.get (first + n)⟩ J rfl
            (by show st < n + 1; omega), ← add_assoc, h.val J, Finset.sum_range_succ]
      · -- the piece is closed, a new one begins
        have e : pieceStep places first (L, some ⟨st, fi, some d, la⟩) n =
            ((⟨st, fi, some d, la⟩ : OpenPiece).close n :: L,
              some ⟨n, places.get (first + n), none, places.get (first + n)⟩) := by
          unfold pieceStep
          simp [hp]
        rw [e]
        refine ⟨fun p hp' => ?_, hfresh, fun J => ?_⟩
        · rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hd
          · exact h.pos p hp'
        · show ((((⟨st, fi, some d, la⟩ : OpenPiece).close n :: L).map
            fun p => pieceAt c p J).sum + openVal _ c J (n + 1) (some _)) = _
          rw [hone, List.map_cons, List.sum_cons, close_val _ c ho J, Finset.sum_range_succ,
            ← h.val J]
          show _ = (L.map fun p => pieceAt c p J).sum + openVal _ c J n (some _) + _
          ring

/-- The loop keeps the state. -/
theorem inv_loop (places : SwitchPlaces) (first : ℕ) (c : ℕ → GE) : ∀ n : ℕ,
    (∀ i j, i < j → j < n → places.get (first + i) < places.get (first + j)) →
    Inv (fun i => places.get (first + i)) c n
      ((List.range n).foldl (pieceStep places first) ([], none))
  | 0, _ => ⟨fun _ hp => absurd hp List.not_mem_nil, rfl, fun _ => by simp [openVal]⟩
  | n + 1, hm => by
    rw [List.range_succ, List.foldl_append]
    exact inv_step places first c n (fun i j h1 h2 => hm i j h1 (by omega)) _
      (inv_loop places first c n fun i j h1 h2 => hm i j h1 (by omega))

/-- What coefficients c on the entries of a stretch give on the index J of the table. -/
def stretchAt (places : SwitchPlaces) (first count : ℕ) (c : ℕ → GE) (J : ℕ) : GE :=
  ∑ i ∈ range count, if places.get (first + i) = J then c i else 0

/-- The pieces of a stretch whose places increase: each has a step other than 0, and together they
give what the stretch gives. -/
theorem switchPieces_sum (places : SwitchPlaces) (first count : ℕ) (c : ℕ → GE)
    (hm : ∀ i j, i < j → j < count → places.get (first + i) < places.get (first + j)) :
    (∀ p ∈ switchPieces places first count, 0 < p.step) ∧
      ∀ J, ((switchPieces places first count).map fun p => pieceAt c p J).sum =
        stretchAt places first count c J := by
  have h := inv_loop places first c count hm
  rw [switchPieces_eq]
  generalize (List.range count).foldl (pieceStep places first) ([], none) = s at h
  obtain ⟨L, oo⟩ := s
  rcases oo with _ | o
  · have h0 : count = 0 := h.ok
    subst h0
    exact ⟨fun _ hp => absurd hp List.not_mem_nil, fun J => by simp [stretchAt]⟩
  · have ho : OpenOK (fun i => places.get (first + i)) count o := h.ok
    refine ⟨fun p hp => ?_, fun J => ?_⟩
    · rcases List.mem_cons.1 (List.mem_reverse.1 hp) with rfl | hp
      · exact ho.pos
      · exact h.pos p hp
    · show (((o.close count :: L).reverse).map fun p => pieceAt c p J).sum = _
      rw [List.map_reverse, List.sum_reverse, List.map_cons, List.sum_cons, close_val _ c ho J,
        add_comm]
      exact h.val J

/-! ## Coefficients on a stretch of the rest -/

/-- Runs added one after the other. -/
theorem coefAt_foldl_addRun (g : ℕ) (part : Part) (K : SwitchPiece → Coeffs) (o : ℕ)
    (part' : Part) (J : ℕ) : ∀ (l : List SwitchPiece) (row : Row),
    coefAt (l.foldl (fun r p => r.addRun g part p.first p.step (K p)) row) o part' J =
      coefAt row o part' J +
        (l.map fun p => runAt ⟨g, part, p.first, p.step, K p⟩ o part' J).sum
  | [], _ => by simp
  | p :: l, row => by
    rw [List.foldl_cons, coefAt_foldl_addRun g part K o part' J l, coefAt_addRun, List.map_cons,
      List.sum_cons, add_assoc]

/-- The general law: coefficients K on the pieces of a stretch that read as c. -/
theorem coefAt_rest (row : Row) (g : ℕ) (part : Part) (places : SwitchPlaces) (first count : ℕ)
    (hm : ∀ i j, i < j → j < count → places.get (first + i) < places.get (first + j))
    (K : SwitchPiece → Coeffs) (c : ℕ → GE) (hK : ∀ p, (K p).size ≤ p.stop - p.start)
    (h1 : ∀ p j, j < (K p).size → readE ((K p).get j) = c (p.start + j))
    (h0 : ∀ p j, (K p).size ≤ j → j < p.stop - p.start → c (p.start + j) = 0)
    (o : ℕ) (part' : Part) (J : ℕ) :
    coefAt ((switchPieces places first count).foldl
        (fun r p => r.addRun g part p.first p.step (K p)) row) o part' J =
      coefAt row o part' J +
        if g == o && part == part' then stretchAt places first count c J else 0 := by
  obtain ⟨hp, hs⟩ := switchPieces_sum places first count c hm
  rw [coefAt_foldl_addRun]
  congr 1
  rw [← hs J]
  have e : ∀ p ∈ switchPieces places first count,
      runAt ⟨g, part, p.first, p.step, K p⟩ o part' J =
        if g == o && part == part' then pieceAt c p J else 0 := fun p hpp =>
    runAt_piece c p (K p) (hp p hpp) (hK p) (h1 p) (h0 p) g part o part' J
  rw [List.map_congr_left e]
  by_cases hg : (g == o && part == part') = true
  · simp [hg]
  · simp [hg]

/-- Coefficients over the extension field on a stretch of the rest whose places increase. -/
theorem coefAt_restE_at (row : Row) (g : ℕ) (part : Part) (places : SwitchPlaces)
    (first count : ℕ)
    (hm : ∀ i j, i < j → j < count → places.get (first + i) < places.get (first + j))
    (coeff : Array E) (o : ℕ) (part' : Part) (J : ℕ) :
    coefAt (switchAddRestE row g part (switchPieces places first count) coeff) o part' J =
      coefAt row o part' J +
        if g == o && part == part' then stretchAt places first count (readV coeff) J else 0 :=
  coefAt_rest row g part places first count hm
    (fun p => .own (coeff.extract p.start p.stop)) (readV coeff)
    (fun p => by
      show (coeff.extract p.start p.stop).size ≤ _
      rw [Array.size_extract]
      omega)
    (fun p j hj => by
      have hj' : j < (coeff.extract p.start p.stop).size := hj
      rw [Array.size_extract] at hj'
      show readE ((coeff.extract p.start p.stop).getD j zeroE) = readV coeff (p.start + j)
      rw [readV_eq_readL]
      unfold readL
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_extract_of_lt (by omega),
        List.getD_eq_getElem?_getD, Array.getElem?_toList,
        Array.getElem?_eq_getElem (show p.start + j < coeff.size by omega)])
    (fun p j hj hl => by
      have hj' : (coeff.extract p.start p.stop).size ≤ j := hj
      rw [Array.size_extract] at hj'
      exact readV_of_le coeff _ (by omega))
    o part' J

/-- The same for coefficients over the base field. -/
theorem coefAt_restF_at (row : Row) (g : ℕ) (part : Part) (places : SwitchPlaces)
    (first count : ℕ)
    (hm : ∀ i j, i < j → j < count → places.get (first + i) < places.get (first + j))
    (coeff : Array F) (o : ℕ) (part' : Part) (J : ℕ) :
    coefAt (switchAddRestF row g part (switchPieces places first count) coeff) o part' J =
      coefAt row o part' J +
        if g == o && part == part' then
          stretchAt places first count (fun i => algebraMap GF GE (toF (coeff.getD i 0))) J
        else 0 :=
  coefAt_rest row g part places first count hm
    (fun p => .stretch coeff p.start (p.stop - p.start))
    (fun i => algebraMap GF GE (toF (coeff.getD i 0)))
    (fun _ => le_rfl)
    (fun p j hj => by
      have hj' : j < p.stop - p.start := hj
      show readE (if j < p.stop - p.start then OnBytes.ofF (coeff.getD (p.start + j) 0)
        else zeroE) = _
      rw [if_pos hj', readE_ofF])
    (fun p j hj hl => absurd hl (Nat.not_lt.2 hj))
    o part' J

end OnBytes.Slice

#print axioms OnBytes.Slice.switchPieces_sum
#print axioms OnBytes.Slice.coefAt_rest
#print axioms OnBytes.Slice.coefAt_restE_at
#print axioms OnBytes.Slice.coefAt_restF_at
#print axioms OnBytes.Slice.inv_step
#print axioms OnBytes.Slice.sum_hit
#print axioms OnBytes.Slice.runAt_piece
