-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/LedgerLaws.lean: what the ledger of a sampled message gives lies in the mask table and
masks no answer: a proof for all codes and shapes.

`Send.admit` (OnBytes/Iop/Send.lean) gives a sampled message with mask rows a ledger
(`startLedger`, OnBytes/G4/WfStart.lean) and a pad: the entries that mask the answers, at the end of
the last mask row. `WfStartReady` asks two public tests of them, `padB` and `ledgerB`; the second
walks through all entries that the ledger can give. Here both are proved from the message's shape,
so that nothing has to be evaluated at a key's real size.

The argument. An index of the mask table has the row's number in its low bits. `realBelow n` counts
the indices below n whose low bits name a real row. The search for the next real row skips unreal
rows alone, so it keeps that count, and it ends at a real row. So take number j has the count j. The
first entry of the pad has the count rows · (ell − answers) + (rows − 1), which is the number of
entries that the ledger gives. The count grows with the index. So every entry that is given lies
below the first entry of the pad.

Main names:
  `realBelow`, `realBelow_mono`, `realBelow_next`, `next_real`, `realBelow_at`: the count.
  `takes_below`: every entry among the first n that a ledger gives has a count below that of the
  ledger's next index plus n.
  `padOf_mask`: every entry of the pad of a message with mask rows lies in the mask table, at or
  behind the last mask row's place ell − answers.
  `padB_of_shape`: `padB`, from: there are mask rows.
  `ledgerB_of_shape`: `ledgerB`, from: there are mask rows, and at least one answer.
Limits: messages with mask rows alone. Where a mask row is shorter than the number of answers, and
  so also where the mask code is not there, `ledgerB` holds emptily. Nothing on what the entries
  hold.


-/
import OnBytes.G4.WfStart

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-! ## Remainders -/

/-- The remainder of the next number. -/
theorem succ_mod (T n : Nat) (hT : 0 < T) :
    (n % T + 1 < T ∧ (n + 1) % T = n % T + 1) ∨ (n % T + 1 = T ∧ (n + 1) % T = 0) := by
  have hr := Nat.mod_lt n hT
  have hd := Nat.div_add_mod n T
  by_cases h : n % T + 1 < T
  · refine Or.inl ⟨h, ?_⟩
    have e : n + 1 = T * (n / T) + (n % T + 1) := by omega
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · have e1 : n % T + 1 = T := by omega
    refine Or.inr ⟨e1, ?_⟩
    have e : n + 1 = T * (n / T + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [e, Nat.mul_mod_right]

/-- The rounded-up logarithm is large enough. -/
theorem le_pow_ceilLog2 (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  by_cases h : n ≤ 1
  · rw [if_pos h, Nat.pow_zero]
    exact h
  · rw [if_neg h]
    have hlt : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

/-! ## The count of real rows' indices -/

/-- The number of indices below n whose low k bits are below R. -/
def realBelow (R k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => realBelow R k n + (if n % 2 ^ k < R then 1 else 0)

theorem realBelow_mono (R k : Nat) {a : Nat} :
    ∀ {b : Nat}, a ≤ b → realBelow R k a ≤ realBelow R k b
  | 0, h => by
    have : a = 0 := by omega
    rw [this]
    exact Nat.le_refl _
  | b + 1, h => by
    by_cases e : a = b + 1
    · rw [e]
      exact Nat.le_refl _
    · have ih := realBelow_mono R k (a := a) (b := b) (by omega)
      rw [realBelow]
      omega

/-- The search for the next real row keeps the count. -/
theorem realBelow_next (R k : Nat) : ∀ (fuel n : Nat),
    realBelow R k (nextRealRow R k fuel n) = realBelow R k n
  | 0, _ => rfl
  | fuel + 1, n => by
    rw [nextRealRow]
    split
    · rfl
    · rename_i h
      rw [realBelow_next R k fuel (n + 1), realBelow, if_neg h, Nat.add_zero]

/-- The search ends at a real row, if it starts at one or has fuel up to the next multiple of 2^k.
-/
theorem next_real (R k : Nat) (hR : 0 < R) : ∀ (fuel n : Nat),
    (n % 2 ^ k < R ∨ 2 ^ k - n % 2 ^ k ≤ fuel) → nextRealRow R k fuel n % 2 ^ k < R
  | 0, n, h => by
    have hT : 0 < 2 ^ k := Nat.two_pow_pos _
    have hr := Nat.mod_lt n hT
    rw [nextRealRow]
    rcases h with h | h
    · exact h
    · omega
  | fuel + 1, n, h => by
    have hT : 0 < 2 ^ k := Nat.two_pow_pos _
    rw [nextRealRow]
    split
    · assumption
    · rename_i hn
      refine next_real R k hR fuel (n + 1) ?_
      rcases succ_mod (2 ^ k) n hT with ⟨_, e⟩ | ⟨_, e⟩
      · right
        rw [e]
        rcases h with h | h
        · exact absurd h hn
        · omega
      · left
        rw [e]
        exact hR

/-- The count at place p, row r. -/
theorem realBelow_at (R k : Nat) (hR : R ≤ 2 ^ k) : ∀ (p r : Nat), r ≤ 2 ^ k →
    realBelow R k (2 ^ k * p + r) = p * R + min r R
  | 0, 0, _ => by simp [realBelow]
  | p + 1, 0, _ => by
    have ih := realBelow_at R k hR p (2 ^ k) (Nat.le_refl _)
    have e : 2 ^ k * (p + 1) + 0 = 2 ^ k * p + 2 ^ k := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_zero]
    rw [e, ih, Nat.min_eq_right hR, Nat.zero_min, Nat.add_mul, Nat.one_mul, Nat.add_zero]
  | p, r + 1, h => by
    have ih := realBelow_at R k hR p r (by omega)
    have e : 2 ^ k * p + (r + 1) = (2 ^ k * p + r) + 1 := by omega
    have hm : (2 ^ k * p + r) % 2 ^ k = r := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [e, realBelow, ih, hm]
    by_cases hr : r < R
    · rw [if_pos hr, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      omega
    · rw [if_neg hr, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      omega

/-! ## What a ledger gives -/

/-- Every entry among the first n that a ledger gives has a count below that of the ledger's next
index plus n. -/
theorem takes_below : ∀ (n : Nat) (l : Ledger), 0 < l.rows → ∀ i ∈ (takesOf l n).1,
    realBelow l.rows l.logRows i < realBelow l.rows l.logRows l.next + n
  | 0, _, _, i, hi => by cases hi
  | n + 1, l, hR, i, hi => by
    have hT : 0 < 2 ^ l.logRows := Nat.two_pow_pos _
    have hc := realBelow_next l.rows l.logRows (2 ^ l.logRows) l.next
    have hreal := next_real l.rows l.logRows hR (2 ^ l.logRows) l.next (Or.inr (Nat.sub_le _ _))
    rcases List.mem_cons.1 hi with rfl | hi'
    · show realBelow l.rows l.logRows (nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next) < _
      omega
    · have ih := takes_below n (stepLedger l).2 hR i hi'
      have e : realBelow l.rows l.logRows (stepLedger l).2.next =
          realBelow l.rows l.logRows l.next + 1 := by
        show realBelow l.rows l.logRows
          (nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1) = _
        rw [realBelow, if_pos hreal, hc]
      have ih' : realBelow l.rows l.logRows i <
          realBelow l.rows l.logRows (stepLedger l).2.next + n := ih
      omega

/-! ## The pad and the two public tests -/

/-- The pad of a message with mask rows: answer number j is masked by the entry of the last mask row
at place ell − answers + j. -/
theorem padOf_mask (codes : Codes) (s : OracleShape) (hm : s.maskRows ≠ 0) :
    ∀ p ∈ padOf codes s, p.1 = Part.mask ∧
      (s.maskRows - 1) +
        ((codes.mask.getD s.maskCode default).ell - s.answers) * 2 ^ ceilLog2 s.maskRows ≤ p.2 := by
  intro p hp
  have hpos : 0 < s.maskRows := Nat.pos_of_ne_zero hm
  unfold padOf Send.pad at hp
  simp only [Send.cube, hpos, decide_true, if_true, Bool.true_or, Nat.one_mul] at hp
  split at hp
  · simp at hp
  · simp only [Option.getD_some, List.mem_map, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨q, ⟨i, _, t, ht, rfl⟩, rfl⟩ := hp
    refine ⟨rfl, ?_⟩
    show _ ≤ (s.maskRows - 1) + _ * 2 ^ ceilLog2 s.maskRows
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    omega

/-- `padB` holds of every message with mask rows. -/
theorem padB_of_shape (codes : Codes) (s : OracleShape) (hm : s.maskRows ≠ 0) :
    padB codes s = true := by
  unfold padB
  rw [List.all_eq_true]
  intro p hp
  rw [(padOf_mask codes s hm p hp).1]
  rfl

theorem freeMask_zero (R ell a : Nat) (h : ell < a) : Send.freeMaskEntries R ell a = 0 := by
  unfold Send.freeMaskEntries
  rw [if_pos]
  simp [h]

theorem freeMask_eq (R ell a : Nat) (hR : R ≠ 0) (h : a ≤ ell) :
    Send.freeMaskEntries R ell a = R * (ell - a) + (R - 1) := by
  unfold Send.freeMaskEntries
  rw [if_neg]
  simp [hR]
  omega

/-- `ledgerB` holds of every message with mask rows and at least one answer. Where a mask row is
shorter than the number of answers it holds emptily: the ledger then gives no entry (and `Send.pad`
gives no pad, so that `Send.admit` fails). That is also so where the mask code is not there: the
length 0 of the default code is then taken. -/
theorem ledgerB_of_shape (codes : Codes) (s : OracleShape) (hm : s.maskRows ≠ 0)
    (ha : 1 ≤ s.answers) : ledgerB codes s = true := by
  have hpos : 0 < s.maskRows := Nat.pos_of_ne_zero hm
  have hR : s.maskRows ≤ 2 ^ ceilLog2 s.maskRows := le_pow_ceilLog2 _
  have hE : (codes.mask.getD s.maskCode default).ell ≤
      2 ^ (codes.mask.getD s.maskCode default).logEll := le_pow_ceilLog2 _
  have hrows : (startLedger codes s).rows = s.maskRows := Nat.max_eq_left hpos
  unfold ledgerB
  rw [List.all_eq_true]
  intro i hi
  have hb := takes_below _ (startLedger codes s) (by rw [hrows]; exact hpos) i hi
  rw [hrows] at hb
  have hb' : realBelow s.maskRows (ceilLog2 s.maskRows) i <
      Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers := by
    have : realBelow s.maskRows (ceilLog2 s.maskRows) 0 = 0 := rfl
    have hb2 : realBelow s.maskRows (ceilLog2 s.maskRows) i <
        realBelow s.maskRows (ceilLog2 s.maskRows) 0 +
          Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers := hb
    omega
  -- the ledger gives something: so the row is long enough for the pad
  have hlen : s.answers ≤ (codes.mask.getD s.maskCode default).ell := by
    by_cases hc : s.answers ≤ (codes.mask.getD s.maskCode default).ell
    · exact hc
    · exfalso
      have h0 := freeMask_zero s.maskRows (codes.mask.getD s.maskCode default).ell s.answers
        (Nat.lt_of_not_le hc)
      omega
  have hfree : Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers =
      s.maskRows * ((codes.mask.getD s.maskCode default).ell - s.answers) + (s.maskRows - 1) :=
    freeMask_eq _ _ _ hm hlen
  -- the count at the first entry of the pad
  have hat := realBelow_at s.maskRows (ceilLog2 s.maskRows) hR
    ((codes.mask.getD s.maskCode default).ell - s.answers) (s.maskRows - 1) (by omega)
  rw [Nat.min_eq_left (Nat.sub_le _ _)] at hat
  have hlt : i < 2 ^ ceilLog2 s.maskRows * ((codes.mask.getD s.maskCode default).ell - s.answers) +
      (s.maskRows - 1) := by
    by_cases hc : i < 2 ^ ceilLog2 s.maskRows *
        ((codes.mask.getD s.maskCode default).ell - s.answers) + (s.maskRows - 1)
    · exact hc
    · exfalso
      have hmono := realBelow_mono s.maskRows (ceilLog2 s.maskRows) (Nat.le_of_not_lt hc)
      rw [hat] at hmono
      rw [hfree, Nat.mul_comm s.maskRows] at hb'
      omega
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- the entry lies in the mask table
    have hbits : bitsOf codes s .mask =
        ceilLog2 s.maskRows + (codes.mask.getD s.maskCode default).logEll := by
      simp [bitsOf, OracleShape.rows, hm]
    unfold placeB
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true]
    refine ⟨hpos, ?_⟩
    rw [hbits, Nat.pow_add]
    have h1 : 2 ^ ceilLog2 s.maskRows * ((codes.mask.getD s.maskCode default).ell - s.answers) +
        2 ^ ceilLog2 s.maskRows ≤
        2 ^ ceilLog2 s.maskRows * 2 ^ (codes.mask.getD s.maskCode default).logEll := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  · -- the entry masks no answer
    rw [List.all_eq_true]
    intro p hp
    have h2 := (padOf_mask codes s hm p hp).2
    rw [Nat.mul_comm] at h2
    have hne : i ≠ p.2 := by omega
    simp [hne]

end OnBytes.G4

#print axioms OnBytes.G4.takes_below
#print axioms OnBytes.G4.padB_of_shape
#print axioms OnBytes.G4.ledgerB_of_shape
