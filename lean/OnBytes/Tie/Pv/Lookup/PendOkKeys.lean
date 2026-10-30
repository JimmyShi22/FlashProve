-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/PendOkKeys.lean: the tests of `Wf.pendingOf` on a claim's weights hold at the
claims that the lookup itself makes.

After each lookup of a key, the block WF (OnBytes/Iop/Wf.lean) tests the claims on the keys that
the lookup hands on: no weight has a written-out factor, and the weights add up to the sum of the
equality vector over the places that the part's runs cover. Which places are covered is said twice,
both times from the same public runs: `Wf.lookupOf` tells the lookup its padding, and
`Wf.coveredSum` adds over the runs. This file proves that the two descriptions agree: at the value
of `Lkp.keysOf` on `Wf.lookupOf`, for parameters that pass `Wf.lookupOk` and `Wf.fitsMatrix`, both
tests hold at every point of the right length.

How the proof goes.
 1. Both sides of the test are sums of the program, so their words are below the prime, and the
    test on words is an equation in the field (`Slice.beq_iff_readE`). No condition on the words of
    the point is needed.
 2. In the field the weights start as the equality vector, whose entries add up to 1, and lose one
    cube for each cube of each run of the part's padding (`pendOkKeys_weights`).
 3. `Lkp.cubesOf` cuts a run into aligned blocks. A block either makes the next start a multiple of
    a higher power of two, or it is the largest power of two that is left, and from then on the
    blocks shrink. So 125 steps are enough for a run of fewer than 2^62 numbers, and the loop may
    make 130 (`pendOkKeys_grow`, `pendOkKeys_shrink`, `pendOkKeys_run`). The numbers 62 and 130 are
    written out in `Lkp.cubesLoop` and `Lkp.cubesOf` and have no names there.
 4. The weights of the columns add up to 1, so a stretch of places weighs what the table of the
    equality vector at the place coordinates says (`pendOkKeys_blocks`, `pendOkKeys_stretch`).
 5. The padding of a part and its runs together cover each place once (`pendOkKeys_paddingFrom`).

Main definition: `Wf.PendOkKeys`. Main theorem: `Wf.Proved.pendOkKeys`.

What is not claimed. Nothing on `Wf.pendingOf` as a whole: its first test, on the length of the
point, is a premise here, and that `Lkp.verify` hands on the values of `Lkp.keysOf` is not shown
here. Of `Lkp.cubesOf` only runs of consecutive key numbers are treated (logStep = 0), as
`Wf.lookupOf` makes them. The premise that the matrix's size is in order is not used. No statement
on what the block or the protocol shows.
-/
import OnBytes.Iop.Wf
import OnBytes.Slice.ProgMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Wf
open OnBytes.Params (WfRun WfPart WfLookup WfPublic LinShape)

/-- At the claim that the lookup makes of the leaves of part i's tree (`Lkp.keysOf`), the second and
third tests of `Wf.pendingOf` hold: no weight has a written-out factor, and the weights add up to
the sum of the equality vector over the places that the part's runs cover. -/
def PendOkKeys : Prop :=
  ∀ (fBits messageId : Nat) (m : Matrix) (l : WfLookup) (i : Nat) (p : WfPart) (theta alpha : E)
    (c : PointClaim),
    lookupOk fBits l = true → m.ok = true → fitsMatrix m l = true → l.parts[i]? = some p →
    c.point.length = m.kCol + p.logPlaces →
    ((Lkp.keysOf (lookupOf messageId m l) theta alpha i c).weights.tensors.all
        (·.denseVars.isEmpty)) = true ∧
    (sumOfForm (Lkp.keysOf (lookupOf messageId m l) theta alpha i c).weights ==
      coveredSum p (eqPlaces m c.point)) = true

end OnBytes.Wf

namespace OnBytes.Wf.Proved
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice (GE eqW eqW_zero eqW_succ eqW_mod readE readL readV readE_add readE_mul
  readE_zero readE_one readE_sub readE_neg)
open OnBytes.Lkp (growBits cubesLoop cubesOf cubeTensor takeOut)

/-! ## Sums of the equality vector, in the field -/

/-- The sum of f over the len numbers from a on. -/
def pendOkKeys_seg (f : ℕ → GE) (a len : ℕ) : GE := ∑ j ∈ Finset.range len, f (a + j)

/-- The sum over no number is 0. -/
theorem pendOkKeys_seg_zero (f : ℕ → GE) (a : ℕ) : pendOkKeys_seg f a 0 = 0 :=
  Finset.sum_range_zero _

/-- A stretch of numbers, cut in two. -/
theorem pendOkKeys_seg_add (f : ℕ → GE) (a l1 l2 : ℕ) :
    pendOkKeys_seg f a (l1 + l2) = pendOkKeys_seg f a l1 + pendOkKeys_seg f (a + l1) l2 := by
  unfold pendOkKeys_seg
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]

/-- One more number at the end of a stretch. -/
theorem pendOkKeys_seg_succ (f : ℕ → GE) (a len : ℕ) :
    pendOkKeys_seg f a (len + 1) = pendOkKeys_seg f a len + f (a + len) :=
  Finset.sum_range_succ _ _

/-- The weights of all vertices add up to 1. -/
theorem pendOkKeys_sum_eqW (z : ℕ → GE) : ∀ k : ℕ, ∑ c ∈ Finset.range (2 ^ k), eqW k z c = 1
  | 0 => by
      rw [pow_zero, Finset.sum_range_one, eqW_zero]
  | k + 1 => by
      have h0 : ∀ c ∈ Finset.range (2 ^ k), eqW (k + 1) z c = eqW k z c * (1 - z k) := by
        intro c hc
        rw [eqW_succ, Nat.testBit_lt_two_pow (Finset.mem_range.1 hc), if_neg Bool.false_ne_true]
      have h1 : ∀ c ∈ Finset.range (2 ^ k), eqW (k + 1) z (2 ^ k + c) = eqW k z c * z k := by
        intro c hc
        have hc' := Finset.mem_range.1 hc
        have hlow : eqW k z (2 ^ k + c) = eqW k z c := by
          rw [← eqW_mod k z (2 ^ k + c), Nat.add_mod_left, eqW_mod]
        rw [eqW_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hc', Bool.not_false,
          if_pos rfl, hlow]
      rw [pow_succ, Nat.mul_two, Finset.sum_range_add, Finset.sum_congr rfl h0,
        Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.sum_mul, pendOkKeys_sum_eqW z k]
      ring

/-- The weight of a vertex is the weight of its k lowest digits times that of the others. -/
theorem pendOkKeys_eqW_split (k : ℕ) (z : ℕ → GE) (i : ℕ) : ∀ d : ℕ,
    eqW (k + d) z i = eqW k z i * eqW d (fun t => z (k + t)) (i / 2 ^ k)
  | 0 => by
      rw [Nat.add_zero, eqW_zero, mul_one]
  | d + 1 => by
      rw [← Nat.add_assoc, eqW_succ, pendOkKeys_eqW_split k z i d, eqW_succ,
        Nat.testBit_div_two_pow, Nat.add_comm d k, mul_assoc]

/-- The weights of an aligned block of 2^k vertices add up to the weight of the block's number. -/
theorem pendOkKeys_block (k d : ℕ) (z : ℕ → GE) (q : ℕ) :
    pendOkKeys_seg (eqW (k + d) z) (q * 2 ^ k) (2 ^ k) = eqW d (fun t => z (k + t)) q := by
  have h : ∀ c ∈ Finset.range (2 ^ k),
      eqW (k + d) z (q * 2 ^ k + c) = eqW k z c * eqW d (fun t => z (k + t)) q := by
    intro c hc
    have hc' := Finset.mem_range.1 hc
    have hd : (q * 2 ^ k + c) / 2 ^ k = q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hc',
        Nat.zero_add]
    have hm : (q * 2 ^ k + c) % 2 ^ k = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc']
    rw [pendOkKeys_eqW_split, hd, ← eqW_mod k z (q * 2 ^ k + c), hm]
  unfold pendOkKeys_seg
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, pendOkKeys_sum_eqW, one_mul]

/-- A stretch of whole blocks of 2^k vertices: the weights add up as the blocks' numbers' do. -/
theorem pendOkKeys_blocks (k d : ℕ) (z : ℕ → GE) (lo : ℕ) : ∀ len : ℕ,
    pendOkKeys_seg (eqW (k + d) z) (lo * 2 ^ k) (len * 2 ^ k) =
      pendOkKeys_seg (eqW d fun t => z (k + t)) lo len
  | 0 => by
      rw [Nat.zero_mul, pendOkKeys_seg_zero, pendOkKeys_seg_zero]
  | len + 1 => by
      rw [Nat.succ_mul, pendOkKeys_seg_add, pendOkKeys_blocks k d z lo len, ← Nat.add_mul,
        pendOkKeys_block, pendOkKeys_seg_succ]

/-- The sum of the equality vector at z over a cube, in the field. -/
def pendOkKeys_cubeVal (n : ℕ) (z : ℕ → GE) (c : Lkp.Cube) : GE :=
  ∏ t ∈ Finset.range n,
    if c.mask.testBit t then (if c.value.testBit t then z t else 1 - z t) else 1

/-- The product of the factors of the digits from b on. -/
theorem pendOkKeys_high (b : ℕ) (z : ℕ → GE) (q : ℕ) : ∀ d : ℕ,
    (∏ t ∈ Finset.range (b + d),
      if b ≤ t then (if (q * 2 ^ b).testBit t then z t else 1 - z t) else 1) =
      eqW d (fun t => z (b + t)) q
  | 0 => by
      rw [Nat.add_zero, eqW_zero]
      exact Finset.prod_eq_one fun t ht => if_neg (Nat.not_le.2 (Finset.mem_range.1 ht))
  | d + 1 => by
      have hq : (q * 2 ^ b).testBit (b + d) = q.testBit d := by
        rw [Nat.add_comm b d, ← Nat.testBit_div_two_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos b)]
      rw [← Nat.add_assoc, Finset.prod_range_succ, pendOkKeys_high b z q d, eqW_succ,
        if_pos (Nat.le_add_right b d), hq]

/-- The cube that the loop makes of an aligned block of 2^b key numbers. -/
theorem pendOkKeys_cube (n b q : ℕ) (hb : b ≤ n) (z : ℕ → GE) :
    pendOkKeys_cubeVal n z
      ⟨(2 ^ n - 1) ^^^ ((2 ^ n - 1) &&& ((2 ^ b - 1) * 2 ^ 0)), 0 + q * 2 ^ b * 2 ^ 0⟩ =
      pendOkKeys_seg (eqW n z) (q * 2 ^ b) (2 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [pendOkKeys_block, ← pendOkKeys_high]
  unfold pendOkKeys_cubeVal
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  by_cases h : t < b
  · simp [ht', h, Nat.not_le.2 h]
  · simp [ht', h, Nat.le_of_not_lt h]

/-! ## A run of key numbers, cut into cubes -/

/-- One step of the search for a block's size. -/
theorem pendOkKeys_growBits_succ (x left k b : ℕ) :
    growBits x left (k + 1) b =
      if x % 2 ^ (b + 1) == 0 && decide (2 ^ (b + 1) ≤ left) then growBits x left k (b + 1)
      else b := rfl

/-- The size that the search finds: the block is aligned and has at most left numbers, and the
search ended at its bound, or the next size is not aligned, or the next size is too large. -/
theorem pendOkKeys_growBits (x left : ℕ) : ∀ steps b : ℕ, 2 ^ b ∣ x → 2 ^ b ≤ left →
    2 ^ growBits x left steps b ∣ x ∧ 2 ^ growBits x left steps b ≤ left ∧
      (growBits x left steps b = b + steps ∨ ¬ 2 ^ (growBits x left steps b + 1) ∣ x ∨
        left < 2 ^ (growBits x left steps b + 1))
  | 0, _, hx, hl => ⟨hx, hl, Or.inl rfl⟩
  | k + 1, b, hx, hl => by
      have key : ((x % 2 ^ (b + 1) == 0 && decide (2 ^ (b + 1) ≤ left)) = true) ↔
          (2 ^ (b + 1) ∣ x ∧ 2 ^ (b + 1) ≤ left) := by
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
      rw [pendOkKeys_growBits_succ]
      by_cases h : 2 ^ (b + 1) ∣ x ∧ 2 ^ (b + 1) ≤ left
      · rw [if_pos (key.2 h)]
        obtain ⟨a1, a2, a3⟩ := pendOkKeys_growBits x left k (b + 1) h.1 h.2
        refine ⟨a1, a2, ?_⟩
        rcases a3 with a3 | a3
        · exact Or.inl (by omega)
        · exact Or.inr a3
      · rw [if_neg fun c => h (key.1 c)]
        refine ⟨hx, hl, Or.inr ?_⟩
        by_cases h1 : 2 ^ (b + 1) ∣ x
        · exact Or.inr (Nat.lt_of_not_le fun h2 => h ⟨h1, h2⟩)
        · exact Or.inl h1

/-- One step of the loop that cuts a run into cubes, for a run of consecutive numbers. -/
theorem pendOkKeys_cubesLoop_succ (n k x left : ℕ) (h : left ≠ 0) :
    cubesLoop n 0 0 (k + 1) x left =
      ⟨(2 ^ n - 1) ^^^ ((2 ^ n - 1) &&& ((2 ^ growBits x left 62 0 - 1) * 2 ^ 0)),
        0 + x * 2 ^ 0⟩ ::
        cubesLoop n 0 0 k (x + 2 ^ growBits x left 62 0) (left - 2 ^ growBits x left 62 0) := by
  have h' : ¬ (left == 0) = true := fun c => h (beq_iff_eq.1 c)
  show (if left == 0 then [] else _) = _
  rw [if_neg h']

/-- The loop makes no cube of an empty run. -/
theorem pendOkKeys_cubesLoop_none (n k x : ℕ) : cubesLoop n 0 0 k x 0 = [] := by
  cases k <;> rfl

/-- The cube of an aligned block of 2^b numbers that begins at x. -/
theorem pendOkKeys_head (n b x : ℕ) (hb : b ≤ n) (hx : 2 ^ b ∣ x) (z : ℕ → GE) :
    pendOkKeys_cubeVal n z
      ⟨(2 ^ n - 1) ^^^ ((2 ^ n - 1) &&& ((2 ^ b - 1) * 2 ^ 0)), 0 + x * 2 ^ 0⟩ =
      pendOkKeys_seg (eqW n z) x (2 ^ b) := by
  obtain ⟨q, rfl⟩ := hx
  rw [Nat.mul_comm (2 ^ b) q]
  exact pendOkKeys_cube n b q hb z

/-- The cubes that the loop makes in k steps cover the numbers from x on, left of them. -/
def pendOkKeys_Covers (n : ℕ) (z : ℕ → GE) (k x left : ℕ) : Prop :=
  ((cubesLoop n 0 0 k x left).map (pendOkKeys_cubeVal n z)).sum =
    pendOkKeys_seg (eqW n z) x left

/-- An empty run is covered. -/
theorem pendOkKeys_covers_none (n : ℕ) (z : ℕ → GE) (k x : ℕ) :
    pendOkKeys_Covers n z k x 0 := by
  unfold pendOkKeys_Covers
  rw [pendOkKeys_cubesLoop_none, pendOkKeys_seg_zero]
  rfl

/-- If the rest of a run is covered after the first cube, the run is covered. -/
theorem pendOkKeys_covers_step (n : ℕ) (z : ℕ → GE) (k x left b : ℕ) (h0 : left ≠ 0)
    (hb : growBits x left 62 0 = b) (hx : 2 ^ b ∣ x) (hl : 2 ^ b ≤ left) (hn : left ≤ 2 ^ n)
    (rest : pendOkKeys_Covers n z k (x + 2 ^ b) (left - 2 ^ b)) :
    pendOkKeys_Covers n z (k + 1) x left := by
  have hbn : b ≤ n := (Nat.pow_le_pow_iff_right (by decide)).1 (Nat.le_trans hl hn)
  unfold pendOkKeys_Covers at rest ⊢
  rw [pendOkKeys_cubesLoop_succ n k x left h0, hb, List.map_cons, List.sum_cons, rest,
    pendOkKeys_head n b x hbn hx z, ← pendOkKeys_seg_add, Nat.add_sub_cancel' hl]

/-- Where the blocks shrink: x is a multiple of 2^a, fewer than 2^a numbers are left, and the loop
may make a steps. Each block is then the largest power of two that is left. -/
theorem pendOkKeys_shrink (n : ℕ) (z : ℕ → GE) : ∀ k a x left : ℕ, a ≤ k → a ≤ 62 → 2 ^ a ∣ x →
    left < 2 ^ a → left ≤ 2 ^ n → pendOkKeys_Covers n z k x left
  | 0, a, x, left, hk, _, _, hl, _ => by
      have ha : a = 0 := Nat.le_zero.1 hk
      rw [ha, pow_zero] at hl
      have h0 : left = 0 := by omega
      rw [h0]
      exact pendOkKeys_covers_none n z 0 x
  | k + 1, a, x, left, hk, ha, hx, hl, hn => by
      by_cases h0 : left = 0
      · rw [h0]
        exact pendOkKeys_covers_none n z (k + 1) x
      · obtain ⟨b, hb⟩ : ∃ b, growBits x left 62 0 = b := ⟨_, rfl⟩
        have g := pendOkKeys_growBits x left 62 0 (by rw [pow_zero]; exact Nat.one_dvd x)
          (by rw [pow_zero]; exact Nat.pos_of_ne_zero h0)
        rw [hb] at g
        obtain ⟨g1, g2, g3⟩ := g
        have hba : b < a := (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt g2 hl)
        have hlt : left < 2 ^ (b + 1) := by
          rcases g3 with g3 | g3 | g3
          · omega
          · exact absurd (Nat.dvd_trans (Nat.pow_dvd_pow 2 hba) hx) g3
          · exact g3
        rw [pow_succ] at hlt
        exact pendOkKeys_covers_step n z k x left b h0 hb g1 g2 hn
          (pendOkKeys_shrink n z k b _ _ (by omega) (by omega)
            (Nat.dvd_add g1 (Nat.dvd_refl _)) (by omega) (Nat.le_trans (Nat.sub_le _ _) hn))

/-- Where the blocks grow: x is a multiple of 2^a, and fewer than 2^62 numbers are left. Each block
either makes x a multiple of a higher power of two, or is the first of the blocks that shrink. -/
theorem pendOkKeys_grow (n : ℕ) (z : ℕ → GE) : ∀ k a x left : ℕ, a ≤ 62 → (62 - a) + 63 ≤ k →
    2 ^ a ∣ x → left < 2 ^ 62 → left ≤ 2 ^ n → pendOkKeys_Covers n z k x left
  | 0, _, _, _, _, hk, _, _, _ => absurd hk (by omega)
  | k + 1, a, x, left, ha, hk, hx, hl, hn => by
      by_cases h0 : left = 0
      · rw [h0]
        exact pendOkKeys_covers_none n z (k + 1) x
      · obtain ⟨b, hb⟩ : ∃ b, growBits x left 62 0 = b := ⟨_, rfl⟩
        have g := pendOkKeys_growBits x left 62 0 (by rw [pow_zero]; exact Nat.one_dvd x)
          (by rw [pow_zero]; exact Nat.pos_of_ne_zero h0)
        rw [hb] at g
        obtain ⟨g1, g2, g3⟩ := g
        have hb62 : b < 62 := (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt g2 hl)
        refine pendOkKeys_covers_step n z k x left b h0 hb g1 g2 hn ?_
        rcases g3 with g3 | g3 | g3
        · omega
        · have hab : a ≤ b := by
            by_contra hc
            exact g3 (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hx)
          have hdiv : 2 ^ (b + 1) ∣ x + 2 ^ b := by
            obtain ⟨q, hq⟩ := g1
            rcases Nat.even_or_odd' q with ⟨r, hr | hr⟩
            · exact absurd ⟨r, by rw [hq, hr, pow_succ]; ring⟩ g3
            · exact ⟨r + 1, by rw [hq, hr, pow_succ]; ring⟩
          exact pendOkKeys_grow n z k (b + 1) _ _ (by omega) (by omega) hdiv
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hl) (Nat.le_trans (Nat.sub_le _ _) hn)
        · rw [pow_succ] at g3
          exact pendOkKeys_shrink n z k b _ _ (by omega) (by omega)
            (Nat.dvd_add g1 (Nat.dvd_refl _)) (by omega) (Nat.le_trans (Nat.sub_le _ _) hn)

/-- The cubes of a run of consecutive key numbers: their sums of the equality vector add up to the
sum over the run, if a key's number has fewer than 62 bits and the run has at most 2^n numbers. -/
theorem pendOkKeys_run (n : ℕ) (z : ℕ → GE) (p : Lkp.Padding) (h0 : p.logStep = 0)
    (hn : n < 62) (hl : p.length ≤ 2 ^ n) :
    ((cubesOf p n).map (pendOkKeys_cubeVal n z)).sum =
      pendOkKeys_seg (eqW n z) p.first p.length := by
  unfold cubesOf
  rw [h0, pow_zero, Nat.mod_one, Nat.div_one]
  exact pendOkKeys_grow n z 130 0 p.first p.length (by omega) (by omega)
    (by rw [pow_zero]; exact Nat.one_dvd _)
    (Nat.lt_of_le_of_lt hl ((Nat.pow_lt_pow_iff_right (by decide)).2 hn)) hl

/-! ## Sums of the program, read in the field -/

/-- A sum of the program has words below p. -/
theorem pendOkKeys_okE_add (a b : E) : okE (addE a b) = true := by
  rw [okE_triple, addE_triple]
  exact Slice.okE_addE _ _

/-- The program's zero has words below p. -/
theorem pendOkKeys_okE_zero : okE zeroE = true := rfl

/-- A running sum of the program has words below p, if it starts from such words. -/
theorem pendOkKeys_okE_foldl {α : Type} (g : α → E) : ∀ (l : List α) (s : E), okE s = true →
    okE (l.foldl (fun s x => addE s (g x)) s) = true
  | [], _, h => by
      rw [List.foldl_nil]
      exact h
  | x :: l, s, _ => by
      rw [List.foldl_cons]
      exact pendOkKeys_okE_foldl g l (addE s (g x)) (pendOkKeys_okE_add _ _)

/-- A running sum of the program is read as the sum. -/
theorem pendOkKeys_readE_foldl {α : Type} (g : α → E) : ∀ (l : List α) (s : E),
    readE (l.foldl (fun s x => addE s (g x)) s) = readE s + (l.map fun x => readE (g x)).sum
  | [], s => by
      rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | x :: l, s => by
      rw [List.foldl_cons, pendOkKeys_readE_foldl g l, readE_add, List.map_cons, List.sum_cons,
        add_assoc]

/-- The sum over two lists, one after the other. -/
theorem pendOkKeys_sum_append {α : Type} (g : α → GE) : ∀ l1 l2 : List α,
    ((l1 ++ l2).map g).sum = (l1.map g).sum + (l2.map g).sum
  | [], l2 => by
      rw [List.nil_append, List.map_nil, List.sum_nil, zero_add]
  | a :: l1, l2 => by
      rw [List.cons_append, List.map_cons, List.sum_cons, pendOkKeys_sum_append g l1 l2,
        List.map_cons, List.sum_cons, add_assoc]

/-- The sum of a list's entries, by their numbers. -/
theorem pendOkKeys_sumL : ∀ (L : List E) (m : ℕ), L.length ≤ m →
    (L.map readE).sum = ∑ j ∈ Finset.range m, readL L j
  | [], _, _ => (Finset.sum_eq_zero fun j _ => Slice.readL_nil j).symm
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a :: L, m + 1, h => by
      rw [List.map_cons, List.sum_cons, Finset.sum_range_succ',
        pendOkKeys_sumL L m (Nat.le_of_succ_le_succ h), add_comm (readE a)]
      rfl

/-- The program's sum of a slice of an array. -/
theorem pendOkKeys_sumSlice (v : Array E) (a c : ℕ) :
    readE (sumSlice v a c) = pendOkKeys_seg (readV v) a c := by
  unfold sumSlice
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  refine (pendOkKeys_readE_foldl (fun x : E => x) ((v.toList.drop a).take c) zeroE).trans ?_
  rw [readE_zero, zero_add, pendOkKeys_sumL _ c (List.length_take_le _ _)]
  unfold pendOkKeys_seg
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Slice.readL_take _ _ _ (Finset.mem_range.1 hj), Slice.readL_drop, Slice.readV_eq_readL]

/-- The program's sum over the places that a part's runs cover. -/
theorem pendOkKeys_coveredSum (p : WfPart) (e : Array E) :
    readE (coveredSum p e) =
      (p.runs.map fun r => pendOkKeys_seg (readV e) r.firstPlace r.places).sum := by
  unfold coveredSum
  refine (pendOkKeys_readE_foldl (fun r : WfRun => sumSlice e r.firstPlace r.places) p.runs
    zeroE).trans ?_
  rw [readE_zero, zero_add]
  exact congrArg List.sum (List.map_congr_left fun r _ => pendOkKeys_sumSlice e _ _)

/-- The sum over the covered places has words below p. -/
theorem pendOkKeys_okE_coveredSum (p : WfPart) (e : Array E) : okE (coveredSum p e) = true := by
  unfold coveredSum
  exact pendOkKeys_okE_foldl (fun r : WfRun => sumSlice e r.firstPlace r.places) p.runs zeroE
    pendOkKeys_okE_zero

/-! ## The sum of a form's entries -/

/-- The sum of all entries of a vector of product form, in the field. -/
def pendOkKeys_tensorVal (t : Tensor) : GE :=
  readE t.scalar * (t.pairs.map fun p => readE p.1 + readE p.2).prod

/-- The sum of all entries of a form, in the field. -/
def pendOkKeys_formVal (f : Form) : GE :=
  (f.tensors.map pendOkKeys_tensorVal).sum + (f.entries.map fun e => readE e.2).sum

/-- The running product of the sums of the pairs' halves. -/
theorem pendOkKeys_readE_pairs : ∀ (ps : List (E × E)) (s : E),
    readE (ps.foldl (fun r p => mulE r (addE p.1 p.2)) s) =
      readE s * (ps.map fun p => readE p.1 + readE p.2).prod
  | [], s => by
      rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | p :: ps, s => by
      rw [List.foldl_cons, pendOkKeys_readE_pairs ps, readE_mul, readE_add, List.map_cons,
        List.prod_cons, mul_assoc]

/-- The program's sum of all entries of a vector of product form. -/
def pendOkKeys_entrySum (t : Tensor) : E :=
  t.pairs.foldl (fun r p => mulE r (addE p.1 p.2)) t.scalar

/-- The program's sum of a form's entries, written out. -/
theorem pendOkKeys_sumOfForm_eq (f : Form) : sumOfForm f =
    f.entries.foldl (fun s e => addE s e.2)
      (f.tensors.foldl (fun s t => addE s (pendOkKeys_entrySum t)) zeroE) :=
  rfl

/-- The program's sum of a form's entries is read as that sum. -/
theorem pendOkKeys_sumOfForm (f : Form) : readE (sumOfForm f) = pendOkKeys_formVal f := by
  have h1 : ∀ s : E, readE (f.entries.foldl (fun s e => addE s e.2) s) =
      readE s + (f.entries.map fun e => readE e.2).sum :=
    pendOkKeys_readE_foldl (fun e : Nat × E => e.2) f.entries
  have h3 : (f.tensors.map fun t => readE (pendOkKeys_entrySum t)) =
      f.tensors.map pendOkKeys_tensorVal :=
    List.map_congr_left fun t _ => pendOkKeys_readE_pairs t.pairs t.scalar
  rw [pendOkKeys_sumOfForm_eq, h1, pendOkKeys_readE_foldl pendOkKeys_entrySum, h3, readE_zero,
    zero_add]
  rfl

/-- The program's sum of a form's entries has words below p. -/
theorem pendOkKeys_okE_sumOfForm (f : Form) : okE (sumOfForm f) = true := by
  rw [pendOkKeys_sumOfForm_eq]
  exact pendOkKeys_okE_foldl (fun e : Nat × E => e.2) f.entries _
    (pendOkKeys_okE_foldl pendOkKeys_entrySum f.tensors zeroE pendOkKeys_okE_zero)

/-- The entries of the equality vector add up to 1. -/
theorem pendOkKeys_eqVal (pt : List E) : pendOkKeys_tensorVal (Tensor.eq pt) = 1 := by
  have hs : (Tensor.eq pt).scalar = oneE := rfl
  have hp : (Tensor.eq pt).pairs = pt.map fun x => (subE oneE x, x) := rfl
  unfold pendOkKeys_tensorVal
  rw [hs, hp, readE_one, one_mul, List.map_map]
  clear hs hp
  induction pt with
  | nil => rfl
  | cons x pt ih =>
    rw [List.map_cons, List.prod_cons, ih, mul_one, Function.comp_apply, readE_sub, readE_one,
      sub_add_cancel]

/-- A product over a list's entries with their numbers, as a product over the numbers. -/
theorem pendOkKeys_zipProd (h : ℕ → E → GE) : ∀ (pt : List E) (s : ℕ),
    (((List.range' s pt.length).zip pt).map fun p => h p.1 p.2).prod =
      ∏ t ∈ Finset.range pt.length, h (s + t) (pt.getD t zeroE)
  | [], _ => rfl
  | x :: pt, s => by
      have e : (∏ t ∈ Finset.range (pt.length + 1), h (s + t) ((x :: pt).getD t zeroE)) =
          (∏ t ∈ Finset.range pt.length, h (s + 1 + t) (pt.getD t zeroE)) * h s x := by
        rw [Finset.prod_range_succ']
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun t _ => ?_) rfl
        rw [Nat.add_assoc, Nat.add_comm 1 t]
        rfl
      rw [List.length_cons, e, List.range'_succ, List.zip_cons_cons, List.map_cons,
        List.prod_cons, pendOkKeys_zipProd h pt (s + 1), mul_comm]

/-- The entries of minus the equality vector on a cube add up to minus the cube's sum. -/
theorem pendOkKeys_cubeTensor (c : Lkp.Cube) (pt : List E) :
    pendOkKeys_tensorVal (cubeTensor c pt (negE oneE)) =
      -pendOkKeys_cubeVal pt.length (readL pt) c := by
  have hs : (cubeTensor c pt (negE oneE)).scalar = negE oneE := rfl
  have hp : ((cubeTensor c pt (negE oneE)).pairs.map fun p => readE p.1 + readE p.2) =
      ((List.range' 0 pt.length).zip pt).map fun p =>
        if c.mask.testBit p.1 then (if c.value.testBit p.1 then readE p.2 else 1 - readE p.2)
        else 1 := by
    unfold cubeTensor
    simp only [List.map_map]
    rw [List.range_eq_range']
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    cases c.mask.testBit p.1 <;> cases c.value.testBit p.1 <;>
      simp [readE_zero, readE_sub, readE_one]
  have hz : (((List.range' 0 pt.length).zip pt).map fun p =>
        if c.mask.testBit p.1 then (if c.value.testBit p.1 then readE p.2 else 1 - readE p.2)
        else 1).prod =
      ∏ t ∈ Finset.range pt.length,
        if c.mask.testBit (0 + t) then
          (if c.value.testBit (0 + t) then readE (pt.getD t zeroE)
            else 1 - readE (pt.getD t zeroE))
        else 1 :=
    pendOkKeys_zipProd (fun (t : ℕ) (x : E) =>
      if c.mask.testBit t then (if c.value.testBit t then readE x else 1 - readE x) else 1) pt 0
  unfold pendOkKeys_tensorVal
  rw [hs, hp, hz, readE_neg, readE_one, neg_one_mul]
  unfold pendOkKeys_cubeVal
  refine congrArg Neg.neg (Finset.prod_congr rfl fun t _ => ?_)
  rw [Nat.zero_add]
  rfl

/-! ## The weights that the lookup hands on -/

/-- Taking cubes out of a claim on the keys: no weight gets a written-out factor, and the cubes'
sums go off the sum of the weights. -/
theorem pendOkKeys_takeOut (S : Lkp.Public) (theta : E) (pt : List E) (row : ℕ)
    (blk : Option ℕ) : ∀ (cs : List Lkp.Cube) (a : Lkp.KeyAcc) (v : GE),
    a.weights.tensors.all (·.denseVars.isEmpty) = true → pendOkKeys_formVal a.weights = v →
    ((cs.foldl (fun a c => takeOut S theta pt a c row blk) a).weights.tensors.all
        (·.denseVars.isEmpty)) = true ∧
      pendOkKeys_formVal (cs.foldl (fun a c => takeOut S theta pt a c row blk) a).weights =
        v - (cs.map (pendOkKeys_cubeVal pt.length (readL pt))).sum
  | [], _, _, h, hv => ⟨h, by rw [List.foldl_nil, hv, List.map_nil, List.sum_nil, sub_zero]⟩
  | c :: cs, a, v, h, hv => by
      have h1 : (takeOut S theta pt a c row blk).weights.tensors.all (·.denseVars.isEmpty) =
          true := by
        show List.all (cubeTensor c pt (negE oneE) :: a.weights.tensors) _ = true
        rw [List.all_cons, h]
        rfl
      have h2 : pendOkKeys_formVal (takeOut S theta pt a c row blk).weights =
          v - pendOkKeys_cubeVal pt.length (readL pt) c := by
        show pendOkKeys_formVal (a.weights.add (cubeTensor c pt (negE oneE))) = _
        rw [← hv]
        unfold pendOkKeys_formVal Form.add
        rw [List.map_cons, List.sum_cons, pendOkKeys_cubeTensor]
        ring
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ← sub_sub]
      exact pendOkKeys_takeOut S theta pt row blk cs _ _ h1 h2

/-- The same for the cubes of several runs of padding. -/
theorem pendOkKeys_takeOuts (S : Lkp.Public) (theta : E) (pt : List E)
    (blk : Lkp.Padding → Option ℕ) : ∀ (ps : List Lkp.Padding) (a : Lkp.KeyAcc) (v : GE),
    a.weights.tensors.all (·.denseVars.isEmpty) = true → pendOkKeys_formVal a.weights = v →
    ((ps.foldl (fun a p => (cubesOf p pt.length).foldl
        (fun a c => takeOut S theta pt a c p.row (blk p)) a) a).weights.tensors.all
        (·.denseVars.isEmpty)) = true ∧
      pendOkKeys_formVal (ps.foldl (fun a p => (cubesOf p pt.length).foldl
        (fun a c => takeOut S theta pt a c p.row (blk p)) a) a).weights =
        v - (ps.map fun p =>
          ((cubesOf p pt.length).map (pendOkKeys_cubeVal pt.length (readL pt))).sum).sum
  | [], _, _, h, hv => ⟨h, by rw [List.foldl_nil, hv, List.map_nil, List.sum_nil, sub_zero]⟩
  | p :: ps, a, v, h, hv => by
      obtain ⟨h1, h2⟩ := pendOkKeys_takeOut S theta pt p.row (blk p) (cubesOf p pt.length) a v h hv
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ← sub_sub]
      exact pendOkKeys_takeOuts S theta pt blk ps _ _ h1 h2

/-- The weights of the claim on a part's keys, if every block of trees belongs to a function: no
weight has a written-out factor, and they add up to 1 minus the sums of the cubes of the part's
padding. -/
theorem pendOkKeys_weights (S : Lkp.Public) (theta alpha : E) (part : ℕ) (c : PointClaim)
    (hk : S.keys.filter (·.function.isNone) = []) :
    ((Lkp.keysOf S theta alpha part c).weights.tensors.all (·.denseVars.isEmpty)) = true ∧
      pendOkKeys_formVal (Lkp.keysOf S theta alpha part c).weights =
        1 - ((S.padding.filter (·.part == part)).map fun p =>
          ((cubesOf p c.point.length).map
            (pendOkKeys_cubeVal c.point.length (readL c.point))).sum).sum := by
  have hv : pendOkKeys_formVal (Form.ofTensor (Tensor.eq c.point)) = 1 := by
    unfold pendOkKeys_formVal Form.ofTensor
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pendOkKeys_eqVal]
    simp
  unfold Lkp.keysOf
  simp only [hk, List.foldl_nil]
  exact pendOkKeys_takeOuts S theta c.point _ _ _ 1 rfl hv

/-! ## The padding of a part -/

/-- A stretch of padding belongs to the part that it names. -/
theorem pendOkKeys_stretch_part (kCol number row lo hi : ℕ) (x : Lkp.Padding)
    (hx : x ∈ stretch kCol number row lo hi) : x.part = number := by
  unfold stretch at hx
  split at hx
  · rw [List.mem_singleton] at hx
    rw [hx]
  · exact absurd hx List.not_mem_nil

/-- All padding of a part belongs to that part. -/
theorem pendOkKeys_paddingFrom_part (kCol number row L : ℕ) :
    ∀ (runs : List WfRun) (upto : ℕ) (acc : Array Lkp.Padding),
    (∀ x ∈ acc.toList, x.part = number) →
    ∀ x ∈ (paddingFrom kCol number row L upto runs acc).toList, x.part = number
  | [], upto, acc, h => by
      intro x hx
      rw [paddingFrom, Array.toList_appendList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact h x hx
      · exact pendOkKeys_stretch_part _ _ _ _ _ x hx
  | r :: rs, upto, acc, h => by
      rw [paddingFrom]
      refine pendOkKeys_paddingFrom_part kCol number row L rs _ _ fun x hx => ?_
      rw [Array.toList_appendList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact h x hx
      · exact pendOkKeys_stretch_part _ _ _ _ _ x hx

/-- Of lists of padding made part by part, the padding of part number s + i is the list that was
made for it. -/
theorem pendOkKeys_filter (f : WfPart × ℕ → List Lkp.Padding)
    (hf : ∀ q x, x ∈ f q → x.part = q.2) : ∀ (L : List WfPart) (s i : ℕ) (p : WfPart),
    L[i]? = some p → ((L.zipIdx s).flatMap f).filter (·.part == s + i) = f (p, s + i)
  | [], _, _, _, h => by simp at h
  | q :: L, s, 0, p, h => by
      have hq : q = p := by simpa using h
      have h1 : (f (p, s)).filter (·.part == s) = f (p, s) :=
        List.filter_eq_self.2 fun x hx => by rw [hf _ x hx]; exact beq_self_eq_true s
      have h2 : ((L.zipIdx (s + 1)).flatMap f).filter (·.part == s) = [] :=
        List.filter_eq_nil_iff.2 fun x hx => by
          obtain ⟨w, hw, hxw⟩ := List.mem_flatMap.1 hx
          have a1 := List.le_snd_of_mem_zipIdx hw
          have a2 := hf w x hxw
          rw [beq_iff_eq]
          omega
      rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, hq, Nat.add_zero, h1, h2,
        List.append_nil]
  | q :: L, s, i + 1, p, h => by
      have h' : L[i]? = some p := by simpa using h
      have h1 : (f (q, s)).filter (·.part == s + (i + 1)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx => by
          have a2 : x.part = s := hf _ x hx
          rw [beq_iff_eq]
          omega
      have e : s + (i + 1) = s + 1 + i := by omega
      rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, h1, List.nil_append, e]
      exact pendOkKeys_filter f hf L (s + 1) i p h'

/-- The padding of a part and its runs together cover the places from upto on, each once. P: the
weight of a place; g: the weight of a run of padding. -/
theorem pendOkKeys_paddingFrom (kCol number row L : ℕ) (P : ℕ → GE) (g : Lkp.Padding → GE)
    (hg : ∀ lo hi, hi ≤ 2 ^ L →
      ((stretch kCol number row lo hi).map g).sum = pendOkKeys_seg P lo (hi - lo)) :
    ∀ (runs : List WfRun) (upto : ℕ) (acc : Array Lkp.Padding), runsOk L upto runs = true →
    upto ≤ 2 ^ L →
    ((paddingFrom kCol number row L upto runs acc).toList.map g).sum +
        (runs.map fun r => pendOkKeys_seg P r.firstPlace r.places).sum =
      (acc.toList.map g).sum + pendOkKeys_seg P upto (2 ^ L - upto)
  | [], upto, acc, _, _ => by
      rw [paddingFrom, Array.toList_appendList, pendOkKeys_sum_append, hg upto _ (Nat.le_refl _),
        List.map_nil, List.sum_nil, add_zero]
  | r :: rs, upto, acc, hr, _ => by
      rw [runsOk] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩ := hr
      have ih := pendOkKeys_paddingFrom kCol number row L P g hg rs (r.firstPlace + r.places)
        (acc ++ stretch kCol number row upto r.firstPlace) h5 (by omega)
      rw [Array.toList_appendList, pendOkKeys_sum_append, hg upto r.firstPlace (by omega)] at ih
      have e1 : 2 ^ L - upto =
          (r.firstPlace - upto) + (r.places + (2 ^ L - (r.firstPlace + r.places))) := by omega
      have s : pendOkKeys_seg P upto (2 ^ L - upto) =
          pendOkKeys_seg P upto (r.firstPlace - upto) +
            (pendOkKeys_seg P r.firstPlace r.places +
              pendOkKeys_seg P (r.firstPlace + r.places)
                (2 ^ L - (r.firstPlace + r.places))) := by
        rw [e1, pendOkKeys_seg_add, pendOkKeys_seg_add, Nat.add_sub_cancel' h2]
      rw [paddingFrom, List.map_cons, List.sum_cons, s]
      linear_combination ih

/-- Inside the table of the equality vector, its entries are the vertices' weights. -/
theorem pendOkKeys_table (w : List E) (lo len : ℕ) (h : lo + len ≤ 2 ^ w.length) :
    pendOkKeys_seg (readV (eqTable w)) lo len = pendOkKeys_seg (eqW w.length (readL w)) lo len := by
  unfold pendOkKeys_seg
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [Slice.readV_eqTable, if_pos (by omega)]

/-- The cubes of a stretch of padding: their sums add up to the sum of the table of the equality
vector at the place coordinates, over the stretch's places. -/
theorem pendOkKeys_stretch (k L number row : ℕ) (pt : List E) (hlen : pt.length = k + L)
    (hn : k + L < 62) (lo hi : ℕ) (hhi : hi ≤ 2 ^ L) :
    ((stretch k number row lo hi).map fun q =>
      ((cubesOf q pt.length).map (pendOkKeys_cubeVal pt.length (readL pt))).sum).sum =
      pendOkKeys_seg (readV (eqTable (pt.drop k))) lo (hi - lo) := by
  unfold stretch
  by_cases h : lo < hi
  · have hdl : (pt.drop k).length = L := by rw [List.length_drop, hlen]; omega
    have hz : readL (pt.drop k) = fun t => readL pt (k + t) := funext (Slice.readL_drop k pt)
    have hle : (hi - lo) * 2 ^ k ≤ 2 ^ (k + L) := by
      rw [pow_add, Nat.mul_comm (2 ^ k)]
      exact Nat.mul_le_mul_right _ (Nat.le_trans (Nat.sub_le _ _) hhi)
    rw [if_pos h, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      pendOkKeys_table _ _ _ (by rw [hdl]; omega), hdl, hz, hlen,
      pendOkKeys_run (k + L) (readL pt) _ rfl hn hle]
    exact pendOkKeys_blocks k L (readL pt) lo (hi - lo)
  · rw [if_neg h, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt h), pendOkKeys_seg_zero]
    rfl

/-! ## What the tests on the parameters give -/

/-- A key's number in a part of a lookup that fits the matrix has fewer bits than there are
planes. -/
theorem pendOkKeys_partsFit (m : Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (keys : ℕ)
    (p : WfPart), partsFit m l keys ps = true → p ∈ ps → p.logPlaces + m.kCol < planesOf l
  | [], _, _, _, hp => absurd hp List.not_mem_nil
  | q :: ps, keys, p, h, hp => by
      rw [partsFit] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.1 hp with hq | hp'
      · rw [hq]
        exact h.1.1.1.1.2
      · exact pendOkKeys_partsFit m l ps _ p h.2 hp'

/-- A lookup that is in order has at most 62 planes, and the runs of each part are in order. -/
theorem pendOkKeys_lookupOk (fBits : ℕ) (l : WfLookup) (p : WfPart) (h : lookupOk fBits l = true)
    (hp : p ∈ l.parts) : planesOf l ≤ 62 ∧ runsOk p.logPlaces 0 p.runs = true := by
  unfold lookupOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h14⟩ := h
  have hq := (h14 p hp).1
  unfold partOk at hq
  simp only [Bool.and_eq_true] at hq
  exact ⟨h5, hq.1.2⟩

/-! ## The statement -/

/-- The second and third tests of `Wf.pendingOf` hold at the claims that the lookup makes. -/
theorem pendOkKeys : PendOkKeys := by
  intro fBits messageId m l i p theta alpha c hl _ hf hp hc
  have hmem : p ∈ l.parts := List.mem_of_getElem? hp
  obtain ⟨hplanes, hruns⟩ := pendOkKeys_lookupOk fBits l p hl hmem
  have hfit := pendOkKeys_partsFit m l l.parts 0 p hf hmem
  have hn : m.kCol + p.logPlaces < 62 := by omega
  obtain ⟨w1, w2⟩ := pendOkKeys_weights (lookupOf messageId m l) theta alpha i c rfl
  refine ⟨w1, ?_⟩
  have hfil : (lookupOf messageId m l).padding.filter (·.part == i) =
      (paddingFrom m.kCol i l.paddingKey.toNat p.logPlaces 0 p.runs #[]).toList := by
    have a := pendOkKeys_filter
      (fun q => (paddingFrom m.kCol q.2 l.paddingKey.toNat q.1.logPlaces 0 q.1.runs #[]).toList)
      (fun q x hx => pendOkKeys_paddingFrom_part _ _ _ _ _ _ _
        (fun y hy => absurd hy List.not_mem_nil) x hx) l.parts 0 i p hp
    rw [Nat.zero_add] at a
    exact a
  have hpad := pendOkKeys_paddingFrom m.kCol i l.paddingKey.toNat p.logPlaces
    (readV (eqPlaces m c.point))
    (fun q => ((cubesOf q c.point.length).map
      (pendOkKeys_cubeVal c.point.length (readL c.point))).sum)
    (pendOkKeys_stretch m.kCol p.logPlaces i l.paddingKey.toNat c.point hc hn)
    p.runs 0 #[] hruns (Nat.zero_le _)
  have hdl : (c.point.drop m.kCol).length = p.logPlaces := by rw [List.length_drop, hc]; omega
  have hone : pendOkKeys_seg (readV (eqPlaces m c.point)) 0 (2 ^ p.logPlaces - 0) = 1 := by
    unfold eqPlaces
    rw [Nat.sub_zero, pendOkKeys_table _ _ _ (by rw [hdl, Nat.zero_add]), hdl]
    unfold pendOkKeys_seg
    simp only [Nat.zero_add]
    exact pendOkKeys_sum_eqW _ _
  rw [Slice.beq_iff_readE _ _ (pendOkKeys_okE_sumOfForm _) (pendOkKeys_okE_coveredSum _ _),
    pendOkKeys_sumOfForm, w2, pendOkKeys_coveredSum, hfil]
  rw [hone] at hpad
  have hz : ((#[] : Array Lkp.Padding).toList.map fun q =>
      ((cubesOf q c.point.length).map
        (pendOkKeys_cubeVal c.point.length (readL c.point))).sum).sum = 0 := rfl
  rw [hz] at hpad
  linear_combination -hpad

end OnBytes.Wf.Proved
