-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/PlacesLaws.lean: laws of the functions of Fmt/Places.lean.

1. What the file contains. Theorems, and two definitions that say which arguments are meant
   (`RealAt`, `HidOK`).
    `le_two_pow_logUp`, `logUp_le`, `logUp_two_pow`, `two_pow_logUp_pos`: logUp n is the least b
      with n ≤ 2 ^ b.
    `pair_lt`, `pair_inj`: a + Q b with a below Q.
    `entryAt_entryNo`, `entryNo_of_entryAt`: an entry's number and the entry with a number, both
      ways.
    `entryNo_inj`, `entryNo_lt`: one to one on real rows; below 2 ^ (the table's bits).
    `RealAt`: entry c of row r is an entry of the main or of the mask table.
    `tableBits_of_ne`, `cubeNo_main`, `cubeNo_mask_both`, `cubeNo_mask_alone`: unfoldings.
    `cubeNo_lt`, `cubeNo_inj`: an entry's index is below 2 ^ cubeBits, and no two entries have one.
    `padRow_lt_mask`, `padRow_lt_main`: the pad's row is a real row.
    `padEntry_lt`, `padEntry_inj`: where the pad fits its row, its entries lie in the row; they
      differ.
    `pad_first`: in mask rows the pad's first entry is entry e - s of row m - 1.
    `freeAt_row_lt`, `freeAt_entry_lt`: a free entry is an entry.
    `freeAt_mul_add`: the free entry number m c + r, r below m, is entry c of row r.
    `entryNo_freeAt_lt`: the free entries' numbers rise with k.
    `freeAt_below_pad`: the k-th free entry has a number below that of the pad's first entry exactly
      if k is below `freeCount`.
    `freeAt_ne_pad`: no free entry is an entry of the pad.
    `freeAt_inj`: no entry is taken twice.
    `sk_succ`, `sk_le`, `sk_length`, `sk_cons`: the running sum.
    `HidOK`: (l, deg) is a coefficient of the hiding polynomial; `HidOK.cons`, `hidPos_cons`.
    `hidPos_bounds`, `hidPos_lt`, `hidPos_inj`, `hidPos_onto`: a coefficient's entry lies in its
      variable's stretch and below `hidCount`; no two have one; every entry below holds one.
    `hidPos_lt_endNo`: it is below every end value's number.
    `isKey_keyNo`, `keyNo_inj`, `keyNo_of_isKey`, `keyNo_lt`: the key numbers of one call.
    `keyBits_le`: keyBits is the least number from 10 on that holds tau rows of 2 ^ lc.
    `keyIndex_lt`, `keyIndex_inj`: over both calls a key's index is below 2 ^ (nZ + 1), and no two
      key numbers of either call have one.
2. What is checked when the file compiles. The proofs.
3. Theorems. As listed. No Mathlib is below this file. Laws of the same content for `ceilLog2` and
   `Fmt.M2.clog` lie in OnBytes/Slice/ProgCodes.lean and OnBytes/Slice/Corners.lean, with Mathlib
   below them.
4. What is not claimed. Nothing on the programs; nothing on a protocol. No law of `blockAt`,
   `sentNo`, `padInMask`, `padEach`; of `vecAt` only OnBytes/Iop/LedgerPlaces.lean has one. Nothing
   says that a row's number of entries is 2 ^ (its logarithm): `RealAt` takes logarithms,
   `padEntry`, `freeCount`, `vecAt` take lengths.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Places

namespace Fmt.Places

theorem le_two_pow_logUp (n : Nat) : n ≤ 2 ^ logUp n := by
  unfold logUp
  by_cases h : n ≤ 1
  · simp [h]
  · simp only [h, if_false]
    have h1 := @Nat.lt_log2_self (n - 1)
    omega

theorem logUp_le {n b : Nat} (h : n ≤ 2 ^ b) : logUp n ≤ b := by
  unfold logUp
  by_cases h1 : n ≤ 1
  · simp [h1]
  · simp only [h1, if_false]
    have h2 : n - 1 ≠ 0 := by omega
    have h3 : n - 1 < 2 ^ b := by omega
    have := (Nat.log2_lt h2).2 h3
    omega

theorem two_pow_logUp_pos (m : Nat) : 0 < 2 ^ logUp m := Nat.two_pow_pos _

theorem logUp_two_pow (b : Nat) : logUp (2 ^ b) = b := by
  apply Nat.le_antisymm (logUp_le (Nat.le_refl _))
  have h := le_two_pow_logUp (2 ^ b)
  exact (Nat.pow_le_pow_iff_right (by omega)).1 h

theorem pair_lt {Q T a b : Nat} (ha : a < Q) (hb : b < T) : a + Q * b < Q * T := by
  have h1 : Q * (b + 1) ≤ Q * T := Nat.mul_le_mul_left Q hb
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

theorem pair_inj {Q a b a' b' : Nat} (ha : a < Q) (ha' : a' < Q) (e : a + Q * b = a' + Q * b') :
    a = a' ∧ b = b' := by
  have h1 : (a + Q * b) % Q = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h2 : (a' + Q * b') % Q = a' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
  have ea : a = a' := by rw [← h1, e, h2]
  subst ea
  have h3 : Q * b = Q * b' := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) h3⟩

/-- The entry with the number of entry c of row r, r a real row, is that entry. -/
theorem entryAt_entryNo {m r c : Nat} (h : r < m) : entryAt m (entryNo m r c) = some (r, c) := by
  have hQ := le_two_pow_logUp m
  have hr : r < 2 ^ logUp m := Nat.lt_of_lt_of_le h hQ
  have h0 : 0 < 2 ^ logUp m := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  have e1 : (r + 2 ^ logUp m * c) % 2 ^ logUp m = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have e2 : (r + 2 ^ logUp m * c) / 2 ^ logUp m = c := by
    rw [Nat.add_mul_div_left _ _ h0, Nat.div_eq_of_lt hr, Nat.zero_add]
  simp only [entryAt, entryNo, e1, e2, h, if_true]

/-- Two entries of real rows with one number are one entry. -/
theorem entryNo_inj {m r c r' c' : Nat} (h : r < m) (h' : r' < m)
    (e : entryNo m r c = entryNo m r' c') : r = r' ∧ c = c' := by
  have a := entryAt_entryNo (c := c) h
  have b := entryAt_entryNo (c := c') h'
  rw [e, b] at a
  have := Option.some.inj a
  exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩

/-- The entry with the number n, if there is one, stands in a real row and has the number n. -/
theorem entryNo_of_entryAt {m n r c : Nat} (h : entryAt m n = some (r, c)) :
    r < m ∧ entryNo m r c = n := by
  unfold entryAt at h
  by_cases h1 : n % 2 ^ logUp m < m
  · rw [if_pos h1] at h
    have h2 := Option.some.inj h
    have hr : n % 2 ^ logUp m = r := congrArg Prod.fst h2
    have hc : n / 2 ^ logUp m = c := congrArg Prod.snd h2
    refine ⟨hr ▸ h1, ?_⟩
    unfold entryNo
    rw [← hr, ← hc, Nat.add_comm]
    exact Nat.div_add_mod n (2 ^ logUp m)
  · rw [if_neg h1] at h
    exact absurd h (by simp)

/-- An entry's number is below 2 ^ (the table's bits). -/
theorem entryNo_lt {m r c L : Nat} (hr : r < m) (hc : c < 2 ^ L) :
    entryNo m r c < 2 ^ (logUp m + L) := by
  have hQ := le_two_pow_logUp m
  unfold entryNo
  rw [Nat.pow_add]
  have h1 : 2 ^ logUp m * (c + 1) ≤ 2 ^ logUp m * 2 ^ L := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at h1
  generalize 2 ^ logUp m * 2 ^ L = T at h1 ⊢
  generalize 2 ^ logUp m * c = U at h1 ⊢
  omega

/-! ## The cube -/

/-- Entry c of row r is an entry of the main table (mask = false) or of the mask table. -/
def RealAt (M a Z z : Nat) (mask : Bool) (r c : Nat) : Prop :=
  if mask then r < Z ∧ c < 2 ^ z else r < M ∧ c < 2 ^ a

theorem tableBits_of_ne {rows : Nat} (L : Nat) (h : rows ≠ 0) :
    tableBits rows L = logUp rows + L := by
  unfold tableBits
  rw [if_neg h]

theorem cubeNo_main (M a Z z r c : Nat) : cubeNo M a Z z false r c = entryNo M r c := by
  simp [cubeNo]

theorem cubeNo_mask_both {M Z : Nat} (a z r c : Nat) (hM : M ≠ 0) (hZ : Z ≠ 0) :
    cubeNo M a Z z true r c = entryNo Z r c + 2 ^ max (tableBits M a) (tableBits Z z) := by
  simp [cubeNo, cubeBits, hM, hZ]

theorem cubeNo_mask_alone (a Z z r c : Nat) : cubeNo 0 a Z z true r c = entryNo Z r c := by
  simp [cubeNo]

/-- An entry's index is below 2 ^ cubeBits. -/
theorem cubeNo_lt {M a Z z : Nat} {mask : Bool} {r c : Nat} (h : RealAt M a Z z mask r c) :
    cubeNo M a Z z mask r c < 2 ^ cubeBits M a Z z := by
  cases mask with
  | false =>
    have h' : r < M ∧ c < 2 ^ a := h
    have hM : M ≠ 0 := by omega
    rw [cubeNo_main]
    have h1 := entryNo_lt h'.1 h'.2
    rw [← tableBits_of_ne a hM] at h1
    refine Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) ?_)
    unfold cubeBits
    split
    · have := Nat.le_max_left (tableBits M a) (tableBits Z z)
      omega
    · omega
  | true =>
    have h' : r < Z ∧ c < 2 ^ z := h
    have hZ : Z ≠ 0 := by omega
    have h1 := entryNo_lt h'.1 h'.2
    rw [← tableBits_of_ne z hZ] at h1
    by_cases hM : M = 0
    · subst hM
      rw [cubeNo_mask_alone]
      refine Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) ?_)
      unfold cubeBits
      rw [if_neg (by simp)]
      omega
    · rw [cubeNo_mask_both a z r c hM hZ]
      have h2 : 2 ^ tableBits Z z ≤ 2 ^ max (tableBits M a) (tableBits Z z) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      have h3 : cubeBits M a Z z = max (tableBits M a) (tableBits Z z) + 1 := by
        unfold cubeBits
        rw [if_pos ⟨hM, hZ⟩]
      rw [h3, Nat.pow_succ]
      omega

/-- No two entries of an oracle message have one index. -/
theorem cubeNo_inj {M a Z z : Nat} {mask mask' : Bool} {r c r' c' : Nat}
    (h : RealAt M a Z z mask r c) (h' : RealAt M a Z z mask' r' c')
    (e : cubeNo M a Z z mask r c = cubeNo M a Z z mask' r' c') :
    mask = mask' ∧ r = r' ∧ c = c' := by
  have apart : ∀ {r c r' c' : Nat}, RealAt M a Z z false r c → RealAt M a Z z true r' c' →
      cubeNo M a Z z false r c < cubeNo M a Z z true r' c' := by
    intro r c r' c' g g'
    have g1 : r < M ∧ c < 2 ^ a := g
    have g2 : r' < Z ∧ c' < 2 ^ z := g'
    have hM : M ≠ 0 := by omega
    have hZ : Z ≠ 0 := by omega
    rw [cubeNo_main, cubeNo_mask_both a z r' c' hM hZ]
    have h1 := entryNo_lt g1.1 g1.2
    rw [← tableBits_of_ne a hM] at h1
    have h2 : 2 ^ tableBits M a ≤ 2 ^ max (tableBits M a) (tableBits Z z) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    omega
  cases mask <;> cases mask'
  · rw [cubeNo_main, cubeNo_main] at e
    have g : r < M ∧ c < 2 ^ a := h
    have g' : r' < M ∧ c' < 2 ^ a := h'
    exact ⟨rfl, entryNo_inj g.1 g'.1 e⟩
  · exact absurd e (Nat.ne_of_lt (apart h h'))
  · exact absurd e.symm (Nat.ne_of_lt (apart h' h))
  · have g : r < Z ∧ c < 2 ^ z := h
    have g' : r' < Z ∧ c' < 2 ^ z := h'
    have e' : entryNo Z r c = entryNo Z r' c' := by
      unfold cubeNo at e
      simp only [if_true] at e
      omega
    exact ⟨rfl, entryNo_inj g.1 g'.1 e'⟩

/-! ## The free entries and the pad -/

/-- The k-th free entry stands in a real row. -/
theorem freeAt_row_lt {m : Nat} (hm : 0 < m) (k : Nat) : (freeAt m k).1 < m := Nat.mod_lt k hm

/-- The free entry number m c + r, r below m, is entry c of row r. -/
theorem freeAt_mul_add {m r : Nat} (c : Nat) (h : r < m) : freeAt m (m * c + r) = (r, c) := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have e1 : (m * c + r) % m = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  have e2 : (m * c + r) / m = c := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt h, Nat.zero_add]
  simp only [freeAt, e1, e2]

/-- The free entries' numbers rise with k. -/
theorem entryNo_freeAt_lt {m k k' : Nat} (hm : 0 < m) (h : k < k') :
    entryNo m (freeAt m k).1 (freeAt m k).2 < entryNo m (freeAt m k').1 (freeAt m k').2 := by
  simp only [entryNo, freeAt]
  have hQ := le_two_pow_logUp m
  generalize 2 ^ logUp m = Q at hQ ⊢
  have h1 := Nat.mod_lt k hm
  have h2 := Nat.div_add_mod k m
  have h3 := Nat.div_add_mod k' m
  have hd : k / m ≤ k' / m := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hd with hlt | heq
  · have h4 : Q * (k / m + 1) ≤ Q * (k' / m) := Nat.mul_le_mul_left Q hlt
    rw [Nat.mul_add, Nat.mul_one] at h4
    omega
  · rw [heq] at h2 ⊢
    omega

/-- The k-th free entry has a number below that of the pad's first entry, which is entry e - s of
row m - 1, exactly if k is below the number of free entries. -/
theorem freeAt_below_pad {m e s : Nat} (hm : 0 < m) (hs : s ≤ e) (k : Nat) :
    entryNo m (freeAt m k).1 (freeAt m k).2 < entryNo m (m - 1) (e - s) ↔ k < freeCount m e s := by
  have hc : freeCount m e s = m * (e - s) + (m - 1) := by
    unfold freeCount
    rw [if_neg]
    omega
  have hp : freeAt m (m * (e - s) + (m - 1)) = (m - 1, e - s) :=
    freeAt_mul_add (e - s) (by omega)
  have key : entryNo m (m - 1) (e - s) =
      entryNo m (freeAt m (m * (e - s) + (m - 1))).1 (freeAt m (m * (e - s) + (m - 1))).2 := by
    rw [hp]
  rw [hc, key]
  generalize m * (e - s) + (m - 1) = N
  constructor
  · intro h
    rcases Nat.lt_trichotomy k N with h1 | h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_trans h (entryNo_freeAt_lt hm h1)) (Nat.lt_irrefl _)
  · exact entryNo_freeAt_lt hm

/-- With a mask row the pad's row is a real mask row. -/
theorem padRow_lt_mask {Z : Nat} (M : Nat) (h : 0 < Z) : padRow M Z < Z := by
  have h' : (Z != 0) = true := by simp; omega
  unfold padRow
  rw [if_pos h']
  omega

/-- Without a mask row the pad's row is a real main row. -/
theorem padRow_lt_main {M : Nat} (h : 0 < M) : padRow M 0 < M := by
  simp [padRow]
  omega

/-- Where the pad fits its row, its entries lie in the row. -/
theorem padEntry_lt {len s each i t : Nat} (hfit : each * s ≤ len) (hi : i < s) (ht : t < each) :
    padEntry len s each i t < len := by
  unfold padEntry
  have h1 : each * (i + 1) ≤ each * s := Nat.mul_le_mul_left each hi
  rw [Nat.mul_add, Nat.mul_one] at h1
  generalize each * s = A at hfit h1 ⊢
  generalize each * i = B at h1 ⊢
  omega

/-- The pad's entries differ. -/
theorem padEntry_inj {len s each i t i' t' : Nat} (ht : t < each) (ht' : t' < each)
    (e : padEntry len s each i t = padEntry len s each i' t') : i = i' ∧ t = t' := by
  unfold padEntry at e
  have e1 : each * i + t = each * i' + t' := by omega
  have a := freeAt_mul_add i ht
  have b := freeAt_mul_add i' ht'
  rw [e1, b] at a
  exact ⟨(congrArg Prod.snd a).symm, (congrArg Prod.fst a).symm⟩

/-- In mask rows the pad's first entry is entry e - s of row m - 1. -/
theorem pad_first {m : Nat} (M e s : Nat) (hm : 0 < m) :
    padRow M m = m - 1 ∧ padEntry e s 1 0 0 = e - s := by
  have h : (m != 0) = true := by simp; omega
  constructor
  · unfold padRow
    rw [if_pos h]
  · unfold padEntry
    omega

/-- A free entry lies in its row, where a sample has at least one answer and the pad fits. -/
theorem freeAt_entry_lt {m e s k : Nat} (hm : 0 < m) (h1 : 1 ≤ s) (hs : s ≤ e)
    (hk : k < freeCount m e s) : (freeAt m k).2 < e := by
  have hc : freeCount m e s = m * (e - s) + (m - 1) := by
    unfold freeCount
    rw [if_neg]
    omega
  rw [hc] at hk
  have h2 : k < m * (e - s + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h3 : k / m < e - s + 1 := Nat.div_lt_of_lt_mul h2
  show k / m < e
  omega

/-- No free entry is an entry of the pad. -/
theorem freeAt_ne_pad {m e s k i : Nat} (M : Nat) (hm : 0 < m) (hs : s ≤ e)
    (hk : k < freeCount m e s) : freeAt m k ≠ (padRow M m, padEntry e s 1 i 0) := by
  intro h
  have h1 := (freeAt_below_pad hm hs k).2 hk
  have hr : (freeAt m k).1 = padRow M m := congrArg Prod.fst h
  have hc : (freeAt m k).2 = padEntry e s 1 i 0 := congrArg Prod.snd h
  rw [hr, hc, (pad_first M e s hm).1] at h1
  have h2 : 2 ^ logUp m * (e - s) ≤ 2 ^ logUp m * padEntry e s 1 i 0 :=
    Nat.mul_le_mul_left _ (by unfold padEntry; omega)
  unfold entryNo at h1
  generalize 2 ^ logUp m * (e - s) = A at h1 h2
  generalize 2 ^ logUp m * padEntry e s 1 i 0 = B at h1 h2
  omega

/-- No entry is taken twice. -/
theorem freeAt_inj {m k k' : Nat} (hm : 0 < m) (e : freeAt m k = freeAt m k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := entryNo_freeAt_lt hm h
    rw [e] at this
    exact absurd this (Nat.lt_irrefl _)
  · exact h
  · have := entryNo_freeAt_lt hm h
    rw [e] at this
    exact absurd this (Nat.lt_irrefl _)

/-! ## A sumcheck with a hiding sum -/

theorem sk_succ {ks : List Nat} {l : Nat} (h : l < ks.length) :
    sk ks (l + 1) = sk ks l + ks[l] := by
  unfold sk
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h]
  simp

theorem sk_le {ks : List Nat} {l l' : Nat} (h : l ≤ l') (h' : l' ≤ ks.length) :
    sk ks l ≤ sk ks l' := by
  induction l' with
  | zero => exact Nat.le_of_eq (by rw [Nat.le_zero.1 h])
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h1 | h1
    · have := ih (Nat.le_of_lt_succ h1) (Nat.le_of_succ_le h')
      rw [sk_succ (Nat.lt_of_succ_le h')]
      omega
    · rw [h1]
      exact Nat.le_refl _

theorem sk_length (ks : List Nat) : sk ks ks.length = ks.sum := by
  unfold sk
  rw [List.take_length]

/-- (l, deg) is a coefficient of the hiding polynomial: degrees 1 to k_l for every variable but the
last, 0 to k_l for the last. -/
def HidOK (ks : List Nat) (l deg : Nat) : Prop :=
  ∃ h : l < ks.length, deg ≤ ks[l] ∧ (l + 1 < ks.length → 1 ≤ deg)

/-- A coefficient's entry lies from sk l on and before sk (l + 1), but for the last variable's
highest degree, which has the entry sk (l + 1). -/
theorem hidPos_bounds {ks : List Nat} {l deg : Nat} (h : HidOK ks l deg) :
    sk ks l ≤ hidPos ks l deg ∧ (l + 1 < ks.length → hidPos ks l deg < sk ks (l + 1)) ∧
      hidPos ks l deg ≤ sk ks (l + 1) := by
  obtain ⟨hl, hd, h1⟩ := h
  rw [sk_succ hl]
  unfold hidPos
  by_cases c : l + 1 < ks.length
  · have := h1 c
    rw [if_pos c]
    exact ⟨by omega, fun _ => by omega, by omega⟩
  · rw [if_neg c]
    exact ⟨by omega, fun c' => absurd c' c, by omega⟩

/-- Each coefficient has an entry below the number of coefficients. -/
theorem hidPos_lt {ks : List Nat} {l deg : Nat} (h : HidOK ks l deg) :
    hidPos ks l deg < hidCount ks := by
  have b := (hidPos_bounds h).2.2
  have hl : l + 1 ≤ ks.length := h.1
  have d := sk_le hl (Nat.le_refl ks.length)
  rw [sk_length] at d
  unfold hidCount
  omega

/-- No two coefficients have one entry. -/
theorem hidPos_inj {ks : List Nat} {l deg l' deg' : Nat} (h : HidOK ks l deg)
    (h' : HidOK ks l' deg') (e : hidPos ks l deg = hidPos ks l' deg') : l = l' ∧ deg = deg' := by
  have key : ∀ {a da b db : Nat}, HidOK ks a da → HidOK ks b db → a < b →
      hidPos ks a da < hidPos ks b db := by
    intro a da b db ha hb hab
    have hab' : a + 1 ≤ b := hab
    have h1 := (hidPos_bounds ha).2.1 (Nat.lt_of_le_of_lt hab' hb.1)
    have h2 := sk_le hab' (Nat.le_of_lt hb.1)
    have h3 := (hidPos_bounds hb).1
    omega
  rcases Nat.lt_trichotomy l l' with c | c | c
  · exact absurd e (Nat.ne_of_lt (key h h' c))
  · subst c
    refine ⟨rfl, ?_⟩
    obtain ⟨_, _, h1⟩ := h
    obtain ⟨_, _, h1'⟩ := h'
    unfold hidPos at e
    by_cases c : l + 1 < ks.length
    · have := h1 c
      have := h1' c
      rw [if_pos c, if_pos c] at e
      omega
    · rw [if_neg c, if_neg c] at e
      omega
  · exact absurd e.symm (Nat.ne_of_lt (key h' h c))

theorem sk_cons (k : Nat) (ks : List Nat) (l : Nat) : sk (k :: ks) (l + 1) = k + sk ks l := by
  unfold sk
  rw [List.take_succ_cons, List.sum_cons]

theorem HidOK.cons {ks : List Nat} {l deg : Nat} (k : Nat) (h : HidOK ks l deg) :
    HidOK (k :: ks) (l + 1) deg := by
  obtain ⟨hl, hd, h1⟩ := h
  refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
  · simpa only [List.getElem_cons_succ] using hd
  · intro h2
    simp only [List.length_cons] at h2
    exact h1 (by omega)

theorem hidPos_cons {ks : List Nat} {l deg : Nat} (k : Nat) (h : HidOK ks l deg) :
    hidPos (k :: ks) (l + 1) deg = k + hidPos ks l deg := by
  obtain ⟨_, _, h1⟩ := h
  unfold hidPos
  rw [sk_cons]
  simp only [List.length_cons]
  by_cases c : l + 1 < ks.length
  · have := h1 c
    rw [if_pos (by omega), if_pos c]
    omega
  · rw [if_neg (by omega), if_neg c]
    omega

/-- Every entry below the number of coefficients holds a coefficient. -/
theorem hidPos_onto : ∀ {ks : List Nat} {p : Nat}, ks ≠ [] → p < hidCount ks →
    ∃ l deg, HidOK ks l deg ∧ hidPos ks l deg = p
  | [], _, h, _ => absurd rfl h
  | [k], p, _, hp => by
    have hp' : p < 1 + k := by simpa [hidCount] using hp
    refine ⟨0, p, ⟨by simp, by simp only [List.getElem_cons_zero]; omega, ?_⟩, ?_⟩
    · intro h
      simp at h
    · simp [hidPos, sk]
  | k :: k' :: ks, p, _, hp => by
    have hp' : p < 1 + (k + (k' :: ks).sum) := by simpa [hidCount] using hp
    by_cases c : p < k
    · refine ⟨0, p + 1,
        ⟨by simp, by simp only [List.getElem_cons_zero]; omega, fun _ => by omega⟩, ?_⟩
      simp [hidPos, sk]
    · have hq : p - k < hidCount (k' :: ks) := by
        unfold hidCount
        omega
      obtain ⟨l, deg, ho, he⟩ := hidPos_onto (ks := k' :: ks) (by simp) hq
      refine ⟨l + 1, deg, ho.cons k, ?_⟩
      rw [hidPos_cons k ho, he]
      omega

/-- A coefficient's entry is below every end value's number. -/
theorem hidPos_lt_endNo {ks : List Nat} {l deg : Nat} (h : HidOK ks l deg) (i : Nat) :
    hidPos ks l deg < endNo ks i := by
  have := hidPos_lt h
  unfold hidCount at this
  unfold endNo
  omega

/-! ## The lookup on the digits -/

/-- The key number of (u, crow), crow below 2 ^ lc, is no padding position exactly if u is below tau
and crow below mz. -/
theorem isKey_keyNo {tau lc mz u crow : Nat} (h : crow < 2 ^ lc) :
    isKey tau lc mz (keyNo lc u crow) = true ↔ u < tau ∧ crow < mz := by
  have h0 : 0 < 2 ^ lc := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have e1 : (u * 2 ^ lc + crow) / 2 ^ lc = u := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h0, Nat.div_eq_of_lt h, Nat.zero_add]
  have e2 : (u * 2 ^ lc + crow) % 2 ^ lc = crow := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  simp only [isKey, keyNo, e1, e2, Bool.and_eq_true, decide_eq_true_eq]

/-- Two pairs (row of ZZ, cell row) with one key number are one pair. -/
theorem keyNo_inj {lc u crow u' crow' : Nat} (h : crow < 2 ^ lc) (h' : crow' < 2 ^ lc)
    (e : keyNo lc u crow = keyNo lc u' crow') : u = u' ∧ crow = crow' := by
  have h0 : 0 < 2 ^ lc := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  unfold keyNo at e
  have d : ∀ {a b : Nat}, b < 2 ^ lc → (a * 2 ^ lc + b) / 2 ^ lc = a := by
    intro a b hb
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h0, Nat.div_eq_of_lt hb, Nat.zero_add]
  have eu : u = u' := by
    have e' := congrArg (· / 2 ^ lc) e
    simp only [d h, d h'] at e'
    exact e'
  subst eu
  exact ⟨rfl, Nat.add_left_cancel e⟩

/-- A key number that is no padding position has a row below tau and a cell row below mz, and is
the key number of these two. -/
theorem keyNo_of_isKey {tau lc mz x : Nat} (h : isKey tau lc mz x = true) :
    x / 2 ^ lc < tau ∧ x % 2 ^ lc < mz ∧ keyNo lc (x / 2 ^ lc) (x % 2 ^ lc) = x := by
  unfold isKey at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, h.2, ?_⟩
  unfold keyNo
  rw [Nat.mul_comm]
  exact Nat.div_add_mod x (2 ^ lc)

/-- A key number is below the number of a call's key numbers. -/
theorem keyNo_lt {tau lc u crow : Nat} (hu : u < tau) (h : crow < 2 ^ lc) :
    keyNo lc u crow < 2 ^ keyBits tau lc := by
  have h1 : (u + 1) * 2 ^ lc ≤ 2 ^ logUp tau * 2 ^ lc :=
    Nat.mul_le_mul_right _ (Nat.le_trans hu (le_two_pow_logUp tau))
  rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul] at h1
  have h2 : 2 ^ (logUp tau + lc) ≤ 2 ^ keyBits tau lc :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  unfold keyNo
  omega

/-- keyBits is the least number from 10 on whose power of two holds tau rows of 2 ^ lc. -/
theorem keyBits_le {tau lc a : Nat} (h : tau ≤ 2 ^ a) (h10 : 10 ≤ a + lc) :
    keyBits tau lc ≤ a + lc := by
  have := logUp_le h
  unfold keyBits
  exact Nat.max_le.2 ⟨h10, by omega⟩

theorem keyTree_lt {nZ dT call x : Nat} (hd : dT ≤ nZ) (hc : call < 2) (hx : x < 2 ^ nZ) :
    call * 2 ^ (nZ - dT) + x / 2 ^ dT < 2 ^ (nZ - dT + 1) := by
  have e : 2 ^ nZ = 2 ^ dT * 2 ^ (nZ - dT) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : x / 2 ^ dT < 2 ^ (nZ - dT) := Nat.div_lt_of_lt_mul (e ▸ hx)
  have h2 := pair_lt h1 hc
  rw [Nat.pow_succ]
  rw [Nat.mul_comm call]
  omega

/-- Over both calls a key's index is below 2 ^ (nZ + 1). -/
theorem keyIndex_lt {nZ dT call x : Nat} (hd : dT ≤ nZ) (hc : call < 2) (hx : x < 2 ^ nZ) :
    keyIndex nZ dT call x < 2 ^ (nZ + 1) := by
  have h1 := keyTree_lt hd hc hx
  have h2 : x % 2 ^ dT < 2 ^ dT := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 := pair_lt h1 h2
  rw [← Nat.pow_add] at h3
  have e : nZ - dT + 1 + dT = nZ + 1 := by omega
  rw [e] at h3
  exact h3

/-- No two key numbers, of one call or of two, have one index. -/
theorem keyIndex_inj {nZ dT call x call' x' : Nat} (hd : dT ≤ nZ) (hc : call < 2) (hc' : call' < 2)
    (hx : x < 2 ^ nZ) (hx' : x' < 2 ^ nZ) (e : keyIndex nZ dT call x = keyIndex nZ dT call' x') :
    call = call' ∧ x = x' := by
  have h1 := pair_inj (keyTree_lt hd hc hx) (keyTree_lt hd hc' hx') e
  have p : 2 ^ nZ = 2 ^ dT * 2 ^ (nZ - dT) := by rw [← Nat.pow_add]; congr 1; omega
  have y : x / 2 ^ dT < 2 ^ (nZ - dT) := Nat.div_lt_of_lt_mul (p ▸ hx)
  have y' : x' / 2 ^ dT < 2 ^ (nZ - dT) := Nat.div_lt_of_lt_mul (p ▸ hx')
  have e2 : x / 2 ^ dT + 2 ^ (nZ - dT) * call = x' / 2 ^ dT + 2 ^ (nZ - dT) * call' := by
    have := h1.1
    rw [Nat.mul_comm call, Nat.mul_comm call'] at this
    omega
  have h2 := pair_inj y y' e2
  refine ⟨h2.2, ?_⟩
  rw [← Nat.div_add_mod x (2 ^ dT), ← Nat.div_add_mod x' (2 ^ dT), h2.1, h1.2]

end Fmt.Places
