-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/H2K/BoxAt.lean: a tensor laid on a box of the rest by `switchOnBox`
(OnBytes/Iop/Cs.lean), read in the field, at any box; and that it reads as the stretch whose box it
is.

The program's code switch lays the generator's row on a mask row's message as one tensor where the
message's places in the table form a box: 2 ^ vars places at the distance 2 ^ shift from the index
start on (`switchBox`). OnBytes/Slice/BlkCsRows.lean reads `switchOnBox` at the distance 1
(`readE_switchOnBox`). Here the distance is any power of two, as it is where the table is filled row
index first. Statements and proofs, on the program's pure functions alone.
Main names:
  `box_arith`: the index start + i * A taken apart, for a start whose block number is a multiple of
    B.
  `readE_switchOnBox_at`: at an index J below 2 ^ tb the tensor on the box has the entry number J /
    2 ^ shift % 2 ^ vars of the tensor if the low bits and the high bits of J are those of start;
    else 0.
  `switchBox_yes`: what a yes of switchBox says: the places of the stretch are start + i * 2 ^
    shift, and the block number of start is a multiple of 2 ^ vars.
  `sum_box`: the sum over a stretch at such places has at most one term.
  `onBox_stretch`: the tensor on the box of a stretch reads as `stretchAt`
    (OnBytes/Slice/BlkCsStretch.lean) of the tensor's entries on that stretch.
Limits: No soundness is claimed, and nothing is said on hiding.
Premises of onBox_stretch: the tensor has vars variables; shift + vars ≤ tb; start < 2 ^ tb; J < 2 ^
tb. Nothing is said on which stretches of a switch have a box.
Of the library it calls Tensor.entry_insertChoice (OnBytes/Iop/TensorLaws.lean), vars_insertChoice
(OnBytes/Slice/BlkTens.lean) and eq_of_powerOfTwo (OnBytes/Slice/BlkCsRows.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import OnBytes.Slice.BlkCsStretch

set_option autoImplicit false
namespace H2K.Lift
open OnBytes OnBytes.Slice

theorem box_arith (A B start J : ℕ) (hA : 0 < A) (hB : 0 < B) (hal : start / A % B = 0) (i : ℕ)
    (hi : i < B) :
    start + i * A = J ↔
      (J % A = start % A ∧ J / (A * B) = start / (A * B)) ∧ J / A % B = i := by
  have h1 := Nat.mod_add_div start A
  have h2 := Nat.mod_add_div (start / A) B
  rw [hal, Nat.zero_add, Nat.div_div_eq_div_mul] at h2
  have hsm : start % A < A := Nat.mod_lt _ hA
  constructor
  · intro h
    have hJ : J = start % A + A * (i + B * (start / (A * B))) := by
      rw [← h]
      calc start + i * A = (start % A + A * (start / A)) + i * A := by rw [h1]
        _ = start % A + A * (i + start / A) := by ring
        _ = start % A + A * (i + B * (start / (A * B))) := by rw [h2]
    have hd : J / A = i + B * (start / (A * B)) := by
      rw [hJ, Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hsm, Nat.zero_add]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hJ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsm]
    · rw [← Nat.div_div_eq_div_mul, hd, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hi,
        Nat.zero_add]
    · rw [hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  · rintro ⟨⟨a1, a2⟩, a3⟩
    have k1 := Nat.mod_add_div J A
    have k2 := Nat.mod_add_div (J / A) B
    rw [a3, Nat.div_div_eq_div_mul, a2] at k2
    calc start + i * A = (start % A + A * (start / A)) + i * A := by rw [h1]
      _ = start % A + A * (i + B * (start / (A * B))) := by rw [← h2]; ring
      _ = J % A + A * (J / A) := by rw [k2, a1]
      _ = J := k1

/-- A tensor on a box: the tensor's entries at the indices start + i * 2 ^ shift, and 0 elsewhere. -/
theorem readE_switchOnBox_at (b : SwitchBox) (v : Tensor) (vars tb J : ℕ) (hvv : v.vars = vars)
    (hle : b.shift + vars ≤ tb) (hs : b.start < 2 ^ tb) (hJ : J < 2 ^ tb) :
    readE ((switchOnBox b v vars tb).entry J) =
      if J % 2 ^ b.shift = b.start % 2 ^ b.shift ∧
          J / (2 ^ b.shift * 2 ^ vars) = b.start / (2 ^ b.shift * 2 ^ vars)
      then readE (v.entry (J / 2 ^ b.shift % 2 ^ vars)) else 0 := by
  have hpow : 2 ^ (b.shift + vars) * 2 ^ (tb - b.shift - vars) = 2 ^ tb := by
    rw [← pow_add]
    congr 1
    omega
  have hpp : 2 ^ (b.shift + vars) = 2 ^ b.shift * 2 ^ vars := pow_add 2 _ _
  have hin : ∀ i, rdE.val ((v.insertChoice 0 b.shift (b.start % 2 ^ b.shift)).entry i) =
      (if i / 2 ^ 0 % 2 ^ b.shift = b.start % 2 ^ b.shift % 2 ^ b.shift then 1 else 0) *
        rdE.val (v.entry (unshift 0 b.shift i)) :=
    fun i => Tensor.entry_insertChoice rdE v 0 b.shift _ i (Nat.zero_le _)
  show readE (((v.insertChoice 0 b.shift (b.start % 2 ^ b.shift)).insertChoice (b.shift + vars)
    (tb - b.shift - vars) (b.start / 2 ^ (b.shift + vars))).entry J) = _
  refine (Tensor.entry_insertChoice rdE _ _ _ _ J
    (by rw [vars_insertChoice v 0 b.shift _ (Nat.zero_le _), hvv]; omega)).trans ?_
  rw [hin]
  have hq : ∀ x, x < 2 ^ tb → x / 2 ^ (b.shift + vars) < 2 ^ (tb - b.shift - vars) := fun x hx =>
    Nat.div_lt_of_lt_mul (by rw [hpow]; exact hx)
  have hu : unshift (b.shift + vars) (tb - b.shift - vars) J = J % 2 ^ (b.shift + vars) := by
    unfold unshift
    have e : b.shift + vars + (tb - b.shift - vars) = tb := by omega
    rw [e, Nat.div_eq_of_lt hJ, Nat.mul_zero, Nat.add_zero]
  have hu0 : ∀ i, unshift 0 b.shift i = i / 2 ^ b.shift := by
    intro i
    unfold unshift
    rw [pow_zero, Nat.mod_one, Nat.zero_add, Nat.one_mul, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (hq J hJ), Nat.mod_eq_of_lt (hq _ hs), hu, hu0, pow_zero, Nat.div_one,
    Nat.mod_mod, hpp, Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]
  by_cases c1 : J / (2 ^ b.shift * 2 ^ vars) = b.start / (2 ^ b.shift * 2 ^ vars)
  · by_cases c2 : J % 2 ^ b.shift = b.start % 2 ^ b.shift
    · rw [if_pos c1, if_pos c2, if_pos ⟨c2, c1⟩, one_mul, one_mul]
      rfl
    · rw [if_neg c2, zero_mul, mul_zero, if_neg fun h => c2 h.1]
  · rw [if_neg c1, zero_mul, if_neg fun h => c1 h.2]

/-- What a yes of switchBox says. -/
theorem switchBox_yes (places : SwitchPlaces) (first vars : ℕ) (b : SwitchBox)
    (h : switchBox places first vars = some b) :
    (∀ i, i < 2 ^ vars → places.get (first + i) = b.start + i * 2 ^ b.shift) ∧
      b.start / 2 ^ b.shift % 2 ^ vars = 0 := by
  unfold switchBox at h
  dsimp only at h
  split_ifs at h with c1 c2 c3 c4
  have hb : b = ⟨ceilLog2 (places.get (first + 1) - places.get first), places.get first⟩ :=
    (Option.some.inj h).symm
  have hp : places.get (first + 1) - places.get first =
      2 ^ ceilLog2 (places.get (first + 1) - places.get first) :=
    eq_of_powerOfTwo _ (by simpa using c2)
  subst hb
  show (∀ i, i < 2 ^ vars → places.get (first + i) = places.get first +
      i * 2 ^ ceilLog2 (places.get (first + 1) - places.get first)) ∧
    places.get first / 2 ^ ceilLog2 (places.get (first + 1) - places.get first) % 2 ^ vars = 0
  rw [← hp]
  refine ⟨fun i hi => ?_, by simpa using c4⟩
  have c3' : ((List.range (2 ^ vars)).all fun i => places.get (first + i) ==
      places.get first + i * (places.get (first + 1) - places.get first)) = true := by
    simpa using c3
  exact beq_iff_eq.1 (List.all_eq_true.1 c3' i (List.mem_range.2 hi))

/-- The sum over a stretch at the places of a box has at most one term. -/
theorem sum_box (A B start J : ℕ) (hA : 0 < A) (hB : 0 < B) (hal : start / A % B = 0)
    (c : ℕ → GE) :
    (∑ i ∈ Finset.range B, if start + i * A = J then c i else 0) =
      if J % A = start % A ∧ J / (A * B) = start / (A * B) then c (J / A % B) else 0 := by
  have e : ∀ i ∈ Finset.range B, (if start + i * A = J then c i else 0) =
      if J / A % B = i then
        (if J % A = start % A ∧ J / (A * B) = start / (A * B) then c (J / A % B) else 0)
      else 0 := by
    intro i hi
    have hb := box_arith A B start J hA hB hal i (Finset.mem_range.1 hi)
    by_cases k : start + i * A = J
    · obtain ⟨k1, k2⟩ := hb.1 k
      rw [if_pos k, if_pos k2, if_pos k1, k2]
    · rw [if_neg k]
      by_cases k2 : J / A % B = i
      · rw [if_pos k2, if_neg fun k1 => k (hb.2 ⟨k1, k2⟩)]
      · rw [if_neg k2]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.mod_lt _ hB))]

/-- The tensor on the box of a stretch reads as the stretch. -/
theorem onBox_stretch (places : SwitchPlaces) (first vars : ℕ) (b : SwitchBox)
    (h : switchBox places first vars = some b) (v : Tensor) (tb J : ℕ) (hvv : v.vars = vars)
    (hle : b.shift + vars ≤ tb) (hs : b.start < 2 ^ tb) (hJ : J < 2 ^ tb) :
    readE ((switchOnBox b v vars tb).entry J) =
      stretchAt places first (2 ^ vars) (fun i => readE (v.entry i)) J := by
  obtain ⟨h1, h2⟩ := switchBox_yes places first vars b h
  rw [readE_switchOnBox_at b v vars tb J hvv hle hs hJ]
  unfold stretchAt
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i (Finset.mem_range.1 hi)],
    sum_box (2 ^ b.shift) (2 ^ vars) b.start J (Nat.two_pow_pos _) (Nat.two_pow_pos _) h2]

end H2K.Lift

#print axioms H2K.Lift.readE_switchOnBox_at
#print axioms H2K.Lift.switchBox_yes
#print axioms H2K.Lift.onBox_stretch
