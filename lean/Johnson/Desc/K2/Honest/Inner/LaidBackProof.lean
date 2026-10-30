-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/LaidBackProof.lean: THE CARRYING MESSAGE's LAYING READ BACK
(Johnson/Desc/K2/Honest/Carrying.lean): in its two tables entry j of the folded main row stands at
the index that the program's `cutIndex` gives it, and entry i of the rest at the index that
`SwitchPlaces.get` gives it. Statements and proofs. Numbers and lists; no coin, no round, no frame.

  `numberIn_cut`    `numberIn` undoes a cut: at the row and place at which a cut lays entry n it
                    answers n
  `numberIn_off`    it answers nothing at a row outside the block
  `skip_count`      for a pad that rises strictly: as many entries of the pad lie below `skip pad i`
                    as it has stepped over
  `carrying_main`   the main vector
  `carrying_rest`   the rest

By: the laws on the program's three functions (OnBytes/Slice/SwitchPlacesLaws.lean): `cutIndex_mod`,
`cutIndex_div`, `get_eq`, `le_skip`, `skip_of_lt`, `skip_not_mem`.

Premises, all on public numbers: each block lies inside its table's rows (`RowCut.Fits`); the pad's
numbers rise strictly; where both blocks lie in main rows they have no row in common. The main
vector is read in the main table. The first two follow from the program's own test on a target
(`of_check`, `make_pad_rises`, the same file). The third is what that test's clause on the two
blocks asks (the main block from row 0 on, the rest's right behind it): no lemma here says so.

Limits. Nothing on what the rest's entries are. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Carrying
import OnBytes.Slice.SwitchPlacesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.SwitchPlaces (skip get_eq le_skip skip_of_lt skip_not_mem skip_cons)

/-- `numberIn` undoes a cut. -/
theorem numberIn_cut (cut : RowCut) (n : Nat) :
    numberIn cut (cut.firstRow + n % 2 ^ cut.bits) (n / 2 ^ cut.bits) = some n := by
  have hm : n % 2 ^ cut.bits < 2 ^ cut.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hd := Nat.mod_add_div n (2 ^ cut.bits)
  unfold numberIn
  have hc : (decide (cut.firstRow ≤ cut.firstRow + n % 2 ^ cut.bits) &&
      decide (cut.firstRow + n % 2 ^ cut.bits < cut.firstRow + 2 ^ cut.bits)) = true := by
    simp [hm]
  rw [if_pos hc, Nat.add_sub_cancel_left, Nat.mul_comm, hd]

/-- It answers nothing at a row outside the block. -/
theorem numberIn_off (cut : RowCut) (b j : Nat)
    (h : b < cut.firstRow ∨ cut.firstRow + 2 ^ cut.bits ≤ b) : numberIn cut b j = none := by
  unfold numberIn
  have hc : (decide (cut.firstRow ≤ b) && decide (b < cut.firstRow + 2 ^ cut.bits)) = false := by
    rcases h with h | h
    · simp [Nat.not_le.2 h]
    · simp [Nat.not_lt.2 h]
  rw [hc]
  rfl

/-- As many entries of the pad lie below `skip pad i` as it has stepped over. -/
theorem skip_count : ∀ (pad : List Nat), pad.Pairwise (· < ·) → ∀ i : Nat,
    (pad.filter (· < skip pad i)).length + i = skip pad i
  | [], _, i => by simp [skip]
  | p :: ps, hp, i => by
    rw [List.pairwise_cons] at hp
    rw [skip_cons]
    by_cases h : p ≤ i
    · rw [if_pos h]
      have ih := skip_count ps hp.2 (i + 1)
      have hl : p < skip ps (i + 1) := Nat.lt_of_lt_of_le (Nat.lt_succ_of_le h) (le_skip ps (i + 1))
      rw [List.filter_cons_of_pos (by simpa using hl), List.length_cons]
      omega
    · rw [if_neg h]
      have hi : ∀ q ∈ ps, i < q := fun q hq => Nat.lt_trans (Nat.lt_of_not_le h) (hp.1 q hq)
      rw [skip_of_lt ps i hi]
      have hn : (p :: ps).filter (· < i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · simpa using Nat.le_of_lt (Nat.lt_of_not_le h)
        · simpa using Nat.le_of_lt (hi q hq)
      rw [hn]
      simp

/-- **The main vector**: entry j stands at the index that `cutIndex` gives it. -/
theorem carrying_main (Z : Sizes) (W : Left) (free : Part → Nat → Nat → Cb.Gl.E)
    (hF : Z.target.main.Fits (switchRowBits Z.target .main)) (j : Nat)
    (hj : j < (Z.codes.base.getD Z.code default).ell) :
    carryingAt Z W free .main (cutIndex Z.target.main (switchRowBits Z.target .main) j) =
      W.main j := by
  unfold carryingAt carrying
  rw [cutIndex_mod hF, cutIndex_div hF]
  simp only [beq_self_eq_true, if_true, numberIn_cut, hj]

/-- **The rest**: entry i stands at the index that `SwitchPlaces.get` gives it. -/
theorem carrying_rest (Z : Sizes) (W : Left) (free : Part → Nat → Nat → Cb.Gl.E)
    (hR : Z.target.rest.Fits (switchRowBits Z.target Z.target.rest.part))
    (hp : (SwitchPlaces.make Z.codes Z.target).pad.Pairwise (· < ·))
    (hd : Z.target.rest.part = .main →
      Z.target.main.firstRow + 2 ^ Z.target.main.bits ≤ Z.target.rest.firstRow ∨
        Z.target.rest.firstRow + 2 ^ Z.target.rest.bits ≤ Z.target.main.firstRow)
    (i : Nat) (hi : i < (rest Z W).length) :
    carryingAt Z W free Z.target.rest.part ((SwitchPlaces.make Z.codes Z.target).get i) =
      (rest Z W).getD i zeroG := by
  have hcut : (SwitchPlaces.make Z.codes Z.target).cut = Z.target.rest := rfl
  have hrb : (SwitchPlaces.make Z.codes Z.target).rowBits =
      switchRowBits Z.target Z.target.rest.part := rfl
  have hm : skip (SwitchPlaces.make Z.codes Z.target).pad i % 2 ^ Z.target.rest.bits <
      2 ^ Z.target.rest.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmain : (if Z.target.rest.part == Part.main then
      numberIn Z.target.main
        (Z.target.rest.firstRow + skip (SwitchPlaces.make Z.codes Z.target).pad i %
          2 ^ Z.target.rest.bits)
        (skip (SwitchPlaces.make Z.codes Z.target).pad i / 2 ^ Z.target.rest.bits)
      else none) = none := by
    by_cases e : Z.target.rest.part = .main
    · rw [if_pos (by simp [e])]
      apply numberIn_off
      rcases hd e with h | h
      · right; omega
      · left; omega
    · rw [if_neg (by simpa using e)]
  have hc := skip_count _ hp i
  have hnot := skip_not_mem _ hp i
  unfold carryingAt carrying
  rw [get_eq, hcut, hrb, cutIndex_mod hR, cutIndex_div hR]
  simp only [hmain, beq_self_eq_true, if_true, numberIn_cut]
  have hi' : skip (SwitchPlaces.make Z.codes Z.target).pad i -
      ((SwitchPlaces.make Z.codes Z.target).pad.filter
        (· < skip (SwitchPlaces.make Z.codes Z.target).pad i)).length = i := by omega
  rw [hi']
  have hcon : (SwitchPlaces.make Z.codes Z.target).pad.contains
      (skip (SwitchPlaces.make Z.codes Z.target).pad i) = false := by
    simpa using hnot
  have hsz : decide ((rest Z W).toArray.size ≤ i) = false := by
    simpa using hi
  rw [hcon, hsz]
  simp

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.carrying_main
#print axioms VerifiableInference.Desc.K2.Honest.carrying_rest
