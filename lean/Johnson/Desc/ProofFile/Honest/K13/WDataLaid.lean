-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/WDataLaid.lean: THE LAYOUT OF W's DATA (`wData`, WData.lean of
this folder): where the public tests pass, each entry of W below 2^kCol is laid
(`wData_lays_index`); and two places at which data is laid and which hold one number are one place
(`wData_lays_once`). Statements with their proofs.

The library's two functions of a layout undo each other (`entryAt_index`, `index_entryAt`,
OnBytes/Slice/BlkCross.lean); under the test on the public shape the first 2^kCol entries lie in
real rows (`shape_room`, `shape_rows`, Johnson/Desc/K13/Honest/FromShape.lean) and, where the
message length is a power of two, at places of the message (`shape_places`, `places_eq`,
RealPlaces.lean); the number of main rows is at most two to the layout's row bits
(`le_two_pow_ceilLog2`, OnBytes/Slice/ProgCodes.lean). `WIs` (Johnson/Desc/K13/Law/Eval.lean) is
stated with `VectorLay.index`: `wNo_index` is the step from the filling's rows and places to it.
Main names:
  `wNo_index`: **where the shape is lawful at the codes (`linFits`), for e below 2^kCol: the place
    of the table's index of entry e holds entry e.**
  `wData_lays_index`: **where the public tests pass, each entry below 2^kCol is laid**, at that row
    and place.
  `wNo_once`: where the message length of W's code is a power of two: two places in real rows, both
    below that length, that hold one number are one place.
  `wData_lays_once`: **the same for two places at which the filling lays data**: `lays` tests these
    premises itself.

What is not claimed. What WData.lean says is not claimed. That the table so filled meets `WIs` at
any witness. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.WData
import Johnson.Desc.K13.Honest.RealPlaces
import OnBytes.Slice.BlkCross
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params
open OnBytes.Slice (entryAt_index index_entryAt le_two_pow_ceilLog2)
open VerifiableInference.Desc.K13.Honest (shape_room shape_rows shape_places places_eq)

variable {Xi : Type}

/-- **The place of the table's index of entry e holds entry e**: where the shape is lawful at the
codes (`linFits`), for e below 2^kCol. -/
theorem wNo_index {codes : Codes} {Sh : LinShape}
    (h : VerifiableInference.Desc.Own.linFits codes Sh = true) {e : ℕ} (he : e < 2 ^ Sh.kCol) :
    wNo codes Sh ((linLayW codes Sh).index e % 2 ^ (linLayW codes Sh).rowBits)
      ((linLayW codes Sh).index e / 2 ^ (linLayW codes Sh).rowBits) = e := by
  unfold wNo
  rw [Nat.mod_add_div']
  exact entryAt_index _ e (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (shape_room h)))

/-- **Two places in real rows that hold one number are one place**: where the message length of W's
code is a power of two (hp) and both places lie below that length (hj, hj'). -/
theorem wNo_once {codes : Codes} {Sh : LinShape} (hp : powerOfTwo (wEll codes Sh) = true)
    {r r' j j' : ℕ} (hr : r < Sh.w.mainRows) (hr' : r' < Sh.w.mainRows) (hj : j < wEll codes Sh)
    (hj' : j' < wEll codes Sh) (e : wNo codes Sh r j = wNo codes Sh r' j') : r = r' ∧ j = j' := by
  have hB : ∀ a, a < Sh.w.mainRows → a < 2 ^ (linLayW codes Sh).rowBits := fun a ha =>
    lt_of_lt_of_le ha (le_two_pow_ceilLog2 _)
  have hP : 2 ^ (linLayW codes Sh).placeBits = wEll codes Sh := places_eq hp
  have hpos : 0 < 2 ^ (linLayW codes Sh).rowBits := Nat.pos_of_ne_zero (by positivity)
  have hlt : ∀ a b, a < Sh.w.mainRows → b < wEll codes Sh →
      a + b * 2 ^ (linLayW codes Sh).rowBits < 2 ^ (linLayW codes Sh).bits := by
    intro a b ha hb
    have h1 : a + b * 2 ^ (linLayW codes Sh).rowBits <
        (b + 1) * 2 ^ (linLayW codes Sh).rowBits := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      exact Nat.add_lt_add_left (hB a ha) _
    have h2 : (b + 1) * 2 ^ (linLayW codes Sh).rowBits ≤
        2 ^ (linLayW codes Sh).placeBits * 2 ^ (linLayW codes Sh).rowBits :=
      Nat.mul_le_mul_right _ (by rw [hP]; exact hb)
    have h3 : 2 ^ (linLayW codes Sh).placeBits * 2 ^ (linLayW codes Sh).rowBits =
        2 ^ (linLayW codes Sh).bits := by
      unfold VectorLay.bits
      rw [Nat.pow_add, Nat.mul_comm]
    exact lt_of_lt_of_le h1 (h3 ▸ h2)
  have q : r + j * 2 ^ (linLayW codes Sh).rowBits = r' + j' * 2 ^ (linLayW codes Sh).rowBits := by
    rw [← index_entryAt _ _ (hlt r j hr hj), ← index_entryAt _ _ (hlt r' j' hr' hj')]
    exact congrArg _ e
  have m : ∀ a b, a < Sh.w.mainRows →
      (a + b * 2 ^ (linLayW codes Sh).rowBits) % 2 ^ (linLayW codes Sh).rowBits = a ∧
        (a + b * 2 ^ (linLayW codes Sh).rowBits) / 2 ^ (linLayW codes Sh).rowBits = b := by
    intro a b ha
    refine ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hB a ha)], ?_⟩
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (hB a ha), Nat.zero_add]
  exact ⟨by rw [← (m r j hr).1, q, (m r' j' hr').1], by rw [← (m r j hr).2, q, (m r' j' hr').2]⟩

/-- **Where the public tests pass, each entry below 2^kCol is laid**: at the row and place of its
index in the table. -/
theorem wData_lays_index (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) (x : Xi)
    (h : wPublic codes Sh n u = true) {e : ℕ} (he : e < 2 ^ Sh.kCol) :
    (wData codes Sh n u pile x).lays wAddr
      ((linLayW codes Sh).index e % 2 ^ (linLayW codes Sh).rowBits)
      ((linLayW codes Sh).index e / 2 ^ (linLayW codes Sh).rowBits) = true := by
  have h' := h
  unfold wPublic at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := h'
  show (wAddr == wAddr && wPublic codes Sh n u && decide _ && decide _ && decide _) = true
  rw [h, wNo_index h1 he, decide_eq_true (shape_rows h1 e he),
    decide_eq_true (show _ < wEll codes Sh from shape_places h1 h2 e he), decide_eq_true he]
  rfl

/-- **Each entry is laid at one place alone**: two places at which the filling lays data at W's
address and which hold one number are one place. -/
theorem wData_lays_once (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) (x : Xi)
    {r r' j j' : ℕ} (h : (wData codes Sh n u pile x).lays wAddr r j = true)
    (h' : (wData codes Sh n u pile x).lays wAddr r' j' = true)
    (e : wNo codes Sh r j = wNo codes Sh r' j') : r = r' ∧ j = j' := by
  have q : ∀ a b, (wData codes Sh n u pile x).lays wAddr a b = true →
      powerOfTwo (wEll codes Sh) = true ∧ a < Sh.w.mainRows ∧ b < wEll codes Sh := by
    intro a b hl
    have hl' : (wAddr == wAddr && wPublic codes Sh n u && decide (a < Sh.w.mainRows) &&
      decide (b < wEll codes Sh) && decide (wNo codes Sh a b < 2 ^ Sh.kCol)) = true := hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl'
    obtain ⟨⟨⟨⟨_, hp⟩, ha⟩, hb⟩, _⟩ := hl'
    unfold wPublic at hp
    simp only [Bool.and_eq_true] at hp
    exact ⟨hp.1.1.2, ha, hb⟩
  exact wNo_once (q r j h).1 (q r j h).2.1 (q r' j' h').2.1 (q r j h).2.2 (q r' j' h').2.2 e

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.wNo_index
#print axioms ProofFile.Honest.K13.wNo_once
#print axioms ProofFile.Honest.K13.wData_lays_index
#print axioms ProofFile.Honest.K13.wData_lays_once
