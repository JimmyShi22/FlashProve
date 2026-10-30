-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
BUILT OVER Block.lean and State.lean, and over the
seats that go with them (Johnson/Stored/HeadSeatAt.lean, Johnson/Stored/ReplySeatAt.lean).
seat_entry_within: the proof follows the reader that refuses.
Johnson/Desc/Kinds/Law/ReadsFit.lean: FOR THE SUB-ROW reads_covered_K06, THE SECOND HALF: EACH OF THE HEAD's FIVE READS
IS NO LONGER THAN ITS TABLE IN THE VECTOR OF READS. Covered.lean | CoveredAt.lean: every entry that the
head's eleven forms name is entry r i of a read r at an i < readLen r (K06Statement.lean).
CoveredSeat.lean: at the first chain's record entry r i lies on the array iU3 at the position
(the table's first entry) + i. HERE: readLen r ≤ the table's length, in public numbers alone.
  widthOf h L r   the length of read r's table: TO THE LETTER widthF | widthD |
                  widthR (in a file of this project that is not in this library, and which this file does not
                  import): hf: NHf * (k * (m / 2^la)) · hd: 1 * (kD * (mD / T)) · hr: 1 * (kR * (mR / T)).
  readLen_fits    where OnBytes/Model/HeadLayout.lean's numbers returns L, at lt ≤ la and XL = 5:
                  readLen r ≤ widthOf h L r, at the sizes that the seat makes of h (sizesOf).
  readLen_fits_layout   the same where layout returns L: lt < la is then layout's own first test.
  seat_entry_within     at the record: if the table of tables holds read r's name with first entry
                  base r and length widthOf h L r, then entry r i, i < readLen r, lies at a position
                  pos with base r ≤ pos < base r + widthOf h L r.
  row_short_at_four     WHY XL = 5 IS ASKED: at four limbs the program's row has 95 digits, the text's
                  120 (Norm.lean: "five limbs are written in"): the bound fails.
WHAT IT IS NOT. Nothing on soundness. NOT that the record's table of tables is the one that the premise
of seat_entry_within describes (tab_of_fold | find_five, declared nowhere in this library (find_five', ReadsFitNorm.lean, is on tabAtC), say it of the fold of
addFun; whose text makes the table in the description is not settled here). NOT that no width is 0.
h.XL = 5 IS A PREMISE THAT NO TEST OF THE KIND's ASKS: sizesOf and parOf drop XL; layout admits 4 and 5.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Statement
import Johnson.Desc.Kinds.Law.CoveredSeat
import OnBytes.Model.HeadLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Aff roundUp ledNRH)
open OnBytes.Model.Head (Shape HL numbers layout needed admitted)
open VerifiableInference.Desc.First (S)

/-! ## Arithmetic -/

theorem le_roundUp (x w : Nat) (hw : 0 < w) : x ≤ roundUp x w := by
  unfold roundUp
  have h1 := Nat.div_add_mod (x + w - 1) w
  have h2 := Nat.mod_lt (x + w - 1) hw
  rw [Nat.mul_comm] at h1
  omega

theorem roundUp_div_mul (x w : Nat) (hw : 0 < w) : roundUp x w / w * w = roundUp x w := by
  unfold roundUp
  rw [Nat.mul_div_cancel _ hw]

theorem fit_short (x c : Nat) (hc : 0 < c) : x ≤ 1 * (roundUp x c / c * c) := by
  rw [Nat.one_mul, roundUp_div_mul x c hc]
  exact le_roundUp x c hc

theorem fit_long (feat N lm la lt : Nat) (h1 : lt ≤ la) (h2 : la ≤ lm) (hN : 0 < N) :
    feat / 2 ^ (la - lt) ≤
      N * (roundUp feat (N * (2 ^ lm / 2 ^ lt)) / (N * (2 ^ lm / 2 ^ lt)) * (2 ^ lm / 2 ^ la)) := by
  have e1 : 2 ^ lm / 2 ^ la = 2 ^ (lm - la) := Nat.pow_div h2 (by omega)
  have e2 : 2 ^ lm / 2 ^ lt = 2 ^ (lm - lt) := Nat.pow_div (by omega) (by omega)
  have e3 : 2 ^ (lm - lt) = 2 ^ (la - lt) * 2 ^ (lm - la) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e1, e2, e3]
  have hS : 0 < 2 ^ (la - lt) := Nat.two_pow_pos _
  have hu : 0 < 2 ^ (lm - la) := Nat.two_pow_pos _
  have hw : 0 < N * (2 ^ (la - lt) * 2 ^ (lm - la)) := Nat.mul_pos hN (Nat.mul_pos hS hu)
  apply Nat.div_le_of_le_mul
  have e4 : 2 ^ (la - lt) * (N * (roundUp feat (N * (2 ^ (la - lt) * 2 ^ (lm - la))) /
        (N * (2 ^ (la - lt) * 2 ^ (lm - la))) * 2 ^ (lm - la)))
      = roundUp feat (N * (2 ^ (la - lt) * 2 ^ (lm - la))) /
        (N * (2 ^ (la - lt) * 2 ^ (lm - la))) * (N * (2 ^ (la - lt) * 2 ^ (lm - la))) := by
    ring
  rw [e4, roundUp_div_mul _ _ hw]
  exact le_roundUp _ _ hw

/-! ## The program's numbers -/

theorem ok_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem needed_ok {b : Bool} {n : String} {a : Unit} (h : needed b n = .ok a) : b = true := by
  unfold needed at h
  split at h
  · assumption
  · cases h

/-- The length of a read's table in the vector of reads. -/
def widthOf (h : Shape) (L : HL) : Read → Nat
  | .wideAtKeys | .wideAtCosts => h.NHf * (L.k * (L.m / 2 ^ h.la))
  | .actAtLogits => 1 * (L.kD * (L.mD / h.T))
  | .rowAtCosts | .rowCount => 1 * (L.kR * (L.mR / h.T))

/-- **Each read is no longer than its table.** -/
theorem readLen_fits (h : Shape) (L : HL) (hL : numbers h = .ok L) (hla : h.lt ≤ h.la)
    (hXL : h.XL = 5) (r : Read) : @readLen (sizesOf h) r ≤ widthOf h L r := by
  unfold numbers at hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨_, t2, hL⟩ := ok_bind hL
  have t2' := needed_ok t2
  simp at t2'
  cases hL
  have a1 : h.la ≤ h.lmhf := by omega
  have a2 : 0 < h.NHf := by omega
  have a3 : h.lt ≤ h.lmhd := by omega
  have a4 : h.lt ≤ h.lmhr := by omega
  have cD : 0 < 2 ^ h.lmhd / h.T :=
    Nat.div_pos (Nat.pow_le_pow_right (by omega) a3) (Nat.two_pow_pos _)
  have cR : 0 < 2 ^ h.lmhr / h.T :=
    Nat.div_pos (Nat.pow_le_pow_right (by omega) a4) (Nat.two_pow_pos _)
  have wide : (4 * h.d + 6 * roundUp h.V h.S2) / 2 ^ (h.la - h.lt) ≤
      h.NHf * (roundUp (4 * h.d + 6 * roundUp h.V h.S2) (h.NHf * (2 ^ h.lmhf / 2 ^ h.lt)) /
        (h.NHf * (2 ^ h.lmhf / 2 ^ h.lt)) * (2 ^ h.lmhf / 2 ^ h.la)) :=
    fit_long _ _ _ _ _ hla a1 a2
  have row : 99 + 21 ≤ 1 * (roundUp (ledNRH h.XL) (2 ^ h.lmhr / h.T) / (2 ^ h.lmhr / h.T) *
      (2 ^ h.lmhr / h.T)) := by
    rw [hXL]
    exact fit_short _ _ cR
  cases r with
  | wideAtKeys => exact wide
  | wideAtCosts => exact wide
  | actAtLogits => exact fit_short _ _ cD
  | rowAtCosts => exact row
  | rowCount => exact row

/-- The same where the whole layout returns. -/
theorem readLen_fits_layout (h : Shape) (tau : Array OnBytes.F) (L : HL)
    (hL : layout h tau = .ok L) (hXL : h.XL = 5) (r : Read) :
    @readLen (sizesOf h) r ≤ widthOf h L r := by
  unfold layout at hL
  obtain ⟨_, ha, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨L0, h0, hL⟩ := ok_bind hL
  obtain ⟨calls, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨fs, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨kb, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨pub, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  obtain ⟨_, _, hL⟩ := ok_bind hL
  have e := (Except.ok.inj hL).symm
  subst e
  have ha' := needed_ok ha
  unfold admitted at ha'
  simp at ha'
  have hla : h.lt ≤ h.la := by omega
  have key := readLen_fits h L0 h0 hla hXL r
  cases r <;> exact key

/-- Why five limbs are asked: at four the program's row is shorter than the text's. -/
theorem row_short_at_four : ¬ (99 + 21 ≤ 1 * (roundUp (ledNRH 4) 1 / 1 * 1)) := by decide

/-! ## At the record -/

/-- A read's name in the program's table of tables, as the seat has it (HeadSeatAt.lean). -/
def nameOf : Read → String
  | .wideAtKeys => "hf@Z" | .wideAtCosts => "hf@phiZ" | .actAtLogits => "hd@r_H"
  | .rowAtCosts => "hr@phiC" | .rowCount => "hr@rhoC"

/-- **Every entry of a read below its length lies inside the read's own table.** -/
theorem seat_entry_within (h : Shape) (iU3 : Nat) (s : S) (x : FinalNorm.Reads × Reads)
    (hx : (seatAt h iU3).reads s = some x) (L : HL) (hL : numbers h = .ok L) (hla : h.lt ≤ h.la)
    (hXL : h.XL = 5) (o : VerifiableInference.Desc.First.HeadOwn) (tt : OnBytes.Model.Head.Tables)
    (ho : s.here = .head o) (ht : o.t = some tt) (base : Read → Nat)
    (hfind : ∀ r, tt.tab.find? (fun e => e.1 == nameOf r) = some (nameOf r, base r, widthOf h L r)) :
    ∃ cols : Nat, ∀ r i, i < @readLen (sizesOf h) r → ∃ pos,
      x.2.entry r i = Aff.ent iU3 (pos / cols) (pos % cols) ∧ base r ≤ pos ∧
        pos < base r + widthOf h L r := by
  unfold seatAt at hx
  dsimp only at hx
  split at hx
  · rename_i o' F ho' _
    obtain rfl : o = o' := by
      rw [ho] at ho'
      injection ho'
    rw [ht] at hx
    cases htr : F.trees[iU3]? with
    | none => rw [htr] at hx; simp at hx
    | some tr =>
    rw [htr] at hx
    simp only [Option.bind_some] at hx
    split at hx
    · cases hx
    simp only [Option.some.injEq] at hx
    subst hx
    refine ⟨tr.K, fun r i hi => ⟨base r + i, ?_, by omega, ?_⟩⟩
    · have hb : ((tt.tab.find? fun e => e.1 == nameOf r).map (·.2.1)).getD 0 = base r := by
        rw [hfind r]; rfl
      rw [← hb]
      cases r <;> rfl
    · have := readLen_fits h L hL hla hXL r
      omega
  · cases hx

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.readLen_fits
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readLen_fits_layout
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seat_entry_within
#print axioms VerifiableInference.Desc.Kinds.Head.Law.row_short_at_four
