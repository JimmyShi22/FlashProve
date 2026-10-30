-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
BUILT OVER Block.lean and State.lean, and over the
seats that go with them (Johnson/Stored/HeadSeatAt.lean, Johnson/Stored/ReplySeatAt.lean).
seat_entryN_within: the proof follows the reader that refuses.
Johnson/Desc/Kinds/Law/ReadsFitNorm.lean: FOR THE SUB-ROW reads_covered_K06: (1) EVERY NAME THAT THE OUTPUT HEAD's SEAT READS IS IN THE TABLE OF TABLES · (2) EACH OF THE
NORMALIZATION's SEVEN READS, AND ITS SHARE OF THE WIDE READ, IS NO LONGER THAN ITS TABLE · (3) AT THE RECORD, EVERY SUCH ENTRY LIES INSIDE ITS OWN TABLE. Beside
Law/ReadsFit.lean (the head's five reads) and Law/CoveredNorm.lean (which entries the 29 forms and four keys name).
  tabAtC F X D R B   the table of tables (name, first entry, length): fifteen lines: TO THE LETTER tabAt (in a
               file of this project that is not in this library: NOT IMPORTED; the two defs' bodies held alike by program).
  nameOfN r    read r's name, as the seat has it (Johnson/Stored/HeadSeatAt.lean); seatNames: the seat's twelve names (thirteen uses: "hf@Z"
               is read by the norm's "wide" and by the head's wideAtKeys).
  names_in_tab       every one of seatNames is found in tabAtC, whatever the five lengths are. WHY IT MATTERS: the seat's text takes the first entry 0
               where a name is not found ("getD 0"): it fails open: at this table that arm is never taken.
  find_seven | find_five'   each name's line: first entry and length.
  widthOfN h L b r   the length of read r's table: the stream's: 1 * (kxb * (mxb / 2^la)) (that file's widthX) · act's, the row's: as in ReadsFit.
  readLenN_fits      readLenN r ≤ widthOfN h L b r · wideLenN_fits: wideLenN ≤ the wide table's length.
  seat_entryN_within at the record: entry r i, i < readLenN r, and wide i, i < wideLenN, lie at a position inside the read's own table.
TWO PREMISES THAT NO TEST OF THE KIND's ASKS, BESIDE XL = 5:
  (a) StreamFits h b: 5 d / S2 ≤ kxb * (mxb / 2^la): on the LAYERS' layout's numbers (the stream's matrix is theirs): not derived here.
  (b) NOT A PREMISE OF ANY THEOREM HERE, BUT OF THE TEXT's MEANING: HeadNorm.lean lays limb l of the stream at feature l d, from feature 0 on; `verify-on-bytes`
      reads it at off + l * cnt * J (OnBytes/Model/HeadForms.lean:117; Tensors.lean: tenCell). THE TWO AGREE JUST IF off = 0 AND cnt * J = d. The program's own
      test (plan-tensor-layout) asks only S2 | off, S2 | cnt * J, d ≤ J. stream_at_zero says the arithmetic.
  AT THE STORED FULL-SIZE EXAMPLE, BY AN EVALUATION (a trial, in a file of evaluations that is not named here; no theorem): off 0 · nl 5 · cnt 1 · J 5120 = d · the four lengths 19264 | 400 | 10240 | 120
  against 320 (and 19264) | 400 | 10240 | 120 spent: THE STREAM's, act's AND THE ROW's TABLES ARE SPENT TO THE LAST ENTRY.
WHAT IT IS NOT. Nothing on soundness. NOT that the record's table of tables is tabAtC at these lengths (tab_of_fold, declared nowhere in this library, says it of the fold of
addFun; whose text makes the table in the description is not settled here). Not that no length is 0.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsFit
import Johnson.Desc.Kinds.Law.CoveredNorm
import OnBytes.Model.HeadPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Aff roundUp ledNRH)
open OnBytes.Model.Head (Shape HL Border numbers)
open VerifiableInference.Desc.First (S)

/-! ## The names -/

/-- The fifteen tables, from the lengths of a table on hf (F), on the stream (X), on hd (D), on hr
(R) and on bH (B). -/
def tabAtC (F X D R B : ℕ) : List (String × ℕ × ℕ) :=
  [("hf@Z", 0, F), ("hf@phiZ", F, F),
   ("xbL@Z_V", 2 * F, X), ("xbL@Y_N", 2 * F + X, X),
   ("hd@zt_FC", 2 * F + 2 * X, D), ("hd@r_H", 2 * F + 2 * X + D, D),
   ("hr@zt_ROW", 2 * F + 2 * X + 2 * D, R), ("hr@P_V", 2 * F + 2 * X + 2 * D + R, R),
   ("hr@r_tV", 2 * F + 2 * X + 2 * D + 2 * R, R), ("hr@rt_N", 2 * F + 2 * X + 2 * D + 3 * R, R),
   ("hr@phiC", 2 * F + 2 * X + 2 * D + 4 * R, R), ("hr@rhoC", 2 * F + 2 * X + 2 * D + 5 * R, R),
   ("bH-bits-0", 2 * F + 2 * X + 2 * D + 6 * R, B),
   ("bH-bits-1", 2 * F + 2 * X + 2 * D + 6 * R + B, B),
   ("bH-pin", 2 * F + 2 * X + 2 * D + 6 * R + 2 * B, B)]

/-- A read's name in the table of tables, as the seat has it. -/
def nameOfN : FinalNorm.Read → String
  | .streamAtSquares => "xbL@Z_V" | .streamAtNormed => "xbL@Y_N"
  | .actAtKeys => "hd@zt_FC" | .rowAtKeys => "hr@zt_ROW" | .rowAtPV => "hr@P_V"
  | .rowAtProducts => "hr@r_tV" | .rowAtNormed => "hr@rt_N"

/-- All names that the seat's reader takes. -/
def seatNames : List String :=
  [nameOfN .streamAtSquares, nameOfN .streamAtNormed, nameOfN .actAtKeys, nameOfN .rowAtKeys,
   nameOfN .rowAtPV, nameOfN .rowAtProducts, nameOfN .rowAtNormed, "hf@Z",
   nameOf .wideAtKeys, nameOf .wideAtCosts, nameOf .actAtLogits, nameOf .rowAtCosts,
   nameOf .rowCount]

/-- A read's first entry and length at the table. -/
def lineOfN (F X D R : ℕ) : FinalNorm.Read → ℕ × ℕ
  | .streamAtSquares => (2 * F, X) | .streamAtNormed => (2 * F + X, X)
  | .actAtKeys => (2 * F + 2 * X, D) | .rowAtKeys => (2 * F + 2 * X + 2 * D, R)
  | .rowAtPV => (2 * F + 2 * X + 2 * D + R, R) | .rowAtProducts => (2 * F + 2 * X + 2 * D + 2 * R, R)
  | .rowAtNormed => (2 * F + 2 * X + 2 * D + 3 * R, R)

@[inherit_doc lineOfN] def lineOf (F X D R : ℕ) : Read → ℕ × ℕ
  | .wideAtKeys => (0, F) | .wideAtCosts => (F, F) | .actAtLogits => (2 * F + 2 * X + D, D)
  | .rowAtCosts => (2 * F + 2 * X + 2 * D + 4 * R, R) | .rowCount => (2 * F + 2 * X + 2 * D + 5 * R, R)

/-- The normalization's seven names, each with its line. -/
theorem find_seven (F X D R B : ℕ) (r : FinalNorm.Read) :
    (tabAtC F X D R B).find? (fun e => e.1 == nameOfN r) = some (nameOfN r, lineOfN F X D R r) := by
  cases r <;> rfl

/-- The head's five names, each with its line. -/
theorem find_five' (F X D R B : ℕ) (r : Read) :
    (tabAtC F X D R B).find? (fun e => e.1 == nameOf r) = some (nameOf r, lineOf F X D R r) := by
  cases r <;> rfl

/-- **EVERY NAME THAT THE SEAT READS IS IN THE TABLE.** -/
theorem names_in_tab (F X D R B : ℕ) (n : String) (hn : n ∈ seatNames) :
    ((tabAtC F X D R B).find? fun e => e.1 == n).isSome = true := by
  simp only [seatNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The lengths -/

/-- The length of a read's table in the vector of reads. -/
def widthOfN (h : Shape) (L : HL) (b : Border) : FinalNorm.Read → Nat
  | .streamAtSquares | .streamAtNormed => 1 * (b.kxb * (b.mxb / 2 ^ h.la))
  | .actAtKeys => 1 * (L.kD * (L.mD / h.T))
  | .rowAtKeys | .rowAtPV | .rowAtProducts | .rowAtNormed => 1 * (L.kR * (L.mR / h.T))

/-- A PREMISE ON THE LAYERS' LAYOUT's NUMBERS: the stream's five limbs fit its table. -/
def StreamFits (h : Shape) (b : Border) : Prop :=
  5 * h.d / h.S2 ≤ 1 * (b.kxb * (b.mxb / 2 ^ h.la))

/-- **Each of the seven reads is no longer than its table.** -/
theorem readLenN_fits (h : Shape) (L : HL) (b : Border) (hL : numbers h = .ok L)
    (hla : h.lt ≤ h.la) (hXL : h.XL = 5) (hX : StreamFits h b) (r : FinalNorm.Read) :
    @readLenN (sizesOf h) r ≤ widthOfN h L b r := by
  have hA := readLen_fits h L hL hla hXL .actAtLogits
  have hR := readLen_fits h L hL hla hXL .rowCount
  have hR' : NR + 21 ≤ 1 * (L.kR * (L.mR / h.T)) := hR
  cases r with
  | streamAtSquares => exact hX
  | streamAtNormed => exact hX
  | actAtKeys => exact hA
  | rowAtKeys => exact hR
  | rowAtPV => exact Nat.le_trans (Nat.le_add_right _ _) hR'
  | rowAtProducts => exact Nat.le_trans (Nat.le_add_right _ _) hR'
  | rowAtNormed => exact Nat.le_trans (Nat.le_add_right _ _) hR'

/-- The normalization's share of the wide read is within the head's, and so within the table. -/
theorem wideLenN_fits (h : Shape) (L : HL) (hL : numbers h = .ok L) (hla : h.lt ≤ h.la)
    (hXL : h.XL = 5) : @wideLenN (sizesOf h) ≤ widthOf h L .wideAtKeys := by
  refine Nat.le_trans ?_ (readLen_fits h L hL hla hXL .wideAtKeys)
  exact Nat.div_le_div_right (Nat.le_add_right _ _)

/-- Where the text's place of the stream's limb l is `verify-on-bytes`'s. -/
theorem stream_at_zero (b : Border) (dd : Nat) (h0 : b.off = 0) (hJ : b.cnt * b.J = dd) (l : Nat) :
    b.cell l 0 = l * dd := by
  show b.off + (l * b.cnt + 0) * b.J + 0 = l * dd
  rw [h0, ← hJ]
  ring

/-! ## At the record -/

/-- **Every entry of a read of the normalization's below the length spent lies inside the read's own table**, and so
does its share of the wide read. -/
theorem seat_entryN_within (h : Shape) (iU3 : Nat) (s : S) (x : FinalNorm.Reads × Reads)
    (hx : (seatAt h iU3).reads s = some x) (L : HL) (b : Border) (hL : numbers h = .ok L)
    (hla : h.lt ≤ h.la) (hXL : h.XL = 5) (hX : StreamFits h b)
    (o : VerifiableInference.Desc.First.HeadOwn) (tt : OnBytes.Model.Head.Tables)
    (ho : s.here = .head o) (ht : o.t = some tt) (B : Nat)
    (htab : tt.tab = tabAtC (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
      (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) B) :
    ∃ cols : Nat,
      (∀ r i, i < @readLenN (sizesOf h) r → ∃ pos base,
        x.1.entry r i = Aff.ent iU3 (pos / cols) (pos % cols) ∧
          tt.tab.find? (fun e => e.1 == nameOfN r) = some (nameOfN r, base, widthOfN h L b r) ∧
          base ≤ pos ∧ pos < base + widthOfN h L b r) ∧
      ∀ i, i < @wideLenN (sizesOf h) → ∃ pos,
        x.1.wide i = Aff.ent iU3 (pos / cols) (pos % cols) ∧
          tt.tab.find? (fun e => e.1 == "hf@Z") = some ("hf@Z", 0, widthOf h L .wideAtKeys) ∧
          pos < widthOf h L .wideAtKeys := by
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
    refine ⟨tr.K, fun r i hi => ?_, fun i hi => ?_⟩
    · have hf := find_seven (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
        (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) B r
      rw [← htab] at hf
      have hw : (lineOfN (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
          (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) r).2 = widthOfN h L b r := by
        cases r <;> rfl
      refine ⟨(lineOfN (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
          (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) r).1 + i, _, ?_, ?_,
          Nat.le_add_right _ _, ?_⟩
      · have hb : ((tt.tab.find? fun e => e.1 == nameOfN r).map (·.2.1)).getD 0 =
            (lineOfN (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
              (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) r).1 := by
          rw [hf]; rfl
        rw [← hb]
        cases r <;> rfl
      · rw [hf, ← hw]
      · have := readLenN_fits h L b hL hla hXL hX r
        omega
    · have hf := find_five' (widthOf h L .wideAtKeys) (widthOfN h L b .streamAtSquares)
        (widthOfN h L b .actAtKeys) (widthOfN h L b .rowAtKeys) B .wideAtKeys
      rw [← htab] at hf
      refine ⟨0 + i, ?_, hf, ?_⟩
      · have hb : ((tt.tab.find? fun e => e.1 == "hf@Z").map (·.2.1)).getD 0 = 0 := by
          have hf' : tt.tab.find? (fun e => e.1 == "hf@Z") = _ := hf
          rw [hf']; rfl
        have e : ∀ c : Nat, Aff.ent iU3
            ((((tt.tab.find? fun e => e.1 == "hf@Z").map (·.2.1)).getD 0 + i) / c)
            ((((tt.tab.find? fun e => e.1 == "hf@Z").map (·.2.1)).getD 0 + i) % c)
            = Aff.ent iU3 ((0 + i) / c) ((0 + i) % c) := fun c => by rw [hb]
        exact e _
      · have := wideLenN_fits h L hL hla hXL
        omega
  · cases hx

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.names_in_tab
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readLenN_fits
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seat_entryN_within
