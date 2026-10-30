-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LinkZeroKept.lean (kind K10): AT LINK 0 THE SWITCH's WRITTEN ROW AND
THE FIVE-LIST HAVE THE SAME KEPT ROWS, NUMBER BY NUMBER: what `hCar_ren`
(Johnson/Desc/First/Link/Law/HCarRen.lean) asks of the row at link 0. Statements and proofs;
evaluations by the kernel.

Why. K10's typed group at link 0 is cut over `loFive` (LinkZeroFive.lean, beside this file); the
switch's own row there bears the six messages' list. `hCar_ren` ties the two by one sentence on
numbers: at every number n the two lists' messages number n have as many kept rows (`keptRowsAt`,
KeptEquiv.lean). The kept messages of link 0 stand in front of the struck one: so their numbers are
the same in both lists.
  `keptLikeFive r`: the test: r's list has at most 6 messages; its radius is at most the written
    one; at every n below 6 the kept rows agree. `zeroKeptB`: row 0 of the written table
    (`tableFullLit`) passes: by the kernel.
  NEGATIVE LINES, by the kernel: `zeroKeptB_next`: row 1 does not pass; `zeroKept_next_rows`: IT
    FALLS AT THE KEPT ROWS: these alone say no there; `zeroKept_next_rest`: the two other clauses
    say yes there. `zeroKept_notIdle`: at row 0 some message has kept rows: the sentence is not 0 =
    0 throughout.
  `zero_front`, `zero_gs`: row 0's group in front r.g is one of the three written ones and has the
    six-list's number of row variables (`five_corners_at`'s premise): SO gs := r.g MAY BE LAID AT
    LINK 0; then the law's stage `stageOf gs 219` is the row's.
  `zero_like`, `zero_kept`: at that row, at EVERY n, the kept rows agree (by `keptRows_of_below`).
    `zero_hr`: the three things that `hCar_ren` asks of the row, at s := `stageOf r.g 219`, e :=
    `radFull`, lo := `loFive`, kb := `kbFive`.
Limits. Closed facts on written values. That the switch's row at a file's plan IS the written
table's is not this file's. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LinkZeroFive
import Johnson.Desc.First.Link.Law.KeptEquiv
import Johnson.Top.H0.K2Caller.TableWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.LinkJoin (keptRowsAt keptRows_of_below)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)

/-- The test on a row of the switch's table. -/
def keptLikeFive (r : SwRow) : Bool :=
  decide (r.lo.length ≤ 6) && decide (r.rad ≤ radFull) &&
    (List.range 6).all fun n =>
      keptRowsAt r.lo r.mem r.kp n ==
        keptRowsAt loFive (memMain loFive) (fun a => kbFive a.1 = true) n

theorem zeroKeptB : (tableFullLit[0]?).any keptLikeFive = true := by decide +kernel

/-- A negative line: the next row does not pass. -/
theorem zeroKeptB_next : (tableFullLit[1]?).any keptLikeFive = false := by decide +kernel

/-- The negative line falls AT THE KEPT ROWS: these alone say no at the next row. -/
theorem zeroKept_next_rows :
    (tableFullLit[1]?).any (fun r => (List.range 6).all fun n =>
      keptRowsAt r.lo r.mem r.kp n ==
        keptRowsAt loFive (memMain loFive) (fun a => kbFive a.1 = true) n) = false := by
  decide +kernel

/-- The next row passes the two other clauses of the test. -/
theorem zeroKept_next_rest :
    (tableFullLit[1]?).any (fun r => decide (r.lo.length ≤ 6) && decide (r.rad ≤ radFull)) =
      true := by decide +kernel

/-- Row 0's group in front is one of the three written ones, with the six-list's number of row
variables: so it may be laid for gs at link 0. -/
theorem zero_front :
    (tableFullLit[0]?).any (fun r => decide (r.g ∈ frontFull) &&
      decide (r.g.k = kLay loSix kbSix)) = true := by decide +kernel

theorem zero_gs (r : SwRow) (hr : tableFullLit[0]? = some r) :
    r.g ∈ frontFull ∧ r.g.k = kLay loSix kbSix := by
  have h := zero_front
  rw [hr] at h
  have h' : (decide (r.g ∈ frontFull) && decide (r.g.k = kLay loSix kbSix)) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨of_decide_eq_true h'.1, of_decide_eq_true h'.2⟩

/-- The sentence is not idle: some message of row 0 has kept rows. -/
theorem zeroKept_notIdle :
    (tableFullLit[0]?).any (fun r => (List.range 6).any fun n =>
      keptRowsAt r.lo r.mem r.kp n != 0) = true := by decide +kernel

theorem zero_like (r : SwRow) (hr : tableFullLit[0]? = some r) : keptLikeFive r = true := by
  have h := zeroKeptB
  rw [hr] at h
  exact h

/-- **The kept rows agree at every number.** -/
theorem zero_kept (r : SwRow) (hr : tableFullLit[0]? = some r) (n : ℕ) :
    keptRowsAt r.lo r.mem r.kp n =
      keptRowsAt loFive (memMain loFive) (fun a => kbFive a.1 = true) n := by
  have h := zero_like r hr
  unfold keptLikeFive at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine keptRows_of_below _ _ _ _ _ _ 6 (of_decide_eq_true h.1.1)
    (by rw [five_length]; omega) (fun m hm => ?_) n
  exact beq_iff_eq.1 (List.all_eq_true.1 h.2 m (List.mem_range.2 hm))

/-- **What hCar_ren asks of the row, at link 0.** -/
theorem zero_hr (r : SwRow) (hr : tableFullLit[0]? = some r) :
    (∃ t₀, stageOf r.g 219 = stageOf r.g t₀) ∧
      (∀ n, keptRowsAt r.lo r.mem r.kp n =
        keptRowsAt loFive (memMain loFive) (fun a => kbFive a.1 = true) n) ∧ r.rad ≤ radFull := by
  have h := zero_like r hr
  unfold keptLikeFive at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨⟨219, rfl⟩, zero_kept r hr, of_decide_eq_true h.1.2⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.zeroKeptB
#print axioms VerifiableInference.Desc.First.Close.zeroKeptB_next
#print axioms VerifiableInference.Desc.First.Close.zeroKept_next_rows
#print axioms VerifiableInference.Desc.First.Close.zeroKept_next_rest
#print axioms VerifiableInference.Desc.First.Close.zero_front
#print axioms VerifiableInference.Desc.First.Close.zero_gs
#print axioms VerifiableInference.Desc.First.Close.zeroKept_notIdle
#print axioms VerifiableInference.Desc.First.Close.zero_like
#print axioms VerifiableInference.Desc.First.Close.zero_kept
#print axioms VerifiableInference.Desc.First.Close.zero_hr
