-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SlotsOfFrame.lean: the typed caller's kept slots are a public frame's kept
rows, under a test on public lists.
The caller of the code switch at a place's numbers r (`SwRow`, Row.lean) keeps whole members: its
slots are
`((rowsAt r H t₀ oM oZ).keep r.kp).Kp`: a kept member of the typed group and one of its main rows. A
frame W of the programs (`OnBytes.SwitchFrame`) lists the kept members in the order of sending, each
with its number of main rows.
`SwRow.keptAt r W`: THE TEST, on two public lists, BY PLACE: the numbers of rows of W's kept members
are, in order, the numbers of main rows of the messages of r.lo that r.kept names. It reads none of
a frame's three kinds of message numbers (g, old, anew): r numbers the old group's messages
by their places in r.lo, a frame of the programs by the statement's own numbers.
`keptIdx`: under the test, the kept members of the typed group, one to one onto the places of
W.kept. `keptIdx_kept`: r.kept holds the member's number at that place. `keptIdx_rows`: the member's
main rows are as many as the place's.
`slotsEquiv`: so the slots, one to one onto the pairs (place of W.kept, row below its number of
rows). `slotsEquiv_kept`, `slotsEquiv_row`: what it does to a slot.
Limits. The test is a premise: that it says yes at any r and frame is not shown here. Nothing
is said on the other fields of a frame. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.Row
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR

namespace SwRow

/-- **The test**, by place: the frame's kept members have, in order, the numbers of main rows of the
kept members that r names. -/
def keptAt (r : SwRow) (W : OnBytes.SwitchFrame) : Bool :=
  decide (W.kept.map (·.rows) =
    r.kept.map fun i => ((r.lo[i]?).map fun x => x.1.mainRows).getD 0)

variable {r : SwRow}

theorem OK.kept_lt (H : r.OK) {i : ℕ} (hi : i ∈ r.kept) : i < r.lo.length := by
  have h := H.kept i hi
  by_contra k
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

theorem OK.keptNat_mem (H : r.OK) {i : ℕ} (hi : i ∈ r.kept) : r.mem ⟨i, H.kept_lt hi⟩ := by
  have h := H.kept i hi
  rw [List.getElem?_eq_getElem (H.kept_lt hi)] at h
  simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem keptAt_rows {W : OnBytes.SwitchFrame} (h : r.keptAt W = true) :
    W.kept.map (·.rows) = r.kept.map fun i => ((r.lo[i]?).map fun x => x.1.mainRows).getD 0 := by
  unfold keptAt at h
  exact of_decide_eq_true h

theorem keptAt_length {W : OnBytes.SwitchFrame} (h : r.keptAt W = true) :
    r.kept.length = W.kept.length := by
  have e := congrArg List.length (keptAt_rows h)
  rw [List.length_map, List.length_map] at e
  exact e.symm

end SwRow

open SwRow

section
variable {r : SwRow} (H : r.OK) {W : OnBytes.SwitchFrame} (h : r.keptAt W = true)

/-- The kept members of the typed group, as the numbers in the list r.kept. -/
def keptNat : {a : {i // r.mem i} // r.kp a} ≃ {x : ℕ // x ∈ r.kept} where
  toFun a := ⟨a.1.1.val, a.2⟩
  invFun x := ⟨⟨⟨x.1, H.kept_lt x.2⟩, H.keptNat_mem x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The kept members of the typed group, one to one onto the places of the frame's list.** -/
def keptIdx : {a : {i // r.mem i} // r.kp a} ≃ Fin W.kept.length :=
  (keptNat H).trans (((List.Nodup.getEquiv r.kept H.nodup).symm).trans (finCongr (keptAt_length h)))

/-- The list r.kept at a member's place holds the member's number. -/
theorem keptIdx_kept (a : {a : {i // r.mem i} // r.kp a}) :
    r.kept[(keptIdx H h a).val]? = some a.1.1.val := by
  have e : (List.Nodup.getEquiv r.kept H.nodup)
      ((List.Nodup.getEquiv r.kept H.nodup).symm (keptNat H a)) = keptNat H a :=
    Equiv.apply_symm_apply _ _
  have e' := congrArg Subtype.val e
  have hl : ((List.Nodup.getEquiv r.kept H.nodup).symm (keptNat H a)).val < r.kept.length :=
    ((List.Nodup.getEquiv r.kept H.nodup).symm (keptNat H a)).isLt
  show r.kept[((List.Nodup.getEquiv r.kept H.nodup).symm (keptNat H a)).val]? = _
  rw [List.getElem?_eq_getElem hl]
  exact congrArg some e'

/-- **The member has as many main rows as the place says.** -/
theorem keptIdx_rows (a : {a : {i // r.mem i} // r.kp a}) :
    (r.lo.get a.1.1).1.mainRows = (W.kept.get (keptIdx H h a)).rows := by
  have e := congrArg (fun l : List ℕ => l[(keptIdx H h a).val]?) (keptAt_rows h)
  simp only [List.getElem?_map] at e
  rw [keptIdx_kept H h a, List.getElem?_eq_getElem (keptIdx H h a).isLt] at e
  simp only [Option.map_some, Option.some.injEq] at e
  rw [List.getElem?_eq_getElem a.1.1.isLt] at e
  exact e.symm

variable (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

/-- **The typed caller's slots, one to one onto the frame's kept rows.** -/
noncomputable def slotsEquiv : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp ≃
    Σ a : Fin W.kept.length, Fin (W.kept.get a).rows :=
  Equiv.sigmaCongr (keptIdx H h) fun a => finCongr (keptIdx_rows H h a)

/-- At the slot's place the list r.kept holds the number of the slot's member. -/
theorem slotsEquiv_kept (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) :
    r.kept[(slotsEquiv H h t₀ oM oZ κ).1.val]? = some κ.1.1.1.val :=
  keptIdx_kept H h κ.1

/-- The slot's row stays. -/
theorem slotsEquiv_row (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) :
    (slotsEquiv H h t₀ oM oZ κ).2.val = κ.2.val := rfl

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptIdx_kept
#print axioms VerifiableInference.Desc.First.K2Caller.keptIdx_rows
#print axioms VerifiableInference.Desc.First.K2Caller.slotsEquiv
#print axioms VerifiableInference.Desc.First.K2Caller.slotsEquiv_kept
#print axioms VerifiableInference.Desc.First.K2Caller.slotsEquiv_row
