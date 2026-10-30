-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/EntryWireDepth.lean: no tree of an entry's chain is deeper than 63, at the full-size
and at the small files of the setting "record with work": what the reading back of a leaf's body
asks of the rounds' data.

Main theorems.
 `depth_of_within`   for a description within the limits test `withinX`, at any map of statements:
                every round's tree has at most 2^63 positions, in the form
                `posN d.tree + posN d.tree ≤ 2 ^ 64`.
 `fr_wire_depth`, `sr_wire_depth`   that at `frRds` and at `srRds` (OnBytes/Slice/LinkFamily.lean).

Limits: bounds on typed data. Nothing on a wire's laws, on soundness, on bytes or files.

-/
import OnBytes.Slice.EntryWireNums
import Run.OneIsTypedTop

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf withinX)

/-- No tree is deeper than 63, at a description within the limits test. -/
theorem depth_of_within (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinX S = true) :
    ∀ d ∈ (xdOf S stm).ds, posN d.tree + posN d.tree ≤ 2 ^ 64 := by
  have h := within_ok S stm hw
  unfold XD.ok at h
  simp only [Bool.and_eq_true] at h
  have hq : PQ.ok (xdOf S stm).base = true := h.1.1
  have hs := Fmt.ok_small (specOk_of (xdOf S stm).base hq)
  simp only [Fmt.Spec.small, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hc := Fmt.ok_count (specOk_of (xdOf S stm).base hq)
  have h1 := hs.1.1.1.2
  have h2 := hs.2
  have F : FitsS (xdOf S stm).base 0 := by
    refine fitsS_of (xdOf S stm).base 0 hq (by decide) (by omega) (by omega) ?_
    show (xdOf S stm).base.firstTree + ((xdOf S stm).base.rounds.map (·.entry.roots)).sum ≤ 2 ^ 48
    omega
  exact fun d hd => posN_small d.tree fun sh hsh => (F.small d hd sh hsh).2

/-- No tree of the entry's chain is deeper than 63, at the full size. -/
theorem fr_wire_depth : ∀ d ∈ frRds, posN d.tree + posN d.tree ≤ 2 ^ 64 := by
  have h := depth_of_within _ (fun _ _ => ByteArray.empty) fr_within
  intro d hd
  exact h d (fr_ds_C ▸ hd)

/-- The same at the small files. -/
theorem sr_wire_depth : ∀ d ∈ srRds, posN d.tree + posN d.tree ≤ 2 ^ 64 := by
  have h := depth_of_within _ (fun _ _ => ByteArray.empty) sr_within
  intro d hd
  exact h d (sr_ds_C ▸ hd)

end OnBytes.Slice
