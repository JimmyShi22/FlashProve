-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedAll.lean: "OPENED AT THE TRUTH", WHOLE: ALL 35 FORMS OF THE OUTPUT HEAD's THREE RUNS ARE WORTH 0, AND THE CLAIM ON THE
WEIGHTS IS TRUE, at the ledger's world (atWorld G mask, no sent entries), reads READ AS THE STATED SUMS OF THE CELLS
(normReadsAtCells, readsAt), WHERE THE CELLS ARE HONEST AND THE HIDDEN SCALARS ARE THE TRUE ONES. The converse of the reading
of Law/RowWhole.lean. No chance in it. FOR A MEMBER OF K06_law.
  opened_all   its conclusion is, to the letter, the body of OpenedAt (Law/RowAtDecide.lean), which this file does
               not import: WeightTrue ∧ every form of every run of claims is 0.
  ITS PREMISES: the tests on the request · WeightsOk · |zt| = lt · ls ≤ lPd · S2 ∣ d · the block law of remLow's weights ·
               the four points' sizes · THE CELLS: (dataOf c).Holds (the norm's 17 identities at every position) and
               HonestHead (the two guests 0 at every corner; the two plain sums 0) · WHAT WAS HEARD, BY LETTERS:
               NormTruthW at the ledger's world (Law/OpenedNorm.lean) · HeadTruth (Law/OpenedHead.lean) · the seventh hidden
               product's variable has a canonical constant (it is a form of the row by itself; at a hearing's
               return it is a bare slot).
WHAT IT IS NOT. Nothing on soundness. THAT ANY TAPE MEETS NormTruthW AND HeadTruth, AND THAT HONEST CELLS EXIST, IS NOT SHOWN: so this is
no member yet: it is the stone between an honest tape and Opened. "join" (the 36th form) is not here.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedHead
import Johnson.Desc.Kinds.Law.OpenedNorm
import Johnson.Desc.Kinds.Law.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open Came (val)

/-- A sumcheck's own form has a constant that is written canonically. -/
theorem okE_left (s : Sum) (S0 : E) : okE (s.left S0).const = true := by
  unfold Sum.left
  cases s.psc with
  | none =>
    show okE OnBytes.oneE = true
    decide
  | some h => exact okE_addMul _ _ _

variable [Sizes] [Policy] [Request] [Token]

section Forms
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- Every one of the 29 forms has a constant that is written canonically. -/
theorem okE_normForm (h6 : okE (Norm.P.getD 6 {}).var.const = true) {f : Form}
    (hf : f ∈ FinalNorm.forms) : okE f.const = true := by
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rw [squareForms_eq] at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact okE_left _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
      · rw [productForms_eq] at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · exact okE_addMul _ _ _
        · exact okE_left _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
    · rw [rowForms_eq, List.mem_append] at hf
      rcases hf with hf | hf
      · rw [OnBytes.Desc.First.P6.carries_eq] at hf
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
        exact okE_addMul _ _ _
      · rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
          OnBytes.Desc.First.P6.reciprocal_eq] at hf
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
        · show okE (Norm.P.getD (7 * 0 + 6) {}).var.const = true
          rw [Nat.mul_zero, Nat.zero_add]
          exact h6
        · exact okE_addMul _ _ _
        · exact okE_addMul _ _ _
  · simp only [FinalNorm.normedForms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact okE_left _ _
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _

end Forms

/-- **OPENED AT THE TRUTH, WHOLE.** -/
theorem opened_all [FinalNorm.In] [In] (H : HeardAll) (G : Fork) (c : NCells) (mask : Nat → E)
    (hreq : Request.ok = true) (hy : y < V) (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt)
    (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2)) :
    let _ : Norm.Heard := H.1
    let _ : FinalNorm.Heard := H.2.1
    let _ : Heard := H.2.2
    let _ : FinalNorm.Reads := normReadsAtCells c
    let _ : Reads := readsAt c.toCells
    (Norm.pV).size = lt → Norm.squares.r.size = lPd + lt → Norm.products.r.size = lt →
    FinalNorm.normed.r.size = lt →
    (dataOf c).Holds → HonestHead c.toCells →
    NormTruthW (worldE G mask noEnt) c → okE (Norm.P.getD 6 {}).var.const = true →
    HeadTruth c.toCells G mask noEnt →
    WeightTrue c.toCells G mask noEnt ∧
      ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0 := by
  intro _ _ _ _ _ hpV hrS hrP hrN hH hC hN h6 hT
  have hreads : TrueReads c.toCells G mask noEnt := fun _ _ _ => rfl
  obtain ⟨o1, o2, o3⟩ := opened_head c.toCells G mask noEnt hreq hy hw hzt hreads hC hT
  have hNR := Came.normReads_true (worldE G mask noEnt) c hpV hrP
  have hNN : NormedReads (worldE G mask noEnt) c :=
    ⟨fun _ _ => Came.val_coe _ _, fun _ _ => Came.val_coe _ _⟩
  have o0 := opened_norm c (worldE G mask noEnt) hH hls hdS hblock hrS hrN hNR hNN hN
  refine ⟨o1, fun name fs hl f hf => ?_⟩
  unfold claims at hl
  simp only [List.lookup_cons, List.lookup_nil] at hl
  split at hl
  · obtain rfl := Option.some.inj hl
    apply zero_of_rd (okE_atWorld G mask noEnt f (okE_normForm h6 hf))
    rw [rd_atWorld]
    exact o0 f hf
  · split at hl
    · obtain rfl := Option.some.inj hl
      exact o2 f hf
    · split at hl
      · obtain rfl := Option.some.inj hl
        exact o3 f hf
      · cases hl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.opened_all
