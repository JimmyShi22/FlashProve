-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedFromSeat.lean.
WHAT IT DOES NOT SHOW. No soundness. FOUR PREMISES ARE OTHER LAWS' AND ARE PAID BY NOBODY HERE: h0:
the
forms that the runs state at the fillings N, R are worth 0 in a world W with the ledger's and the
mask's slots (the batching's) · A: below each read's length the fillings' entries are worth, in
that
world, the reads in truth (the smallness test's tie, and that the run's weights are the kind's
letters) · hW: the claim on the weights is true (the merge's) · B, h6: the heard variables name no
entry, and one of them has a canonical constant (a hearing's return). NOT K6Out: "join"'s form, and
the readers of a record, are not here.
LETTERS. No "there is". N, R: any fillings (meant: what a seat's reads answer) · W: any world whose
slots are the ledger's and the mask's (hs): its entries are what was sent, read in the field.
OBJECT. Law/RowAtDecide.lean's OpenedAt g H G c mask.
USER. The last step from "the claims that the seat's runs state are worth 0" to what the output
head's row opens.
WHAT IT IS. WHAT THE ROW OPENS, FROM THE FORMS AS A SEAT STATES THEM.
  slots_same        the worlds of one ledger and mask at two tables of sent reads have the same
  slots.
  okE_form          each of the 35 forms has a canonical constant.
  opened_forms      the 35 at the reads in truth are 0 AS ELEMENTS, in the world that looks at no
                    entry.
  openedAt_of_seat  so OpenedAt.

-/
import Johnson.Desc.Kinds.Law.AlikeWorth
import Johnson.Desc.Kinds.Law.OpenedAll
import Johnson.Desc.Kinds.Law.RowAtDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)

/-- One ledger and mask, two tables of sent reads: the same slots. -/
theorem slots_same (G : Fork) (mask : Nat → E) (ent ent' : Nat → Nat → Nat → E) :
    ∀ j, (worldE G mask ent).slot j = (worldE G mask ent').slot j := fun _ => rfl

section

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- Each of the 35 forms has a canonical constant. -/
theorem okE_form (N : FinalNorm.Reads) (R : Reads)
    (h6 : okE (Norm.P.getD 6 {}).var.const = true) :
    ∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → okE f.const = true := by
  intro name fs hl f hf
  unfold claimsAt claims at hl
  simp only [List.lookup_cons, List.lookup_nil] at hl
  split at hl
  · obtain rfl := Option.some.inj hl
    exact @okE_normForm _ _ _ _ _ _ _ N h6 f hf
  · split at hl
    · obtain rfl := Option.some.inj hl
      unfold policy at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact okE_addMul _ _ _
      · exact okE_addMul _ _ _
      · exact okE_addMul _ _ _
      · exact okE_addMul _ _ _
    · split at hl
      · obtain rfl := Option.some.inj hl
        unfold logitForms at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact okE_left _ _
        · exact okE_addMul _ _ _
      · cases hl

/-- **THE 35 AT THE READS IN TRUTH ARE 0, AS ELEMENTS.** -/
theorem opened_forms (G : Fork) (mask : Nat → E) (W : World K)
    (hs : ∀ j, W.slot j = (worldE G mask noEnt).slot j) (c : NCells)
    (N : FinalNorm.Reads) (R : Reads)
    (A : EntriesAlike W (worldE G mask noEnt) N (normReadsAtCells c) R (readsAt c.toCells))
    (B : HeardBare) (hd : S2 ∣ d) (h6 : okE (Norm.P.getD 6 {}).var.const = true)
    (h0 : ∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → vW W f = 0) :
    ∀ name fs, (claimsAt (normReadsAtCells c) (readsAt c.toCells)).lookup name = some fs →
      ∀ f, f ∈ fs → atWorld G mask noEnt f = 0 := by
  intro name fs hl f hf
  apply zero_of_rd (okE_atWorld G mask noEnt f (okE_form _ _ h6 name fs hl f hf))
  rw [rd_atWorld]
  exact zero_claims _ _ hs N _ R _ A B hd h0 name fs hl f hf

end

/-- **WHAT THE ROW OPENS, FROM THE FORMS AS A SEAT STATES THEM.** -/
theorem openedAt_of_seat (g : Given) (H : HeardAll) (G : Fork) (c : NCells) (mask : Nat → E)
    (W : World K) (hs : ∀ j, W.slot j = (worldE G mask noEnt).slot j) (N : FinalNorm.Reads)
    (R : Reads) :
    let _ : Norm.Heard := H.1
    let _ : FinalNorm.Heard := H.2.1
    let _ : Heard := H.2.2
    EntriesAlike W (worldE G mask noEnt) N (normReadsAtCells c) R (readsAt c.toCells) →
    HeardBare → S2 ∣ d → okE (Norm.P.getD 6 {}).var.const = true →
    WeightTrue c.toCells G mask noEnt →
    (∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → vW W f = 0) →
    OpenedAt g H G c mask := by
  intro _ _ _ A B hd h6 hW h0
  exact ⟨hW, opened_forms G mask W hs c N R A B hd h6 h0⟩

end VerifiableInference.Desc.Kinds.Head.Law
