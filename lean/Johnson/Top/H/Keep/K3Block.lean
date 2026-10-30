-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/K3Block.lean: The kind "lookup" (K3): EVERY STEP OF ITS BLOCK, in the
form of Johnson/Desc/Part/LedgerKeeps.lean's stepsOf (the decision; each run of claims; each run
behind the batching), HAS THE LAW "a stretch that is owed stays owed" UNDER K3's PROMISE. Statements
and proofs. The promises and the single steps' laws: Johnson/Top/H/Keep/K3Inv.lean, K3Start.lean.

Main names:
  same_keeps: a step that leaves the record has the law under every promise.
  guestsRun: the run "guests", as K3.block states it. guests_same: its yes leaves the record.
  block_steps: the block's steps are three: its decision, "objects", "guests": by rfl.
  caller_steps: with "planes" stated behind (K3Runs.lean's withCaller): four.
  block_keepsA, caller_keepsA: role (A): beside another's stretch: ALL steps of the block, and of
    the block with "planes".
  block_keepsB: role (B): at K3's own stretch: all steps of the block WITHOUT "planes", which is
    the stretch's own writer.

Limits. The run "join" is stated by no block here (a calling kind's): its law is
Johnson/Top/H/Keep/K3Inv.lean's join_keepsA | join_keepsB. K3.block, not the seated Law.blockVia.
The limits of the two files named above hold here too.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (Seat SeatReads planesRun Readers withCaller)
open VerifiableInference.Desc.Part (StepKeepsUnder decides stepsOf)

variable {S Cl : Type}

/-- A step that leaves the record has the law under every promise. -/
theorem same_keeps (Inv : S → Prop) (ledger? : S → Option Fork) (a n : ℕ) (r : S → S → Prop)
    (h : ∀ s s', r s s' → s' = s) : StepKeepsUnder Inv ledger? a n r := by
  intro s s' F hI hr hF ho
  obtain rfl := h s s' hr
  exact ⟨hI, F, hF, Later.refl F, ho⟩

/-- The run "guests", as K3.block states it. -/
def guestsRun (guests : List (Desc.First.Look.Guest S Cl)) (_ : ℕ) (s : S) :
    Except String (List Cl × S) :=
  named "K3 guests: a guest refuses"
    ((guests.mapM fun (g : Desc.First.Look.Guest S Cl) => g.form s).map fun l => (l, s))

/-- Its yes leaves the record. -/
theorem guests_same (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
    (h : runStep (guestsRun guests) s s') : s' = s := by
  obtain ⟨i, l, h⟩ := h
  unfold guestsRun at h
  cases ho : (guests.mapM fun (g : Desc.First.Look.Guest S Cl) => g.form s) with
  | none =>
    rw [ho] at h
    cases h
  | some x =>
    rw [ho] at h
    exact (congrArg Prod.snd (Except.ok.inj h)).symm

section
variable (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))

/-- **The block's steps.** -/
theorem block_steps :
    stepsOf (Desc.K3.block seat piece laid before p guests) =
      [decides (Desc.K3.block seat piece laid before p guests), runStep (objectsRun seat),
        runStep (guestsRun guests)] := rfl

/-- **With "planes" stated behind.** -/
theorem caller_steps (readers : Readers S) :
    stepsOf (withCaller seat p readers (Desc.K3.block seat piece laid before p guests)) =
      [decides (Desc.K3.block seat piece laid before p guests), runStep (objectsRun seat),
        runStep (guestsRun guests), runStep (planesRun seat p.lm readers)] := rfl

variable (form : Cl → Aff) (hs : SeatFits seat form) (hk : SeatKeeps seat) (hr : SeatReads seat)
include hs hk hr

/-- **Role (A): every step of the block.** -/
theorem block_keepsA (a n : ℕ) :
    ∀ r ∈ stepsOf (Desc.K3.block seat piece laid before p guests),
      StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n r := by
  intro r hm
  rw [block_steps] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact decide_keepsA seat piece laid before p guests hk hr a n
  · exact objects_keepsA seat form hs a n
  · exact same_keeps _ _ a n _ (guests_same guests)

/-- **Role (A): every step of the block with "planes".** -/
theorem caller_keepsA (readers : Readers S) (a n : ℕ) :
    ∀ r ∈ stepsOf (withCaller seat p readers (Desc.K3.block seat piece laid before p guests)),
      StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n r := by
  intro r hm
  rw [caller_steps] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact decide_keepsA seat piece laid before p guests hk hr a n
  · exact objects_keepsA seat form hs a n
  · exact same_keeps _ _ a n _ (guests_same guests)
  · exact planes_keepsA seat form hs a n p.lm readers

omit hk hr in
/-- **Role (B): every step of the block without "planes".** -/
theorem block_keepsB (g : Forest.Heard) (a n : ℕ) :
    ∀ r ∈ stepsOf (Desc.K3.block seat piece laid before p guests),
      StepKeepsUnder (K3InvB seat.fork seat.heard g) seat.fork a n r := by
  intro r hm
  rw [block_steps] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact decide_keepsB seat piece laid before p guests g a n
  · exact objects_keepsB seat form hs g a n
  · exact same_keeps _ _ a n _ (guests_same guests)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.block_steps
#print axioms VerifiableInference.OnPublicFiles.caller_steps
#print axioms VerifiableInference.OnPublicFiles.block_keepsA
#print axioms VerifiableInference.OnPublicFiles.caller_keepsA
#print axioms VerifiableInference.OnPublicFiles.block_keepsB
