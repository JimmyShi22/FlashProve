-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/AlikeLaid.lean: THE GUARD ON THE REPLY: two descriptions that are alike are laid
alike.

What the file is. Alike F F' (Unguarded.lean) says that two descriptions of the proof file part in
the first chain's structure alone, and that the two first chains have one flat list and one last
block's rounds. Here it is shown that whatever is laid of a description for the proof file
(LPFD.Full.proofDataAndDecisionOfDescription, Johnson/Desc/Laid/ProofFull.lean) is then the same for both: the words of
the tests on the plan, the data, the tests that the laws ask, and the decision. The reason is
one: every function on a description that proofDataAndDecisionOfDescription calls reads the first chain through
Chain.blocksInOrder alone, but FileDescription.sealLast, which reads the last block's rounds.

How. In general first: withFirst F c is F with c for its first chain. Under
hf : c.blocksInOrder = F.first.blocksInOrder and hl : c.last.rounds = F.first.last.rounds there is one equation a
function, each by unfolding that one function and rewriting by hf, by hl or by the equations above
it. Then ProofFile.fileDescBy at c' is withFirst of ProofFile.fileDescBy at c (fileDescBy_w: by unfolding: c
goes into the field first and into no other).

Main names.
* withFirst.
* One equation a function of Johnson/Desc/Block.lean: decl_w, places_w, firstTree₃_w, labelsOk_w,
  beforeOk_w, roots_w, bookOk_w, placesOk_w, readsOk_w, sealLast_w, sentFit_w, planOkCore_w,
  planOk_w, planWord_w, run_w; of Johnson/Desc/BlockSlot.lean: data_w.
* Of the proof file's laying: runPOf_w, seatPinnedProof_w, cutRow_w, lawsAsk_w, laidOfDesc_w.
* Alike.w: Alike F F' gives F' = withFirst F c with hf and hl.
* planWord_alike, data_alike, run_alike, laidOfDesc_alike: the same from Alike F F'.

What it leans on. Unguarded.lean (Alike). The library's definitions named above, and
FileDescription.pull_run (Johnson/Desc/Block.lean). No proof is carried from another file.

Limits. That the guarded and the unguarded description are alike is not shown here. Of
FileDescription.wantedOk and FileDescription.owedOk, which proofDataAndDecisionOfDescription does not call, nothing is shown. The full
size's laying alone (LPFD.Full). Nothing on soundness.


-/
import Johnson.LPFGuard.Unguarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference
open VerifiableInference.Desc (Block FileDescription Chain)
open VerifiableInference.Desc.First (S)

/-- F with c for its first chain. -/
@[reducible] def withFirst {Xi : Type} (F : FileDescription Xi) (c : Chain F.S₁ F.Cl) : FileDescription Xi :=
  { F with first := c }

section general

variable {Xi : Type} (F : FileDescription Xi) (c : Chain F.S₁ F.Cl) (hf : c.blocksInOrder = F.first.blocksInOrder)
  (hl : c.last.rounds = F.first.last.rounds)

include hf

theorem decl_w : (withFirst F c).roundsDeclaredByBlocks = F.roundsDeclaredByBlocks := by
  unfold FileDescription.roundsDeclaredByBlocks
  dsimp only [withFirst]
  rw [hf]

theorem places_w : (withFirst F c).places = F.places := by
  unfold FileDescription.places
  dsimp only [withFirst]
  rw [hf]

theorem firstTree₃_w : (withFirst F c).lastChainFirstTreeNumber = F.lastChainFirstTreeNumber := by
  unfold FileDescription.lastChainFirstTreeNumber
  rw [decl_w F c hf]

theorem labelsOk_w : (withFirst F c).labelsOk = F.labelsOk := by
  unfold FileDescription.labelsOk
  rw [decl_w F c hf, firstTree₃_w F c hf]

theorem beforeOk_w : (withFirst F c).beforeOk = F.beforeOk := by
  unfold FileDescription.beforeOk
  rw [decl_w F c hf]
  dsimp only [withFirst]
  rw [hf]

theorem roots_w : (withFirst F c).roots = F.roots := by
  unfold FileDescription.roots
  dsimp only [withFirst]
  rw [hf]

theorem bookOk_w : (withFirst F c).treeSharingOk = F.treeSharingOk := by
  unfold FileDescription.treeSharingOk
  rw [decl_w F c hf, roots_w F c hf]

theorem placesOk_w : (withFirst F c).placesOk = F.placesOk := by
  unfold FileDescription.placesOk
  rw [places_w F c hf]
  dsimp only [withFirst]
  rw [hf]

theorem readsOk_w : (withFirst F c).readsOk = F.readsOk := by
  unfold FileDescription.readsOk
  rw [decl_w F c hf]

theorem sentFit_w : (withFirst F c).sentFit = F.sentFit := by
  unfold FileDescription.sentFit
  rw [decl_w F c hf]
  dsimp only [withFirst]
  rw [hf]

theorem planOkCore_w : (withFirst F c).planOkCore = F.planOkCore := by
  unfold FileDescription.planOkCore
  rw [decl_w F c hf, labelsOk_w F c hf, placesOk_w F c hf, beforeOk_w F c hf, bookOk_w F c hf,
    readsOk_w F c hf, sentFit_w F c hf]
  dsimp only [withFirst]
  rw [hf]

/-- The data of the file's rounds. -/
theorem data_w (file : String) : (withFirst F c).data file = F.data file := by
  unfold FileDescription.data
  rw [decl_w F c hf]

omit hf in
include hl in
theorem sealLast_w : (withFirst F c).sealLast = F.sealLast := by
  unfold FileDescription.sealLast
  dsimp only [withFirst]
  rw [hl]

include hl

theorem planOk_w : (withFirst F c).planOk = F.planOk := by
  unfold FileDescription.planOk
  rw [planOkCore_w F c hf, sealLast_w F c hl]

/-- The words of the refusal on the plan. -/
theorem planWord_w : (withFirst F c).planWord = F.planWord := by
  unfold FileDescription.planWord
  rw [planOk_w F c hf hl, decl_w F c hf, roots_w F c hf]
  dsimp only [withFirst]
  rw [hf]

/-- The decision. -/
theorem run_w (x : Xi) (v₁ v₂ v₃ : Fmt.View) :
    (withFirst F c).run x v₁ v₂ v₃ = F.run x v₁ v₂ v₃ := by
  unfold FileDescription.run FileDescription.runEnd
  rw [planWord_w F c hf hl, firstTree₃_w F c hf]
  dsimp only [withFirst]
  rw [hf]

end general

/-! ## What is laid for the proof file -/

section laid

variable (F : FileDescription ProofFile.Inst) (c : Chain F.S₁ F.Cl) (hf : c.blocksInOrder = F.first.blocksInOrder)
  (hl : c.last.rounds = F.first.last.rounds)

include hf

theorem seatPinnedProof_w (pol : ByteArray) :
    PlanWritten.seatPinnedProof pol (withFirst F c) = PlanWritten.seatPinnedProof pol F := by
  unfold PlanWritten.seatPinnedProof PlanWritten.descPinnedProof PlanWritten.descPinned
  rw [decl_w F c hf]

theorem cutRow_w : PlanWritten.cutRow (withFirst F c) = PlanWritten.cutRow F := by
  funext Z
  unfold PlanWritten.cutRow PlanWritten.cutIs
  dsimp only [withFirst]
  rw [hf]

/-- The tests that the laws ask. -/
theorem lawsAsk_w (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (D : OnBytes.Maker.WholeD) :
    LPFD.lawsAsk o pol lay KL (withFirst F c) D = LPFD.lawsAsk o pol lay KL F D := by
  unfold LPFD.lawsAsk
  rw [seatPinnedProof_w F c hf, cutRow_w F c hf]

include hl

/-- The proof file's decision. -/
theorem runPOf_w : LPFD.Full.proofDecisionOfDescription (withFirst F c) = LPFD.Full.proofDecisionOfDescription F := by
  funext x v₁ v₂ v₃
  unfold LPFD.Full.proofDecisionOfDescription
  rw [FileDescription.pull_run, FileDescription.pull_run]
  exact run_w F c hf hl _ v₁ v₂ v₃

/-- **What is laid, of a description.** -/
theorem laidOfDesc_w (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL (withFirst F c) = LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F := by
  unfold LPFD.Full.proofDataAndDecisionOfDescription
  simp only [planWord_w F c hf hl, data_w F c hf, lawsAsk_w F c hf, runPOf_w F c hf hl]

end laid

/-! ## From Alike -/

/-- The proof file's description takes its first chain into the field first, and into no other. -/
theorem fileDescBy_w (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat) (c c' : Chain S ProofFile.Cl) :
    ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c' =
      withFirst (ProofFile.fileDescBy o mk Z A B (fun s => s) (ProofFile.startS Z) c) c' := rfl

variable {F F' : FileDescription ProofFile.Inst}

/-- Alike, in the general form: F' is F with another first chain, of the same flat list and the
same last block's rounds. The one step that looks into the proof file's description. -/
theorem Alike.w (h : Alike F F') : ∃ c : Chain F.S₁ F.Cl,
    F' = withFirst F c ∧ c.blocksInOrder = F.first.blocksInOrder ∧ c.last.rounds = F.first.last.rounds := by
  obtain ⟨o, mk, Z, A, B, c, c', rfl, rfl, hf, hl⟩ := h
  exact ⟨c', fileDescBy_w o mk Z A B c c', hf, hl⟩

theorem planWord_alike (h : Alike F F') : F'.planWord = F.planWord := by
  obtain ⟨c, rfl, hf, hl⟩ := h.w
  exact planWord_w F c hf hl

theorem data_alike (h : Alike F F') (file : String) : F'.data file = F.data file := by
  obtain ⟨c, rfl, hf, -⟩ := h.w
  exact data_w F c hf file

theorem run_alike (h : Alike F F') (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View) :
    F'.run x v₁ v₂ v₃ = F.run x v₁ v₂ v₃ := by
  obtain ⟨c, rfl, hf, hl⟩ := h.w
  exact run_w F c hf hl x v₁ v₂ v₃

/-- **TWO DESCRIPTIONS THAT ARE ALIKE ARE LAID ALIKE.** -/
theorem laidOfDesc_alike (h : Alike F F') (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F' = LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F := by
  obtain ⟨c, rfl, hf, hl⟩ := h.w
  exact laidOfDesc_w F c hf hl o pol lay KL

#print axioms Alike.w
#print axioms planWord_alike
#print axioms data_alike
#print axioms run_alike
#print axioms laidOfDesc_alike

end LPFGuard
