-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Scales.lean: publicOfO's STEPS P1's SCAN, P2, P3 AND P6 AT THE STORED
  FULL-SIZE FILES, AS RETURNS: scan_zFull · scales_zFull ·
scales_written · fileWords_zFull: a joining of the library's theorems. The Lean text is that of an
  earlier working file of this
project, which is not in this repository (sha256 9e252717…), from its first import line on, to the
letter. Nothing on soundness.
-/
import Johnson.Goal.Meaning.ScalesReturn
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Trial.AttA5ScalesTie
open OnBytes OnBytes.Tie.Pv.Plan

/-- **The words of a file of words are the list, where every word is below 2^32.** -/
theorem fileWords_wordsFile (l : List Nat) (h : ∀ w ∈ l, w < 4294967296) :
    Model.fileWords (wordsFile l) = l.toArray := by
  unfold Model.fileWords
  rw [VerifierAndGoals.Read.size_wordsFile, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  apply Array.ext
  · simp
  · intro i _ h2
    have hi : i < l.length := by simpa using h2
    simp only [Array.getElem_map, Array.getElem_range, List.getElem_toArray]
    rw [VerifierAndGoals.Read.klWord_wordsFile, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, Nat.mod_eq_of_lt (h _ (List.getElem_mem hi))]

/-- The written words are below 2^32. -/
theorem words_small : (scalesF.all fun w => decide (w < 4294967296)) = true := by decide +kernel

/-- **The words of the stored scale file are the written list.** -/
theorem fileWords_zFull : Model.fileWords VerifierAndGoals.storedPublicFiles.KL = scalesF.toArray := by
  rw [VerifierAndGoals.Read.kl_zFull]
  exact fileWords_wordsFile _ fun w hw => of_decide_eq_true (List.all_eq_true.mp words_small w hw)

end OnBytes.Road.K4.Trial.AttA5ScalesTie


namespace OnBytes.Road.K4.Trial.AttJ1
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Tie.Pv.Plan (scalesF)

/-- The strict scan's WRITTEN value at the stored free numbers. -/
def PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- The layers' shape at that value. -/
def hW : Layer.Shape := Verify.layerShape PW

/-- **The strict scan of the stored parameter file returns the written value.** -/
theorem scan_zFull : polScan VerifierAndGoals.storedPublicFiles.pol = .ok PW := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨P, hP, -⟩ := Meaning.Ret.shape_of_read hZ hR
  rw [hP]
  rw [VerifierAndGoals.pol_zFull] at hP
  exact congrArg Except.ok (VerifierAndGoals.Lines.scan_closed hP)

/-- **The three tests on the stored scale file pass, at the written shape.** -/
theorem scales_zFull : ∃ s, Layer.scalesOf hW (fileWords VerifierAndGoals.storedPublicFiles.KL) = .ok s ∧
    Layer.scalesHeld hW s = .ok () ∧ Layer.noWrap hW s 5120 = .ok () := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨P, hP, hS⟩ := Meaning.Ret.shape_of_read hZ hR
  have eP : P = PW := Except.ok.inj (hP.symm.trans scan_zFull)
  rw [eP] at hS
  obtain ⟨a, b, c⟩ := Meaning.Ret.scales_return hZ hR
  rw [← hS] at a b c
  exact ⟨_, a, b, c⟩

/-- The same with the written list for the file's words. -/
theorem scales_written : ∃ s, Layer.scalesOf hW scalesF.toArray = .ok s ∧
    Layer.scalesHeld hW s = .ok () ∧ Layer.noWrap hW s 5120 = .ok () := by
  have h := scales_zFull
  rw [AttA5ScalesTie.fileWords_zFull] at h
  exact h

end OnBytes.Road.K4.Trial.AttJ1

#print axioms OnBytes.Road.K4.Trial.AttJ1.scan_zFull
#print axioms OnBytes.Road.K4.Trial.AttJ1.scales_zFull
#print axioms OnBytes.Road.K4.Trial.AttJ1.scales_written
