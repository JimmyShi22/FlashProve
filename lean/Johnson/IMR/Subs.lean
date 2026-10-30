-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/Subs.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
 A LAW ABOUT ProofFile.subsOf: the row of links that onlineDescription hands the driver (ProofFile.subsOf Z), in the
goals' scope: layers at 2 g, attention at 2 g + 1 (g < 12), the head at 24.
OBJECT. ProofFile.subsOf Z (Johnson/Desc/ProofFile/Frames1.lean). USER. The seats. LETTERS. Z: pubPlain's value · G₀: the blank letters.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

What is not claimed. Nothing outside the scope. No soundness.
-/
import Johnson.IMR.PureJoin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.L5.LinksOrder (zipped)
open VerifiableInference.Desc.First (ModelPart)

/-- A link of the list that is run has the built link's kind. -/
theorem zipped_kind {B : Stages.LinksH} {ls : Array Stages.LinkH} {j : ℕ} {l : Stages.LinkH}
    (h : (zipped B ls)[j]? = some l) : ∃ b, B.links[j]? = some b ∧ b.kind = l.kind := by
  unfold zipped at h
  rw [Array.getElem?_zipWith] at h
  cases hb : B.links[j]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hl : ls[j]? with
    | none => rw [hl] at h; cases h
    | some x =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl⟩

theorem subs_of_kind {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {j : ℕ} {l : LinkH}
    (a : G₀.built[j]? = some l) : (ProofFile.subsOf Z)[j]? = some (ProofFile.subOf l.kind) := by
  obtain ⟨ls, -, -, eB, -⟩ := blank_ground hG
  rw [eB] at a
  obtain ⟨b, hb, kb⟩ := zipped_kind a
  unfold ProofFile.subsOf
  rw [List.getElem?_map, Array.getElem?_toList, hb]
  show some (ProofFile.subOf b.kind) = _
  rw [kb]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **In scope the driver's row of links has layers at 2 g.** -/
theorem subs_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {g : ℕ} (hg : g < 12) :
    (ProofFile.subsOf Z)[2 * g]? = some .layers := by
  obtain ⟨nam, -⟩ := ground_named hS hR hZ hG
  obtain ⟨l, -, a, ka, -⟩ := nam g hg
  rw [subs_of_kind hG a, ka]
  rfl

/-- Attention at 2 g + 1. -/
theorem subs_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {g : ℕ} (hg : g < 12) :
    (ProofFile.subsOf Z)[2 * g + 1]? = some .attention := by
  obtain ⟨nam, -⟩ := ground_named hS hR hZ hG
  obtain ⟨-, l', -, -, -, -, a, ka, -⟩ := nam g hg
  rw [subs_of_kind hG a, ka]
  rfl

/-- The head at 24. -/
theorem subs_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    (ProofFile.subsOf Z)[24]? = some .head := by
  obtain ⟨-, m, fm, km, -⟩ := ground_named hS hR hZ hG
  rw [subs_of_kind hG fm, km]
  rfl

end

end IM

#print axioms IM.subs_at
#print axioms IM.subs_att
#print axioms IM.subs_head
