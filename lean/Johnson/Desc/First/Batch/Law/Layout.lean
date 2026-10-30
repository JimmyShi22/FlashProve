-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Layout.lean
(kind K9's soundness lemma): THEOREMS: two premises made smaller.
  inside_of_layoutOk   the premise "inside" of (T2b) (Law/AsRow.lean: RowPremises) follows from the
                       library's test on a layout: reqLayoutOk codes shape layout = true
                       (OnBytes/Iop/ReqRows.lean): a test with code on public data. Not said here:
                       which step runs that test on the layout that the door reads: until then
                       it is a premise still, of a smaller kind.
  oneK_of_core         a step that keeps the ledger's core (Law/Stages.lean) keeps the value of the
                       one equation, read at any state (the letter "one" of the segment's law).

-/
import Johnson.Desc.First.Batch.Law.Coef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)

/-- **The blocks of a lawful layout lie inside their arrays, and are as large in the table as in the
array.** -/
theorem inside_of_layoutOk (codes : Codes) (s : ReqShape) (layout : ReqLayout)
    (h : reqLayoutOk codes s layout = true) (born : Nat) (name : String) (a : ReqArray)
    (ha : reqArray layout born name = some a) : ∀ b ∈ a.blocks, Inside a b := by
  unfold reqArray at ha
  obtain ⟨arrays, h1, h2⟩ := Option.bind_eq_some_iff.mp ha
  have hmem : a ∈ arrays := List.mem_of_find?_eq_some h2
  simp only [reqLayoutOk, Bool.and_eq_true, beq_iff_eq, zipT_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨hb, e1⟩ := List.getElem?_eq_some_iff.mp h1
  have hb' : born < s.link.length := by rw [← hlen]; exact hb
  have hz : (s.link[born], arrays) ∈ s.link.zip layout.link := by
    rw [List.mem_iff_getElem?]
    refine ⟨born, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hb', h1⟩
  obtain ⟨⟨⟨k1, k2⟩, _⟩, k4⟩ := hall _ hz
  have ok1 := k1 a hmem
  have hm : a.message < s.link[born].messages.length := by simpa using k2 a hmem
  have hzi : (s.link[born].messages[a.message], a.message) ∈ s.link[born].messages.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [hm]
  have ok2 := k4 _ hzi
  have hin : a ∈ arrays.filter fun x => x.message == a.message := by
    simp [List.mem_filter, hmem]
  intro b hbm
  have hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
    simp only [reqArrayOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ok1
    exact (ok1.2 b hbm).1.1.1.1
  simp only [reqMessageLayoutOk, Bool.or_eq_true, Bool.and_eq_true] at ok2
  rcases ok2 with he | ⟨_, hmatch⟩
  · have : (arrays.filter fun x => x.message == a.message) = [] := by simpa using he
    rw [this] at hin
    simp at hin
  · split at hmatch
    · simp only [Bool.and_eq_true, laidOk, List.all_eq_true] at hmatch
      have hmx := hmatch.1.1 a hin
      simp only [laidMatrixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hmx
      have hbb := hmx.1.1 b hbm
      exact ⟨hs, hbb.1.2, hbb.2⟩
    · simp at hmatch

variable {T K : Type} [CommRing K]

/-- **A step that keeps the core keeps the one equation's value.** -/
theorem oneK_of_core (X : K9.Lens T) (ρ : Reading K) (s s' : T) (a a' : K9.Part)
    (h : X.get? s = some a) (h' : X.get? s' = some a') (hc : core a'.F = core a.F) (t : T)
    (y : Bound K) : oneK X ρ t s' y = oneK X ρ t s y := by
  simp only [oneK, h, h']
  cases X.get? t with
  | none => rfl
  | some b => exact total_of_sums ρ _ a.F a'.F (congrArg Prod.fst hc)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.inside_of_layoutOk
#print axioms VerifiableInference.Desc.K9L.oneK_of_core
