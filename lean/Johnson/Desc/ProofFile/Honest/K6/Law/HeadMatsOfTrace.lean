-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HeadMatsOfTrace.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE
AT WHICH publicOf RETURNS X, AT A TRACE THAT MEETS THE BUNDLE MeetsAll, WHERE THE HONEST SIDE COUNTS
THE HEAD's SEGMENT AS NUMBER 24 AND ITS SHAPE IS X's: THE MATRICES THAT THE HONEST SIDE OF THE
SUB-PROTOCOL "the output head's own rounds" READS (headMats, Honest/K6/Wit.lean), THROUGH THE
LIBRARY's READER OF A TRACE BY LABELS (cellOf, Johnson/HonestTrace/Full.lean), ARE THE IMAGES IN THE
FIELD OF LIST 24 OF THE TRACE, AT ALL NUMBERS, ROWS AND COLUMNS: the premise hM of sameCells_trace
(Honest/K6/Law/SameCellsTrace.lean; neither is in this library) at that reader. Statements and
proofs.
IT IMPORTS A MODULE UNDER Johnson/Goal/ DIRECTLY (HonestTrace/FullInScope): it names the goals'
scope. It defines nothing.

What it is not. CONDITIONAL on the three premises on the public files, on the bundle MeetsAll (of
which "outside the shapes every entry is 0" alone is spent), and on two equations on the honest
side's public numbers: THE HEAD's SEGMENT HAS THE NUMBER 24 (h0), and the shape is X's (h1: of it
the number of hf's parts alone is read). AT THE READER cellOf X T ALONE: of another reader of cells
nothing is said. THE FULL SIZE ALONE. Nothing on soundness, on completeness or on what a proof
hides.

  getD_map_name        a list of names, read at a number, is the name of the entry at that number.
  headMatNames_label   where hf lies in four parts: the name at a name's number is its label.
  headMatNames_beyond  where hf lies in four parts: from number 8 on the name is empty.
  headMats_cellOf_in_scope   the main statement.
CALLED: cellOf_label_in_scope, parts_in_scope, planMats_eq (Johnson/Goal/HonestTrace/
FullInScope.lean), whose proof of planName_head_in_scope is the model for the second lemma and for
the plan's list; matsH_size (Johnson/Desc/AtSeats/NamesTieHead.lean); Hd.publicH_of_public,
Hd.planH2_label, matsAt_head.
THE FOUR THEOREMS STAND IN THE LIBRARY's NAMESPACE OnBytes.HonestTrace.
-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.Desc.AtSeats.NamesTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)
open Meaning
open ProofFile.Honest.K6 (HeadWhere headMatNames headMats)
open VerifiableInference.Desc.K1.HeadNames (matsH_size)

/-- A list of names, read at a number, is the name of the entry at that number. -/
theorem getD_map_name (A : Array Model.TMat) (a : ℕ) :
    (A.map (·.name)).getD a "" = (A.getD a {}).name := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[a]? <;> rfl

/-- Where hf lies in four parts: the honest side's name at a name's number is the name's label. -/
theorem headMatNames_label (N : HeadWhere) (hN : N.shape.NHf = 4) {μ : MatName} {a : ℕ}
    (ha : MatName.no? 3 1 1 4 .head μ = some a) : (headMatNames N).getD a "" = μ.label := by
  unfold headMatNames
  rw [getD_map_name]
  unfold Model.Head.matsH
  rw [hN]
  cases μ <;> simp only [MatName.no?] at ha <;>
    first
      | (obtain rfl := Option.some.inj ha; rfl)
      | (split at ha
         · rename_i p hp
           obtain rfl := Option.some.inj ha
           have c4 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
           rcases c4 with rfl | rfl | rfl | rfl <;> rfl
         · exact absurd ha (by simp))
      | exact absurd ha (by simp)

/-- Where hf lies in four parts (hN): from number 8 on the honest side's name is empty. -/
theorem headMatNames_beyond (N : HeadWhere) (hN : N.shape.NHf = 4) {a : ℕ} (ha : 8 ≤ a) :
    (headMatNames N).getD a "" = "" := by
  unfold headMatNames
  rw [getD_map_name, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_none (by rw [matsH_size _ _ _ _ _ hN]; exact ha)]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **THE HONEST SIDE's MATRICES, THROUGH THE READER BY LABELS, ARE LIST 24 OF THE TRACE.** -/
theorem headMats_cellOf_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx} {x : Instance ppref} {T : Tr}
    (M : MeetsAll X i x T) (N : HeadWhere) (h0 : N.seg = 24) (h1 : N.shape = X.hS) (n r k : ℕ) :
    headMats N ⟨cellOf X T⟩ n r k = ((T 24 n r k : ℤ) : Cb.Gl.F) := by
  obtain ⟨-, -, -, pH⟩ := parts_in_scope hZ hR h
  have hN : N.shape.NHf = 4 := by rw [h1]; exact pH
  show cellOf X T N.seg ((headMatNames N).getD n "") r k = _
  rw [h0]
  have step : ∀ (μ : MatName) (a : ℕ), MatName.no? 3 1 1 4 .head μ = some a →
      noAt X .head μ = some a →
      cellOf X T 24 ((headMatNames N).getD a "") r k = ((T 24 a r k : ℤ) : Cb.Gl.F) :=
    fun μ a e1 e2 => by
      rw [headMatNames_label N hN e1]
      exact cellOf_label_in_scope hZ hR h T (σ := .head) trivial e2 r k
  by_cases hn : n < 8
  · interval_cases n
    · exact step (.hf 0) 0 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step (.hf 1) 1 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step (.hf 2) 2 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step (.hf 3) 3 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step .hd 4 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step .hr 5 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step .bH 6 rfl (by unfold noAt; rw [pH]; rfl)
    · exact step .xbL 7 rfl (by unfold noAt; rw [pH]; rfl)
  · have h8 : 8 ≤ n := Nat.le_of_not_lt hn
    have hnone : ∀ a b c, MatName.ofLabel? a b c 4 .head "" = none := fun _ _ _ =>
      (by decide : MatName.ofLabel? 3 1 1 4 .head "" = none)
    have e24 : Seg.ofNo 12 24 = some .head := by decide
    have eL : cellOf X T 24 "" r k = 0 := by
      unfold cellOf
      rw [e24]
      simp only
      rw [pH, hnone]
    obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
    obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
    have em : matsAt X 24 =
        Model.Head.matsH X.hS X.HLy (borderOf X.y) (1 + X.y.NGr) stream.aId := by
      rw [matsAt_head, e]
      exact hm
    have hout : ¬ InShape X 24 n r k := fun I => by
      have hs := I.1
      rw [planMats_eq, em, matsH_size _ _ _ _ _ pH] at hs
      omega
    rw [headMatNames_beyond N hN h8, eL, M.out 24 n r k hout, Int.cast_zero]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.getD_map_name
#print axioms OnBytes.HonestTrace.headMatNames_label
#print axioms OnBytes.HonestTrace.headMatNames_beyond
#print axioms OnBytes.HonestTrace.headMats_cellOf_in_scope
