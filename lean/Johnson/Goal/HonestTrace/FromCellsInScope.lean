-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/FromCellsInScope.lean

The statements of Johnson/HonestTrace/FromCells.lean for public files in scope, at the trace
theTrace X i x of a served request. This file states no goal.

"The three premises on the public files" are: VerifierAndGoals.InScope Z = true; VerifierAndGoals.readFiles Z returns;
publicOf returns X on Z's parameter and scale files.

Main theorems, under these three:
* "partsFit_in_scope": PartsFit X. "namesFit_in_scope": NamesFit X T for every T that is 0 outside
  the shapes of the plans' lists (InShape, Johnson/HonestTrace/Full.lean).
* "midP_layers_cells_in_scope", "midP_att_cells_in_scope", "midP_head_cells_in_scope": if
  ServesAt X i x holds, Cb.Lkp.MidP holds for all θ and al with keys and bits read at fromG, fromA,
  fromH of the readers cellOf X (theTrace X i x) and entryOf i.
* "claimsZero_layers_cells_in_scope", "claimsZero_att_cells_in_scope",
  "claimsZero_head_cells_in_scope": if ServesAt X i x holds, ClaimsZero holds with the key vectors
  read at fromG, fromA, fromH and ν := nuFrom of these readers, for all mask entries, all jLK and
  al, every θ that is 0 where the lookup's shape has one call, and all challenges C with C.Fits.

Limits. It joins the theorems of Johnson/HonestTrace/FromCells.lean with parts_in_scope
(Johnson/Goal/HonestTrace/FullInScope.lean), the lengths of the plans' lists (Meaning.size_even,
size_odd, size_head, Johnson/Goal/Meaning/HidOwner.lean) and lookPub_in_scope, planesLaid_in_scope,
meetsAll_theTrace (Johnson/Goal/HonestTrace/FullPlanesInScope.lean). The limits of these files hold
here.

Not claimed: that a verifier accepts the rounds; that a prover's program sends them; completeness of
the protocol.

-/
import Johnson.HonestTrace.FromCells
import Johnson.Goal.HonestTrace.FullPlanesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model.Verify (publicOf)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

/-- Under the three premises on the public files: PartsFit X. -/
theorem partsFit_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : PartsFit X := by
  obtain ⟨a, b, c, d⟩ := parts_in_scope hZ hR h
  exact ⟨a, b, c, d⟩

/-- Under the three premises on the public files: NamesFit X T for every T that is 0 at every place
outside the shapes of the plans' lists. -/
theorem namesFit_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {T : Tr}
    (hout : ∀ k a r c, ¬ InShape X k a r c → T k a r c = 0) : NamesFit X T := by
  have P := partsFit_in_scope hZ hR h
  have C := Hd.core_of_scope hZ hR h
  refine ⟨P, fun k hk a r c hl => hout k a r c fun hI => ?_⟩
  have ha : a < (Meaning.matsAt X k).size := by
    have := hI.1
    rwa [planMats_eq] at this
  unfold labelAt at hl
  by_cases h24 : k = 24
  · subst h24
    have hσ : Seg.ofNo 12 24 = some .head := rfl
    rw [hσ] at hl
    simp only [Option.bind_some, (parts_at P hσ).1] at hl
    rw [Meaning.size_head h C] at ha
    have e : (MatName.all 3 1 1 4 .head).length = 8 := rfl
    rw [List.getElem?_eq_getElem (by rw [e]; exact ha)] at hl
    exact absurd hl (by simp)
  · by_cases he : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      have hσ : Seg.ofNo 12 (2 * g) = some (.ff g) := Seg.ofNo_no (σ := .ff g) hg
      rw [hσ] at hl
      simp only [Option.bind_some, (parts_at P hσ).1] at hl
      rw [Meaning.size_even h C hg] at ha
      have e : (MatName.all 3 1 1 4 (.ff g)).length = 9 := rfl
      rw [List.getElem?_eq_getElem (by rw [e]; exact ha)] at hl
      exact absurd hl (by simp)
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      have hσ : Seg.ofNo 12 (2 * g + 1) = some (.att g) := Seg.ofNo_no (σ := .att g) hg
      rw [hσ] at hl
      simp only [Option.bind_some, (parts_at P hσ).1] at hl
      rw [Meaning.size_odd h C hg] at ha
      have e : (MatName.all 3 1 1 4 (.att g)).length = 5 := rfl
      rw [List.getElem?_eq_getElem (by rw [e]; exact ha)] at hl
      exact absurd hl (by simp)

variable (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
  (h : publicOf Z.pol Z.KL lay = .ok X) (S : ServesAt X i x)
include hZ hR h S

/-- In scope, at a served request: NamesFit at theTrace X i x. -/
theorem namesFit_theTrace : NamesFit X (theTrace X i x) :=
  namesFit_in_scope hZ hR h (meetsAll_theTrace hZ hR h S).out

/-- In scope, at a served request, for g < 12 and all θ and al: MidP at group g, keys and bits read
at fromG of the readers cellOf X (theTrace X i x) and entryOf i. -/
theorem midP_layers_cells_in_scope {g : ℕ} (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32
      (Ends.G.keyG X.layers g (fromG X (cellOf X (theTrace X i x)) (entryOf i) g) θ)
      (Ends.G.tabG X.layers θ) (FoNums.pads X.y.fo)
      (fun u j =>
        Ends.G.bitsG X.y (fromG X (cellOf X (theTrace X i x)) (entryOf i) g) (u * 32 + j)) al :=
  midP_layers_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) hg θ al

/-- The same at the attention sub-proof of group g, at fromA of cellOf X (theTrace X i x). -/
theorem midP_att_cells_in_scope {g : ℕ} (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP (fsAt X g).v (fsAt X g).d 5 32
      (Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X (theTrace X i x)) g) θ)
      (Ends.A.tabA (fsAt X g) θ) (FoNums.pads (fsAt X g))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g)
        (fromA X (cellOf X (theTrace X i x)) g) (u * 32 + j)) al :=
  midP_att_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) hg θ al

/-- The same at the head, at fromH of cellOf X (theTrace X i x) and entryOf i. -/
theorem midP_head_cells_in_scope (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32
      (Ends.H.keyH (pubHAt X x) (fromH X (cellOf X (theTrace X i x)) (entryOf i)) θ)
      (Ends.H.tabH (pubHAt X x) θ) (FoNums.pads X.HLy.fs)
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs
        (fromH X (cellOf X (theTrace X i x)) (entryOf i)) (u * 32 + j)) al :=
  midP_head_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) θ al

open Look

/-- In scope, at a served request, for g < 12: ClaimsZero at group g, with the key vectors read at
fromG and ν := nuFrom of the readers cellOf X (theTrace X i x) and entryOf i, for all mask entries,
jLK, al, every θ that is 0 where the shape has one call, and all C with C.Fits. -/
theorem claimsZero_layers_cells_in_scope {g : ℕ} (hg : g < 12) (jLK : ℕ) (mask : ℕ → Cb.Gl.E)
    (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK
      (Ends.G.kvG X.layers g (fromG X (cellOf X (theTrace X i x)) (entryOf i) g)) θ al
      (nuFrom X (cellOf X (theTrace X i x)) (2 * g) mask) C :=
  claimsZero_layers_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) hg jLK mask θ al h1 C hC

/-- The same at the attention sub-proof of group g. -/
theorem claimsZero_att_cells_in_scope {g : ℕ} (hg : g < 12) (jLK : ℕ) (mask : ℕ → Cb.Gl.E)
    (θ al : Cb.Gl.E) (h1 : FoNums.several (fsAt X g) = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits (fsAt X g).v (fsAt X g).d 5) :
    ClaimsZero (fsAt X g) (Hd.shapeA X g).cf.lmb jLK
      (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X (theTrace X i x)) g)) θ al
      (nuFrom X (cellOf X (theTrace X i x)) (2 * g + 1) mask) C :=
  claimsZero_att_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) hg jLK mask θ al h1 C hC

/-- The same at the head. -/
theorem claimsZero_head_cells_in_scope (jLK : ℕ) (mask : ℕ → Cb.Gl.E) (θ al : Cb.Gl.E)
    (h1 : FoNums.several X.HLy.fs = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (Ends.H.kvH (pubHAt X x) (fromH X (cellOf X (theTrace X i x)) (entryOf i))) θ al
      (nuFrom X (cellOf X (theTrace X i x)) 24 mask) C :=
  claimsZero_head_cells (namesFit_theTrace hZ hR h S) (lookPub_in_scope hZ hR h)
    (meetsAll_theTrace hZ hR h S) (planesLaid_in_scope hZ hR h i x) jLK mask θ al h1 C hC

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.partsFit_in_scope
#print axioms OnBytes.HonestTrace.namesFit_in_scope
#print axioms OnBytes.HonestTrace.namesFit_theTrace
#print axioms OnBytes.HonestTrace.midP_layers_cells_in_scope
#print axioms OnBytes.HonestTrace.midP_att_cells_in_scope
#print axioms OnBytes.HonestTrace.midP_head_cells_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_layers_cells_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_att_cells_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_head_cells_in_scope
