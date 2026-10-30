-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttOwn.lean

The verifier's function attentionOwners (OnBytes/Model/VerifyCross.lean) fills, in the plan of each
attention sub-proof, the record of the array that it borrows. It keeps every plan's list of
matrices, so also their labels.

* "foldlM_inv": a property that every step of a fold keeps holds at its end.
* "place_mats": attentionOwnerPlace keeps the list of matrices (over borderMeans_keeps of
  Johnson/Road/FormsKeysPlan.lean).
* "owners_mats": attentionOwners p4 NGr G A = .ok A': at every number j the plan A'[j] has the list
  of matrices of A[j].
* "owners_plan": the same for the records that publicOf makes of the plans of group.

Who reads it: publicOf (OnBytes/Model/VerifyPublic.lean) puts the records that attentionOwners
returns in the place of seam.tl in the plans that group has returned; with this file the label of
the copy of qa (Johnson/Road/Lane5AttLabel.lean) is still there.
-/
import Johnson.Road.Lane5AttPlan
import Johnson.Road.FormsKeysPlan
import OnBytes.Model.VerifyCross

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Model (TMat)
open OnBytes.Model.Verify (SubPlan attentionOwnerPlace attentionOwnerPlaces attentionOwners)

/-- A property that every step of a fold keeps holds at its end. -/
theorem foldlM_inv {α β : Type} {Q : β → Prop} {f : β → α → Except String β}
    (hstep : ∀ b a b', Q b → f b a = Except.ok b' → Q b') :
    ∀ (l : List α) (b b' : β), Q b → l.foldlM f b = Except.ok b' → Q b'
  | [], b, b', hb, h => by
    have e : b = b' := Except.ok.inj h
    exact e ▸ hb
  | a :: l, b, b', hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b1, h1, h⟩ := bind_ok h
    exact foldlM_inv hstep l b1 b' (hstep b a b1 hb h1) h

/-- Writing, at a number that the array has, a member with the same image leaves all images. -/
theorem set_keeps {α β : Type} (f : α → β) (out : Array α) {g : ℕ} {X X' : α}
    (hO : out[g]? = some X) (hf : f X' = f X) (j : ℕ) :
    ((out.setIfInBounds g X')[j]?).map f = (out[j]?).map f := by
  obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.1 hO
  by_cases e : g = j
  · subst e
    simp [hlt, hf, hx]
  · simp [e]

/-- attentionOwnerPlace keeps the list of matrices. -/
theorem place_mats {g : ℕ} {O X X' : SubPlan} (h : attentionOwnerPlace g O X = Except.ok X') :
    X'.tl.mats = X.tl.mats := by
  unfold attentionOwnerPlace at h
  obtain ⟨tl, ht, h⟩ := bind_ok h
  obtain ⟨own, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  have e := Except.ok.inj h
  subst e
  exact (borderMeans_keeps ht).1

/-- **attentionOwners keeps every plan's list of matrices.** -/
theorem owners_mats {p4 : Bool} {NGr : ℕ} {G A A' : Array SubPlan}
    (h : attentionOwners p4 NGr G A = Except.ok A') (j : ℕ) :
    (A'[j]?).map (fun X => X.tl.mats) = (A[j]?).map (fun X => X.tl.mats) := by
  unfold attentionOwners at h
  cases p4 with
  | false =>
    have e : A = A' := Except.ok.inj h
    rw [e]
  | true =>
    have h' : (Model.Verify.attentionOwnerShapes NGr G A >>= fun _ =>
        attentionOwnerPlaces NGr G A) = Except.ok A' := h
    obtain ⟨-, -, h2⟩ := bind_ok h'
    unfold attentionOwnerPlaces at h2
    refine foldlM_inv
      (Q := fun out => ∀ j, (out[j]?).map (fun X => X.tl.mats) = (A[j]?).map fun X => X.tl.mats)
      (fun out g out' hq hs => ?_) _ _ _ (fun _ => rfl) h2 j
    cases hG : G[g]? with
    | none =>
      simp only [hG] at hs
      have hs' : (Except.error "internal-a-owner-shape" : Except String (Array SubPlan)) =
          Except.ok out' := hs
      cases hs'
    | some O =>
      cases hO : out[g]? with
      | none =>
        simp only [hG, hO] at hs
        have hs' : (Except.error "internal-a-owner-shape" : Except String (Array SubPlan)) =
            Except.ok out' := hs
        cases hs'
      | some X =>
        simp only [hG, hO] at hs
        obtain ⟨X', hX, hs⟩ := bind_ok hs
        have e : out.setIfInBounds g X' = out' := Except.ok.inj hs
        intro i
        rw [← e, set_keeps (fun X => X.tl.mats) out hO (place_mats hX) i]
        exact hq i

/-- **The list of matrices in the record that takes the place of seam.tl is the plan's own.** A0:
the plans that group has returned; seenA: what attentionOwners returns on their records. -/
theorem owners_plan {p4 : Bool} {NGr : ℕ} {G seenA : Array SubPlan} {A0 : Array Attention.Plan}
    (h : attentionOwners p4 NGr G (A0.map fun Z => ⟨Z.seam.tl, Z.seam.Fp, Z.seam.Tp⟩) =
      Except.ok seenA) {g : ℕ} {Xg : Attention.Plan} {s : SubPlan} (h0 : A0[g]? = some Xg)
    (hs : seenA[g]? = some s) : s.tl.mats = Xg.seam.tl.mats := by
  have k := owners_mats h g
  rw [hs, Array.getElem?_map, h0] at k
  exact Option.some.inj k

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.owners_mats
#print axioms OnBytes.Road.L5.owners_plan
