-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscMeaning.lean: the public part of a form that is a sum of slots, against
the form's value in the world of Fork.worldOf; the end claims of what the block's Psc.run hands on.

Main names:
  `shown_vp`, `publicPart_fold`: steps toward publicPart_sum.
  `publicPart_sum`: for a form C without an entry of a virtual row, the public part of C minus the
    value of C in the world of Fork.worldOf is the sum over C's slots of the coefficient times the
    slot's factor times the slot's mask entry.
  `claimMasks`: that sum as a mask form of the block (OnBytes/Iop/Psc.lean).
  `ends_get`: the j-th end claim of outW, at slots in a row (freshOf).
Limits: a form with entries of virtual rows has no such mask form, since publicPart drops the
entries. No statement here ties claimMasks to a world of the block. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscSeam

set_option autoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight claimAfter hidingWalk hidingEntries)

/-! ## (a) The claim's mask form -/

theorem shown_vp {F : Fork} {j : Nat} {y : E} (h : F.shown j = some y) : y = F.vp.getD j zeroE := by
  unfold Fork.shown at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem publicPart_fold {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) : ∀ (l :
    List (Nat × E)) (v τ : E),
    l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v = some
        τ →
    ρ.val τ = ρ.val v + (l.map fun x => ρ.val x.2 * ρ.val (F.vp.getD x.1 zeroE)).sum
  | [], v, τ, h => by
    simp only [List.foldlM_nil] at h
    rw [← Option.some.inj h]; simp
  | x :: l, v, τ, h => by
    simp only [List.foldlM_cons] at h
    cases e : F.shown x.1 with
    | none => rw [e] at h; cases h
    | some y =>
      rw [e] at h
      have := publicPart_fold ρ F l _ τ h
      rw [this, ρ.add, ρ.mul, shown_vp e, List.map_cons, List.sum_cons]
      ring

/-- The public part of a sum of slots, against its value at the hidden values. -/
theorem publicPart_sum {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) (C : Aff) (τ : E)
    (h : F.publicPart C = some τ) (he : C.ents = #[]) (mask : Nat → K) (entry : Nat → Nat → Nat →
        K) :
    ρ.val τ - C.value ρ (F.worldOf ρ mask entry) =
      (C.slots.toList.map fun x => ρ.val x.2 * ρ.val (F.mf.getD x.1 zeroE) * mask x.1).sum := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  rw [publicPart_fold ρ F _ _ _ h]
  unfold Aff.value
  rw [he]
  simp only [List.map_nil, List.sum_nil, zero_add]
  have key : ∀ l : List (Nat × E),
      (l.map fun x => ρ.val x.2 * ρ.val (F.vp.getD x.1 zeroE)).sum -
        (l.map (slotValue ρ (F.worldOf ρ mask entry))).sum =
      (l.map fun x => ρ.val x.2 * ρ.val (F.mf.getD x.1 zeroE) * mask x.1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      show _ - (ρ.val x.2 * (ρ.val (F.vp.getD x.1 zeroE) - ρ.val (F.mf.getD x.1 zeroE) * mask x.1) +
          _) = _
      ring
  rw [← key]
  ring

/-- The block's mask form for a claim that is a sum of slots: each slot's mask entry (in the mask
row of oracle orc) with the coefficient times the slot's factor. -/
def claimMasks (orc : Nat) (F : Fork) (C : Aff) : MaskForm :=
  C.slots.toList.map fun x => (⟨orc, x.1⟩, mulE x.2 (F.mf.getD x.1 zeroE))

/-! ## (b) The end claims -/

/-- The j-th end claim of what the block's run hands on, at the run's own slots in a row. -/
theorem ends_get (ws : List Weight) (m : MaskForm) (τ : E) (S : OnBytes.Psc.Summand) (orc first :
    Nat)
    (mu eps beta : E) (rs : List (List E × E)) (sentY v : List E) (len : rs.length = ws.length)
    (n1 : 1 ≤ S.shown) (hv : v.length = S.shown) (hd : ∀ w ∈ ws, 1 ≤ w.d) (j : Nat) (hj :
        j < v.length) :
    (outW ⟨ws, m, τ⟩ S (freshOf orc first (OnBytes.Psc.masksOf ⟨ws, m, τ⟩ S))
        (heardOf mu eps rs sentY beta v)).ends[j]? =
      some ⟨rs.map (·.2),
        [(⟨orc, first + hidingEntries (ws ++ [Weight.atZero (S.degree + 1)]) + j⟩, beta)],
            v.getD j zeroE⟩ := by
  have hs0 : (S.shown == 0) = false := by
    cases hh : S.shown with
    | zero => omega
    | succ k => rfl
  have hvars : OnBytes.Psc.varsOf ⟨ws, m, τ⟩ S = ws ++ [Weight.atZero (S.degree + 1)] := by
    simp [OnBytes.Psc.varsOf, hs0]
  have htake : ((rs ++ [(sentY, beta)]).map (·.2)).take ws.length = rs.map (·.2) := by
    rw [List.map_append, List.take_append_of_le_length (by simp [len]),
        List.take_of_length_le (by simp [len])]
  have hwl : (hidingWalk ((ws ++ [Weight.atZero (S.degree + 1)]).zip ((rs ++ [(sentY,
      beta)]).map (·.2)))).1.length =
      hidingEntries (ws ++ [Weight.atZero (S.degree + 1)]) := by
    refine walk_length _ _ (by simp) (by simp [len]) ?_
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hd w hw
    · rw [List.mem_singleton.1 hw]
      show 1 ≤ S.degree + 1
      omega
  have hlast : ((rs ++ [(sentY, beta)]).map (·.2)).getLast? = some beta := by simp
  unfold outW
  simp only [heardOf, hvars, htake, hwl, hs0, hlast, freshOf_drop, Bool.false_eq_true, if_false,
    Option.getD_some, List.getElem?_map, OnBytes.Psc.masksOf]
  have h1 : (freshOf orc (first + hidingEntries (ws ++ [Weight.atZero (S.degree + 1)]))
      (hidingEntries (ws ++ [Weight.atZero (S.degree + 1)]) + S.shown -
        hidingEntries (ws ++ [Weight.atZero (S.degree + 1)])))[j]? =
      some ⟨orc, first + hidingEntries (ws ++ [Weight.atZero (S.degree + 1)]) + j⟩ :=
    freshOf_get _ _ _ _ (by omega)
  have h2 : v[j]? = some (v.getD j zeroE) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hz := (List.getElem?_zip_eq_some (z := ((⟨orc, first + hidingEntries (ws ++ [Weight.atZero
      (S.degree + 1)]) + j⟩ : Slot),
    v.getD j zeroE))).2 ⟨h1, h2⟩
  rw [hz]
  rfl

#print axioms publicPart_sum
#print axioms ends_get

end OnBytes.Model.Road
