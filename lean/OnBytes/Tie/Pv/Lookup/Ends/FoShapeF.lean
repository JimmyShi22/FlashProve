-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShapeF.lean: the numbers of the arrays ZZ and BZ and of the matrices'
arrays, from the success of the routine that lays them.

HTailF2.shapeF numbers the arrays of a sub-proof's smallness test in this order: the vectors U1 to
U3 that the sub-proof has, the arrays of its own matrices, ZZ, BZ, the arrays of earlier sub-proofs'
matrices. It ends by calling HTailF2.piecesF.

 - shapeF_ix: if shapeF returns tl', then tl' is what piecesF returns for some record; BZ's number
   is ZZ's plus 1; and for each matrix mu below NM the number of its array (gtTree) lies below ZZ's
   or above BZ's. The proof walks the routine's first loop (a matrix of either own kind leaves its
   list not empty) and its third (each number that is pushed).
 - shapeF_apart: so BZ is not ZZ and no matrix's array is BZ or ZZ.
 - coefOK_of_shape: CoefOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean) from shapeF's success and
   three facts on the state's arrays: BZ has 32 rows; the state has BZ's virtual rows 0, 1, 2; it
   has ZZ's virtual rows below 2 * zzBlocks.

Not claimed: anything on soundness, completeness or hiding.
Nor are the three facts that are left claimed here: HTailF2.addTreesF is to lay them, and the
routines between it and coefficientsF are to keep them.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoCoefOf

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

private theorem ok_bind' {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ok_jp' {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

private theorem forIn_keepsE {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (l0 : List α)
    (I : List α → σ → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ s s', I pre s → f a s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [a]) t) :
    ∀ (l pre : List α) (s r : σ), l0 = pre ++ l → I pre s → forIn l s f = .ok r → I l0 r
  | [], pre, s, r, e, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [e, List.append_nil, ← hr]
    exact hI
  | a :: l, pre, s, r, e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := ok_bind' h
    obtain ⟨t, rfl, hI'⟩ := step pre a l e s s' hI hs
    exact forIn_keepsE f l0 I step l (pre ++ [a]) t r (by rw [e]; simp) hI' h

theorem getD_map_range (c n i : Nat) :
    (Array.map (fun x => c + x) (Array.range n)).getD i 0 = if i < n then c + i else 0 := by
  by_cases h : i < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

theorem shapeF_ix {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    (∃ tl₀ : HTailF2, tl₀.piecesF = .ok tl') ∧ tl'.ix.BZ = tl'.ix.ZZ + 1 ∧
      ∀ mu < tl'.NM, tl'.gtTree.getD mu 0 < tl'.ix.ZZ ∨ tl'.ix.BZ < tl'.gtTree.getD mu 0 := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨r1, h1, h⟩ := ok_bind' h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨r2, h2, h⟩ := ok_bind' h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := ok_bind' h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨e1, e2, e3, _⟩ := piecesF_keys h
  refine ⟨⟨_, h⟩, ?_⟩
  rw [e1, e2, e3]
  refine ⟨rfl, ?_⟩
  clear h e1 e2 e3 h2
  -- the first loop: a matrix of either own kind leaves its list not empty
  have K1 := forIn_keepsE _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) =>
      ∀ mu ∈ pre, ((m.getD mu {}).kind == 0) = true →
        (txOf.getD mu none = none → 0 < s.2.1.size) ∧
        (∀ i, txOf.getD mu none = some i → 0 < s.2.2.size))
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨k, pk, px⟩ := s
      dsimp only at hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i i hi
          obtain ⟨_, hs⟩ := ok_jp' hs
          refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
          rcases List.mem_append.1 hmu with hm | hm
          · refine ⟨(hI mu hm hkm).1, fun j hj => ?_⟩
            have := (hI mu hm hkm).2 j hj
            simp only [Array.size_push]
            omega
          · have : mu = a := by simpa using hm
            subst this
            exact ⟨fun hn => (by rw [hi] at hn; cases hn), fun _ _ => (by simp)⟩
        · rename_i hi
          refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
          rcases List.mem_append.1 hmu with hm | hm
          · refine ⟨fun hn => ?_, (hI mu hm hkm).2⟩
            have := (hI mu hm hkm).1 hn
            simp only [Array.size_push]
            omega
          · have : mu = a := by simpa using hm
            subst this
            exact ⟨fun _ => (by simp), fun j hj => (by rw [hi] at hj; cases hj)⟩
      · rename_i hk
        refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
        rcases List.mem_append.1 hmu with hm | hm
        · exact hI mu hm hkm
        · have : mu = a := by simpa using hm
          subst this
          exact absurd hkm hk)
    (List.range m.size) [] _ _ rfl (fun _ h => by cases h) h1
  clear h1
  -- the third loop: each member of gtTree lies below ZZ or above BZ
  have K3 := forIn_keepsE _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      s.1.size = pre.length ∧ ∀ x ∈ s.1.toList, x < count + pkMat.size + pxMat.size ∨
        count + pkMat.size + pxMat.size + 1 < x)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      have ha : a ∈ List.range m.size := by rw [e]; simp
      have push : ∀ y, (y < count + pkMat.size + pxMat.size ∨
          count + pkMat.size + pxMat.size + 1 < y) →
          (gt.push y).size = (pre ++ [a]).length ∧ ∀ x ∈ (gt.push y).toList,
            x < count + pkMat.size + pxMat.size ∨ count + pkMat.size + pxMat.size + 1 < x := by
        intro y hy
        refine ⟨by simp [hI.1], fun x hx => ?_⟩
        rw [Array.toList_push] at hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hI.2 x hx
        · have : x = y := by simpa using hx
          rw [this]
          exact hy
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_jp' hs
      obtain ⟨_, hs⟩ := ok_jp' hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i hi
          refine ⟨_, (Except.ok.inj hs).symm, push _ (Or.inl ?_)⟩
          have hp : 0 < pkMat.size := (K1 a ha hk).1 hi
          rw [getD_map_range]
          split <;> omega
        · rename_i i hi
          refine ⟨_, (Except.ok.inj hs).symm, push _ (Or.inl ?_)⟩
          have hp : 0 < pxMat.size := (K1 a ha hk).2 i hi
          rw [getD_map_range]
          split <;> omega
      · split at hs
        · split at hs
          · rename_i j _
            simp only [pure_bind] at hs
            split at hs
            · rename_i X hX
              have hj : j < f.size := (Array.getElem?_eq_some_iff.1 hX).1
              split at hs
              · cases hs
              · split at hs
                · cases hs
                · refine ⟨_, (Except.ok.inj hs).symm, push _ (Or.inr ?_)⟩
                  rw [getD_map_range, if_pos hj]
                  omega
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl ⟨rfl, fun _ h => by cases h⟩ h3
  intro mu hmu
  have hs : gtTree.size = m.size := by rw [K3.1, List.length_range]
  have hmem : gtTree.getD mu 0 ∈ gtTree.toList := by
    have hlt : mu < gtTree.size := by rw [hs]; exact hmu
    simp [Array.getD, hlt]
  exact K3.2 _ hmem

theorem shapeF_apart {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.ix.BZ ≠ tl'.ix.ZZ ∧
      ∀ mu < tl'.NM, tl'.gtTree.getD mu 0 ≠ tl'.ix.BZ ∧ tl'.gtTree.getD mu 0 ≠ tl'.ix.ZZ := by
  obtain ⟨_, h1, h2⟩ := shapeF_ix h
  refine ⟨by omega, fun mu hmu => ?_⟩
  have := h2 mu hmu
  constructor <;> omega

/-- CoefOK from the maker's success and three facts on the state's arrays. -/
theorem coefOK_of_shape {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') (Fc : Fork)
    (hR : (Fc.trees.getD tl'.ix.BZ {}).R = 32)
    (hB : HasRow Fc tl'.ix.BZ 0 ∧ HasRow Fc tl'.ix.BZ 1 ∧ HasRow Fc tl'.ix.BZ 2)
    (hr : ∀ i < 2 * tl'.zzBlocks, HasRow Fc tl'.ix.ZZ i) : CoefOK tl' Fc := by
  obtain ⟨⟨tl₀, h0⟩, _, _⟩ := shapeF_ix h
  exact coefOK_of_pieces h0 Fc (shapeF_apart h).1 (shapeF_apart h).2 hR hB hr

end Fo
