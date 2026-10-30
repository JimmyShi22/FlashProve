-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/ShapePx.lean: THE LIST pxMat OF A PLAN, BY ITS MAKER: where shapeF
(OnBytes/Model/Tail.lean) returns tl', the list tl'.pxMat of the sub-proof's own matrices that
another sub-proof reads is the filtered range of the matrices' numbers; there are as many trees
tl'.ix.TX; and the number that txOf gives such a matrix is how many of them stand below it. No scope
is asked.

  `isPX m txOf mu`: matrix mu is the sub-proof's own and another sub-proof reads it.
  `cntX m txOf n`: how many such matrices stand below n. `cntX_succ`, `cntX_flat`: its laws.
  **`shapeF_px`**: the three sentences. Premise: shapeF returns.
  `shapeF_last`: where μ is the last such matrix: tl'.pxMat[tl'.ix.TX.size - 1]? = some μ.
Limits. Nothing on the steps of a plan behind shapeF. K04_law, the law of K4's sub-protocol itself,
IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Names.ShapeNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- Matrix mu is the sub-proof's own, and another sub-proof reads it. -/
def isPX (m : Array TMat) (txOf : Array (Option Nat)) (mu : Nat) : Bool :=
  (m.getD mu {}).kind == 0 && (txOf.getD mu none).isSome

/-- How many such matrices stand below n. -/
def cntX (m : Array TMat) (txOf : Array (Option Nat)) (n : Nat) : Nat :=
  ((List.range n).filter (isPX m txOf)).length

theorem cntX_succ (m : Array TMat) (txOf : Array (Option Nat)) (n : Nat) :
    cntX m txOf (n + 1) = cntX m txOf n + (if isPX m txOf n = true then 1 else 0) := by
  unfold cntX
  rw [filt_succ, List.length_append]
  by_cases h : isPX m txOf n = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- Where no such matrix stands from a on, the count stays. -/
theorem cntX_flat (m : Array TMat) (txOf : Array (Option Nat)) (a : Nat) :
    ∀ n, a ≤ n → (∀ k, a ≤ k → k < n → isPX m txOf k = false) → cntX m txOf n = cntX m txOf a
  | 0, h, _ => by
    obtain rfl : a = 0 := by omega
    rfl
  | n + 1, h, hk => by
    by_cases hc : a = n + 1
    · rw [hc]
    · have hp : ¬ isPX m txOf n = true := by
        rw [hk n (by omega) (by omega)]
        exact Bool.false_ne_true
      rw [cntX_succ, if_neg hp, Nat.add_zero]
      exact cntX_flat m txOf a n (by omega) fun k h1 h2 => hk k h1 (by omega)

variable {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)} {f : Array T2Foreign}
  {hasU : Array Bool} {tau : Nat}

/-- **The list pxMat, the number of its trees, and what txOf says.** -/
theorem shapeF_px (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.pxMat.toList = (List.range m.size).filter (isPX m txOf) ∧
      tl'.ix.TX.size = tl'.pxMat.size ∧
      ∀ mu, mu < m.size → (m.getD mu {}).kind = 0 → ∀ i, txOf.getD mu none = some i →
        i = cntX m txOf mu := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r1, h1, h⟩ := ok_of_bind h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r2, h2, h⟩ := ok_of_bind h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := ok_of_bind h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨e1, -, -, -⟩ := Fo.piecesF_keys h
  obtain ⟨-, e5, -⟩ := piecesF_lists h
  rw [e1, e5]
  clear h e1 e5 h2 h3
  have K1 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) =>
      s.snd.snd.toList = (List.range pre.length).filter (isPX m txOf) ∧
        ∀ mu, mu < pre.length → (m.getD mu {}).kind = 0 → ∀ i, txOf.getD mu none = some i →
          i = cntX m txOf mu)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨kT, pk, px⟩ := s
      have I1 : px.toList = (List.range pre.length).filter (isPX m txOf) := hI.1
      have I2 := hI.2
      have ha := range_split e
      subst ha
      have hlen : (pre ++ [pre.length]).length = pre.length + 1 := by simp
      dsimp only at hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i i hi
          obtain ⟨hne, hs⟩ := ok_of_jp hs
          have hi2 : i = px.size := by simpa using hne
          have hp : isPX m txOf pre.length = true := by
            unfold isPX
            rw [hi, hk]
            rfl
          refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · show (px.push pre.length).toList = _
            rw [hlen, filt_succ, if_pos hp, Array.toList_push, I1]
          · intro mu hmu hk0 i' hi'
            rw [hlen] at hmu
            by_cases hc : mu < pre.length
            · exact I2 mu hc hk0 i' hi'
            · obtain rfl : mu = pre.length := by omega
              obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
              rw [hi2, ← Array.length_toList, I1]
              rfl
        · rename_i hi
          have hp : ¬ isPX m txOf pre.length = true := by
            unfold isPX
            rw [hi]
            simp
          refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · show px.toList = _
            rw [hlen, filt_succ, if_neg hp, List.append_nil]
            exact I1
          · intro mu hmu hk0 i' hi'
            rw [hlen] at hmu
            by_cases hc : mu < pre.length
            · exact I2 mu hc hk0 i' hi'
            · obtain rfl : mu = pre.length := by omega
              rw [hi] at hi'
              cases hi'
      · rename_i hk
        have hp : ¬ isPX m txOf pre.length = true := by
          unfold isPX
          intro hx
          rw [Bool.and_eq_true] at hx
          exact hk hx.1
        refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
        · show px.toList = _
          rw [hlen, filt_succ, if_neg hp, List.append_nil]
          exact I1
        · intro mu hmu hk0 i' hi'
          rw [hlen] at hmu
          by_cases hc : mu < pre.length
          · exact I2 mu hc hk0 i' hi'
          · obtain rfl : mu = pre.length := by omega
            exact absurd (by rw [hk0]; rfl) hk)
    (List.range m.size) [] _ _ rfl ⟨rfl, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩ h1
  dsimp only at K1
  rw [List.length_range] at K1
  refine ⟨K1.1, ?_, K1.2⟩
  show (Array.map (fun x => count + pkMat.size + x) (Array.range pxMat.size)).size = pxMat.size
  rw [Array.size_map, Array.size_range]

/-- Where μ is the last of the sub-proof's own matrices that another sub-proof reads, it is the
last entry of pxMat, counted by the trees. -/
theorem shapeF_last (h : tl.shapeF m txOf f hasU tau = .ok tl') {μ : Nat} (hμ : μ < m.size)
    (hp : isPX m txOf μ = true) (hl : ∀ k, μ + 1 ≤ k → k < m.size → isPX m txOf k = false) :
    tl'.pxMat[tl'.ix.TX.size - 1]? = some μ := by
  obtain ⟨a1, a2, _⟩ := shapeF_px h
  have hs : tl'.pxMat.size = cntX m txOf μ + 1 := by
    rw [← Array.length_toList, a1]
    show cntX m txOf m.size = _
    rw [cntX_flat m txOf (μ + 1) m.size (by omega) hl, cntX_succ, if_pos hp]
  rw [a2, hs, Nat.add_sub_cancel, ← Array.getElem?_toList, a1]
  exact filter_range_at _ _ _ hμ hp

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.cntX_flat
#print axioms OnBytes.Road.K4.Names.shapeF_px
#print axioms OnBytes.Road.K4.Names.shapeF_last
