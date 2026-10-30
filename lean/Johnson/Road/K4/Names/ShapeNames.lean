-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/ShapeNames.lean: WHICH TREE IS WHICH MATRIX's, BY THE PLAN's OWN MAKER: where
shapeF (OnBytes/Model/Tail.lean) returns tl', the tree tl'.gtTree[μ] of matrix number μ stands in
one of the three lists of trees tl'.ix.PK, tl'.ix.TX, tl'.ix.FT, at a place at which the list of
matrices beside it (pkMat, pxMat) holds μ. No scope is asked; PlanPort.lean alone is imported.

  `isPK m txOf mu`: matrix mu is the sub-proof's own and no other sub-proof reads it.
  `cnt m txOf n`: how many such matrices stand below n.
  `filter_range_at`, `range_split`, `filt_succ`: facts on List.range. `GtAt`: what is said of the
    tree of one matrix. `piecesF_lists`: the last step of shapeF keeps three lists.
  **`shapeF_names`**: the three sentences at μ < m.size: see its statement. Premise: shapeF returns.
The walk is that of shapeF_gt (Johnson/Goal/Meaning/PlanPort.lean), with other invariants.
Limits. Nothing on the steps of a plan behind shapeF. K04_law, the law of K4's sub-protocol itself,
IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Goal.Meaning.PlanPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- Matrix mu is the sub-proof's own, and no other sub-proof reads it. -/
def isPK (m : Array TMat) (txOf : Array (Option Nat)) (mu : Nat) : Bool :=
  (m.getD mu {}).kind == 0 && (txOf.getD mu none).isNone

/-- How many such matrices stand below n. -/
def cnt (m : Array TMat) (txOf : Array (Option Nat)) (n : Nat) : Nat :=
  ((List.range n).filter (isPK m txOf)).length

theorem cnt_succ (m : Array TMat) (txOf : Array (Option Nat)) (n : Nat) :
    cnt m txOf (n + 1) = cnt m txOf n + (if isPK m txOf n = true then 1 else 0) := by
  unfold cnt
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : isPK m txOf n = true
  · rw [if_pos h, List.filter_cons_of_pos h]
    rfl
  · rw [if_neg h, List.filter_cons_of_neg h]
    rfl

/-- The member μ of a filtered range stands at the number of members below it. -/
theorem filter_range_at (p : Nat → Bool) : ∀ (n μ : Nat), μ < n → p μ = true →
    ((List.range n).filter p)[((List.range μ).filter p).length]? = some μ
  | 0, μ, h, _ => absurd h (Nat.not_lt_zero μ)
  | n + 1, μ, h, hp => by
    rw [List.range_succ, List.filter_append]
    by_cases hc : μ < n
    · have ih := filter_range_at p n μ hc hp
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ih).1]
      exact ih
    · obtain rfl : μ = n := by omega
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.filter_cons_of_pos hp]
      rfl

/-- Where a range is cut, the member at the cut is the number of members in front. -/
theorem range_split {n a : Nat} {pre rest : List Nat} (e : List.range n = pre ++ a :: rest) :
    a = pre.length := by
  have h1 : (List.range n)[pre.length]? = some a := by
    rw [e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.1 h1
  rw [List.getElem_range] at he
  exact he.symm

/-- The filtered range, one longer. -/
theorem filt_succ (p : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).filter p =
      (List.range n).filter p ++ (if p n = true then [n] else []) := by
  rw [List.range_succ, List.filter_append]
  by_cases h : p n = true
  · rw [if_pos h, List.filter_cons_of_pos h]
    rfl
  · rw [if_neg h, List.filter_cons_of_neg h]
    rfl

theorem getD_some {a : Array Nat} {r : Nat} (h : r < a.size) : a[r]? = some (a.getD r 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

theorem getD_of_some {a : Array Nat} {r v : Nat} (h : a[r]? = some v) : a.getD r 0 = v := by
  rw [Array.getD_eq_getD_getElem?, h]
  rfl

/-- What is said of the tree v of matrix number mu. -/
def GtAt (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign) (PK TX FT : Array Nat)
    (mu : Nat) (v : Option Nat) : Prop :=
  (isPK m txOf mu = true → v = some (PK.getD (cnt m txOf mu) 0)) ∧
    ((m.getD mu {}).kind = 0 → ∀ i, txOf.getD mu none = some i → v = some (TX.getD i 0)) ∧
    ((m.getD mu {}).kind = 1 → ∀ j, (m.getD mu {}).foreign = some j →
      v = some (FT.getD j 0) ∧ j < f.size)

/-- One more tree is pushed. -/
theorem gt_push {m : Array TMat} {txOf : Array (Option Nat)} {f : Array T2Foreign}
    {PK TX FT gt : Array Nat} {n y : Nat} (hs : gt.size = n)
    (I : ∀ mu, mu < n → GtAt m txOf f PK TX FT mu gt[mu]?)
    (hy : GtAt m txOf f PK TX FT n (some y)) :
    ∀ mu, mu < n + 1 → GtAt m txOf f PK TX FT mu (gt.push y)[mu]? := by
  intro mu hmu
  by_cases hc : mu < n
  · have hl : mu < gt.size := by omega
    rw [Array.getElem?_push_lt hl, ← Array.getElem?_eq_getElem hl]
    exact I mu hc
  · obtain rfl : mu = n := by omega
    rw [← hs, Array.getElem?_push_size]
    rw [← hs] at hy
    exact hy

/-- The last step of shapeF keeps the two lists of matrices and the readers' list. -/
theorem piecesF_lists {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    tl'.pkMat = tl.pkMat ∧ tl'.pxMat = tl.pxMat ∧ tl'.plFor = tl.plFor := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨f9, _, h⟩ := ok_of_bind h
  obtain ⟨pub, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl, rfl⟩

variable {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)} {f : Array T2Foreign}
  {hasU : Array Bool} {tau : Nat}

/-- **Which tree is which matrix's.** -/
theorem shapeF_names (h : tl.shapeF m txOf f hasU tau = .ok tl') {μ : Nat} (hμ : μ < m.size) :
    ((m.getD μ {}).kind = 0 → txOf.getD μ none = none →
        ∃ r : Nat, tl'.ix.PK[r]? = some (tl'.gtTree.getD μ 0) ∧ tl'.pkMat[r]? = some μ) ∧
      ((m.getD μ {}).kind = 0 → ∀ i, txOf.getD μ none = some i →
        tl'.ix.TX[i]? = some (tl'.gtTree.getD μ 0) ∧ tl'.pxMat[i]? = some μ) ∧
      ((m.getD μ {}).kind = 1 → ∀ j, (m.getD μ {}).foreign = some j →
        tl'.ix.FT[j]? = some (tl'.gtTree.getD μ 0) ∧ j < tl'.plFor.size) := by
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
  obtain ⟨e1, e2, -, -⟩ := Fo.piecesF_keys h
  obtain ⟨e4, e5, e6⟩ := piecesF_lists h
  rw [e1, e2, e4, e5, e6]
  clear h e1 e2 e4 e5 e6 h2
  have K1 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) =>
      s.snd.fst.toList = (List.range pre.length).filter (isPK m txOf) ∧
        ∀ mu, mu < pre.length → (m.getD mu {}).kind = 0 → ∀ i, txOf.getD mu none = some i →
          s.snd.snd[i]? = some mu)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨kT, pk, px⟩ := s
      have I1 : pk.toList = (List.range pre.length).filter (isPK m txOf) := hI.1
      have I2 : ∀ mu, mu < pre.length → (m.getD mu {}).kind = 0 → ∀ i,
          txOf.getD mu none = some i → px[i]? = some mu := hI.2
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
          have hp : ¬ isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi]
            simp
          refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · show pk.toList = _
            rw [hlen, filt_succ, if_neg hp, List.append_nil]
            exact I1
          · intro mu hmu hk0 i' hi'
            show (px.push pre.length)[i']? = some mu
            rw [hlen] at hmu
            by_cases hc : mu < pre.length
            · have o := I2 mu hc hk0 i' hi'
              have hl := (Array.getElem?_eq_some_iff.1 o).1
              rw [Array.getElem?_push_lt hl, ← Array.getElem?_eq_getElem hl]
              exact o
            · obtain rfl : mu = pre.length := by omega
              obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
              rw [hi2, Array.getElem?_push_size]
        · rename_i hi
          have hp : isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi, hk]
            rfl
          refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · show (pk.push pre.length).toList = _
            rw [hlen, filt_succ, if_pos hp, Array.toList_push, I1]
          · intro mu hmu hk0 i' hi'
            show px[i']? = some mu
            rw [hlen] at hmu
            by_cases hc : mu < pre.length
            · exact I2 mu hc hk0 i' hi'
            · obtain rfl : mu = pre.length := by omega
              rw [hi] at hi'
              cases hi'
      · rename_i hk
        have hp : ¬ isPK m txOf pre.length = true := by
          unfold isPK
          intro hx
          rw [Bool.and_eq_true] at hx
          exact hk hx.1
        refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
        · show pk.toList = _
          rw [hlen, filt_succ, if_neg hp, List.append_nil]
          exact I1
        · intro mu hmu hk0 i' hi'
          show px[i']? = some mu
          rw [hlen] at hmu
          by_cases hc : mu < pre.length
          · exact I2 mu hc hk0 i' hi'
          · obtain rfl : mu = pre.length := by omega
            exact absurd (by rw [hk0]; rfl) hk)
    (List.range m.size) [] _ _ rfl ⟨rfl, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩ h1
  have K3 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      s.fst.size = pre.length ∧ s.snd.snd.fst = cnt m txOf pre.length ∧
        s.snd.snd.snd.snd.snd.fst.size = f.size ∧
        ∀ mu, mu < pre.length → GtAt m txOf f
          (Array.map (fun x => count + x) (Array.range pkMat.size))
          (Array.map (fun x => count + pkMat.size + x) (Array.range pxMat.size))
          (Array.map (fun x => count + pkMat.size + pxMat.size + 2 + x) (Array.range f.size))
          mu s.fst[mu]?)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      have J1 : gt.size = pre.length := hI.1
      have J2 : nPK' = cnt m txOf pre.length := hI.2.1
      have J3 : plFor'.size = f.size := hI.2.2.1
      have J4 := hI.2.2.2
      have ha := range_split e
      subst ha
      have hlen : (pre ++ [pre.length]).length = pre.length + 1 := by simp
      have push : ∀ y, (gt.push y).size = (pre ++ [pre.length]).length := by
        intro y
        rw [Array.size_push, J1, hlen]
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      split at hs
      · rename_i hk
        have hk0 : (m.getD pre.length {}).kind = 0 := by simpa using hk
        split at hs
        · rename_i hi
          have hp : isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi, hk]
            rfl
          refine ⟨_, (Except.ok.inj hs).symm, push _, ?_, J3, ?_⟩
          · show nPK' + 1 = cnt m txOf (pre ++ [pre.length]).length
            rw [hlen, cnt_succ, if_pos hp, J2]
          · rw [hlen]
            refine gt_push J1 J4 ⟨fun _ => by rw [J2], fun _ i hi' => ?_, fun h1 => ?_⟩
            · rw [hi] at hi'
              cases hi'
            · rw [hk0] at h1
              cases h1
        · rename_i i hi
          have hp : ¬ isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi]
            simp
          refine ⟨_, (Except.ok.inj hs).symm, push _, ?_, J3, ?_⟩
          · show nPK' = cnt m txOf (pre ++ [pre.length]).length
            rw [hlen, cnt_succ, if_neg hp, J2]
            rfl
          · rw [hlen]
            refine gt_push J1 J4 ⟨fun hx => absurd hx hp, fun _ i' hi' => ?_, fun h1 => ?_⟩
            · obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
              rfl
            · rw [hk0] at h1
              cases h1
      · rename_i hk
        have hp : ¬ isPK m txOf pre.length = true := by
          unfold isPK
          intro hx
          rw [Bool.and_eq_true] at hx
          exact hk hx.1
        split at hs
        · split at hs
          · rename_i j hj
            simp only [pure_bind] at hs
            split at hs
            · rename_i Xf hXf
              split at hs
              · cases hs
              · split at hs
                · cases hs
                · refine ⟨_, (Except.ok.inj hs).symm, push _, ?_, ?_, ?_⟩
                  · show nPK' = cnt m txOf (pre ++ [pre.length]).length
                    rw [hlen, cnt_succ, if_neg hp, J2]
                    rfl
                  · show (plFor'.modify j _).size = f.size
                    rw [Array.size_modify]
                    exact J3
                  · rw [hlen]
                    refine gt_push J1 J4 ⟨fun hx => absurd hx hp, fun h0 => ?_,
                      fun _ j' hj' => ?_⟩
                    · exact absurd (by rw [h0]; rfl) hk
                    · obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
                      exact ⟨rfl, (Array.getElem?_eq_some_iff.1 hXf).1⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl
    ⟨rfl, rfl, Array.size_replicate, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩ h3
  dsimp only at K1 K3
  rw [List.length_range] at K1 K3
  obtain ⟨A1, A2⟩ := K1
  obtain ⟨_, _, B3, B4⟩ := K3
  obtain ⟨G1, G2, G3⟩ := B4 μ hμ
  refine ⟨fun hk ht => ?_, fun hk i hi => ?_, fun hk j hj => ?_⟩
  · have hp : isPK m txOf μ = true := by
      unfold isPK
      rw [hk, ht]
      rfl
    have hr : pkMat[cnt m txOf μ]? = some μ := by
      rw [← Array.getElem?_toList]
      show pkMat.toList[cnt m txOf μ]? = some μ
      rw [show pkMat.toList = (List.range m.size).filter (isPK m txOf) from A1]
      exact filter_range_at _ _ _ hμ hp
    have hl := (Array.getElem?_eq_some_iff.1 hr).1
    refine ⟨cnt m txOf μ, ?_, hr⟩
    show (Array.map (fun x => count + x) (Array.range pkMat.size))[cnt m txOf μ]? =
      some (gtTree.getD μ 0)
    rw [getD_of_some (G1 hp)]
    exact getD_some (by rw [Array.size_map, Array.size_range]; exact hl)
  · have hr : pxMat[i]? = some μ := A2 μ hμ hk i hi
    have hl := (Array.getElem?_eq_some_iff.1 hr).1
    refine ⟨?_, hr⟩
    show (Array.map (fun x => count + pkMat.size + x) (Array.range pxMat.size))[i]? =
      some (gtTree.getD μ 0)
    rw [getD_of_some (G2 hk i hi)]
    exact getD_some (by rw [Array.size_map, Array.size_range]; exact hl)
  · obtain ⟨g1, g2⟩ := G3 hk j hj
    refine ⟨?_, ?_⟩
    · show (Array.map (fun x => count + pkMat.size + pxMat.size + 2 + x)
        (Array.range f.size))[j]? = some (gtTree.getD μ 0)
      rw [getD_of_some g1]
      exact getD_some (by rw [Array.size_map, Array.size_range]; exact g2)
    · show j < plFor.size
      rw [show plFor.size = f.size from B3]
      exact g2

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.filter_range_at
#print axioms OnBytes.Road.K4.Names.piecesF_lists
#print axioms OnBytes.Road.K4.Names.shapeF_names
