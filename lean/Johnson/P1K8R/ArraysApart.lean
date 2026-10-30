-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ArraysApart.lean: THE SMALLNESS TEST: IN WHAT THE ROUTINE OF SHAPES (shapeF,
OnBytes/Model/Tail.lean) RETURNS NO TWO MATRICES HAVE ONE ARRAY; SO AT THE RECORD OF EVERY SMALLNESS
TEST IN WHAT Verify.publicOf RETURNS. A definition with code, statements and proofs. On the routines
that make a plan alone: no state, no prover. Lemmas; none of the library's goals.

  `at_map`   an entry of a stretch of numbers c, c + 1, …
  **`shapeF_lists`**   the three lists of the matrices' arrays (PK, TX, FT) are stretches of
      numbers, one behind the other, two numbers between the second and the third
  **`shapeF_foreign`**   two matrices of an earlier sub-proof (TMat.kind = 1) with one number of an
      earlier array (TMat.foreign) are one matrix
  **`shapeF_inj`**   two matrices with one array are one matrix
  **`oneEachB tl`**   with code: no two matrices below NM have one array
  **`made_oneEach`**   `Made tlc` (Johnson/P1K8R/MadeAtPlans.lean) gives `oneEachB tlc`
By: shapeF_names (Johnson/Road/K4/Names/ShapeNames.lean) · shapeF_kinds, shapeF_NM (ShapeTrees.lean)
· Fo.piecesF_keys (OnBytes/Tie/Pv/Lookup/Forest/FoPiecesF.lean) · the walk of shapeF_cols
(Johnson/Desc/First/Look/ColsAt.lean) through the third loop · addTreesF_fits
(OnBytes/Tie/Pv/Tail/EndSame.lean).
Limits. Nothing on a record that a later routine of a run has turned.

-/
import Johnson.P1K8R.MadeAtPlans
import Johnson.Road.K4.Names.ShapeTrees
import OnBytes.Tie.Pv.Lookup.Forest.FoPiecesF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open OnBytes.Road.K4.Names (shapeF_names shapeF_kinds shapeF_NM)

/-- An entry of a stretch of numbers. -/
theorem at_map {c n i t : Nat} (h : ((Array.range n).map fun x => c + x)[i]? = some t) :
    i < n ∧ t = c + i := by
  obtain ⟨hl, he⟩ := Array.getElem?_eq_some_iff.1 h
  simp only [Array.size_map, Array.size_range] at hl
  simp only [Array.getElem_map, Array.getElem_range] at he
  exact ⟨hl, he.symm⟩

variable {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)} {f : Array T2Foreign}
  {hasU : Array Bool} {tau : Nat}

/-- **The three lists are stretches of numbers, one behind the other.** -/
theorem shapeF_lists (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    ∃ c a b n, tl'.ix.PK = ((Array.range a).map fun x => c + x) ∧
      tl'.ix.TX = ((Array.range b).map fun x => c + a + x) ∧
      tl'.ix.FT = ((Array.range n).map fun x => c + a + b + 2 + x) := by
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
  rw [e1]
  exact ⟨count, pkMat.size, pxMat.size, f.size, rfl, rfl, rfl⟩

/-- **Two matrices of an earlier sub-proof with one number of an earlier array are one.** -/
theorem shapeF_foreign (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    ∀ mu nu, mu < m.size → nu < m.size → (m.getD mu {}).kind = 1 → (m.getD nu {}).kind = 1 →
      ∀ j, (m.getD mu {}).foreign = some j → (m.getD nu {}).foreign = some j → mu = nu := by
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
  clear h h2 h1
  have K3 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      (∀ mu ∈ pre, (m.getD mu {}).kind = 1 → ∀ j, (m.getD mu {}).foreign = some j →
        j < s.2.2.2.1) ∧
      ∀ mu ∈ pre, ∀ nu ∈ pre, (m.getD mu {}).kind = 1 → (m.getD nu {}).kind = 1 →
        ∀ j, (m.getD mu {}).foreign = some j → (m.getD nu {}).foreign = some j → mu = nu)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      obtain ⟨i1, i2⟩ : (∀ mu ∈ pre, (m.getD mu {}).kind = 1 →
          ∀ j, (m.getD mu {}).foreign = some j → j < nextF') ∧
        ∀ mu ∈ pre, ∀ nu ∈ pre, (m.getD mu {}).kind = 1 → (m.getD nu {}).kind = 1 →
          ∀ j, (m.getD mu {}).foreign = some j → (m.getD nu {}).foreign = some j → mu = nu := hI
      -- where the new matrix is the sub-proof's own, nothing turns
      have keep0 : (m.getD a {}).kind = 0 →
          (∀ mu ∈ pre ++ [a], (m.getD mu {}).kind = 1 →
            ∀ j, (m.getD mu {}).foreign = some j → j < nextF') ∧
          ∀ mu ∈ pre ++ [a], ∀ nu ∈ pre ++ [a], (m.getD mu {}).kind = 1 →
            (m.getD nu {}).kind = 1 → ∀ j, (m.getD mu {}).foreign = some j →
            (m.getD nu {}).foreign = some j → mu = nu := by
        intro hk
        have old : ∀ mu ∈ pre ++ [a], (m.getD mu {}).kind = 1 → mu ∈ pre := by
          intro mu hmu h1
          rcases List.mem_append.1 hmu with h | h
          · exact h
          · obtain rfl := List.mem_singleton.1 h
            rw [hk] at h1
            exact absurd h1 (by decide)
        exact ⟨fun mu hmu h1 => i1 mu (old mu hmu h1) h1,
          fun mu hmu nu hnu h1 h2 => i2 mu (old mu hmu h1) nu (old nu hnu h2) h1 h2⟩
      -- where it is an earlier sub-proof's, its number is the next one
      have keep1 : (m.getD a {}).foreign = some nextF' →
          (∀ mu ∈ pre ++ [a], (m.getD mu {}).kind = 1 →
            ∀ j, (m.getD mu {}).foreign = some j → j < nextF' + 1) ∧
          ∀ mu ∈ pre ++ [a], ∀ nu ∈ pre ++ [a], (m.getD mu {}).kind = 1 →
            (m.getD nu {}).kind = 1 → ∀ j, (m.getD mu {}).foreign = some j →
            (m.getD nu {}).foreign = some j → mu = nu := by
        intro hf
        refine ⟨fun mu hmu h1 j hj => ?_, fun mu hmu nu hnu h1 h2 j hj hj' => ?_⟩
        · rcases List.mem_append.1 hmu with h | h
          · exact Nat.lt_succ_of_lt (i1 mu h h1 j hj)
          · obtain rfl := List.mem_singleton.1 h
            rw [hf] at hj
            obtain rfl := Option.some.inj hj
            exact Nat.lt_succ_self _
        · rcases List.mem_append.1 hmu with h | h <;> rcases List.mem_append.1 hnu with h' | h'
          · exact i2 mu h nu h' h1 h2 j hj hj'
          · obtain rfl := List.mem_singleton.1 h'
            rw [hf] at hj'
            obtain rfl := Option.some.inj hj'
            exact absurd (i1 mu h h1 _ hj) (Nat.lt_irrefl _)
          · obtain rfl := List.mem_singleton.1 h
            rw [hf] at hj
            obtain rfl := Option.some.inj hj
            exact absurd (i1 nu h' h2 _ hj') (Nat.lt_irrefl _)
          · rw [List.mem_singleton.1 h, List.mem_singleton.1 h']
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      split at hs
      · rename_i hk0
        have hk : (m.getD a {}).kind = 0 := by simpa using hk0
        split at hs
        · exact ⟨_, (Except.ok.inj hs).symm, keep0 hk⟩
        · exact ⟨_, (Except.ok.inj hs).symm, keep0 hk⟩
      · split at hs
        · split at hs
          · rename_i j hj
            simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · rename_i hne
                  have ej : j = nextF' := by simpa using hne
                  exact ⟨_, (Except.ok.inj hs).symm, keep1 (by rw [hj, ej])⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl
    ⟨fun _ hj => absurd hj List.not_mem_nil, fun _ hj => absurd hj List.not_mem_nil⟩ h3
  intro mu nu hmu hnu
  exact K3.2 mu (List.mem_range.2 hmu) nu (List.mem_range.2 hnu)

/-- **Two matrices with one array are one.** -/
theorem shapeF_inj (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    ∀ mu nu, mu < tl'.NM → nu < tl'.NM → tl'.gtTree.getD mu 0 = tl'.gtTree.getD nu 0 →
      mu = nu := by
  obtain ⟨c, a, b, n, ePK, eTX, eFT⟩ := shapeF_lists h
  rw [shapeF_NM h]
  -- where a matrix's array lies, and what ties it to the matrix
  have cls : ∀ mu, mu < m.size →
      (∃ r, r < a ∧ tl'.gtTree.getD mu 0 = c + r ∧ tl'.pkMat[r]? = some mu) ∨
      (∃ i, i < b ∧ tl'.gtTree.getD mu 0 = c + a + i ∧ tl'.pxMat[i]? = some mu) ∨
      (∃ j, j < n ∧ tl'.gtTree.getD mu 0 = c + a + b + 2 + j ∧ (m.getD mu {}).kind = 1 ∧
        (m.getD mu {}).foreign = some j) := by
    intro mu hmu
    obtain ⟨n1, n2, n3⟩ := shapeF_names h hmu
    rcases shapeF_kinds h mu hmu with hk | ⟨hk, j, hj⟩
    · cases ht : txOf.getD mu none with
      | none =>
        obtain ⟨r, r1, r2⟩ := n1 hk ht
        rw [ePK] at r1
        obtain ⟨q1, q2⟩ := at_map r1
        exact Or.inl ⟨r, q1, q2, r2⟩
      | some i =>
        obtain ⟨r1, r2⟩ := n2 hk i ht
        rw [eTX] at r1
        obtain ⟨q1, q2⟩ := at_map r1
        exact Or.inr (Or.inl ⟨i, q1, q2, r2⟩)
    · obtain ⟨r1, -⟩ := n3 hk j hj
      rw [eFT] at r1
      obtain ⟨q1, q2⟩ := at_map r1
      exact Or.inr (Or.inr ⟨j, q1, q2, hk, hj⟩)
  intro mu nu hmu hnu e
  rcases cls mu hmu with ⟨r, r1, r2, r3⟩ | ⟨r, r1, r2, r3⟩ | ⟨r, r1, r2, r3, r4⟩ <;>
    rcases cls nu hnu with ⟨s, s1, s2, s3⟩ | ⟨s, s1, s2, s3⟩ | ⟨s, s1, s2, s3, s4⟩
  · obtain rfl : r = s := by omega
    exact Option.some.inj (r3.symm.trans s3)
  · omega
  · omega
  · omega
  · obtain rfl : r = s := by omega
    exact Option.some.inj (r3.symm.trans s3)
  · omega
  · omega
  · omega
  · obtain rfl : r = s := by omega
    exact shapeF_foreign h mu nu hmu hnu r3 s3 r r4 s4

/-- No two matrices below NM have one array. -/
def oneEachB (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu => (List.range tl.NM).all fun nu =>
    nu == mu || tl.gtTree.getD nu 0 != tl.gtTree.getD mu 0

/-- **At every record that is made so.** -/
theorem made_oneEach {tlc : HTailF2} (M : Made tlc) : oneEachB tlc = true := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  obtain ⟨-, -, hE⟩ := OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine ha
  have eN : tl'.NM = tl.NM := by rw [hE]
  have eG : tl'.gtTree = tl.gtTree := by rw [hE]
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  have cG : tlc.gtTree = tl'.gtTree := congrArg (·.gtTree) hr
  unfold oneEachB
  rw [cN, cG, eN, eG]
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true, List.mem_range]
  intro mu hmu nu hnu
  by_cases e : nu = mu
  · exact Or.inl e
  · exact Or.inr fun eg => e (shapeF_inj hs nu mu hnu hmu eg)

end P1K8

#print axioms P1K8.at_map
#print axioms P1K8.shapeF_lists
#print axioms P1K8.shapeF_foreign
#print axioms P1K8.shapeF_inj
#print axioms P1K8.made_oneEach
