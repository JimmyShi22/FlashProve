-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/ShapeTrees.lean.
WHAT IT DOES NOT SHOW. No soundness. That shapeF returns at any arguments: h is a premise
throughout. Nothing on the steps of a plan behind shapeF (addTreesF, ownerIs, borderMeans, trimL):
that these keep ix, NM and gtTree is others' to say. Nothing on the arrays U1 to U3, ZZ, BZ.
WORDS. "Array": a committed matrix in a sub-proof's list; names taken from the C++ call it a tree
(gtTree). "The three lists": ix.PK (the arrays of the sub-proof's own matrices that no other
sub-proof reads), ix.TX (of its own that another reads), ix.FT (of earlier sub-proofs' matrices).
LETTERS. No "there is" in a premise. General in tl, m, txOf, f, hasU, tau: no scope is asked.
OBJECT. What HTailF2.shapeF (OnBytes/Model/Tail.lean) returns.
USER. The laws of the planners' shared routine addTreesF, array by array: "an array of the sort of a
matrix's" can then be said by the matrices' own list gtTree.
WHAT IT IS. shapeF_trees: A NUMBER t STANDS IN ONE OF THE THREE LISTS JUST IF IT IS THE ARRAY OF A
MATRIX: gtTree.getD mu 0 = t for a mu below NM. From the right to the left it is
shapeF_names (Johnson/Road/K4/Names/ShapeNames.lean), arm by arm, once each matrix's kind is known
to be 0 or 1. From the left to the right each index of each list is hit: PK and TX since the lists
of matrices beside them are filtered ranges, without a member twice; FT since the routine takes the
earlier sub-proofs' arrays in order and refuses unless all are taken.
shapeF_more: what lacked, off one more walk through the routine: NM = m.size; each kind is 0, or 1
with a "foreign"; pkMat is the range filtered by isPK; PK has pkMat's size and FT has f's; each j
below f.size is the "foreign" of a matrix of kind 1. shapeF_NM, shapeF_kinds, shapeF_pk,
shapeF_pkSize, shapeF_ftSize, shapeF_ftHit: its parts by name.
THE WALK IS ANOTHER FILE's: that of shapeF_names, line by line where the routine is cut (ok_of_jp,
ok_of_bind, forIn_keeps), with other invariants: said plainly. NOT TO BE TAKEN FOR
Meaning.Plan.shapeF_gt (Johnson/Goal/Meaning/PlanPort.lean), which says gtTree.size = NM.

-/
import Johnson.Road.K4.Names.ShapePx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- Matrix mu is of kind 0, or of kind 1 with the number of an earlier sub-proof's array. -/
def KindOk (m : Array TMat) (mu : Nat) : Prop :=
  (m.getD mu {}).kind = 0 ∨ ((m.getD mu {}).kind = 1 ∧ ∃ j, (m.getD mu {}).foreign = some j)

/-- Array number j of the earlier sub-proofs' is taken by a matrix below n. -/
def FtHit (m : Array TMat) (n j : Nat) : Prop :=
  ∃ mu, mu < n ∧ (m.getD mu {}).kind = 1 ∧ (m.getD mu {}).foreign = some j

theorem FtHit.mono {m : Array TMat} {n j : Nat} (h : FtHit m n j) : FtHit m (n + 1) j := by
  obtain ⟨mu, h1, h2⟩ := h
  exact ⟨mu, Nat.lt_succ_of_lt h1, h2⟩

/-- One matrix more, of a kind that is in order. -/
theorem kinds_succ {m : Array TMat} {n : Nat} (I : ∀ mu, mu < n → KindOk m mu) (h : KindOk m n) :
    ∀ mu, mu < n + 1 → KindOk m mu := by
  intro mu hmu
  by_cases hc : mu < n
  · exact I mu hc
  · obtain rfl : mu = n := by omega
    exact h

variable {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)} {f : Array T2Foreign}
  {hasU : Array Bool} {tau : Nat}

/-- **What lacked, off one more walk through the routine.** -/
theorem shapeF_more (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.NM = m.size ∧ (∀ mu, mu < m.size → KindOk m mu) ∧
      tl'.pkMat.toList = (List.range m.size).filter (isPK m txOf) ∧
      tl'.ix.PK.size = tl'.pkMat.size ∧ tl'.ix.FT.size = f.size ∧
      ∀ j, j < f.size → FtHit m m.size j := by
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
  obtain ⟨hnf, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨e1, -, e3, -⟩ := Fo.piecesF_keys h
  obtain ⟨e4, -, -⟩ := piecesF_lists h
  rw [e1, e3, e4]
  clear h e1 e3 e4 h2
  have hF : nextF = f.size := by simpa using hnf
  have K1 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) =>
      s.snd.fst.toList = (List.range pre.length).filter (isPK m txOf))
    (fun pre a rest e s s' hI hs => by
      obtain ⟨kT, pk, px⟩ := s
      have I1 : pk.toList = (List.range pre.length).filter (isPK m txOf) := hI
      have ha := range_split e
      subst ha
      have hlen : (pre ++ [pre.length]).length = pre.length + 1 := by simp
      dsimp only at hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i i hi
          obtain ⟨_, hs⟩ := ok_of_jp hs
          have hp : ¬ isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi]
            simp
          refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
          show pk.toList = _
          rw [hlen, filt_succ, if_neg hp, List.append_nil]
          exact I1
        · rename_i hi
          have hp : isPK m txOf pre.length = true := by
            unfold isPK
            rw [hi, hk]
            rfl
          refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
          show (pk.push pre.length).toList = _
          rw [hlen, filt_succ, if_pos hp, Array.toList_push, I1]
      · rename_i hk
        have hp : ¬ isPK m txOf pre.length = true := by
          unfold isPK
          intro hx
          rw [Bool.and_eq_true] at hx
          exact hk hx.1
        refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
        show pk.toList = _
        rw [hlen, filt_succ, if_neg hp, List.append_nil]
        exact I1)
    (List.range m.size) [] _ _ rfl rfl h1
  have K3 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      (∀ mu, mu < pre.length → KindOk m mu) ∧
        ∀ j, j < s.snd.snd.snd.fst → FtHit m pre.length j)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      have J1 : ∀ mu, mu < pre.length → KindOk m mu := hI.1
      have J2 : ∀ j, j < nextF' → FtHit m pre.length j := hI.2
      have ha := range_split e
      subst ha
      have hlen : (pre ++ [pre.length]).length = pre.length + 1 := by simp
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      split at hs
      · rename_i hk
        have hk0 : (m.getD pre.length {}).kind = 0 := by simpa using hk
        split at hs
        · refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · rw [hlen]
            exact kinds_succ J1 (Or.inl hk0)
          · intro j hj
            rw [hlen]
            exact (J2 j hj).mono
        · refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
          · rw [hlen]
            exact kinds_succ J1 (Or.inl hk0)
          · intro j hj
            rw [hlen]
            exact (J2 j hj).mono
      · split at hs
        · rename_i hk1
          have hk1' : (m.getD pre.length {}).kind = 1 := by simpa using hk1
          split at hs
          · rename_i j hj
            simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · rename_i hjn
                  have hjn' : j = nextF' := by simpa using hjn
                  refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
                  · rw [hlen]
                    exact kinds_succ J1 (Or.inr ⟨hk1', j, hj⟩)
                  · intro j' hj'
                    have hj2 : j' < nextF' + 1 := hj'
                    rw [hlen]
                    by_cases hc : j' < nextF'
                    · exact (J2 j' hc).mono
                    · obtain rfl : j' = j := by omega
                      exact ⟨pre.length, Nat.lt_succ_self _, hk1', hj⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl
    ⟨fun _ hx => absurd hx (Nat.not_lt_zero _), fun _ hx => absurd hx (Nat.not_lt_zero _)⟩ h3
  dsimp only at K1 K3
  rw [List.length_range] at K1 K3
  obtain ⟨B1, B2⟩ := K3
  refine ⟨rfl, B1, K1, ?_, ?_, fun j hj => B2 j (by rw [hF]; exact hj)⟩
  · show (Array.map (fun x => count + x) (Array.range pkMat.size)).size = pkMat.size
    rw [Array.size_map, Array.size_range]
  · show (Array.map (fun x => count + pkMat.size + pxMat.size + 2 + x) (Array.range f.size)).size =
      f.size
    rw [Array.size_map, Array.size_range]

theorem shapeF_NM (h : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.NM = m.size :=
  (shapeF_more h).1

theorem shapeF_kinds (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    ∀ mu, mu < m.size → KindOk m mu := (shapeF_more h).2.1

theorem shapeF_pk (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.pkMat.toList = (List.range m.size).filter (isPK m txOf) := (shapeF_more h).2.2.1

/-- **The list PK has just as many entries as the list of matrices beside it.** -/
theorem shapeF_pkSize (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.ix.PK.size = tl'.pkMat.size := (shapeF_more h).2.2.2.1

/-- **The list FT has just as many entries as there are earlier sub-proofs' arrays.** -/
theorem shapeF_ftSize (h : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.ix.FT.size = f.size :=
  (shapeF_more h).2.2.2.2.1

theorem shapeF_ftHit (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    ∀ j, j < f.size → FtHit m m.size j := (shapeF_more h).2.2.2.2.2

/-- In a filtered range a member stands at one index alone. -/
theorem filt_once (p : Nat → Bool) (n : Nat) {a : Array Nat}
    (ha : a.toList = (List.range n).filter p) {i r μ : Nat} (hi : a[i]? = some μ)
    (hr : a[r]? = some μ) : r = i := by
  have hnd : a.toList.Nodup := by
    rw [ha]
    exact List.Nodup.filter _ List.nodup_range
  have hl : r < a.toList.length := by
    rw [Array.length_toList]
    exact (Array.getElem?_eq_some_iff.1 hr).1
  refine List.getElem?_inj hl hnd ?_
  rw [Array.getElem?_toList, Array.getElem?_toList, hr, hi]

/-- A member of such a list lies below n and passes the test. -/
theorem filt_mem (p : Nat → Bool) (n : Nat) {a : Array Nat}
    (ha : a.toList = (List.range n).filter p) {i μ : Nat} (hi : a[i]? = some μ) :
    μ < n ∧ p μ = true := by
  have hm : μ ∈ a.toList := List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hi)
  rw [ha] at hm
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hm
  exact ⟨List.mem_range.1 h1, h2⟩

/-- **A NUMBER STANDS IN ONE OF THE THREE LISTS JUST IF IT IS THE ARRAY OF A MATRIX.** -/
theorem shapeF_trees (h : tl.shapeF m txOf f hasU tau = .ok tl') (t : Nat) :
    (∃ i : Nat, tl'.ix.PK[i]? = some t ∨ tl'.ix.TX[i]? = some t ∨ tl'.ix.FT[i]? = some t) ↔
      ∃ mu, mu < tl'.NM ∧ tl'.gtTree.getD mu 0 = t := by
  obtain ⟨hNM, hK, hpk, hPK, hFT, hHit⟩ := shapeF_more h
  obtain ⟨hpx, hTX, -⟩ := shapeF_px h
  rw [hNM]
  constructor
  · rintro ⟨i, hi | hi | hi⟩
    · have hl : i < tl'.pkMat.size := by
        rw [← hPK]
        exact (Array.getElem?_eq_some_iff.1 hi).1
      have hμ := getD_some hl
      obtain ⟨hlt, hp⟩ := filt_mem _ _ hpk hμ
      unfold isPK at hp
      rw [Bool.and_eq_true] at hp
      have hk : (m.getD (tl'.pkMat.getD i 0) {}).kind = 0 := by simpa using hp.1
      have ht : txOf.getD (tl'.pkMat.getD i 0) none = none := Option.isNone_iff_eq_none.1 hp.2
      obtain ⟨r, r1, r2⟩ := (shapeF_names h hlt).1 hk ht
      obtain rfl := filt_once _ _ hpk hμ r2
      exact ⟨_, hlt, Option.some.inj (r1.symm.trans hi)⟩
    · have hl : i < tl'.pxMat.size := by
        rw [← hTX]
        exact (Array.getElem?_eq_some_iff.1 hi).1
      have hμ := getD_some hl
      obtain ⟨hlt, hp⟩ := filt_mem _ _ hpx hμ
      unfold isPX at hp
      rw [Bool.and_eq_true] at hp
      have hk : (m.getD (tl'.pxMat.getD i 0) {}).kind = 0 := by simpa using hp.1
      obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 hp.2
      obtain ⟨r1, r2⟩ := (shapeF_names h hlt).2.1 hk i' hi'
      obtain rfl := filt_once _ _ hpx hμ r2
      exact ⟨_, hlt, Option.some.inj (r1.symm.trans hi)⟩
    · have hl : i < f.size := by
        rw [← hFT]
        exact (Array.getElem?_eq_some_iff.1 hi).1
      obtain ⟨mu, hlt, hk, hj⟩ := hHit i hl
      exact ⟨mu, hlt, Option.some.inj (((shapeF_names h hlt).2.2 hk i hj).1.symm.trans hi)⟩
  · rintro ⟨mu, hmu, rfl⟩
    rcases hK mu hmu with hk | ⟨hk, j, hj⟩
    · cases ht : txOf.getD mu none with
      | none =>
        obtain ⟨r, r1, -⟩ := (shapeF_names h hmu).1 hk ht
        exact ⟨r, Or.inl r1⟩
      | some i => exact ⟨i, Or.inr (Or.inl ((shapeF_names h hmu).2.1 hk i ht).1)⟩
    · exact ⟨j, Or.inr (Or.inr ((shapeF_names h hmu).2.2 hk j hj).1)⟩

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.shapeF_more
#print axioms OnBytes.Road.K4.Names.shapeF_NM
#print axioms OnBytes.Road.K4.Names.shapeF_kinds
#print axioms OnBytes.Road.K4.Names.shapeF_pk
#print axioms OnBytes.Road.K4.Names.shapeF_pkSize
#print axioms OnBytes.Road.K4.Names.shapeF_ftSize
#print axioms OnBytes.Road.K4.Names.shapeF_ftHit
#print axioms OnBytes.Road.K4.Names.filt_once
#print axioms OnBytes.Road.K4.Names.filt_mem
#print axioms OnBytes.Road.K4.Names.FtHit.mono
#print axioms OnBytes.Road.K4.Names.kinds_succ
#print axioms OnBytes.Road.K4.Names.shapeF_trees
