-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/RestIsPartsProof.lean: THE REST, AS
Johnson/Desc/K2/Honest/Carrying.lean's ONE LIST HAS IT, HAS THE LENGTH AND THE OFFSETS OF THE
PROGRAM's `switchParts` (OnBytes/Iop/Cs.lean). Statements and proofs. Lists and numbers; no coin, no
round, no frame.

  `Lists.inFive`            an entry of five lists in a row, by the list and the number in it
  `Lists.len_blocks`      the length of a list made of blocks of one length
  `startsFrom_getD`   an entry of the program's list of equally spaced starts
  `padsFold`        the program's fold over the kept members' pads: the starts and the end
  `Lists.map_zipIdx_fst`, `Lists.before_zipIdx`, `Lists.zipIdx_at`   a numbered list, where the
                    numbers are not read
  `restIsParts`     `RestIsParts` (Johnson/Desc/K2/Honest/Inner/Statement.lean)

By: the lemmas on a list made of blocks (`flatMap_at`, `flatMap_block`, `before_const`,
`length_flatMap_before`, Johnson/Top/H0/K2Hands/RowsAt.lean).

Limits. Nothing on where the rest lies in the carrying message: LaidBackProof.lean. Nothing on any
property.

-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Top.H0.K2Hands.RowsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open VerifiableInference.Desc.First.K2Hands (before flatMap_at flatMap_block before_const
  length_flatMap_before)

/-- An entry of five lists in a row. -/
theorem Lists.inFive {α : Type} (A B C D E : List α) :
    (∀ i, i < A.length → (A ++ B ++ C ++ D ++ E)[i]? = A[i]?) ∧
    (∀ i, i < B.length → (A ++ B ++ C ++ D ++ E)[A.length + i]? = B[i]?) ∧
    (∀ i, i < C.length → (A ++ B ++ C ++ D ++ E)[A.length + B.length + i]? = C[i]?) ∧
    (∀ i, i < D.length →
      (A ++ B ++ C ++ D ++ E)[A.length + B.length + C.length + i]? = D[i]?) ∧
    ∀ i, (A ++ B ++ C ++ D ++ E)[A.length + B.length + C.length + D.length + i]? = E[i]? := by
  refine ⟨fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i => ?_⟩
  · rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left h]
  · rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  · rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]
    omega
  · rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]
    omega
  · rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
    congr 1
    simp only [List.length_append]
    omega

/-- The length of a list made of blocks of one length. -/
theorem Lists.len_blocks {α β : Type} (f : α → List β) (R : Nat) (l : List α)
    (hR : ∀ x ∈ l, (f x).length = R) : (l.flatMap f).length = l.length * R := by
  rw [length_flatMap_before, before_const f R l l.length hR (Nat.le_refl _)]

/-- An entry of the program's list of equally spaced starts. -/
theorem startsFrom_getD (s st n j : Nat) (h : j < n) :
    (startsFrom s st n).getD j 0 = s + st * j := by
  unfold startsFrom
  rw [Array.getD_eq_getD_getElem?]
  simp [h]

/-- An entry of a list of values of a function on the numbers below n. -/
theorem Lists.range_map_at {β : Type} (f : Nat → β) (n i : Nat) (h : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  simp [h]

/-- The program's fold over the kept members' pads, on lists: entry a of the starts is the start
plus the lengths in front; the end is the start plus all lengths. -/
theorem padsFold (len : Nat → Nat) : ∀ (l : List Nat) (acc : Array Nat) (d : Nat),
    (l.foldl (fun (s : Array Nat × Nat) o => (s.1.push s.2, s.2 + len o)) (acc, d)).2 =
        d + (l.map len).sum ∧
    ∀ a, a < l.length →
      (l.foldl (fun (s : Array Nat × Nat) o => (s.1.push s.2, s.2 + len o)) (acc, d)).1.getD
          (acc.size + a) 0 = d + ((l.take a).map len).sum
  | [], acc, d => by simp
  | o :: l, acc, d => by
    have ih := padsFold len l (acc.push d) (d + len o)
    refine ⟨?_, fun a ha => ?_⟩
    · rw [List.foldl_cons, ih.1, List.map_cons, List.sum_cons]
      omega
    · rw [List.foldl_cons]
      cases a with
      | zero =>
        have keep : ∀ (l : List Nat) (acc : Array Nat) (d i : Nat), i < acc.size →
            (l.foldl (fun (s : Array Nat × Nat) o => (s.1.push s.2, s.2 + len o)) (acc, d)).1.getD
              i 0 = acc.getD i 0 := by
          intro l
          induction l with
          | nil => intro acc d i _; rfl
          | cons o l ih2 =>
            intro acc d i hi
            rw [List.foldl_cons, ih2 (acc.push d) (d + len o) i (by simp; omega)]
            rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
              Array.getElem?_push_lt hi]
            simp [hi]
        rw [Nat.add_zero, keep l (acc.push d) (d + len o) acc.size (by simp)]
        simp
      | succ a =>
        have h2 := ih.2 a (by simpa using Nat.lt_of_succ_lt_succ ha)
        rw [Array.size_push] at h2
        rw [show acc.size + (a + 1) = acc.size + 1 + a by omega, h2, List.take_succ_cons,
          List.map_cons, List.sum_cons]
        omega

/-- A map over a numbered list that does not read the numbers. -/
theorem Lists.map_zipIdx_fst {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.zipIdx n).map (fun s => f s.1) = l.map f
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, Lists.map_zipIdx_fst f l (n + 1)]

/-- The blocks in front of block a of a numbered list, where a block's length does not hang on the
number. -/
theorem Lists.before_zipIdx {α β : Type} (f : α × Nat → List β) (h : α → Nat)
    (hf : ∀ x, (f x).length = h x.1) : ∀ (l : List α) (n a : Nat),
    before f (l.zipIdx n) a = ((l.take a).map h).sum
  | [], _, _ => by simp [before]
  | _ :: _, _, 0 => by simp [before]
  | x :: l, n, a + 1 => by
    have ih := Lists.before_zipIdx f h hf l (n + 1) a
    unfold before at ih ⊢
    simp only [hf] at ih
    simp only [List.zipIdx_cons, List.take_succ_cons, List.map_cons, List.sum_cons, hf, ih]

/-- An entry of a numbered list. -/
theorem Lists.zipIdx_at {α : Type} (l : List α) (a : Nat) (x : α) (h : l[a]? = some x) :
    l.zipIdx[a]? = some (x, a) := by
  simp [h]

/-- **The rest has the length and the offsets of the program's `switchParts`.** -/
theorem restIsParts : RestIsParts := by
  intro S old T W hm hF Z P c zk v keptRows
  -- the five lists
  let fA : Nat → List Cb.Gl.E := fun j => (List.range zk.ell).map (W.mask j)
  let B : List Cb.Gl.E := (List.range c.r).map W.mainTail
  let fK : Nat × Nat → List Cb.Gl.E := fun x => (List.range c.r).map ((W.kept x.1).tail x.2)
  let fD : Nat → List Cb.Gl.E := fun j => (List.range zk.r).map (W.maskTail j)
  let fE : OracleShape × Nat → List Cb.Gl.E := fun x =>
    (padPlaces Z.codes x.1).map fun p => (W.kept x.2).entry x.1 p.index
  have hC : (Z.kept.zipIdx.flatMap fun x =>
      (List.range x.1.mainRows).flatMap fun b => (List.range c.r).map ((W.kept x.2).tail b)) =
      keptRows.flatMap fK := by
    show _ = (Z.kept.zipIdx.flatMap fun s =>
      (List.range s.1.mainRows).map fun b => (s.2, b)).flatMap fK
    rw [List.flatMap_assoc]
    congr 1
    funext s
    rw [List.flatMap_map]
  have hrest : rest Z W =
      (List.range 2).flatMap fA ++ B ++ keptRows.flatMap fK ++ (List.range 2).flatMap fD ++
        Z.kept.zipIdx.flatMap fE := by
    rw [← hC]
    rfl
  have rA : ∀ x ∈ List.range 2, (fA x).length = zk.ell := fun x _ => by simp [fA]
  have rK : ∀ x ∈ keptRows, (fK x).length = c.r := fun x _ => by simp [fK]
  have rD : ∀ x ∈ List.range 2, (fD x).length = zk.r := fun x _ => by simp [fD]
  have lA : ((List.range 2).flatMap fA).length = 2 * zk.ell := by
    rw [Lists.len_blocks fA zk.ell _ rA, List.length_range]
  have lB : B.length = c.r := by simp [B]
  have lK0 : keptRows.length = old.keptRows := by
    show (Z.kept.zipIdx.flatMap fun s =>
      (List.range s.1.mainRows).map fun b => (s.2, b)).length = _
    rw [List.length_flatMap, hF.rows]
    have e : (Z.kept.zipIdx.map fun s : OracleShape × Nat =>
        ((List.range s.1.mainRows).map fun b => (s.2, b)).length) =
        Z.kept.zipIdx.map fun s => (fun t : OracleShape => t.mainRows) s.1 := by
      apply List.map_congr_left
      intro s _
      simp
    rw [e, Lists.map_zipIdx_fst]
    show (((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).map
      fun t : OracleShape => t.mainRows).sum = _
    rw [List.map_map]
    rfl
  have lK : (keptRows.flatMap fK).length = old.keptRows * c.r := by
    rw [Lists.len_blocks fK c.r _ rK, lK0]
  have lD : ((List.range 2).flatMap fD).length = 2 * zk.r := by
    rw [Lists.len_blocks fD zk.r _ rD, List.length_range]
  have hE : ∀ x : OracleShape × Nat, (fE x).length = (padPlaces S.codes x.1).length :=
    fun x => by simp [fE]; rfl
  obtain ⟨f1, f2, f3, f4, f5⟩ := Lists.inFive ((List.range 2).flatMap fA) B (keptRows.flatMap fK)
    ((List.range 2).flatMap fD) (Z.kept.zipIdx.flatMap fE)
  rw [lA, lB, lK, lD] at f5
  rw [lA, lB, lK] at f4
  rw [lA, lB] at f3
  rw [lA] at f2
  have hv : ∀ i x, (rest Z W)[i]? = some x → v i = x := fun i x h => by
    show (rest Z W).getD i zeroG = x
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  -- the program's fold over the pads
  have hpads := padsFold (fun o => (padOf S o).length) (switchKept old).toList #[]
    (old.masks * zk.ell + c.r + old.keptRows * c.r + old.masks * zk.r)
  have hPl : P.length = old.masks * zk.ell + c.r + old.keptRows * c.r + old.masks * zk.r +
      ((switchKept old).toList.map fun o => (padOf S o).length).sum := by
    rw [← hpads.1, Array.foldl_toList]
    rfl
  have hPo : ∀ a, a < (switchKept old).toList.length → P.oldPadAt.getD a 0 =
      old.masks * zk.ell + c.r + old.keptRows * c.r + old.masks * zk.r +
        (((switchKept old).toList.take a).map fun o => (padOf S o).length).sum := by
    intro a ha
    have h := hpads.2 a ha
    rw [Array.foldl_toList] at h
    simpa using h
  have hsum : ∀ a, ((Z.kept.take a).map fun s => (padPlaces S.codes s).length).sum =
      (((switchKept old).toList.take a).map fun o => (padOf S o).length).sum := by
    intro a
    show ((((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).take a).map
      fun s => (padPlaces S.codes s).length).sum = _
    rw [← List.map_take, List.map_map]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the length
    rw [hrest, hPl, hm]
    simp only [List.length_append, lA, lB, lK, lD]
    rw [length_flatMap_before, Lists.before_zipIdx fE (fun s => (padPlaces S.codes s).length) hE,
      List.length_zipIdx, List.take_length]
    have h := hsum Z.kept.length
    rw [List.take_length] at h
    have h2 : (switchKept old).toList.take Z.kept.length = (switchKept old).toList := by
      apply List.take_of_length_le
      show _ ≤ ((switchKept old).toList.map _).length
      rw [List.length_map]
    rw [h2] at h
    rw [h]
  · -- the two mask rows' messages
    intro r i hr hi
    apply hv
    have e : P.maskAt.getD r 0 = 0 + zk.ell * r := startsFrom_getD 0 zk.ell old.masks r (by omega)
    rw [e, hrest, show 0 + zk.ell * r + i = r * zk.ell + i by rw [Nat.zero_add, Nat.mul_comm],
      f1 _ (by rw [lA]; nlinarith),
      flatMap_block fA zk.ell _ rA r i r (by simp [hr]) hi]
    exact Lists.range_map_at _ _ _ hi
  · -- the main row's tail
    intro q hq
    apply hv
    rw [hrest, show P.mainTailAt + q = 2 * zk.ell + q by show old.masks * zk.ell + q = _; rw [hm],
      f2 _ (by rw [lB]; exact hq)]
    exact Lists.range_map_at _ _ _ hq
  · -- the kept rows' tails
    intro n x q hx hq
    apply hv
    have hn : n < old.keptRows := by
      rw [← lK0]
      exact (List.getElem?_eq_some_iff.1 hx).1
    have e : P.keptTailAt.getD n 0 = old.masks * zk.ell + c.r + c.r * n :=
      startsFrom_getD _ c.r old.keptRows n hn
    rw [e, hm, hrest, show 2 * zk.ell + c.r + c.r * n + q = 2 * zk.ell + c.r + (n * c.r + q) by
        rw [Nat.mul_comm c.r n]; omega,
      f3 _ (by rw [lK]; nlinarith), flatMap_block fK c.r _ rK n q x hx hq]
    exact Lists.range_map_at _ _ _ hq
  · -- the two mask rows' tails
    intro r q hr hq
    apply hv
    have e : P.maskTailAt.getD r 0 =
        old.masks * zk.ell + c.r + old.keptRows * c.r + zk.r * r :=
      startsFrom_getD _ zk.r old.masks r (by omega)
    rw [e, hm, hrest, show 2 * zk.ell + c.r + old.keptRows * c.r + zk.r * r + q =
        2 * zk.ell + c.r + old.keptRows * c.r + (r * zk.r + q) by
        rw [Nat.mul_comm zk.r r]; omega,
      f4 _ (by rw [lD]; nlinarith), flatMap_block fD zk.r _ rD r q r (by simp [hr]) hq]
    exact Lists.range_map_at _ _ _ hq
  · -- the old pads
    intro a s t p hs hp
    apply hv
    have ha : a < (switchKept old).toList.length := by
      have := (List.getElem?_eq_some_iff.1 hs).1
      have e : Z.kept.length = (switchKept old).toList.length := by
        show ((switchKept old).toList.map _).length = _
        rw [List.length_map]
      omega
    have ht : t < (fE (s, a)).length := by
      rw [hE]
      exact (List.getElem?_eq_some_iff.1 hp).1
    rw [hPo a ha, hm, hrest, ← hsum a,
      ← Lists.before_zipIdx fE (fun s => (padPlaces S.codes s).length) hE Z.kept 0 a,
      Nat.add_assoc, f5,
      flatMap_at fE _ a t (s, a) (Lists.zipIdx_at _ _ _ hs) ht]
    show ((padPlaces S.codes s).map fun p => (W.kept a).entry s p.index)[t]? = _
    rw [List.getElem?_map, hp]
    rfl

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.restIsParts
