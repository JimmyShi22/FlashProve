-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/KeptLaw2.lean: proofs of the three statements L-2 of
KeptSpec.lean, on where `sortedOf` (RunOf.lean) takes the value at an address from.

  `src_reads`    `Spec.src_reads`: `sortedOf` at an address is the value at `srcOf`, encoded
  `src_nodup`    `Spec.src_nodup`: `allSrc` has no repeat
  `kept_perm`    `Spec.kept_perm`: where the stages pass `StagesOk`, `srcOf` maps the list of kept
                 addresses onto a rearrangement of `allSrc`
  `seg`, `seg_add`, `grid_seg`   a stretch of the switches' values; two stretches in a row; a grid
                 read row by row is a stretch
  `hideIx`, `hide_perm`   the number, in the hiding polynomial's own order, of the coefficient that
                 `hideOf` numbers n; the 2 k + 1 numbers of `hideNums` go onto 0 to 2 k
  `ride_perm`, `switch_perm`, `from_perm`   what rides with a new stage; one switch; the switches
                 from a stage on: each list of kept addresses goes onto its own stretch

By what. `src_reads`: by cases on the address; the two definitions have the same offsets arm by arm.
`src_nodup`: three lists under three constructors, each the image of a range or a grid under a
function that is one to one. `kept_perm`: a switch's kept addresses are cut into the main rows'
tails, the free entries with the pad, the mask rows' tails and what rides; each piece is a stretch
that begins where the piece before ends (`marksAt`), but for two rearrangements: the hiding
polynomial's coefficients (`hide_perm`) and the masking word's four lists. Then induction along the
stages: `startAt_succ` moves the beginning by `dueSwitch`, as `dueFrom` counts.

Limits. Of `StagesOk` the proof uses two things: that there are two stages or more, and at each
switch the second clause of `switchFitB`, through `free_of_fit`: at least one free entry, so that
the pad's number is the last of the free room. Together the three say what KeptSpec.lean's head says
of L-2: on the list of kept addresses `srcOf` is one to one, within the counts, and onto. L-1, L-3
and L-4 are not proved here, and L-5 is not stated here (it is in LentSpec.lean): nothing on what a
run reads, on the members' values, or on the step from a part's values to a `TestCoins`. Nothing
here says that the values at these numbers differ, or how they are sampled. Nothing on completeness,
soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.KeptSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE)
open Fmt.M1 (E Stage)

/-! ## 1 `sortedOf` reads at `srcOf` -/

/-- **L-2, first half.** -/
theorem src_reads : Spec.src_reads := by
  intro stages C a
  cases a with
  | main i b n => rfl
  | mask i b n => rfl
  | hide i n =>
    simp only [Sorted.read, sortedOf, srcOf]
    split_ifs <;> rfl
  | fresh i b n =>
    simp only [Sorted.read, sortedOf, srcOf]
    split_ifs <;> rfl
  | free i n => rfl
  | pad i => rfl
  | word i j n =>
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => rfl

/-! ## 2 Grids; `allSrc` has no repeat -/

theorem mem_grid {α : Type} {r m : ℕ} {f : ℕ → ℕ → α} {x : α} :
    x ∈ grid r m f ↔ ∃ b, b < r ∧ ∃ n, n < m ∧ f b n = x := by
  simp only [grid, List.mem_flatMap, List.mem_map, List.mem_range]

theorem grid_succ {α : Type} (r m : ℕ) (f : ℕ → ℕ → α) :
    grid (r + 1) m f = grid r m f ++ (List.range m).map (f r) := by
  simp only [grid, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem grid_map {α β : Type} (F : α → β) (r m : ℕ) (f : ℕ → ℕ → α) :
    (grid r m f).map F = grid r m fun b n => F (f b n) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [grid_succ, grid_succ, List.map_append, ih, List.map_map]
    rfl

/-- A grid of a function that is one to one in both arguments has no repeat. -/
theorem grid_nodup {α : Type} (r m : ℕ) (f : ℕ → ℕ → α)
    (hf : ∀ b n b' n', f b n = f b' n' → b = b' ∧ n = n') : (grid r m f).Nodup := by
  induction r with
  | zero => exact List.nodup_nil
  | succ r ih =>
    rw [grid_succ]
    refine List.Nodup.append ih
      (List.Nodup.map (fun n n' h => (hf _ _ _ _ h).2) (List.nodup_range ..)) fun x hx hx' => ?_
    obtain ⟨b, hb, n, _, rfl⟩ := mem_grid.1 hx
    obtain ⟨n', _, h⟩ := List.mem_map.1 hx'
    have := (hf _ _ _ _ h).1
    omega

/-- **L-2, third part.** -/
theorem src_nodup : Spec.src_nodup := by
  intro stages
  cases stages with
  | nil => exact List.nodup_nil
  | cons s rest =>
    show ((List.range (2 * s.k + 1)).map CoinSrc.hide ++ grid (2 ^ s.h) s.Z.r CoinSrc.tails ++
      (List.range (dueRest (s :: rest))).map CoinSrc.rest).Nodup
    refine List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_
    · exact List.Nodup.map (fun _ _ h => CoinSrc.hide.inj h) (List.nodup_range ..)
    · exact grid_nodup _ _ _ fun _ _ _ _ h => CoinSrc.tails.inj h
    · intro x hx hx'
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, _, n, _, e⟩ := mem_grid.1 hx'
      cases e
    · exact List.Nodup.map (fun _ _ h => CoinSrc.rest.inj h) (List.nodup_range ..)
    · intro x hx hx'
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx'
      rcases List.mem_append.1 hx with h | h
      · obtain ⟨a, _, e⟩ := List.mem_map.1 h
        cases e
      · obtain ⟨b, _, n, _, e⟩ := mem_grid.1 h
        cases e

/-! ## 3 Stretches of the switches' values -/

/-- The numbers a, .., a + n - 1 of the switches' values. -/
def seg (a n : ℕ) : List CoinSrc := (List.range n).map fun t => .rest (a + t)

theorem seg_add (a n m : ℕ) : seg a (n + m) = seg a n ++ seg (a + n) m := by
  unfold seg
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  show CoinSrc.rest (a + (n + t)) = CoinSrc.rest (a + n + t)
  rw [Nat.add_assoc]

theorem seg_zero (n : ℕ) : seg 0 n = (List.range n).map .rest := by
  unfold seg
  simp only [Nat.zero_add]

theorem seg_four (a x y z w : ℕ) : seg a (x + y + z + w) =
    seg a x ++ seg (a + x) y ++ seg (a + x + y) z ++ seg (a + x + y + z) w := by
  rw [seg_add, seg_add, seg_add]
  simp only [Nat.add_assoc]

theorem grid_seg (a r m : ℕ) :
    (grid r m fun b n => CoinSrc.rest (a + b * m + n)) = seg a (r * m) := by
  induction r with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ r ih =>
    rw [grid_succ, ih, Nat.succ_mul, seg_add]
    rfl

/-- The free entries but the last, then the pad. -/
theorem free_pad (x f : ℕ) : ((List.range f).map fun n => CoinSrc.rest (x + n)) ++
    [CoinSrc.rest (x + (f + 1) - 1)] = seg x (f + 1) := by
  have e : x + (f + 1) - 1 = x + f + 0 := by omega
  rw [seg_add, e]
  rfl

/-! ## 4 The hiding polynomial's coefficients -/

/-- The number, in the polynomial's own order, of the coefficient that `hideOf` numbers n. -/
def hideIx (k n : ℕ) : ℕ :=
  if n = 0 then 2 * (k - 1)
  else if (n - 1) / 2 < k then 2 * ((n - 1) / 2 - 1) + (n - 2 * ((n - 1) / 2) - 1)
  else 2 * (k - 1) + (n - 2 * ((n - 1) / 2))

theorem hideIx_zero (k : ℕ) : hideIx k 0 = 2 * (k - 1) := if_pos rfl

/-- A variable that is not the last: degrees 1 and 2. -/
theorem hideIx_low {k l : ℕ} (h : l + 1 < k) :
    hideIx k (2 * (l + 1) + 1) = 2 * l ∧ hideIx k (2 * (l + 1) + 2) = 2 * l + 1 := by
  have d1 : (2 * (l + 1) + 1 - 1) / 2 = l + 1 := by omega
  have d2 : (2 * (l + 1) + 2 - 1) / 2 = l + 1 := by omega
  constructor
  · unfold hideIx
    rw [if_neg (by omega), d1, if_pos h]
    omega
  · unfold hideIx
    rw [if_neg (by omega), d2, if_pos h]
    omega

/-- The last variable: degrees 1 and 2. -/
theorem hideIx_last (l : ℕ) : hideIx (l + 1) (2 * (l + 1) + 1) = 2 * l + 1 ∧
    hideIx (l + 1) (2 * (l + 1) + 2) = 2 * l + 1 + 1 := by
  have d1 : (2 * (l + 1) + 1 - 1) / 2 = l + 1 := by omega
  have d2 : (2 * (l + 1) + 2 - 1) / 2 = l + 1 := by omega
  constructor
  · unfold hideIx
    rw [if_neg (by omega), d1, if_neg (by omega)]
    omega
  · unfold hideIx
    rw [if_neg (by omega), d2, if_neg (by omega)]
    omega

theorem pairs_range (k : ℕ) : ∀ n, n < k →
    ((List.range n).flatMap fun l => [2 * (l + 1) + 1, 2 * (l + 1) + 2]).map (hideIx k) =
      List.range (2 * n)
  | 0, _ => rfl
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := hideIx_low h
    rw [List.range_succ, List.flatMap_append, List.map_append, pairs_range k n (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
    rw [h1, h2, show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ,
      List.append_assoc]
    rfl

/-- The 2 k + 1 numbers of `hideNums` go onto 0, .., 2 k. -/
theorem hide_perm (k : ℕ) : ((hideNums k).map (hideIx k)).Perm (List.range (2 * k + 1)) := by
  cases k with
  | zero => exact List.Perm.of_eq rfl
  | succ k =>
    have h0 : hideIx (k + 1) 0 = 2 * k := hideIx_zero (k + 1)
    obtain ⟨h1, h2⟩ := hideIx_last k
    have e : (hideNums (k + 1)).map (hideIx (k + 1)) =
        2 * k :: (List.range (2 * k) ++ [2 * k + 1, 2 * k + 1 + 1]) := by
      unfold hideNums
      rw [List.map_cons, List.range_succ, List.flatMap_append, List.map_append,
        pairs_range (k + 1) k (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      rw [h0, h1, h2]
    rw [e, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by omega, List.range_succ, List.range_succ,
      List.range_succ]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact List.perm_middle.symm

theorem srcOf_hide (stages : List Stage) (i n k : ℕ)
    (hk : (stages.getD (i - 1) default).k = k) : srcOf stages (.hide i n) =
      if i = 1 then .hide (hideIx k n) else .rest ((marksAt stages (i - 2)).ride + hideIx k n) := by
  subst hk
  simp only [srcOf, hideIx]
  split_ifs <;> rfl

/-! ## 5 One switch -/

/-- What rides with the stage that switch j makes. -/
theorem ride_perm (stages : List Stage) (j : ℕ) (last : Bool) :
    ((keptRide (j + 2) (stages.getD (j + 1) default) last).map (srcOf stages)).Perm
      (seg (marksAt stages j).ride
        (if last then dueWord (stages.getD (j + 1) default)
          else dueFresh (stages.getD (j + 1) default))) := by
  cases last with
  | false =>
    show (((hideNums (stages.getD (j + 1) default).k).map (CoinAt.hide (j + 2)) ++
      grid (2 ^ (stages.getD (j + 1) default).h) (stages.getD (j + 1) default).Z.r
        (CoinAt.fresh (j + 2))).map (srcOf stages)).Perm
      (seg (marksAt stages j).ride (2 * (stages.getD (j + 1) default).k + 1 +
        2 ^ (stages.getD (j + 1) default).h * (stages.getD (j + 1) default).Z.r))
    have e1 : ((hideNums (stages.getD (j + 1) default).k).map (CoinAt.hide (j + 2))).map
        (srcOf stages) = ((hideNums (stages.getD (j + 1) default).k).map
          (hideIx (stages.getD (j + 1) default).k)).map
            fun t => CoinSrc.rest ((marksAt stages j).ride + t) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro n _
      exact (srcOf_hide stages (j + 2) n _ rfl).trans (if_neg (by omega))
    have e2 : (grid (2 ^ (stages.getD (j + 1) default).h) (stages.getD (j + 1) default).Z.r
        (CoinAt.fresh (j + 2))).map (srcOf stages) =
        seg ((marksAt stages j).ride + (2 * (stages.getD (j + 1) default).k + 1))
          (2 ^ (stages.getD (j + 1) default).h * (stages.getD (j + 1) default).Z.r) := by
      rw [grid_map, ← grid_seg]
      rfl
    rw [List.map_append, e1, e2, seg_add]
    exact ((hide_perm _).map _).append_right _
  | true =>
    show (((List.range (stages.getD (j + 1) default).C.l).map (CoinAt.word (j + 2) 0) ++
      (List.range (stages.getD (j + 1) default).Z.l).map (CoinAt.word (j + 2) 1) ++
      (List.range (stages.getD (j + 1) default).C.r).map (CoinAt.word (j + 2) 2) ++
      (List.range (stages.getD (j + 1) default).Z.r).map (CoinAt.word (j + 2) 3)).map
        (srcOf stages)).Perm
      (seg (marksAt stages j).ride ((stages.getD (j + 1) default).C.r +
        (stages.getD (j + 1) default).C.l + (stages.getD (j + 1) default).Z.l +
        (stages.getD (j + 1) default).Z.r))
    rw [seg_four, List.map_append, List.map_append, List.map_append, List.map_map, List.map_map,
      List.map_map, List.map_map, List.append_assoc (seg _ _) (seg _ _) (seg _ _)]
    exact List.perm_append_comm.append_right _

/-- **The kept addresses of switch j go onto the switch's own stretch.** -/
theorem switch_perm (stages : List Stage) (j : ℕ) (last : Bool)
    (hf : 1 ≤ freeRoom (stages.getD j default) (stages.getD (j + 1) default)) :
    ((keptSwitch (j + 2) (stages.getD j default) (stages.getD (j + 1) default) last).map
      (srcOf stages)).Perm
      (seg (marksAt stages j).main
        (dueSwitch (stages.getD j default) (stages.getD (j + 1) default) last)) := by
  obtain ⟨f, hf'⟩ : ∃ f, freeRoom (stages.getD j default) (stages.getD (j + 1) default) = f + 1 :=
    ⟨_, (Nat.sub_add_cancel hf).symm⟩
  have e1 : (grid (2 ^ (stages.getD (j + 1) default).k) (stages.getD (j + 1) default).C.r
      (CoinAt.main (j + 2))).map (srcOf stages) = seg (marksAt stages j).main
        (2 ^ (stages.getD (j + 1) default).k * (stages.getD (j + 1) default).C.r) := by
    rw [grid_map, ← grid_seg]
    rfl
  have e2 : ((List.range (freeRoom (stages.getD j default) (stages.getD (j + 1) default) - 1)).map
      (CoinAt.free (j + 2))).map (srcOf stages) ++ [srcOf stages (.pad (j + 2))] =
      seg ((marksAt stages j).main +
        2 ^ (stages.getD (j + 1) default).k * (stages.getD (j + 1) default).C.r)
        (freeRoom (stages.getD j default) (stages.getD (j + 1) default)) := by
    have ep : srcOf stages (.pad (j + 2)) = .rest ((marksAt stages j).main +
        2 ^ (stages.getD (j + 1) default).k * (stages.getD (j + 1) default).C.r +
        freeRoom (stages.getD j default) (stages.getD (j + 1) default) - 1) := rfl
    rw [ep, hf', Nat.add_sub_cancel, List.map_map, ← free_pad]
    rfl
  have e3 : (grid (2 ^ (stages.getD (j + 1) default).h) (stages.getD (j + 1) default).Z.r
      (CoinAt.mask (j + 2))).map (srcOf stages) = seg ((marksAt stages j).main +
        2 ^ (stages.getD (j + 1) default).k * (stages.getD (j + 1) default).C.r +
        freeRoom (stages.getD j default) (stages.getD (j + 1) default))
        (2 ^ (stages.getD (j + 1) default).h * (stages.getD (j + 1) default).Z.r) := by
    rw [grid_map, ← grid_seg]
    rfl
  unfold keptSwitch dueSwitch
  rw [seg_four, List.map_append, List.map_append, List.map_append, List.map_append, e1, e3,
    List.map_cons, List.map_nil, List.append_assoc (seg _ _) (List.map _ _) [_], e2]
  exact (ride_perm stages j last).append_left _

/-! ## 6 All switches -/

theorem getD_drop_next : ∀ (l : List Stage) (j : ℕ) (x : Stage) (t : List Stage),
    l.drop j = x :: t → l.getD j default = x ∧ l.drop (j + 1) = t
  | [], j, x, t, h => by simp at h
  | a :: l, 0, x, t, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | a :: l, j + 1, x, t, h => by
    have := getD_drop_next l j x t (by simpa using h)
    simpa using this

theorem startAt_succ : ∀ (j : ℕ) (s : Stage) (l : List Stage) (cur next : Stage)
    (rest : List Stage), (s :: l).drop j = cur :: next :: rest →
    startAt s l (j + 1) = startAt s l j + dueSwitch cur next rest.isEmpty
  | 0, s, l, cur, next, rest, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases rest <;> simp [startAt]
  | j + 1, s, l, cur, next, rest, h => by
    cases l with
    | nil => simp at h
    | cons s1 l1 =>
      have ih := startAt_succ j s1 l1 cur next rest (by simpa using h)
      simp only [startAt]
      rw [ih, Nat.add_assoc]

theorem main_succ (stages : List Stage) (j : ℕ) (cur next : Stage) (rest : List Stage)
    (h : stages.drop j = cur :: next :: rest) :
    (marksAt stages (j + 1)).main = (marksAt stages j).main + dueSwitch cur next rest.isEmpty := by
  cases stages with
  | nil => simp at h
  | cons s l => exact startAt_succ j s l cur next rest h

theorem free_of_fit {s n : Stage} (h : switchFitB s n = true) : 1 ≤ freeRoom s n := by
  simp only [switchFitB, Bool.and_eq_true, decide_eq_true_eq] at h
  have := h.1.1.1.2
  unfold freeRoom carriedIn
  omega

/-- **The kept addresses of the switches from stage j on go onto these switches' stretch.** -/
theorem from_perm (stages : List Stage) : ∀ (rest : List Stage) (cur : Stage) (j : ℕ),
    stages.drop j = cur :: rest → okFrom cur rest = true →
    ((keptFrom j cur rest).map (srcOf stages)).Perm
      (seg (marksAt stages j).main (dueFrom cur rest))
  | [], _, _, _, _ => List.Perm.of_eq rfl
  | next :: rest, cur, j, hd, hok => by
    obtain ⟨hc, hd1⟩ := getD_drop_next stages j cur (next :: rest) hd
    obtain ⟨hn, _⟩ := getD_drop_next stages (j + 1) next rest hd1
    simp only [okFrom, Bool.and_eq_true] at hok
    have ih := from_perm stages rest next (j + 1) hd1 hok.2
    rw [main_succ stages j cur next rest hd] at ih
    have sw := switch_perm stages j rest.isEmpty (by rw [hc, hn]; exact free_of_fit hok.1.2)
    rw [hc, hn] at sw
    show ((keptSwitch (j + 2) cur next rest.isEmpty ++ keptFrom (j + 1) next rest).map
      (srcOf stages)).Perm
      (seg (marksAt stages j).main (dueSwitch cur next rest.isEmpty + dueFrom next rest))
    rw [List.map_append, seg_add]
    exact sw.append ih

/-! ## 7 The whole list -/

/-- **L-2, second half.** -/
theorem kept_perm : Spec.kept_perm := by
  intro stages h
  match stages, h with
  | [], h => simp [StagesOk] at h
  | [_], h => simp [StagesOk] at h
  | s :: n :: rest, h =>
    have hB := from_perm (s :: n :: rest) (n :: rest) s 0 rfl h
    show (((hideNums s.k).map (CoinAt.hide 1) ++ grid (2 ^ s.h) s.Z.r (CoinAt.fresh 1) ++
      keptFrom 0 s (n :: rest)).map (srcOf (s :: n :: rest))).Perm
      ((List.range (2 * s.k + 1)).map CoinSrc.hide ++ grid (2 ^ s.h) s.Z.r CoinSrc.tails ++
        (List.range (dueFrom s (n :: rest))).map CoinSrc.rest)
    have e1 : ((hideNums s.k).map (CoinAt.hide 1)).map (srcOf (s :: n :: rest)) =
        ((hideNums s.k).map (hideIx s.k)).map CoinSrc.hide := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro t _
      exact (srcOf_hide (s :: n :: rest) 1 t s.k rfl).trans (if_pos rfl)
    have e2 : (grid (2 ^ s.h) s.Z.r (CoinAt.fresh 1)).map (srcOf (s :: n :: rest)) =
        grid (2 ^ s.h) s.Z.r CoinSrc.tails := by
      rw [grid_map]
      rfl
    rw [List.map_append, List.map_append, e1, e2, ← seg_zero]
    exact (((hide_perm s.k).map _).append_right _).append hB

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.src_reads
#print axioms ProofFile.Honest.K12.Light.mem_grid
#print axioms ProofFile.Honest.K12.Light.grid_succ
#print axioms ProofFile.Honest.K12.Light.grid_map
#print axioms ProofFile.Honest.K12.Light.grid_nodup
#print axioms ProofFile.Honest.K12.Light.src_nodup
#print axioms ProofFile.Honest.K12.Light.seg_add
#print axioms ProofFile.Honest.K12.Light.seg_zero
#print axioms ProofFile.Honest.K12.Light.seg_four
#print axioms ProofFile.Honest.K12.Light.grid_seg
#print axioms ProofFile.Honest.K12.Light.free_pad
#print axioms ProofFile.Honest.K12.Light.hideIx_zero
#print axioms ProofFile.Honest.K12.Light.hideIx_low
#print axioms ProofFile.Honest.K12.Light.hideIx_last
#print axioms ProofFile.Honest.K12.Light.pairs_range
#print axioms ProofFile.Honest.K12.Light.hide_perm
#print axioms ProofFile.Honest.K12.Light.srcOf_hide
#print axioms ProofFile.Honest.K12.Light.ride_perm
#print axioms ProofFile.Honest.K12.Light.switch_perm
#print axioms ProofFile.Honest.K12.Light.getD_drop_next
#print axioms ProofFile.Honest.K12.Light.startAt_succ
#print axioms ProofFile.Honest.K12.Light.main_succ
#print axioms ProofFile.Honest.K12.Light.free_of_fit
#print axioms ProofFile.Honest.K12.Light.from_perm
#print axioms ProofFile.Honest.K12.Light.kept_perm
#print axioms ProofFile.Honest.K12.Light.seg
#print axioms ProofFile.Honest.K12.Light.hideIx
