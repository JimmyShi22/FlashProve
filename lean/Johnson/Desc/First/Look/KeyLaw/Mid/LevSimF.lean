-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimF.lean: the key trees of all parts in the course over the
field (`cKeys`, Course.lean) go with `A.keysRun L` (LevRunD.lean), between the relations `Sim` at
the seams 3 and 4 (Relation.lean). The course is our text of the program's lookup, over the field.
That the program's run, read in the field, is this course is not shown here.

Main names:
  `cOne`, `cKey_succ` one part's tree in the course; the parts, split at the first.
  `cLevels_pt0` a tree without variables at level 0 does not read the point of the claim on its
    root.
  `ownP` the mask entries of the first message that the parts below i take.
  `KInv` what holds between the parts' trees.
  `part_goes`, `key_goes` one part; the parts from i on.
  `keys_goes` the field `keys` of `Sims`.
Limits: D.S = A.toPub; 1 ≤ m; 1 ≤ v i for i < m; `PlAt` at each level of each part (the orders and
places are the course's).

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

/-- One part's tree in the course. -/
def cOne (D : Dt) (i : ℕ) (s : Cs) : Cs :=
  { (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2 with
    leaves := Function.update (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2.leaves i
      (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).1 }

theorem cKey_succ (D : Dt) (n i : ℕ) (s : Cs) : cKey D (n + 1) i s = cKey D n (i + 1) (cOne D i
    s) :=
  rfl

/-- A tree without variables at level 0 does not read the point of the claim on its root. -/
theorem cLevels_pt0 (D : Dt) (keys : Bool) (n : ℕ) (c : PscF.PointClaim) (s : Cs)
    (h0 : (if (keys && n == 0) then ordFirst D.S.order (0 + 0) else ordDown (0 + 0)) = []) :
    cLevels D keys 0 (n + 1) 0 c s = cLevels D keys 0 (n + 1) 0 ⟨[], c.masks, c.value⟩ s := by
  have e : cLev D (keys && n == 0) (0 + 0) c s =
      cLev D (keys && n == 0) (0 + 0) ⟨[], c.masks, c.value⟩ s := by
    unfold cLev
    rw [h0]
    rfl
  rw [cLevels_succ, cLevels_succ, e]

variable (A : Dat GE) (sl : Slot → A.J) (L : LevPl A)

/-- the mask entries of the first message that the parts below i take -/
def ownP : ℕ → ℕ
  | 0 => 0
  | i + 1 => ownP i + (ownN 0 (A.v i - 1) + (2 * (0 + (A.v i - 1)) + 5 - 2))

/-- What holds between the parts' trees; s₀, x: the stand and the state before the first. -/
structure KInv (s₀ : Cs) (x : A.XS) (i : ℕ) (s : Cs) (ss : SS GE A.J A.XS) : Prop where
  base : ss.1 = x
  alpha : s.alpha = s₀.alpha
  roots : s.roots = s₀.roots
  top : s.top = s₀.top
  len : ss.2.1.length = i
  cls : ∀ j < i, ss.2.1.getD j ⟨0, 0, 0⟩ = rdCl A sl s₀.alpha (A.v j) (s.leaves j)
  rows : ∃ new : List RowF, (∀ r ∈ new, r.maps = []) ∧ s.rows = s₀.rows ++ new ∧
    ss.2.2 = new.map (rd0 sl)
  own : s.own = s₀.own + ownP A i
  idx : s.idx = s₀.idx + 2 * i

/-- What one part's tree leaves behind, from what its levels leave behind. -/
theorem part_fin (s₀ : Cs) (x : A.XS) (hal : x.al = s₀.alpha) (i : ℕ) (hv : 1 ≤ A.v i) (s : Cs)
    (ss : SS GE A.J A.XS) (h : KInv A sl s₀ x i s ss) (cs : PscF.PointClaim × Cs)
    (a₀ a' : Acc GE A.J) (ha₀ : a₀.rows = []) (nr ow ix : ℕ)
    (how : ownP A (i + 1) = ownP A i + ow) (hix : ix = 2) (r1 : RelC sl cs.1 a')
    (r3 : Outs sl s cs.2 nr ow ix a₀ a') :
    KInv A sl s₀ x (i + 1) { cs.2 with leaves := Function.update cs.2.leaves i cs.1 }
        (partOut (B := A.kb) (A.part L i) (ss, a')) ∧
      cs.2.rounds = s.rounds.drop nr := by
  obtain ⟨new, hnew, e1, e2⟩ := r3.rows
  obtain ⟨old, hold, o1, o2⟩ := h.rows
  have hcl : (⟨ptTop (A.v i - 1 + 1) a'.pt, fun j => - a'.mf j, ss.1.al - a'.tg⟩ :
      Cb.LdLkp.MCl GE A.J) = rdCl A sl s₀.alpha (A.v i) cs.1 := by
    rw [h.base, hal, r1.pt, r1.mf, r1.tg, Nat.sub_add_cancel hv]
    rfl
  refine ⟨⟨h.base, ?_, ?_, ?_, ?_, ?_, ⟨old ++ new, ?_, ?_, ?_⟩, ?_, ?_⟩, r3.rounds⟩
  · show cs.2.alpha = _
    rw [r3.same.alpha, h.alpha]
  · show cs.2.roots = _
    rw [r3.same.roots, h.roots]
  · show cs.2.top = _
    rw [r3.same.top, h.top]
  · show (ss.2.1 ++ [_]).length = i + 1
    rw [List.length_append, h.len]
    rfl
  · intro j hj
    show (ss.2.1 ++ [(⟨ptTop (A.v i - 1 + 1) a'.pt, fun j => - a'.mf j, ss.1.al - a'.tg⟩ :
      Cb.LdLkp.MCl GE A.J)]).getD j ⟨0, 0, 0⟩ =
      rdCl A sl s₀.alpha (A.v j) (Function.update cs.2.leaves i cs.1 j)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [h.len]; exact hj),
        Function.update_of_ne (Nat.ne_of_lt hj), r3.same.leaves]
      exact h.cls j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [h.len]), h.len, Nat.sub_self,
        Function.update_self, hcl]
      rfl
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hold r hr
    · exact hnew r hr
  · show cs.2.rows = _
    rw [e1, o1, List.append_assoc]
  · show ss.2.2 ++ a'.rows = _
    rw [e2, o2, ha₀, List.map_append]
    rfl
  · show cs.2.own = _
    rw [r3.own, h.own, how, Nat.add_assoc]
  · show cs.2.idx = _
    rw [r3.idx, h.idx, hix]
    omega

/-- **One part.** -/
theorem part_goes (D : Dt) (hS : D.S = A.toPub) (s₀ : Cs) (x : A.XS) (hal : x.al = s₀.alpha)
    (i : ℕ) (hr : x.roots i = rdS A sl (s₀.roots i)) (hv : 1 ≤ A.v i)
    (hp : ∀ l < A.v i, PlAt sl D (partD (A.part L i)) (decide (l + 1 = A.v i)) l
      (s₀.own + ownP A i + ownN 0 l) (s₀.idx + 2 * i))
    (s : Cs) (ss : SS GE A.J A.XS) (h : KInv A sl s₀ x i s ss)
    (hf : fitsAll (fmT 0 (A.v i - 1)) (s.rounds.take (fmT 0 (A.v i - 1)).length) = true) :
    KInv A sl s₀ x (i + 1) (cOne D i s)
        (partStep (B := A.kb) (A.part L i) ss (s.rounds.take (fmT 0 (A.v i - 1)).length)) ∧
      (cOne D i s).rounds = s.rounds.drop (fmT 0 (A.v i - 1)).length := by
  obtain ⟨n, hn⟩ : ∃ n, A.v i = n + 1 := ⟨A.v i - 1, by omega⟩
  have hn' : A.v i - 1 = n := by omega
  have hown : ownP A (i + 1) = ownP A i + (ownN 0 n + (2 * (0 + n) + 5 - 2)) := by
    show ownP A i + (ownN 0 (A.v i - 1) + (2 * (0 + (A.v i - 1)) + 5 - 2)) = _
    rw [hn']
  rw [hn', fmT_eq] at hf ⊢
  have hrel : RelC sl ⟨[], (s.roots i).masks, (s.roots i).value⟩
      (partIn (B := A.kb) (A.part L i) ss).2 :=
    ⟨rfl, by
        show (ss.1.roots i).mf = _
        rw [h.base, hr, h.roots]
        rfl, by
        show (ss.1.roots i).tg = _
        rw [h.base, hr, h.roots]
        rfl⟩
  have hq : PlAt sl D (partD (A.part L i)) true n (s.own + ownN 0 n) s.idx := by
    have h0 := hp n (by omega)
    rw [decide_eq_true (by omega : n + 1 = A.v i)] at h0
    rw [h.own, h.idx]
    exact h0
  have hpl : ∀ l < n, PlAt sl D (partD (A.part L i)) false l (s.own + ownN 0 l) s.idx := by
    intro l hl
    have h0 := hp l (by omega)
    rw [decide_eq_false (by omega : ¬ l + 1 = A.v i)] at h0
    rw [h.own, h.idx]
    exact h0
  have r := tree_goes sl D (partD (A.part L i)) ⟨[], (s.roots i).masks, (s.roots i).value⟩
    (partIn (B := A.kb) (A.part L i) ss).2 s hrel true n hpl hq hf
  have h00 : (if (true && n == 0) then ordFirst D.S.order (0 + 0) else ordDown (0 + 0)) = [] := by
    cases n with
    | zero =>
      have := hq.ord
      simpa using this
    | succ n => rfl
  have eC : cOne D i s =
      { (cLevels D true 0 (n + 1) 0 ⟨[], (s.roots i).masks, (s.roots i).value⟩ s).2 with
        leaves := Function.update
          (cLevels D true 0 (n + 1) 0 ⟨[], (s.roots i).masks, (s.roots i).value⟩ s).2.leaves i
          (cLevels D true 0 (n + 1) 0 ⟨[], (s.roots i).masks, (s.roots i).value⟩ s).1 } := by
    unfold cOne
    rw [hS]
    show ({ (cLevels D true 0 (A.v i) 0 (s.roots i) s).2 with
      leaves := Function.update (cLevels D true 0 (A.v i) 0 (s.roots i) s).2.leaves i
        (cLevels D true 0 (A.v i) 0 (s.roots i) s).1 } : Cs) = _
    rw [hn, cLevels_pt0 D true n (s.roots i) s h00]
  have eR : partStep (B := A.kb) (A.part L i) ss (s.rounds.take (fmN 0 (n + 1)).length) =
      partOut (B := A.kb) (A.part L i) (ss, stepsN (partD (A.part L i)) (n + 1)
        (partIn (B := A.kb) (A.part L i) ss).2 (s.rounds.take (fmN 0 (n + 1)).length)) := by
    unfold partStep
    show partOut (B := A.kb) (A.part L i) (treeStep (partD (A.part L i)) (A.v i - 1)
      (ss, (partIn (B := A.kb) (A.part L i) ss).2) _) = _
    rw [hn', treeStep_eq]
  rw [eC, eR]
  exact part_fin A sl L s₀ x hal i hv s ss h _ _ _ rfl _ _ _ (by rw [hown, if_pos rfl])
    (by rw [if_pos rfl]) r.1 r.2.2

/-- the parts from i on, n of them -/
def pFrom (i n : ℕ) : List (KeyPart A.kb) := (List.range n).map fun j => A.part L (i + j)

theorem pFrom_succ (i n : ℕ) : pFrom A L i (n + 1) = A.part L i :: pFrom A L (i + 1) n := by
  unfold pFrom
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg (List.cons (A.part L i)) (List.map_congr_left fun j _ => ?_)
  show A.part L (i + (j + 1)) = A.part L (i + 1 + j)
  rw [Nat.add_right_comm, Nat.add_assoc i j 1]

theorem tailP_eq : A.tailP L = pFrom A L 1 (A.m - 1) :=
  List.map_congr_left fun j _ => by rw [Nat.add_comm]

/-- **The parts from i on.** -/
theorem key_goes (D : Dt) (hS : D.S = A.toPub) (s₀ : Cs) (x : A.XS) (hal : x.al = s₀.alpha)
    (hr : ∀ i < A.m, x.roots i = rdS A sl (s₀.roots i)) (hv : ∀ i < A.m, 1 ≤ A.v i)
    (hp : ∀ i < A.m, ∀ l < A.v i, PlAt sl D (partD (A.part L i)) (decide (l + 1 = A.v i)) l
      (s₀.own + ownP A i + ownN 0 l) (s₀.idx + 2 * i)) :
    ∀ (n i : ℕ), i + (n + 1) = A.m → ∀ (s : Cs) (ss : SS GE A.J A.XS), KInv A sl s₀ x i s ss →
      fitsAll (fmSides (B := A.kb) (A.part L i) (pFrom A L (i + 1) n))
        (s.rounds.take (fmSides (B := A.kb) (A.part L i) (pFrom A L (i + 1) n)).length) = true →
      KInv A sl s₀ x (i + (n + 1)) (cKey D (n + 1) i s)
          (sidesStep (B := A.kb) (A.part L i) (pFrom A L (i + 1) n) ss
            (s.rounds.take (fmSides (B := A.kb) (A.part L i) (pFrom A L (i + 1) n)).length)) ∧
        (cKey D (n + 1) i s).rounds =
          s.rounds.drop (fmSides (B := A.kb) (A.part L i) (pFrom A L (i + 1) n)).length
  | 0, i, hi, s, ss, h, hf =>
    part_goes A sl L D hS s₀ x hal i (hr i (by omega)) (hv i (by omega)) (hp i (by omega)) s ss h hf
  | n + 1, i, hi, s, ss, h, hf => by
    rw [pFrom_succ] at hf ⊢
    have hl : (fmSides (B := A.kb) (A.part L i)
        (A.part L (i + 1) :: pFrom A L (i + 1 + 1) n)).length =
        (fmT 0 (A.v i - 1)).length +
          (fmSides (B := A.kb) (A.part L (i + 1)) (pFrom A L (i + 1 + 1) n)).length := by
      show (fmT 0 (A.v i - 1) ++ fmSides (B := A.kb) (A.part L (i + 1))
        (pFrom A L (i + 1 + 1) n)).length = _
      rw [List.length_append]
    rw [hl] at hf ⊢
    obtain ⟨h1, h2⟩ := fitsAll_app (fmT 0 (A.v i - 1))
      (fmSides (B := A.kb) (A.part L (i + 1)) (pFrom A L (i + 1 + 1) n)) _ hf
    rw [take_take_add] at h1
    rw [drop_take_add] at h2
    obtain ⟨p1, p2⟩ := part_goes A sl L D hS s₀ x hal i (hr i (by omega)) (hv i (by omega))
      (hp i (by omega)) s ss h h1
    rw [← p2] at h2
    obtain ⟨q1, q2⟩ := key_goes D hS s₀ x hal hr hv hp n (i + 1) (by omega) _ _ p1 h2
    have ei : i + (n + 1 + 1) = i + 1 + (n + 1) := by omega
    refine ⟨?_, ?_⟩
    · rw [ei, cKey_succ]
      show KInv A sl s₀ x (i + 1 + (n + 1)) _
        (sidesStep (B := A.kb) (A.part L (i + 1)) (pFrom A L (i + 1 + 1) n)
          (partStep (B := A.kb) (A.part L i) ss ((s.rounds.take _).take (fmT 0 (A.v i - 1)).length))
          ((s.rounds.take _).drop (fmT 0 (A.v i - 1)).length))
      rw [take_take_add, drop_take_add, ← p2]
      exact q1
    · rw [cKey_succ, q2, p2, List.drop_drop]

/-- the entries that all parts take, as Relation.lean counts them -/
theorem ownP_take (hv : ∀ i < A.m, 1 ≤ A.v i) : ∀ i ≤ A.m, ownP A i =
    ((A.parts.take i).map fun v => ((List.range v).map fun l => 2 * l + 5).sum - 2).sum
  | 0, _ => rfl
  | i + 1, hi => by
    have hi' : i < A.parts.length := hi
    have e : A.v i = A.parts[i] := List.getD_eq_getElem _ _ hi'
    have h1 := hv i hi
    obtain ⟨n, hn⟩ : ∃ n, A.v i = n + 1 := ⟨A.v i - 1, by omega⟩
    have hs : ((List.range (n + 1)).map fun l => 2 * l + 5).sum = ownN 0 n + (2 * (0 + n) + 5) := by
      have h0 : ownN 0 n + (2 * (0 + n) + 5) = _ := ownN_sum 0 (n + 1)
      simp only [Nat.zero_add] at h0 ⊢
      exact h0.symm
    show ownP A i + (ownN 0 (A.v i - 1) + (2 * (0 + (A.v i - 1)) + 5 - 2)) = _
    rw [List.take_succ_eq_append_getElem hi', List.map_append, List.sum_append,
      ← ownP_take hv i (Nat.le_of_succ_le hi), ← e, hn]
    show _ = ownP A i + (((List.range (n + 1)).map fun l => 2 * l + 5).sum - 2 + 0)
    rw [hs]
    have e1 : n + 1 - 1 = n := rfl
    rw [e1]
    omega

/-- From what holds behind the last part to the relation at seam 4. -/
theorem keys_fin (st : A.St) (own idx : ℕ) (hv : ∀ i < A.m, 1 ≤ A.v i) (s : Cs) (x : A.XS)
    (hs : Sim A sl st own idx 3 s x) (s' : Cs) (ss : SS GE A.J A.XS)
    (k1 : KInv A sl s x A.m s' ss) : Sim A sl st own idx 4 s' (A.keysBack ss) := by
  obtain ⟨new, hnew, e1, e2⟩ := k1.rows
  obtain ⟨ht1, ht2, ht3⟩ := hs.top (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun _ h => absurd h (by decide), fun _ _ => ⟨?_, ?_, ?_⟩, fun _ i hi => ?_,
    fun h => absurd h (by decide)⟩
  · show ss.1.st = st
    rw [k1.base]
    exact hs.st
  · show ss.1.al = s'.alpha
    rw [k1.base, k1.alpha]
    exact hs.al
  · show ss.1.rows ++ ss.2.2 = s'.rows.map (rdRow A sl)
    rw [k1.base, e1, e2, rows_read A sl _ _ hnew, hs.rows]
  · show s'.own = own + ownAt A.toPub 4
    have e4 : ownAt A.toPub 4 = ownAt A.toPub 3 +
        (A.parts.map fun v => ((List.range v).map fun l => 2 * l + 5).sum - 2).sum := by
      simp only [ownAt]
    have eT : A.parts.take A.m = A.parts := List.take_length
    rw [k1.own, hs.own, e4, ownP_take A hv A.m (Nat.le_refl _), eT, Nat.add_assoc]
  · show s'.idx = idx + idxAt A.toPub 4
    rw [k1.idx, hs.idx]
    rfl
  · show ss.1.top = rdS A sl s'.top
    rw [k1.base, k1.top]
    exact ht1
  · show s'.top.point.length = A.mu + 0
    rw [k1.top]
    exact ht2
  · intro t ht
    show ss.1.pt t = s'.top.point.getD t 0
    rw [k1.base, k1.top]
    rw [k1.top] at ht
    exact ht3 t ht
  · show ss.2.1.getD i ⟨0, 0, 0⟩ = rdCl A sl s'.alpha (A.v i) (s'.leaves i)
    rw [k1.alpha]
    exact k1.cls i hi

/-- **The key trees of all parts.** -/
theorem keys_goes (D : Dt) (st : A.St) (own idx : ℕ) (hS : D.S = A.toPub) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i)
    (hp : ∀ i < A.m, ∀ l < A.v i, PlAt sl D (partD (A.part L i)) (decide (l + 1 = A.v i)) l
      (own + ownAt A.toPub 3 + ownP A i + ownN 0 l) (idx + idxAt A.toPub 3 + 2 * i)) :
    Goes (Sim A sl st own idx 3) (Sim A sl st own idx 4) (cKeys D) (A.keysRun L) (A.keysFm L) := by
  intro s x hs hf
  obtain ⟨n, hn⟩ : ∃ n, A.m = n + 1 := ⟨A.m - 1, by omega⟩
  have e0 : A.tailP L = pFrom A L (0 + 1) n := by
    rw [tailP_eq, hn]
    rfl
  have eF : A.keysFm L = fmSides (B := A.kb) (A.part L 0) (pFrom A L (0 + 1) n) := by
    unfold Dat.keysFm
    rw [e0]
  rw [eF] at hf ⊢
  have k := key_goes A sl L D hS s x hs.al (hs.roots (by omega) (by omega)) hv
    (fun i hi l hl => by
      rw [hs.own, hs.idx]
      exact hp i hi l hl) n 0 (by omega) s (x, [], [])
    ⟨rfl, rfl, rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      ⟨[], fun _ h => absurd h List.not_mem_nil, (List.append_nil _).symm, rfl⟩, rfl, rfl⟩ hf
  have eC : cKeys D s = cKey D (n + 1) 0 s := by
    unfold cKeys
    rw [hS]
    show cKey D A.m 0 s = _
    rw [hn]
  have eR : A.keysRun L x (s.rounds.take
      (fmSides (B := A.kb) (A.part L 0) (pFrom A L (0 + 1) n)).length) =
      A.keysBack (sidesStep (B := A.kb) (A.part L 0) (pFrom A L (0 + 1) n) (x, [], [])
        (s.rounds.take (fmSides (B := A.kb) (A.part L 0) (pFrom A L (0 + 1) n)).length)) := by
    unfold Dat.keysRun
    rw [e0]
  rw [eC, eR]
  have hmn : 0 + (n + 1) = A.m := by omega
  rw [hmn] at k
  exact ⟨keys_fin A sl st own idx hv s x hs _ _ k.1, k.2⟩

end Lk6.Mid

#print axioms Lk6.Mid.part_goes
#print axioms Lk6.Mid.keys_goes
