-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Round.lean: the folded tables compute the specification's
round polynomial and end values. Conditional on the hypotheses below. Theorems, with five
definitions (`Holds`, `Inv`, `terms`, `sum3`, `AllOk`), on arrays alone: no lookup is named here.

Terms. Honest/K3/GLOSSARY.md; for marks, free bits and the short cube, Honest/K3/FastLaw/Cube.lean.
In this file: Honest/K3/JobsFast.lean has one routine for every sumcheck with variables: `prodRound`
(the round polynomial of kappa + A B under equality weights, by binding bits of two arrays) and
`prodEnds` (the arrays' values at the point of all challenges). The specification
(Johnson/HonestTrace/LookDefs.lean) has `pjRound` and `ext`, on functions of a number, over a field.

What is shown.
  `prodRound_read'`: read in the library's field, coefficient for coefficient, `prodRound` is
    `pjRound`.
  `prodEnds_read'`: read in the library's field, `prodEnds` is `ext` at the point of the challenges.
    In these two the specification's tables are any functions that agree with the arrays below
    2 ^ m: what such a function is from 2 ^ m on is not read.
  `prodRound_read`, `prodEnds_read`: the same at the arrays' own readings.
  `prodRound_ok`: the words of the round polynomial's coefficients are below the prime: with no
    hypothesis.
  `prodEnds_ok`, `prodEnds_ok'`: the same of the end values: where every entry of every table has
    words below the prime; or where neither the order nor the list of challenges is empty. Where no
    bit is bound an end value is the table's own first entry.
  `leaves_cut`: two ways of saying which rounds of the leaves' sumcheck bind a plane's bit are one.
  `orderDefault_getD`, `orderDefault_perm`: two facts on the library's default order.

Hypotheses that remain.
  `ho`: the order is a permutation of the numbers below m.
  `hz`: the point has m coordinates.
  `hA`, `hB`, `ht`: each array has 2 ^ m entries. In the primed forms, `hfA` and `hfB` (a round),
    `h` (the end values; it says the arrays' sizes too): each function agrees with its array below
    2 ^ m.
  `hl`: (for a round) there are fewer challenges than variables.
  `hx`: (for the end values) there are just m challenges.
  In `prodEnds_ok`: `h`: every entry of every table, and what is read beyond a table's end, has
    words below the prime. In `prodEnds_ok'`: `ho`, `hx`: neither the order nor the list of
    challenges is empty. In `leaves_cut` and `orderDefault_getD`: `h`: l lies below mu + d, or below
    m.
  In the theorems on the way. `O`: o is an order of m bits (`Ord`, Cube.lean). `hm`: there are at
    most m challenges. `hb`: bit b is free. `h`, `hA`, `hB`: (in `holds_bind`, `inv_step`,
    `round_core`) `Holds`, or `Inv`, in front of the step. `ht`, `hf`: (in `holds_start`) the array
    has 2 ^ m entries and reads as f. `hr`: the challenge as read. `hR`: (in `map_of_forall₂`) the
    relation gives the equation. `hM`, `hlen`, `hw`, `hwv`: (in `weights_read`, `round_core`) the
    list of marks, and the array of weights, have their lengths, and the weights read as the
    specification's. Without a name, in front of arrows: in `spread_all`, `inv_go`,
    `map_of_forall₂`, `fold_ok`.

How the proof goes. `Holds M g t` says that the short array t holds the function g on the bits that
the marks M leave free. By `holds_bind`, binding one free bit takes `Holds` to `Holds`, at the
specification's `fixAt`. So, by `Inv` and `inv_all`, behind l rounds the cube holds `foldN`. The sum
over the short cube is the specification's sum under weights with zeros (`sum_spread`, Cube.lean).

Users. The primed forms are the ones that are called: `prodEnds_read'` in
Honest/K3/FastLaw/InY.lean, `prodRound_read'` in Honest/K3/FastLaw/Rounds.lean.

Limits. The equalities hold after `readE`. That the lists are equal as lists of the program's
elements follows with the theorems on words below the prime and `eq_downs`
(Honest/K3/FastLaw/Read.lean). Nothing is said where a hypothesis fails. No statement of this file
says that the arrays are a lookup's tables.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Cube
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Read
import OnBytes.Tie.Pv.Lookup.Ends.FoRowH
import OnBytes.Tie.Pv.Lookup.Ends.FoSlEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open Finset TwV
open OnBytes (E addE subE mulE zeroE oneE foldPairE okE)
open OnBytes.Slice (readE readV readE_add readE_sub readE_mul readE_zero)
open OnBytes.HonestTrace.Look (setBit wtN foldN fixAt pjRound ext Ord ord_of_perm foldN_zero)
open ProofFile.Honest.K3.Fast (at0 bindAt Cube bindAll coord prodRound prodEnds)

/-! ## 1 A short array that holds a function -/

/-- The array t has an entry for each short number of the marks M, and read it is g at that number
laid out. -/
def Holds (M : List Bool) (g : ℕ → KE) (t : Array E) : Prop :=
  t.size = 2 ^ nM M ∧ ∀ i, i < 2 ^ nM M → readV t i = g (spreadM M i)

theorem nM_all : ∀ m, nM (List.replicate m true) = m
  | 0 => rfl
  | m + 1 => by
    show nM (List.replicate m true) + 1 = m + 1
    rw [nM_all m]

theorem spread_all : ∀ (m i : ℕ), i < 2 ^ m → spreadM (List.replicate m true) i = i
  | 0, i, h => by
    have : i = 0 := by simpa using h
    subst this
    rfl
  | m + 1, i, h => by
    show 2 * spreadM (List.replicate m true) (i / 2) + i % 2 = i
    rw [spread_all m (i / 2) (by rw [pow_succ] at h; omega)]
    omega

theorem spread_zero : ∀ M : List Bool, spreadM M 0 = 0
  | [] => rfl
  | true :: M => by
    show 2 * spreadM M (0 / 2) + 0 % 2 = 0
    simp [spread_zero M]
  | false :: M => by
    show 2 * spreadM M 0 = 0
    rw [spread_zero M]

/-- An array of 2 ^ m entries holds, at no bit bound, every function that agrees with it below
2 ^ m. -/
theorem holds_start (m : ℕ) (t : Array E) (f : ℕ → KE) (ht : t.size = 2 ^ m)
    (hf : ∀ X, X < 2 ^ m → readV t X = f X) : Holds (List.replicate m true) f t := by
  refine ⟨by rw [nM_all]; exact ht, fun i hi => ?_⟩
  rw [nM_all] at hi
  rw [spread_all m i hi]
  exact hf i hi

/-- **One free bit bound**: if t holds g at the marks M, and bit b is free in M, then t with that
bit bound at r holds g with bit b fixed at r as read, at the marks with b no longer free. -/
theorem holds_bind {M : List Bool} {g : ℕ → KE} {t : Array E} (b : ℕ) (r : E)
    (hb : M.getD b false = true) (h : Holds M g t) :
    Holds (M.set b false) (fixAt b (readE r) g) (bindAt (posM M b) r t) := by
  obtain ⟨h1, h2, h3, h4⟩ := take_out b M hb
  obtain ⟨hs, hv⟩ := h
  have hhalf : t.size / 2 = 2 ^ nM (M.set b false) := by
    rw [hs, h1, pow_succ]
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · show ((Array.range (t.size / 2)).map _).size = _
    rw [tab_size, hhalf]
  · have hi' : i < t.size / 2 := by rw [hhalf]; exact hi
    have e : readV (bindAt (posM M b) r t) i =
        readE (foldPairE (t.getD (at0 (posM M b) i) zeroE)
          (t.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE) r) :=
      readV_tab (t.size / 2) _ hi'
    have hlt := h2 i hi
    have a0 : readE (t.getD (at0 (posM M b) i) zeroE) =
        g (setBit b false (spreadM (M.set b false) i)) := by
      rw [← h3]
      exact hv _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt)
    have a1 : readE (t.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE) =
        g (setBit b true (spreadM (M.set b false) i)) := by
      rw [← h4]
      exact hv _ hlt
    rw [e, OnBytes.foldPairE_def, readE_add, readE_mul, readE_sub, a0, a1]
    show _ = (1 - readE r) * g (setBit b false _) + readE r * g (setBit b true _)
    ring

/-! ## 2 The cube behind l rounds -/

/-- Behind l rounds of the order o at the challenges rs: the free bits are those of the marks, and
each table holds its function, folded. -/
structure Inv (m : ℕ) (o : List ℕ) (rs : List KE) (fs : List (ℕ → KE)) (l : ℕ) (c : Cube) :
    Prop where
  free : c.free = idx (maskN o m l)
  tabs : List.Forall₂ (fun t f => Holds (maskN o m l) (foldN o rs f l) t) c.tabs fs

theorem inv_step {m : ℕ} {o : List ℕ} (O : Ord o m) {rs : List KE} {fs : List (ℕ → KE)} {l : ℕ}
    {c : Cube} (hl : l < m) (r : E) (hr : readE r = rs.getD l 0) (h : Inv m o rs fs l c) :
    Inv m o rs fs (l + 1) (c.bind (o.getD l 0) r) := by
  have hp : c.pos (o.getD l 0) = posM (maskN o m l) (o.getD l 0) := by
    show (c.free.filter (· < o.getD l 0)).length = _
    rw [h.free, idx_pos]
  refine ⟨?_, ?_⟩
  · show c.free.filter (· != o.getD l 0) = idx ((maskN o m l).set (o.getD l 0) false)
    rw [h.free, idx_filter]
  · show List.Forall₂ _ (c.tabs.map (bindAt (c.pos (o.getD l 0)) r)) fs
    rw [List.forall₂_map_left_iff, hp]
    refine h.tabs.imp fun t f ht => ?_
    show Holds ((maskN o m l).set (o.getD l 0) false)
      (fixAt (o.getD l 0) (rs.getD l 0) (foldN o rs f l)) _
    rw [← hr]
    exact holds_bind _ r (maskN_next O hl) ht

theorem inv_go {m : ℕ} {o : List ℕ} (O : Ord o m) (rs : List E) (fs : List (ℕ → KE))
    (hm : rs.length ≤ m) : ∀ (k l : ℕ) (c : Cube), l + k = rs.length →
    Inv m o (rs.map readE) fs l c →
    Inv m o (rs.map readE) fs rs.length
      (((o.drop l).zip (rs.drop l)).foldl (fun c x => c.bind x.1 x.2) c)
  | 0, l, c, hk, h => by
    have e : l = rs.length := by omega
    subst e
    simpa using h
  | k + 1, l, c, hk, h => by
    have hl : l < rs.length := by omega
    have hlo : l < o.length := by rw [O.len]; omega
    rw [List.drop_eq_getElem_cons hlo, List.drop_eq_getElem_cons hl, List.zip_cons_cons,
      List.foldl_cons]
    refine inv_go O rs fs hm k (l + 1) _ (by omega) ?_
    have e1 : o[l] = o.getD l 0 := (List.getD_eq_getElem _ _ hlo).symm
    have e2 : readE rs[l] = (rs.map readE).getD l 0 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
    show Inv m o (rs.map readE) fs (l + 1) (c.bind o[l] rs[l])
    rw [e1]
    exact inv_step O (by omega) _ e2 h

/-- **The cube behind the rounds of all challenges given.** fs: for each table a function that
agrees with it below 2 ^ m. -/
theorem inv_all {m : ℕ} {o : List ℕ} (O : Ord o m) (tabs : List (Array E)) (fs : List (ℕ → KE))
    (rs : List E) (hm : rs.length ≤ m)
    (h : List.Forall₂ (fun t f => t.size = 2 ^ m ∧ ∀ X, X < 2 ^ m → readV t X = f X) tabs fs) :
    Inv m o (rs.map readE) fs rs.length (bindAll m o tabs rs) := by
  have h0 : Inv m o (rs.map readE) fs 0 ⟨List.range m, tabs⟩ :=
    ⟨(idx_all m).symm, h.imp fun t f ht => holds_start m t f ht.1 ht.2⟩
  have := inv_go O rs fs hm rs.length 0 _ (by omega) h0
  simpa [bindAll] using this

/-! ## 3 The end values -/

theorem map_of_forall₂ {α β γ : Type} {R : α → β → Prop} {p : α → γ} {q : β → γ}
    (hR : ∀ a b, R a b → p a = q b) : ∀ {l : List α} {u : List β}, List.Forall₂ R l u →
    l.map p = u.map q
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.map_cons, List.map_cons, hR _ _ h, map_of_forall₂ hR t]

/-- **Conditional on: the order is a permutation of the numbers below m; m challenges; each array
has 2 ^ m entries and agrees with its function below 2 ^ m. The end values, read, are the functions'
extensions at the point of the challenges.** An instance: the data of
Honest/K3/JobsFastGuards.lean [not in this library], section 1. They meet the hypotheses by the way
they are written; no test there evaluates a hypothesis, and its tests hold `prodEnds` against
written numbers, not against `ext`. -/
theorem prodEnds_read' (m : ℕ) (o : List ℕ) (tabs : List (Array E)) (fs : List (ℕ → KE))
    (xs : List E) (ho : o.Perm (List.range m)) (hx : xs.length = m)
    (h : List.Forall₂ (fun t f => t.size = 2 ^ m ∧ ∀ X, X < 2 ^ m → readV t X = f X) tabs fs) :
    (prodEnds m o tabs xs).map readE = fs.map fun f => ext m f (byVar o (xs.map readE)) := by
  have O := ord_of_perm ho
  have hnd : o.Nodup := ho.nodup_iff.2 List.nodup_range
  have I := inv_all O tabs fs xs (le_of_eq hx) h
  show ((bindAll m o tabs xs).tabs.map (·.getD 0 zeroE)).map readE = _
  rw [List.map_map]
  refine map_of_forall₂ (fun t f ht => ?_) I.tabs
  have e := ht.2 0 (Nat.two_pow_pos _)
  rw [spread_zero, hx, foldN_zero O hnd] at e
  exact e

/-- The same at the arrays' own readings. -/
theorem prodEnds_read (m : ℕ) (o : List ℕ) (tabs : List (Array E)) (xs : List E)
    (ho : o.Perm (List.range m)) (ht : ∀ t ∈ tabs, t.size = 2 ^ m) (hx : xs.length = m) :
    (prodEnds m o tabs xs).map readE =
      tabs.map fun t => ext m (readV t) (byVar o (xs.map readE)) := by
  have h : List.Forall₂ (fun t f => t.size = 2 ^ m ∧ ∀ X, X < 2 ^ m → readV t X = f X) tabs
      (tabs.map readV) := by
    rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun t h => ⟨ht t h, fun _ _ => rfl⟩
  rw [prodEnds_read' m o tabs _ xs ho hx h, List.map_map]
  rfl

/-! ## 4 The round polynomial -/

/-- The three terms of place i of the short cube. -/
def terms (kappa : E) (p : ℕ) (ta tb w : Array E) (i : ℕ) : E × E × E :=
  let a0 := ta.getD (at0 p i) zeroE
  let a1 := subE (ta.getD (at0 p i + 2 ^ p) zeroE) a0
  let b0 := tb.getD (at0 p i) zeroE
  let b1 := subE (tb.getD (at0 p i + 2 ^ p) zeroE) b0
  let wi := w.getD i zeroE
  (mulE wi (addE kappa (mulE a0 b0)), mulE wi (addE (mulE a0 b1) (mulE a1 b0)),
   mulE wi (mulE a1 b1))

/-- Three sums at once. -/
def sum3 (n : ℕ) (T : ℕ → E × E × E) : E × E × E :=
  (Array.range n).foldl
    (fun (acc : E × E × E) i =>
      (addE acc.1 (T i).1, addE acc.2.1 (T i).2.1, addE acc.2.2 (T i).2.2))
    (zeroE, zeroE, zeroE)

theorem sum3_list (n : ℕ) (T : ℕ → E × E × E) :
    sum3 n T = (List.range n).foldl
      (fun (acc : E × E × E) i =>
        (addE acc.1 (T i).1, addE acc.2.1 (T i).2.1, addE acc.2.2 (T i).2.2))
      (zeroE, zeroE, zeroE) := by
  unfold sum3
  rw [← Array.foldl_toList, Array.toList_range]

theorem sum3_read (T : ℕ → E × E × E) : ∀ n,
    readE (sum3 n T).1 = ∑ i ∈ range n, readE (T i).1 ∧
    readE (sum3 n T).2.1 = ∑ i ∈ range n, readE (T i).2.1 ∧
    readE (sum3 n T).2.2 = ∑ i ∈ range n, readE (T i).2.2
  | 0 => by
    rw [sum3_list]
    simp [readE_zero]
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := sum3_read T n
    rw [sum3_list] at h1 h2 h3 ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, readE_add, sum_range_succ, h1, h2, h3, and_self]

/-- `prodRound`, written with `terms` and `sum3`. -/
theorem prodRound_def (kappa : E) (m : ℕ) (o : List ℕ) (z A B : Array E) (rs : List E) :
    prodRound kappa m o z A B rs =
      (let c := bindAll m o [A, B] rs
       let b := o.getD rs.length 0
       let w := OnBytes.Model.eqTab ((c.free.filter (· != b)).reverse.map (coord m z)).toArray
       let out := sum3 w.size (terms kappa (c.pos b) (c.tabs.getD 0 #[]) (c.tabs.getD 1 #[]) w)
       [out.1, out.2.1, out.2.2]) := rfl

/-- The weights of the short cube: the table of equality weights at the free bits' coordinates, the
highest first, read, is eqN at the point cut down to the free bits. -/
theorem weights_read (m : ℕ) (z : Array E) (hz : z.size = m) (M : List Bool) (hM : M.length = m) :
    (OnBytes.Model.eqTab ((idx M).reverse.map (coord m z)).toArray).size = 2 ^ nM M ∧
    ∀ i, i < 2 ^ nM M →
      readE ((OnBytes.Model.eqTab ((idx M).reverse.map (coord m z)).toArray).getD i zeroE) =
        eqN (compact M (byBit z)) i := by
  have hs : ((idx M).reverse.map (coord m z)).toArray.size = nM M := by
    simp [idx_length]
  refine ⟨by rw [Fo.eqTab_size, hs], fun i hi => ?_⟩
  have e := Fo.eqTab_at OnBytes.Model.Reading.gl ((idx M).reverse.map (coord m z)).toArray i
    (by rw [hs]; exact hi)
  have hl : M.length = (byBit z).length := by rw [byBit_length, hz, hM]
  have e2 : (Fo.rdA OnBytes.Model.Reading.gl ((idx M).reverse.map (coord m z)).toArray).reverse =
      compact M (byBit z) := by
    rw [← idx_map M (byBit z) hl]
    show ((((idx M).reverse.map (coord m z)).toArray).toList.map readE).reverse = _
    simp only [List.map_reverse, List.reverse_reverse, List.map_map]
    refine List.map_congr_left fun b hb => ?_
    have hb' : b < z.size := by rw [hz, ← hM]; exact idx_lt M b hb
    rw [byBit_getD z b hb', hz]
    rfl
  rw [e2] at e
  exact e

/-- **The three sums over the short cube are the specification's three sums.** M: the marks in front
of the round; b: the round's bit, free in M. -/
theorem round_core (kappa : E) (M : List Bool) (b : ℕ) (zK : List KE) (gA gB : ℕ → KE)
    (ta tb w : Array E) (hb : M.getD b false = true) (hlen : M.length = zK.length)
    (hA : Holds M gA ta) (hB : Holds M gB tb) (hw : w.size = 2 ^ nM (M.set b false))
    (hwv : ∀ i, i < 2 ^ nM (M.set b false) →
      readE (w.getD i zeroE) = eqN (compact (M.set b false) zK) i) :
    readE (sum3 w.size (terms kappa (posM M b) ta tb w)).1 =
      ∑ X ∈ range (2 ^ zK.length), eqN (wts (M.set b false) zK) X *
        (readE kappa + gA (setBit b false X) * gB (setBit b false X)) ∧
    readE (sum3 w.size (terms kappa (posM M b) ta tb w)).2.1 =
      ∑ X ∈ range (2 ^ zK.length), eqN (wts (M.set b false) zK) X *
        (gA (setBit b false X) * (gB (setBit b true X) - gB (setBit b false X)) +
          (gA (setBit b true X) - gA (setBit b false X)) * gB (setBit b false X)) ∧
    readE (sum3 w.size (terms kappa (posM M b) ta tb w)).2.2 =
      ∑ X ∈ range (2 ^ zK.length), eqN (wts (M.set b false) zK) X *
        ((gA (setBit b true X) - gA (setBit b false X)) *
          (gB (setBit b true X) - gB (setBit b false X))) := by
  obtain ⟨_, t2, t3, t4⟩ := take_out b M hb
  have hl' : (M.set b false).length = zK.length := by rw [List.length_set]; exact hlen
  have A0 : ∀ i, i < 2 ^ nM (M.set b false) → readE (ta.getD (at0 (posM M b) i) zeroE) =
      gA (setBit b false (spreadM (M.set b false) i)) := fun i hi => by
    rw [← t3]
    exact hA.2 _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (t2 i hi))
  have A1 : ∀ i, i < 2 ^ nM (M.set b false) →
      readE (ta.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE) =
      gA (setBit b true (spreadM (M.set b false) i)) := fun i hi => by
    rw [← t4]
    exact hA.2 _ (t2 i hi)
  have B0 : ∀ i, i < 2 ^ nM (M.set b false) → readE (tb.getD (at0 (posM M b) i) zeroE) =
      gB (setBit b false (spreadM (M.set b false) i)) := fun i hi => by
    rw [← t3]
    exact hB.2 _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (t2 i hi))
  have B1 : ∀ i, i < 2 ^ nM (M.set b false) →
      readE (tb.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE) =
      gB (setBit b true (spreadM (M.set b false) i)) := fun i hi => by
    rw [← t4]
    exact hB.2 _ (t2 i hi)
  obtain ⟨s1, s2, s3⟩ := sum3_read (terms kappa (posM M b) ta tb w) w.size
  rw [s1, s2, s3, hw, sum_spread _ zK hl', sum_spread _ zK hl', sum_spread _ zK hl']
  refine ⟨sum_congr rfl fun i hi => ?_, sum_congr rfl fun i hi => ?_,
    sum_congr rfl fun i hi => ?_⟩
  · have hi' := mem_range.1 hi
    show readE (mulE (w.getD i zeroE) (addE kappa (mulE (ta.getD (at0 (posM M b) i) zeroE)
      (tb.getD (at0 (posM M b) i) zeroE)))) = _
    rw [readE_mul, readE_add, readE_mul, hwv i hi', A0 i hi', B0 i hi']
  · have hi' := mem_range.1 hi
    show readE (mulE (w.getD i zeroE) (addE
      (mulE (ta.getD (at0 (posM M b) i) zeroE)
        (subE (tb.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE)
          (tb.getD (at0 (posM M b) i) zeroE)))
      (mulE (subE (ta.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE)
          (ta.getD (at0 (posM M b) i) zeroE))
        (tb.getD (at0 (posM M b) i) zeroE)))) = _
    rw [readE_mul, readE_add, readE_mul, readE_mul, readE_sub, readE_sub, hwv i hi', A0 i hi',
      B0 i hi', A1 i hi', B1 i hi']
  · have hi' := mem_range.1 hi
    show readE (mulE (w.getD i zeroE) (mulE
      (subE (ta.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE)
        (ta.getD (at0 (posM M b) i) zeroE))
      (subE (tb.getD (at0 (posM M b) i + 2 ^ posM M b) zeroE)
        (tb.getD (at0 (posM M b) i) zeroE)))) = _
    rw [readE_mul, readE_mul, readE_sub, readE_sub, hwv i hi', A0 i hi', B0 i hi', A1 i hi',
      B1 i hi']

/-- **Conditional on: the order is a permutation of the numbers below m; the point has m
coordinates; both arrays have 2 ^ m entries; fA, fB agree with them below 2 ^ m; fewer challenges
than m. The round polynomial, read, is the specification's.** An instance: the data of
Honest/K3/JobsFastGuards.lean [not in this library], section 1. They meet the hypotheses by the way
they are written; no test there evaluates a hypothesis, and its tests hold `prodRound` against
written numbers, not against `pjRound`. Honest/K3/FastLaw/RoundsMember.lean [not in this library]
applies, at four stages of a small synthetic lookup, the theorems of Honest/K3/FastLaw/Rounds.lean,
which call this one (by proof). -/
theorem prodRound_read' (kappa : E) (m : ℕ) (o : List ℕ) (z A B : Array E) (fA fB : ℕ → KE)
    (rs : List E) (ho : o.Perm (List.range m)) (hz : z.size = m)
    (hA : A.size = 2 ^ m) (hB : B.size = 2 ^ m)
    (hfA : ∀ X, X < 2 ^ m → readV A X = fA X) (hfB : ∀ X, X < 2 ^ m → readV B X = fB X)
    (hl : rs.length < m) :
    (prodRound kappa m o z A B rs).map readE =
      pjRound m (readE kappa) fA fB o (byBit z) (rs.map readE) := by
  have O := ord_of_perm ho
  have I := inv_all O [A, B] [fA, fB] rs (le_of_lt hl)
    (.cons ⟨hA, hfA⟩ (.cons ⟨hB, hfB⟩ .nil))
  rw [prodRound_def]
  generalize bindAll m o [A, B] rs = c at I ⊢
  obtain ⟨free, tabs⟩ := c
  obtain ⟨hfree, htabs⟩ := I
  have hfree' : free = idx (maskN o m rs.length) := hfree
  subst hfree'
  cases htabs with
  | cons h1 ht =>
    cases ht with
    | cons h2 hn =>
      cases hn
      rename_i ta tb
      have hzK : (byBit z).length = m := by rw [byBit_length, hz]
      have hb := maskN_next O hl
      have hML : (maskN o m rs.length).length = (byBit z).length := by
        rw [maskN_length, hzK]
      have hW := weights_read m z hz ((maskN o m rs.length).set (o.getD rs.length 0) false)
        (by rw [List.length_set, maskN_length])
      have hwt : wts ((maskN o m rs.length).set (o.getD rs.length 0) false) (byBit z) =
          wtN o (byBit z) (rs.length + 1) := by
        have := wts_maskN o (byBit z) (rs.length + 1)
        rw [hzK] at this
        exact this
      obtain ⟨c1, c2, c3⟩ := round_core kappa (maskN o m rs.length) (o.getD rs.length 0) (byBit z)
        (foldN o (rs.map readE) fA rs.length) (foldN o (rs.map readE) fB rs.length) ta tb _ hb hML
        h1 h2 hW.1 hW.2
      rw [hwt, hzK] at c1 c2 c3
      have hp : Cube.pos ⟨idx (maskN o m rs.length), [ta, tb]⟩ (o.getD rs.length 0) =
          posM (maskN o m rs.length) (o.getD rs.length 0) := idx_pos _ _
      simp only [hp, idx_filter, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
        List.map_nil]
      rw [c1, c2, c3]
      simp only [pjRound, List.length_map]

/-- The same at the arrays' own readings. -/
theorem prodRound_read (kappa : E) (m : ℕ) (o : List ℕ) (z A B : Array E) (rs : List E)
    (ho : o.Perm (List.range m)) (hz : z.size = m) (hA : A.size = 2 ^ m) (hB : B.size = 2 ^ m)
    (hl : rs.length < m) :
    (prodRound kappa m o z A B rs).map readE =
      pjRound m (readE kappa) (readV A) (readV B) o (byBit z) (rs.map readE) :=
  prodRound_read' kappa m o z A B _ _ rs ho hz hA hB (fun _ _ => rfl) (fun _ _ => rfl) hl

/-! ## 5 The results' words are below the prime -/

theorem sum3_ok (T : ℕ → E × E × E) : ∀ n,
    okE (sum3 n T).1 = true ∧ okE (sum3 n T).2.1 = true ∧ okE (sum3 n T).2.2 = true
  | 0 => by
    rw [sum3_list]
    exact ⟨rfl, rfl, rfl⟩
  | n + 1 => by
    rw [sum3_list, List.range_succ, List.foldl_append]
    exact ⟨ok_add _ _, ok_add _ _, ok_add _ _⟩

/-- Every coefficient of a round polynomial has its words below the prime, whatever the arrays
hold. -/
theorem prodRound_ok (kappa : E) (m : ℕ) (o : List ℕ) (z A B : Array E) (rs : List E) :
    ∀ x ∈ prodRound kappa m o z A B rs, okE x = true := by
  rw [prodRound_def]
  intro x hx
  obtain ⟨h1, h2, h3⟩ := sum3_ok
    (terms kappa ((bindAll m o [A, B] rs).pos (o.getD rs.length 0))
      ((bindAll m o [A, B] rs).tabs.getD 0 #[]) ((bindAll m o [A, B] rs).tabs.getD 1 #[])
      (OnBytes.Model.eqTab ((((bindAll m o [A, B] rs).free.filter
        (· != o.getD rs.length 0)).reverse.map (coord m z)).toArray)))
    (OnBytes.Model.eqTab ((((bindAll m o [A, B] rs).free.filter
        (· != o.getD rs.length 0)).reverse.map (coord m z)).toArray)).size
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- Every entry of every table, and what is read beyond a table's end, has its words below the
prime. -/
def AllOk (c : Cube) : Prop := ∀ t ∈ c.tabs, ∀ i, okE (t.getD i zeroE) = true

theorem bindAt_ok (p : ℕ) (r : E) (t : Array E) (i : ℕ) :
    okE ((bindAt p r t).getD i zeroE) = true := by
  show okE (((Array.range (t.size / 2)).map fun i =>
    foldPairE (t.getD (at0 p i) zeroE) (t.getD (at0 p i + 2 ^ p) zeroE) r).getD i zeroE) = true
  by_cases h : i < t.size / 2
  · rw [tab_getD _ _ h]
    exact ok_fold _ _ _
  · have e : ((Array.range (t.size / 2)).map fun i =>
        foldPairE (t.getD (at0 p i) zeroE) (t.getD (at0 p i + 2 ^ p) zeroE) r).getD i zeroE =
        zeroE := by
      simp [Array.getD, h]
    rw [e]
    rfl

theorem bind_ok (c : Cube) (b : ℕ) (r : E) : AllOk (c.bind b r) := by
  intro t ht i
  obtain ⟨t', _, rfl⟩ := List.mem_map.1 ht
  exact bindAt_ok _ _ _ _

theorem fold_ok : ∀ (L : List (ℕ × E)) (c : Cube), AllOk c ∨ L ≠ [] →
    AllOk (L.foldl (fun c x => c.bind x.1 x.2) c)
  | [], c, h => by
    rcases h with h | h
    · exact h
    · exact absurd rfl h
  | x :: L, c, _ => fold_ok L _ (Or.inl (bind_ok c x.1 x.2))

/-- The end values' words are below the prime, if those of all entries of all tables are. -/
theorem prodEnds_ok (m : ℕ) (o : List ℕ) (tabs : List (Array E)) (xs : List E)
    (h : ∀ t ∈ tabs, ∀ i, okE (t.getD i zeroE) = true) :
    ∀ x ∈ prodEnds m o tabs xs, okE x = true := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact fold_ok (o.zip xs) ⟨List.range m, tabs⟩ (Or.inl h) t ht 0

/-- The same without a hypothesis on the tables, where at least one bit is bound: an end value is
then the result of a fold. -/
theorem prodEnds_ok' (m : ℕ) (o : List ℕ) (tabs : List (Array E)) (xs : List E)
    (ho : o ≠ []) (hx : xs ≠ []) : ∀ x ∈ prodEnds m o tabs xs, okE x = true := by
  intro x hx'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx'
  have hz : o.zip xs ≠ [] := by
    cases o with
    | nil => exact absurd rfl ho
    | cons a o =>
      cases xs with
      | nil => exact absurd rfl hx
      | cons y xs => simp
  exact fold_ok (o.zip xs) ⟨List.range m, tabs⟩ (Or.inr hz) t ht 0

/-! ## 6 The order from the top down -/

/-- Round l of the order from the top down binds bit m - 1 - l. -/
theorem orderDefault_getD (m l : ℕ) (h : l < m) :
    (OnBytes.Model.orderDefault m).getD l 0 = m - 1 - l := by
  unfold OnBytes.Model.orderDefault
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_reverse]
  simp

/-- **The two ways of cutting the leaves' rounds are one**: in the order from the top down over
mu + d bits, round l binds a plane's bit (one of the mu low ones) just if l is not below d. -/
theorem leaves_cut (mu d l : ℕ) (h : l < mu + d) :
    (OnBytes.Model.orderDefault (mu + d)).getD l 0 < mu ↔ ¬ l < d := by
  rw [orderDefault_getD _ _ h]
  omega

theorem orderDefault_perm (m : ℕ) : (OnBytes.Model.orderDefault m).Perm (List.range m) :=
  List.reverse_perm _

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.holds_bind
#print axioms ProofFile.Honest.K3.FastLaw.inv_all
#print axioms ProofFile.Honest.K3.FastLaw.prodEnds_read'
#print axioms ProofFile.Honest.K3.FastLaw.prodEnds_read
#print axioms ProofFile.Honest.K3.FastLaw.sum3_read
#print axioms ProofFile.Honest.K3.FastLaw.prodRound_def
#print axioms ProofFile.Honest.K3.FastLaw.weights_read
#print axioms ProofFile.Honest.K3.FastLaw.round_core
#print axioms ProofFile.Honest.K3.FastLaw.prodRound_read'
#print axioms ProofFile.Honest.K3.FastLaw.prodRound_read
#print axioms ProofFile.Honest.K3.FastLaw.prodRound_ok
#print axioms ProofFile.Honest.K3.FastLaw.prodEnds_ok
#print axioms ProofFile.Honest.K3.FastLaw.prodEnds_ok'
#print axioms ProofFile.Honest.K3.FastLaw.leaves_cut
#print axioms ProofFile.Honest.K3.FastLaw.orderDefault_perm
#print axioms ProofFile.Honest.K3.FastLaw.nM_all
#print axioms ProofFile.Honest.K3.FastLaw.spread_all
#print axioms ProofFile.Honest.K3.FastLaw.spread_zero
#print axioms ProofFile.Honest.K3.FastLaw.holds_start
#print axioms ProofFile.Honest.K3.FastLaw.inv_step
#print axioms ProofFile.Honest.K3.FastLaw.inv_go
#print axioms ProofFile.Honest.K3.FastLaw.map_of_forall₂
#print axioms ProofFile.Honest.K3.FastLaw.sum3_list
#print axioms ProofFile.Honest.K3.FastLaw.sum3_ok
#print axioms ProofFile.Honest.K3.FastLaw.bindAt_ok
#print axioms ProofFile.Honest.K3.FastLaw.bind_ok
#print axioms ProofFile.Honest.K3.FastLaw.fold_ok
#print axioms ProofFile.Honest.K3.FastLaw.orderDefault_getD
