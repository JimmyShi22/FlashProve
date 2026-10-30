-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookRows.lean

The linear claims of a lookup argument, all but the one on the keys, hold at the flat trace "trT" of
Johnson/HonestTrace/LookDefs.lean.

Cb/Pv/Lookup/Out/TwV.lean makes of a flat trace (TwV.Trace: what each sumcheck of a lookup leaves) a
list of sparse linear rows on entries. "Fo.rows16" (OnBytes/Tie/Pv/Lookup/Forest/FoV.lean) is that
list without its last row, the keys'. LookDefs.lean defines "trT D μ C": a flat trace as a term of
the public numbers, the keys, the bits of the counts, the mask entries (what μ reads at the places
of TwV.Led) and the challenges C.

How the proof goes. A sumcheck's row (TwV.rowU) says: the form TwV.hide at the challenges, plus eps
times the incoming form, is worth the last value less eps times the summand at the shown values. In
"trT" a last value is written as: the value of TwV.hide's form, plus eps times (the summand at the
shown values, plus the shown target, less the true sum). So the row holds if the incoming form is
worth the shown target less the true sum ("rowU_of"). A shown value is a true value plus a challenge
times a mask entry, and an incoming form lists these challenges at these mask entries. What is left
is that the true values fit: the roots of the two trees are the products, and the two halves of a
level, joined on a line, are the level at the new point.

Main theorems:
* "rows16_hon": under "PremT", every row of Fo.rows16 D.N (trT D μ C) holds of μ. Only together with
  "trace_hon" (Johnson/HonestTrace/LookTrace.lean) does it say that the rounds "rsT" make the rows
  hold: see Limits.
* "keyEnd_hon": under "PremT", the key side's last shown target in "trT", less the value of the form
  that the last line step hands on, is the extension of the factors al - key at the key side's
  point.
* "tieInc_val", "keyInc_val", "tabInc_val": an incoming form is worth the shown target less the true
  value.
* The rows by kind: "tieRows_hon", "keyRows_hon", "tabRows_hon", "rowEnd_hon", "rowBitU_hon",
  "rowBitE_hon", "rowNum_hon".
Definitions: "tieSc", "keySc", "tabSc": the members of the three lists of "trT", by number.

Limits. The statements speak of the term "trT", not of rounds: that TwV.traceOfFlat reads "trT" off
the rounds "rsT" is not shown in this file. The last values in "trT" are written in the form that
the rows ask for; that a run of a sumcheck ends at them is not shown in this file. So the tie's rows
hold here without a premise. "Data.Mid" is used at two places: its clause on the sum of the counts
in "rowNum_hon", and as the premise of "bitsJob_sum" (Johnson/HonestTrace/LookJobs.lean) in
"rowBitU_hon". The keys' row (TwV.rowKey) is not covered: "keyEnd_hon" says nothing on what μ reads
at the keys' places. μ and C are arguments: nothing is drawn. Whether "PremT" can be met is not said
in this file.

Not claimed: that a verifier accepts anything; that a prover's program computes or sends these
values; anything on what the values show of the keys or the counts.

-/
import Johnson.HonestTrace.LookSum
import Johnson.HonestTrace.LookJobs
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open Finset TwV
open OnBytes.Model
open Cb.Lkp

section
variable {K : Type} [Field K] {P : Type}

/-! ## 1 · Values of sparse forms; lists over a range -/

/-- The empty form is worth 0. -/
theorem valS_nil (μ : P → K) : _root_.Fo.valS ([] : List (P × K)) μ = 0 := by
  simp [_root_.Fo.valS]

/-- A form of one term is worth its coefficient times the entry at its place. -/
theorem valS_one (p : P) (c : K) (μ : P → K) : _root_.Fo.valS [(p, c)] μ = c * μ p := by
  simp [_root_.Fo.valS]

/-- A form of two terms is worth the sum of the two products of coefficient and entry. -/
theorem valS_two (p q : P) (c e : K) (μ : P → K) :
    _root_.Fo.valS [(p, c), (q, e)] μ = c * μ p + e * μ q := by
  simp [_root_.Fo.valS]

/-- A form listed over the numbers below n is worth the sum, over these numbers, of coefficient
times entry. -/
theorem valS_map_range (p : ℕ → P) (c : ℕ → K) (μ : P → K) (n : ℕ) :
    _root_.Fo.valS ((List.range n).map fun e => (p e, c e)) μ = ∑ e ∈ range n, c e * μ (p e) := by
  unfold _root_.Fo.valS
  rw [List.map_map]
  exact _root_.Fo.lsum _ n

/-- Forms laid one behind the other over the numbers below n are worth the sum of their values. -/
theorem valS_flatMap_range (f : ℕ → List (P × K)) (μ : P → K) :
    ∀ n, _root_.Fo.valS ((List.range n).flatMap f) μ = ∑ i ∈ range n, _root_.Fo.valS (f i) μ
  | 0 => by simp [_root_.Fo.valS]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, _root_.Fo.valS_append, valS_flatMap_range f μ n,
      Finset.sum_range_succ]
    simp

/-- The list of f over the numbers below m, reversed, has m members. -/
theorem len_rev {α : Type} (f : ℕ → α) (m : ℕ) : ((List.range m).map f).reverse.length = m := by
  simp

/-- The list of f over the numbers below m + 1, reversed, is f m in front of the reversed list over
the numbers below m. -/
theorem rev_succ {α : Type} (f : ℕ → α) (m : ℕ) :
    ((List.range (m + 1)).map f).reverse = f m :: ((List.range m).map f).reverse := by
  rw [List.range_succ, List.map_append, List.reverse_append]
  rfl

/-- For i < m, member i of the list of f over the numbers below m is f i. -/
theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {m i : ℕ} (h : i < m) :
    ((List.range m).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- A list without its last member reads as the list does at every place but the last. -/
theorem getD_dropLast {α : Type} (d : α) :
    ∀ (xs : List α) (i : ℕ), i + 1 < xs.length → xs.dropLast.getD i d = xs.getD i d
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [_], _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | _ :: _ :: _, 0, _ => rfl
  | _ :: y :: xs, i + 1, h => getD_dropLast d (y :: xs) i (Nat.lt_of_succ_lt_succ h)

/-- TwV.byVar gives as many coordinates as the order has members. -/
theorem byVar_length (o : List ℕ) (xs : List K) : (byVar o xs).length = o.length := by
  simp [byVar]

/-- An order that lists the numbers below m, each once, has m members. -/
theorem perm_length {o : List ℕ} {m : ℕ} (ho : o.Perm (List.range m)) : o.length = m := by
  rw [ho.length_eq, List.length_range]

/-- If o lists the numbers below m, each once, and xs has m + 1 members, TwV.byVar o reads the same
point off xs and off xs without its last member. -/
theorem byVar_dropLast {o : List ℕ} {m : ℕ} (xs : List K) (ho : o.Perm (List.range m))
    (hx : xs.length = m + 1) : byVar o xs.dropLast = byVar o xs := by
  unfold byVar
  refine List.map_congr_left fun c hc => ?_
  have hc' : c < m := by
    rw [List.mem_range, perm_length ho] at hc
    exact hc
  have hm : c ∈ o := ho.mem_iff.mpr (List.mem_range.mpr hc')
  have hi : o.idxOf c < m := by
    have := List.idxOf_lt_length_of_mem hm
    rwa [perm_length ho] at this
  exact getD_dropLast 0 xs _ (by omega)

/-- At a point of w + d coordinates, the extension of a function that reads of X only X / 2^w is the
sum over r < 2^d of eq(the coordinates from w on, r) times the function at r. -/
theorem ext_rows (w d : ℕ) (g : ℕ → K) (pt : List K) (hp : pt.length = w + d) :
    ext (w + d) (fun X => g (X / 2 ^ w)) pt =
      ((List.range (2 ^ d)).map fun r => eqN (pt.drop w) r * g r).sum := by
  rw [_root_.Fo.lsum]
  have hl : (pt.take w).length = w := by rw [List.length_take]; omega
  have hd : (pt.drop w).length = d := by rw [List.length_drop]; omega
  have h := _root_.Fo.eqN_split (pt.take w) (pt.drop w) fun _ j => g j
  rw [List.take_append_drop, hl, hd] at h
  have ht := _root_.Fo.eqN_total (pt.take w)
  rw [hl] at ht
  refine h.trans ?_
  rw [← Finset.sum_mul, ht, one_mul]

/-! ## 2 · One row of a masked sumcheck -/

/-- If the last value of a sumcheck s is the value under μ of the form TwV.hide L dg s.xs plus s.eps
(S0 + (tg - C)), and the incoming form is worth tg - C under μ, then the row TwV.rowU L dg s inc S0
holds of μ. -/
theorem rowU_of (L : Led P) (μ : P → K) (dg : List ℕ) (s : Sc K) (inc : List (P × K))
    (S0 tg C : K)
    (hfin : s.fin = _root_.Fo.valS (hide L dg s.xs) μ + s.eps * (S0 + (tg - C)))
    (hinc : _root_.Fo.valS inc μ = tg - C) : _root_.Fo.SRowHolds (rowU L dg s inc S0) μ := by
  obtain ⟨eps, xs, fin, vals⟩ := s
  have hfin' : fin = _root_.Fo.valS (hide L dg xs) μ + eps * (S0 + (tg - C)) := hfin
  subst hfin'
  exact rowU_hon L μ dg eps tg C S0 xs vals inc hinc

/-- If for every s < m the row of tie step s, made of f s and the steps in front of it, holds of μ,
then every row of TwV.tieRowsR at the steps f 0, ..., f (m - 1) holds of μ. -/
theorem tieRows_mem (N : Nums P K) (lam : K) (f : ℕ → Sc K) (μ : P → K) :
    ∀ m : ℕ, (∀ s < m, _root_.Fo.SRowHolds
        (rowU (N.ledTie s) [3] (f s) (tieInc N ((List.range s).map f).reverse)
          (tieS0 N lam s (f s))) μ) →
      ∀ r ∈ tieRowsR N lam ((List.range m).map f).reverse, _root_.Fo.SRowHolds r μ
  | 0, _, r, hr => by simp [tieRowsR] at hr
  | m + 1, h, r, hr => by
    rw [rev_succ, tieRowsR, len_rev] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact h m (Nat.lt_succ_self m)
    · exact tieRows_mem N lam f μ m (fun s hs => h s (Nat.lt_succ_of_lt hs)) r hr'

/-- If for every l < m the row of level l, made of f l and the levels in front of it, holds of μ,
then every row of TwV.lvRowsR at the levels f 0, ..., f (m - 1) holds of μ. -/
theorem lvRows_mem (led : ℕ → Led P) (g : ℕ) (inc0 : List (P × K)) (f : ℕ → Sc K × K)
    (μ : P → K) :
    ∀ m : ℕ, (∀ l < m, _root_.Fo.SRowHolds
        (rowU (led l) (List.replicate (g + l) 2 ++ [2]) (f l).1
          (incTop led inc0 ((List.range l).map f).reverse) ((f l).1.v 0 * (f l).1.v 1)) μ) →
      ∀ r ∈ lvRowsR led g inc0 ((List.range m).map f).reverse, _root_.Fo.SRowHolds r μ
  | 0, _, r, hr => by simp [lvRowsR] at hr
  | m + 1, h, r, hr => by
    rw [rev_succ, lvRowsR, len_rev] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact h m (Nat.lt_succ_self m)
    · exact lvRows_mem led g inc0 f μ m (fun s hs => h s (Nat.lt_succ_of_lt hs)) r hr'

/-- Shown value 0 of the job "pj": the extension of A at the point of all challenges but the last,
plus the last challenge times the mask entry at L.sh 0. -/
theorem shown_pj0 (L : Led P) (μ : P → K) (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ)
    (z xs : List K) :
    (shownOf L μ (pj m κ A B o z) xs).getD 0 0 =
      ext m A (byVar o xs.dropLast) + xs.getLastD 0 * μ (L.sh 0) := rfl

/-- Shown value 1 of the job "pj": the extension of B at the point of all challenges but the last,
plus the last challenge times the mask entry at L.sh 1. -/
theorem shown_pj1 (L : Led P) (μ : P → K) (m : ℕ) (κ : K) (A B : ℕ → K) (o : List ℕ)
    (z xs : List K) :
    (shownOf L μ (pj m κ A B o z) xs).getD 1 0 =
      ext m B (byVar o xs.dropLast) + xs.getLastD 0 * μ (L.sh 1) := rfl

/-- If o lists the numbers below m, each once, and s has m + 1 challenges, then the form
TwV.lineForm L s ρ is worth under μ: (1 - ρ) times shown value 0 plus ρ times shown value 1 of the
job of the two halves of f, less the extension of f over m + 1 coordinates at the point (TwV.byVar o
s.xs, ρ). -/
theorem line_val (L : Led P) (μ : P → K) (m : ℕ) (κ : K) (f : ℕ → K) (o : List ℕ) (z : List K)
    (s : Sc K) (ρ : K) (ho : o.Perm (List.range m)) (hx : s.xs.length = m + 1) :
    _root_.Fo.valS (lineForm L s ρ) μ =
      ((1 - ρ) * (shownOf L μ (pj m κ f (fun X => f (X + 2 ^ m)) o z) s.xs).getD 0 0 +
        ρ * (shownOf L μ (pj m κ f (fun X => f (X + 2 ^ m)) o z) s.xs).getD 1 0) -
      ext (m + 1) f (byVar o s.xs ++ [ρ]) := by
  rw [← ext_line m f (byVar o s.xs) ρ ((byVar_length o s.xs).trans (perm_length ho)), shown_pj0,
    shown_pj1, byVar_dropLast s.xs ho hx]
  show _root_.Fo.valS [(L.sh 0, s.xs.getLastD 0 * (1 - ρ)), (L.sh 1, s.xs.getLastD 0 * ρ)] μ = _
  rw [valS_two]
  ring

/-- If the incoming form is worth under μ the target tg less the true sum of the job pj m 0 A B o z,
then the row that TwV.lvRowsR makes of a level holds of μ at "scJob" of that job and tg. -/
theorem lvRow_hon (L : Led P) (μ : P → K) (m : ℕ) (A B : ℕ → K) (o : List ℕ) (z : List K)
    (eps tg : K) (xs : List K) (inc : List (P × K))
    (hinc : _root_.Fo.valS inc μ = tg - (pj m 0 A B o z).sum) :
    _root_.Fo.SRowHolds
      (rowU L (List.replicate m 2 ++ [2]) (scJob L μ (pj m 0 A B o z) eps tg xs) inc
        ((scJob L μ (pj m 0 A B o z) eps tg xs).v 0 * (scJob L μ (pj m 0 A B o z) eps tg xs).v 1))
      μ := by
  have h : (scJob L μ (pj m 0 A B o z) eps tg xs).fin =
      _root_.Fo.valS (hide L (List.replicate m 2 ++ [2]) (scJob L μ (pj m 0 A B o z) eps tg xs).xs)
          μ +
        (scJob L μ (pj m 0 A B o z) eps tg xs).eps *
          ((0 + (scJob L μ (pj m 0 A B o z) eps tg xs).v 0 *
              (scJob L μ (pj m 0 A B o z) eps tg xs).v 1) + (tg - (pj m 0 A B o z).sum)) := rfl
  rw [zero_add] at h
  exact rowU_of L μ _ _ inc _ tg _ h hinc

/-! ## 3 · The parts of the flat trace, by number -/

variable (D : Data P K) (μ : P → K) (C : Chal K)

/-- Step s of the tie in "trT". -/
def tieSc (s : ℕ) : Sc K :=
  scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s]

/-- Level l of the key side in "trT", with its line's draw. -/
def keySc (l : ℕ) : Sc K × K :=
  (scJob (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyE l) (keyTg D μ C l) (C.keyX l), C.keyR l)

/-- Level l of the table's side in "trT", with its line's draw. -/
def tabSc (l : ℕ) : Sc K × K :=
  (scJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (tabTg D μ C l) (C.tabX l), C.tabR l)

/-- The tie of "trT" is the list of "tieSc" over the numbers below n + 1. -/
theorem trT_tie : (trT D μ C).tie = (List.range (D.N.n + 1)).map (tieSc D μ C) := rfl

/-- The key side of "trT" is the list of "keySc" over the numbers below v. -/
theorem trT_keys : (trT D μ C).keys = (List.range D.v).map (keySc D μ C) := rfl

/-- The table's side of "trT" is the list of "tabSc" over the numbers below d. -/
theorem trT_tabl : (trT D μ C).tabl = (List.range D.N.d).map (tabSc D μ C) := rfl

/-! ## 4 · The tie -/

/-- Behind step 0 the next step takes up shown value 0. -/
theorem nxAt_succ (s : ℕ) : nxAt (s + 1) = 0 := if_neg (Nat.succ_ne_zero s)

/-- Behind step 0 the plane's root is shown value 1. -/
theorem ptAt_succ (s : ℕ) : TwV.ptAt (s + 1) = 1 := if_neg (Nat.succ_ne_zero s)

/-- The end values of tie step 0: Z, Pc 1, G 0. -/
theorem tie_ends_zero (xs : List K) : (tieJob D 0).ends xs = [D.Z, D.Pc 1, D.G 0] := by
  show (if (0 : ℕ) = 0 then [D.Z, D.Pc 1, D.G 0] else [D.Pc (0 + 1), D.G 0]) = _
  exact if_pos rfl

/-- The end values of tie step s + 1: Pc (s + 2), G (s + 1). -/
theorem tie_ends_succ (s : ℕ) (xs : List K) :
    (tieJob D (s + 1)).ends xs = [D.Pc (s + 1 + 1), D.G (s + 1)] := by
  show (if s + 1 = 0 then [D.Z, D.Pc 1, D.G 0] else [D.Pc (s + 1 + 1), D.G (s + 1)]) = _
  exact if_neg (Nat.succ_ne_zero s)

/-- The field "sum" of tie step 0 is 0. -/
theorem tie_sum_zero : (tieJob D 0).sum = 0 := by
  show (if (0 : ℕ) = 0 then (0 : K) else D.Pc 0) = 0
  exact if_pos rfl

/-- The field "sum" of tie step s + 1 is Pc (s + 1). -/
theorem tie_sum_succ (s : ℕ) : (tieJob D (s + 1)).sum = D.Pc (s + 1) := by
  show (if s + 1 = 0 then (0 : K) else D.Pc (s + 1)) = _
  exact if_neg (Nat.succ_ne_zero s)

/-- Shown value 0 of tie step 0 is Z plus the step's challenge times the mask entry at its place. -/
theorem tieShown_key : tieShown D μ C 0 0 = D.Z + C.tieB 0 * μ ((D.N.ledTie 0).sh 0) := by
  unfold tieShown shownOf
  rw [tie_ends_zero]
  rfl

/-- The shown value of tie step s that step s + 1 takes up is Pc (s + 1) plus the step's challenge
times the mask entry at its place. -/
theorem tieShown_nx (s : ℕ) :
    tieShown D μ C s (nxAt s) = D.Pc (s + 1) + C.tieB s * μ ((D.N.ledTie s).sh (nxAt s)) := by
  unfold tieShown shownOf
  cases s with
  | zero =>
    rw [tie_ends_zero]
    rfl
  | succ s =>
    rw [tie_ends_succ, nxAt_succ]
    rfl

/-- The shown value of tie step s at TwV.ptAt s is G s plus the step's challenge times the mask
entry at its place. -/
theorem tieShown_pt (s : ℕ) :
    tieShown D μ C s (TwV.ptAt s) = D.G s + C.tieB s * μ ((D.N.ledTie s).sh (TwV.ptAt s)) := by
  unfold tieShown shownOf
  cases s with
  | zero =>
    rw [tie_ends_zero]
    rfl
  | succ s =>
    rw [tie_ends_succ, ptAt_succ]
    rfl

/-- The form that comes into tie step s of "trT" is worth under μ the step's shown target "tieTg"
less the field "sum" of its job. No premise. -/
theorem tieInc_val (s : ℕ) :
    _root_.Fo.valS (tieInc D.N ((List.range s).map (tieSc D μ C)).reverse) μ =
      tieTg D μ C s - (tieJob D s).sum := by
  cases s with
  | zero =>
    have h1 : tieTg D μ C 0 = 0 := if_pos rfl
    rw [h1, tie_sum_zero, sub_zero]
    exact valS_nil μ
  | succ s =>
    have h1 : tieTg D μ C (s + 1) = tieShown D μ C s (nxAt s) := if_neg (Nat.succ_ne_zero s)
    rw [h1, tie_sum_succ, tieShown_nx, rev_succ, tieInc, len_rev, valS_one]
    show C.tieB s * _ = _
    ring

/-- Every row of TwV.tieRowsR at the tie of "trT" holds of μ. No premise: the last values in "trT"
are written in the form that "rowU_of" asks for. That a run of the sumcheck ends at these values is
not said here. -/
theorem tieRows_hon :
    ∀ r ∈ tieRowsR D.N D.al ((List.range (D.N.n + 1)).map (tieSc D μ C)).reverse,
      _root_.Fo.SRowHolds r μ :=
  tieRows_mem D.N D.al (tieSc D μ C) μ (D.N.n + 1) fun s _ =>
    rowU_of (D.N.ledTie s) μ [3] (tieSc D μ C s) _ _ (tieTg D μ C s) (tieJob D s).sum rfl
      (tieInc_val D μ C s)

/-! ## 5 · The key side -/

/-- The extension over no coordinate of level 0 of the key side's tree is Z, the product of al - key
over all 2^v keys. -/
theorem kLvl_root : ext 0 (D.kLvl 0) [] = D.Z := by
  show ∑ X ∈ range (2 ^ 0), eqN [] X * Blocks.lvl 0 D.v (facK D.key D.al) 0 X =
    ∏ b ∈ range (2 ^ D.v), (D.al - D.key b)
  rw [pow_zero, Finset.sum_range_one, Blocks.lvl_zero]
  show 1 * _ = _
  rw [one_mul]
  refine Finset.prod_congr rfl fun j _ => ?_
  show D.al - D.key (j * 2 ^ 0 + 0) = D.al - D.key j
  rw [pow_zero, Nat.mul_one, Nat.add_zero]

/-- The point that TwV.pntTop reads at the top of the first l levels of the key side of "trT" is
"keyPt" l. -/
theorem keyPt_eq (l : ℕ) :
    pntTop D.N.oK [] ((List.range l).map (keySc D μ C)).reverse = keyPt D C l := by
  cases l with
  | zero => rfl
  | succ l =>
    rw [rev_succ, pntTop, len_rev]
    rfl

/-- Under "PremT", for l ≤ v: the form at the top of the first l levels of the key side of "trT" is
worth under μ the shown target "keyTg" l less the extension of level l of the key side's tree at
"keyPt" l. -/
theorem keyInc_val (H : PremT D μ C) (l : ℕ) (hl : l ≤ D.v) :
    _root_.Fo.valS (incTop D.N.ledK (fK D.N (trT D μ C))
        ((List.range l).map (keySc D μ C)).reverse) μ =
      keyTg D μ C l - ext l (D.kLvl l) (keyPt D C l) := by
  cases l with
  | zero =>
    show _root_.Fo.valS [((D.N.ledTie 0).sh 0, ((trT D μ C).tie.getD 0 Sc.zero).be)] μ =
      tieShown D μ C 0 0 - ext 0 (D.kLvl 0) []
    rw [trT_tie, getD_map_range _ _ (Nat.succ_pos _), valS_one, tieShown_key, kLvl_root]
    show C.tieB 0 * _ = _
    ring
  | succ l =>
    rw [rev_succ, incTop, len_rev]
    exact line_val (D.N.ledK l) μ l 0 (D.kLvl (l + 1)) (D.N.oK l) (keyPt D C l)
      (keySc D μ C l).1 (C.keyR l) (H.oK l hl) (H.chal.keyX l hl)

/-- Under "PremT" every row of TwV.lvRowsR at the key side of "trT" holds of μ. -/
theorem keyRows_hon (H : PremT D μ C) :
    ∀ r ∈ lvRowsR D.N.ledK 0 (fK D.N (trT D μ C)) ((List.range D.v).map (keySc D μ C)).reverse,
      _root_.Fo.SRowHolds r μ := by
  refine lvRows_mem D.N.ledK 0 _ (keySc D μ C) μ D.v fun l hl => ?_
  rw [Nat.zero_add]
  refine lvRow_hon (D.N.ledK l) μ l (D.kLvl (l + 1)) (fun X => D.kLvl (l + 1) (X + 2 ^ l))
    (D.N.oK l) (keyPt D C l) (C.keyE l) (keyTg D μ C l) (C.keyX l) _ ?_
  rw [keyInc_val D μ C H l hl.le]
  exact congrArg (keyTg D μ C l - ·) (keyJob_sum D hl _).symm

/-! ## 6 · The table's side -/

/-- For X < 2^w, entry X of level 0 of the table side's tree is G X, the root of plane X. -/
theorem tLvl_root {X : ℕ} (hX : X < 2 ^ D.N.w) : D.tLvl 0 X = D.G X := by
  show Blocks.lvl D.N.w D.N.d (facT D.N.w D.N.tab D.bits D.al) 0 X =
    ∏ u ∈ range (2 ^ D.N.d), (1 + D.bits u X * (D.al - 1 - D.N.tab u))
  rw [Blocks.lvl_zero]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : (j * 2 ^ D.N.w + X) / 2 ^ D.N.w = j := by
    rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hX, Nat.add_zero]
  have e2 : (j * 2 ^ D.N.w + X) % 2 ^ D.N.w = X := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hX]
  show 1 + D.bits ((j * 2 ^ D.N.w + X) / 2 ^ D.N.w) ((j * 2 ^ D.N.w + X) % 2 ^ D.N.w) *
    (D.al - 1 - D.N.tab ((j * 2 ^ D.N.w + X) / 2 ^ D.N.w)) = _
  rw [e1, e2]

/-- For th < n + 2, the form TwV.formT of plane th at "trT" is worth under μ the shown root "gShown"
th less G th. -/
theorem formT_val {th : ℕ} (hth : th < D.N.n + 2) :
    _root_.Fo.valS (formT D.N (trT D μ C) th) μ = gShown D μ C th - D.G th := by
  unfold formT gShown
  by_cases h : th < D.N.n + 1
  · rw [if_pos h, if_pos h, trT_tie, getD_map_range _ _ h, valS_one, tieShown_pt]
    show C.tieB th * _ = _
    ring
  · have h' : th = D.N.n + 1 := by omega
    have hP : D.Pc (D.N.n + 1) = D.G (D.N.n + 1) := by
      unfold Data.Pc
      rw [Nat.sub_self]
      rfl
    rw [if_neg h, if_pos h', if_neg h, trT_tie, getD_map_range _ _ (Nat.lt_succ_self _), valS_one,
      tieShown_nx, hP, h']
    show C.tieB D.N.n * _ = _
    ring

/-- Under "PremT", for l ≤ d: the form at the top of the first l levels of the table's side of "trT"
is worth under μ the shown target "tabTg" l less the extension of level l of the table side's tree
at "tabPt" l. -/
theorem tabInc_val (H : PremT D μ C) (l : ℕ) (hl : l ≤ D.N.d) :
    _root_.Fo.valS (incTop D.N.ledT (incT0 D.N (trT D μ C))
        ((List.range l).map (tabSc D μ C)).reverse) μ =
      tabTg D μ C l - ext (D.N.w + l) (D.tLvl l) (tabPt D C l) := by
  cases l with
  | zero =>
    show _root_.Fo.valS ((List.range (2 ^ D.N.w)).flatMap fun th =>
        scale (eqN C.join th) (formT D.N (trT D μ C) th)) μ =
      ((List.range (2 ^ D.N.w)).map fun j => eqN C.join j * gShown D μ C j).sum -
        ∑ X ∈ range (2 ^ D.N.w), eqN C.join X * D.tLvl 0 X
    rw [valS_flatMap_range, _root_.Fo.lsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun th hth => ?_
    have hth' : th < 2 ^ D.N.w := Finset.mem_range.mp hth
    rw [_root_.Fo.valS_scale, formT_val D μ C (by rw [H.planes]; exact hth'), tLvl_root D hth']
    ring
  | succ l =>
    rw [rev_succ, incTop, len_rev]
    exact line_val (D.N.ledT l) μ (D.N.w + l) 0 (D.tLvl (l + 1)) (D.N.oT l) (tabPt D C l)
      (tabSc D μ C l).1 (C.tabR l) (H.oT l hl) (H.chal.tabX l hl)

/-- Under "PremT" every row of TwV.lvRowsR at the table's side of "trT" holds of μ. -/
theorem tabRows_hon (H : PremT D μ C) :
    ∀ r ∈ lvRowsR D.N.ledT D.N.w (incT0 D.N (trT D μ C))
        ((List.range D.N.d).map (tabSc D μ C)).reverse,
      _root_.Fo.SRowHolds r μ := by
  refine lvRows_mem D.N.ledT D.N.w _ (tabSc D μ C) μ D.N.d fun l hl => ?_
  refine lvRow_hon (D.N.ledT l) μ (D.N.w + l) (D.tLvl (l + 1))
    (fun X => D.tLvl (l + 1) (X + 2 ^ (D.N.w + l))) (D.N.oT l) (tabPt D C l) (C.tabE l)
    (tabTg D μ C l) (C.tabX l) _ ?_
  rw [tabInc_val D μ C H l hl.le]
  exact congrArg (tabTg D μ C l - ·) (tabJob_sum D hl _).symm

/-! ## 7 · The leaves, the bits, the count -/

/-- Under "PremT" the form TwV.bitsForm at any point is worth under μ the extension of the bits at
that point. -/
theorem bitsForm_val (H : PremT D μ C) (pt : List K) :
    _root_.Fo.valS (bitsForm D.N pt) μ = ext (D.N.w + D.N.d) D.bitAt pt := by
  refine (valS_map_range (fun e => D.N.bAt (e / 2 ^ D.N.w) (e % 2 ^ D.N.w)) (fun e => eqN pt e) μ
    (2 ^ (D.N.w + D.N.d))).trans ?_
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e < 2 ^ D.N.w * 2 ^ D.N.d := by
    rw [← pow_add]
    exact Finset.mem_range.mp he
  rw [H.bits (e / 2 ^ D.N.w) (Nat.div_lt_of_lt_mul he') (e % 2 ^ D.N.w)
    (Nat.mod_lt _ (by positivity))]
  rfl

/-- Under "PremT" the row TwV.rowEnd at "trT" holds of μ. -/
theorem rowEnd_hon (H : PremT D μ C) : _root_.Fo.SRowHolds (rowEnd D.N (trT D μ C)) μ := by
  have hlen : (byVar D.N.oE C.clsX).length = D.N.w + D.N.d :=
    (byVar_length _ _).trans (perm_length H.oE)
  have hs : ((List.range (2 ^ D.N.d)).map fun r =>
      eqN ((byVar D.N.oE C.clsX).drop D.N.w) r * (D.al - 1 - D.N.tab r)).sum =
      ext (D.N.w + D.N.d) D.rowAt (byVar D.N.oE C.clsX) :=
    (ext_rows D.N.w D.N.d (fun r => D.al - 1 - D.N.tab r) (byVar D.N.oE C.clsX) hlen).symm
  show _root_.Fo.valS (hide D.N.ledE (dgE D.N) C.clsX ++
        scale C.clsE (incTop D.N.ledT (incT0 D.N (trT D μ C))
          ((List.range D.N.d).map (tabSc D μ C)).reverse) ++
        scale (C.clsE * ((List.range (2 ^ D.N.d)).map fun r =>
          eqN ((byVar D.N.oE C.clsX).drop D.N.w) r * (D.al - 1 - D.N.tab r)).sum)
          (bitsForm D.N (byVar D.N.oE C.clsX))) μ =
      (_root_.Fo.valS (hide D.N.ledE (dgE D.N) C.clsX) μ +
        C.clsE * ((1 + ext (D.N.w + D.N.d) D.bitAt (byVar D.N.oE C.clsX) *
            ext (D.N.w + D.N.d) D.rowAt (byVar D.N.oE C.clsX)) +
          (tabTg D μ C D.N.d - (leavesJob D (tabPt D C D.N.d)).sum))) - C.clsE * 1
  rw [_root_.Fo.valS_append, _root_.Fo.valS_append, _root_.Fo.valS_scale, _root_.Fo.valS_scale,
    tabInc_val D μ C H D.N.d le_rfl, bitsForm_val D μ C H, leavesJob_sum, hs]
  ring

/-- Under "PremT" the row TwV.rowBitU at "trT" holds of μ. -/
theorem rowBitU_hon (H : PremT D μ C) : _root_.Fo.SRowHolds (rowBitU D.N (trT D μ C)) μ := by
  refine rowU_of D.N.ledB μ (List.replicate (D.N.w + D.N.d) 2 ++ [2]) (trT D μ C).bits [] _ 0
    (bitsJob D C.zero).sum rfl ?_
  rw [bitsJob_sum D H.mid, sub_zero]
  exact valS_nil μ

/-- Under "PremT" the row TwV.rowBitE at "trT" holds of μ. -/
theorem rowBitE_hon (H : PremT D μ C) : _root_.Fo.SRowHolds (rowBitE D.N (trT D μ C)) μ := by
  show _root_.Fo.valS (bitsForm D.N (byVar D.N.oB C.bitX) ++
      [(D.N.ledB.sh 0, C.bitX.getLastD 0)]) μ =
    ext (D.N.w + D.N.d) D.bitAt (byVar D.N.oB C.bitX.dropLast) +
      C.bitX.getLastD 0 * μ (D.N.ledB.sh 0)
  rw [_root_.Fo.valS_append, bitsForm_val D μ C H, valS_one, byVar_dropLast _ H.oB H.chal.bitX]

/-- Under "PremT" the row TwV.rowNum, on the sum of the counts, holds of μ. -/
theorem rowNum_hon (H : PremT D μ C) : _root_.Fo.SRowHolds (rowNum D.N) μ := by
  have hN : ∑ u ∈ range (2 ^ D.N.d), ∑ j ∈ range (D.N.n + 2), (2 : K) ^ j * D.bits u j =
      ((2 ^ (D.N.v' + 1) - (D.N.pads.map Prod.snd).sum : ℕ) : K) := H.mid.2.1
  show _root_.Fo.valS ((List.range (2 ^ D.N.d)).flatMap fun u =>
      (List.range (D.N.n + 2)).map fun j => (D.N.bAt u j, (2 : K) ^ j)) μ =
    ((2 ^ (D.N.v' + 1) - (D.N.pads.map Prod.snd).sum : ℕ) : K)
  rw [valS_flatMap_range, ← hN]
  refine Finset.sum_congr rfl fun u hu => ?_
  refine (valS_map_range (fun j => D.N.bAt u j) (fun j => (2 : K) ^ j) μ (D.N.n + 2)).trans ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [H.bits u (Finset.mem_range.mp hu) j (by rw [← H.planes]; exact Finset.mem_range.mp hj)]

/-! ## 8 · The two statements -/

/-- **Every row but the keys' holds at the term "trT".** Under "PremT", every row of "Fo.rows16" at
the public numbers D.N and the flat trace "trT D μ C" holds of the reading μ. The last values in
"trT" are written in the form that the rows ask for: only together with "trace_hon"
(Johnson/HonestTrace/LookTrace.lean), by which TwV.traceOfFlat reads "trT" off the rounds "rsT",
does this say that the rounds make the rows hold. -/
theorem rows16_hon (H : PremT D μ C) :
    ∀ r ∈ _root_.Fo.rows16 D.N (trT D μ C), _root_.Fo.SRowHolds r μ := by
  intro r hr
  unfold _root_.Fo.rows16 at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | ((h | h | h | h) | h)
  · exact tieRows_hon D μ C r h
  · exact keyRows_hon D μ C H r h
  · exact tabRows_hon D μ C H r h
  · rw [h]; exact rowEnd_hon D μ C H
  · rw [h]; exact rowBitU_hon D μ C H
  · rw [h]; exact rowBitE_hon D μ C H
  · rw [h]; exact rowNum_hon D μ C H

/-- **The end of the key side.** Under "PremT", the last shown target of the key side in
"trT D μ C", less the value under μ of the form that the last line step hands on, is the extension
of the factors al - key at the key side's point. -/
theorem keyEnd_hon (H : PremT D μ C) :
    (trT D μ C).kT -
        _root_.Fo.valS (incTop D.N.ledK (fK D.N (trT D μ C)) (trT D μ C).keys.reverse) μ =
      ext D.v (facK D.key D.al) (_root_.Fo.pntK D.N (trT D μ C)) := by
  have hp : _root_.Fo.pntK D.N (trT D μ C) = keyPt D C D.v := keyPt_eq D μ C D.v
  have hk : D.kLvl D.v = facK D.key D.al := Blocks.lvl_top 0 D.v _
  rw [hp, trT_keys, keyInc_val D μ C H D.v le_rfl, hk]
  show keyTg D μ C D.v - _ = _
  ring

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.valS_nil
#print axioms OnBytes.HonestTrace.Look.valS_one
#print axioms OnBytes.HonestTrace.Look.valS_two
#print axioms OnBytes.HonestTrace.Look.valS_map_range
#print axioms OnBytes.HonestTrace.Look.valS_flatMap_range
#print axioms OnBytes.HonestTrace.Look.len_rev
#print axioms OnBytes.HonestTrace.Look.rev_succ
#print axioms OnBytes.HonestTrace.Look.getD_map_range
#print axioms OnBytes.HonestTrace.Look.getD_dropLast
#print axioms OnBytes.HonestTrace.Look.byVar_length
#print axioms OnBytes.HonestTrace.Look.perm_length
#print axioms OnBytes.HonestTrace.Look.byVar_dropLast
#print axioms OnBytes.HonestTrace.Look.ext_rows
#print axioms OnBytes.HonestTrace.Look.rowU_of
#print axioms OnBytes.HonestTrace.Look.tieRows_mem
#print axioms OnBytes.HonestTrace.Look.lvRows_mem
#print axioms OnBytes.HonestTrace.Look.shown_pj0
#print axioms OnBytes.HonestTrace.Look.shown_pj1
#print axioms OnBytes.HonestTrace.Look.line_val
#print axioms OnBytes.HonestTrace.Look.lvRow_hon
#print axioms OnBytes.HonestTrace.Look.trT_tie
#print axioms OnBytes.HonestTrace.Look.trT_keys
#print axioms OnBytes.HonestTrace.Look.trT_tabl
#print axioms OnBytes.HonestTrace.Look.nxAt_succ
#print axioms OnBytes.HonestTrace.Look.ptAt_succ
#print axioms OnBytes.HonestTrace.Look.tie_ends_zero
#print axioms OnBytes.HonestTrace.Look.tie_ends_succ
#print axioms OnBytes.HonestTrace.Look.tie_sum_zero
#print axioms OnBytes.HonestTrace.Look.tie_sum_succ
#print axioms OnBytes.HonestTrace.Look.tieShown_key
#print axioms OnBytes.HonestTrace.Look.tieShown_nx
#print axioms OnBytes.HonestTrace.Look.tieShown_pt
#print axioms OnBytes.HonestTrace.Look.tieInc_val
#print axioms OnBytes.HonestTrace.Look.tieRows_hon
#print axioms OnBytes.HonestTrace.Look.kLvl_root
#print axioms OnBytes.HonestTrace.Look.keyPt_eq
#print axioms OnBytes.HonestTrace.Look.keyInc_val
#print axioms OnBytes.HonestTrace.Look.keyRows_hon
#print axioms OnBytes.HonestTrace.Look.tLvl_root
#print axioms OnBytes.HonestTrace.Look.formT_val
#print axioms OnBytes.HonestTrace.Look.tabInc_val
#print axioms OnBytes.HonestTrace.Look.tabRows_hon
#print axioms OnBytes.HonestTrace.Look.bitsForm_val
#print axioms OnBytes.HonestTrace.Look.rowEnd_hon
#print axioms OnBytes.HonestTrace.Look.rowBitU_hon
#print axioms OnBytes.HonestTrace.Look.rowBitE_hon
#print axioms OnBytes.HonestTrace.Look.rowNum_hon
#print axioms OnBytes.HonestTrace.Look.rows16_hon
#print axioms OnBytes.HonestTrace.Look.keyEnd_hon
