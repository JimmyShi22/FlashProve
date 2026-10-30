-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimLink.lean: what the rows of the entry file's link compute, in the field.

The written verifier of the link (Fmt/M3Link.lean) forms linear claims, called rows, on the two
folded rows that the prover has sent: the equality row, two sample rows, and a row for every draw
of a position in one of the two stored tables. It adds them up under the powers of a challenge and
puts the sum on the table of the group of the two. This file reads each of these arrays in the
field `GE` and gives every entry as a closed form: the inputs as they are read in the field, sums,
powers, and the weight `eqW` of a vertex of the cube (OnBytes/Slice/SimBasic.lean).

Main theorems.
 The vectors on the entries of a folded row: `toE_foldCol`, `vec_colVec`, `vec_colVec_gen`,
   `vec_eqVec`, `vec_negV`.
 From entries to the member's table: `vec_layHi`, `loAt_idx`.
 Rows member by member and their sum: `vec_oneAt`, `vec_axpyL`, `vec_sumM_main`, `vec_sumM_mask`,
   `toE_sumM_t`.
 The group's table: `vec_layAll`, `starts_mems`, `kOf_mems`, `vec_toK_c`, `vec_toK_d`.
 The rows: `vec_colRow_main`, `colRow_t`, `eqRow_main_zero`, `vec_eqRow_main_one`,
   `vec_smpRow_main`, `colRows_some`.
 Against the library's link at the sizes of an entry file (OnBytes/Slice/LinkAt.lean): `colF_eq`,
   `layF_eq` (the library's forms of a column and of the layout are the written rows' forms),
   `foldSym₀_eq`, `foldSym₁_eq` (the library's fold of a symbol is the written fold of its column).

Not claimed. Nothing on a protocol. What a sample row holds is left as the format's `sampleOf`.
The library's `rows` and `claims` (Cb/Ld/LdLinkClose.lean: the forms carried to a group, the targets
read off the explicit part) are not compared here. `layF_eq` speaks of the equality row's vector
over the format's second field, so whoever uses it for `eqRow P` owes P.fld = .two.
The two comparisons of forms ask that `high` is set (entry e is in row e / 2 ^ aP at place
e % 2 ^ aP of the member's table) and that a row of the code C has 2 ^ aP places. Nothing on the
other field of the format.
-/
import OnBytes.Slice.SimBasic
import OnBytes.Slice.Corners
import Fmt.M3Link
import Cb.Ld.LdLinkClose

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1 Fmt.M2 Fmt.M3

/-! ## Reading -/

/-- Entry e of an array that is given by a function. -/
theorem vec_ofFn (n : ℕ) (f : Fin n → E) (e : ℕ) :
    vec (Array.ofFn f) e = if h : e < n then toE (f ⟨e, h⟩) else 0 := by
  unfold vec ent
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : e < n
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    exact toE_zeroE

/-- The array without entries is read as 0 everywhere. -/
theorem vec_noEntries (i : ℕ) : vec #[] i = 0 := vec_of_le #[] i (Nat.zero_le _)

/-! ## The vectors of the rows, on the entries of a folded row -/

/-- The fold of an opened column: its words under the weights of the point gamma. -/
theorem toE_foldCol (gamma : List E) (col : List UInt64) :
    toE (foldCol .two gamma col) =
      ∑ b ∈ Finset.range (2 ^ gamma.length),
        eqW gamma.length (lst gamma) b * algebraMap GF GE (toF (col.getD b 0)) := by
  show toE (dotG (opsOf .two) (pvG (opsOf .two) Fmt.Fld.oneE gamma)
    (col.map Fmt.Fld.ofF).toArray) = _
  rw [← pv_at, ← dot_at, toE_dot_of_le _ _ (2 ^ gamma.length)
    (by rw [size_pv]; exact Nat.min_le_left _ _)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [vec_pv, if_pos (Finset.mem_range.1 hb), toE_oneE, one_mul, vec_toArray, lst_map_ofF]

/-- A draw's vector: gm from entry 0 on, gt from entry t0 on, 0 elsewhere. -/
theorem vec_colVec (t0 n : ℕ) (gm gt : List E) (e : ℕ) :
    vec (colVecG (opsOf .two) t0 n gm gt) e =
      if e < n then (if e < gm.length then lst gm e else if t0 ≤ e then lst gt (e - t0) else 0)
      else 0 := by
  unfold colVecG
  rw [vec_ofFn]
  by_cases h : e < n
  · rw [dif_pos h, if_pos h]
    show toE (if e < gm.toArray.size then gm.toArray.getD e Fmt.Fld.zeroE
      else if t0 ≤ e then gt.toArray.getD (e - t0) Fmt.Fld.zeroE else Fmt.Fld.zeroE) = _
    rw [List.size_toArray]
    by_cases h1 : e < gm.length
    · rw [if_pos h1, if_pos h1]
      exact vec_toArray gm e
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : t0 ≤ e
      · rw [if_pos h2, if_pos h2]
        exact vec_toArray gt (e - t0)
      · rw [if_neg h2, if_neg h2]
        exact toE_zeroE
  · rw [dif_neg h, if_neg h]

/-- The equality row's vector: at an entry below the cut the weight of that entry's vertex at the
point phi, at every other entry 0. -/
theorem vec_eqVec (cut n : ℕ) (phi : List E) (e : ℕ) :
    vec (eqVecG (opsOf .two) cut n phi) e =
      if e < n then (if e < cut then (if e < 2 ^ phi.length then eqW phi.length (lst phi) e else 0)
        else 0) else 0 := by
  unfold eqVecG
  rw [vec_ofFn]
  by_cases h : e < n
  · rw [dif_pos h, if_pos h]
    show toE (if e < cut then (pv .two Fmt.Fld.oneE phi).getD e Fmt.Fld.zeroE
      else Fmt.Fld.zeroE) = _
    by_cases h1 : e < cut
    · rw [if_pos h1, if_pos h1]
      show vec (pv .two Fmt.Fld.oneE phi) e = _
      rw [vec_pv, toE_oneE, one_mul]
    · rw [if_neg h1, if_neg h1]
      exact toE_zeroE
  · rw [dif_neg h, if_neg h]

/-- The negative of a vector. -/
theorem vec_negV (v : Array E) (e : ℕ) : vec (negVG (opsOf .two) v) e = -vec v e := by
  unfold vec ent negVG
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases v[e]? with
  | none =>
    show toE Fmt.Fld.zeroE = -toE Fmt.Fld.zeroE
    rw [toE_zeroE, neg_zero]
  | some a => exact toE_negE a

/-! ## From the entries of a folded row to the member's table -/

/-- A vector on entries, put on the member's table: index i holds the entry whose place it is. -/
theorem vec_layHi (P : Fmt.M3.Par) (w : Array E) (i : ℕ) :
    vec (layHi P w) i = if i < 2 ^ (P.aR + P.aP) then vec w (loAt P.high P.aR P.aP i) else 0 := by
  unfold layHi layHiG
  rw [vec_ofFn]
  by_cases h : i < 2 ^ (P.aR + P.aP)
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]

/-- The entry at row r, place p of the member's table. -/
theorem loAt_idx (aR aP r p : ℕ) (hr : r < 2 ^ aR) :
    loAt true aR aP (r + 2 ^ aR * p) = r * 2 ^ aP + p := by
  show (r + 2 ^ aR * p) % 2 ^ aR * 2 ^ aP + (r + 2 ^ aR * p) / 2 ^ aR = _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_mul_div_left _ _ (Nat.two_pow_pos aR),
    Nat.div_eq_of_lt hr, Nat.zero_add]

/-! ## Rows member by member, and their sum under the powers of a challenge -/

/-- The row without members and with the target 0. It is what is read beyond a list's end. -/
def noM : MRow := ⟨[], [], Fmt.Fld.zeroE⟩

/-- v at member i, the empty form at the others. -/
theorem vec_oneAt (n i : ℕ) (v : Array E) (j e : ℕ) :
    vec ((oneAt n i v).getD j #[]) e = if j < n ∧ j = i then vec v e else 0 := by
  unfold oneAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < n
  · rw [List.getElem?_range hj]
    show vec (if j == i then v else #[]) e = _
    by_cases hi : j = i
    · rw [if_pos (by simpa using hi), if_pos ⟨hj, hi⟩]
    · rw [if_neg (by simpa using hi), if_neg (fun h => hi h.2), vec_noEntries]
  · rw [List.getElem?_eq_none (by simpa using hj), if_neg (fun h => hj h.1)]
    exact vec_noEntries e

/-- For each member j: the result's form is u's form plus s times v's form. -/
theorem vec_axpyL (s : E) : ∀ (u v : List (Array E)) (j e : ℕ),
    vec ((axpyL .two u s v).getD j #[]) e = vec (u.getD j #[]) e + toE s * vec (v.getD j #[]) e
  | a :: u, b :: v, 0, e => vec_axpy a s b e
  | a :: u, b :: v, j + 1, e => by
    simp only [axpyL, List.getD_cons_succ]
    exact vec_axpyL s u v j e
  | [], v, j, e => by
    show vec ((v.map (axpy .two #[] s)).getD j #[]) e = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_nil, vec_noEntries, zero_add,
      List.getD_eq_getElem?_getD]
    cases v[j]? with
    | none =>
      show vec #[] e = toE s * vec #[] e
      rw [vec_noEntries, mul_zero]
    | some b =>
      show vec (axpy .two #[] s b) e = toE s * vec b e
      rw [vec_axpy, vec_noEntries, zero_add]
  | a :: u, [], j, e => by
    show vec (((a :: u).map fun a => axpy .two a s #[]).getD j #[]) e = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_nil, vec_noEntries, mul_zero,
      add_zero, List.getD_eq_getElem?_getD]
    cases (a :: u)[j]? with
    | none => rfl
    | some b =>
      show vec (axpy .two b s #[]) e = vec b e
      rw [vec_axpy, vec_noEntries, mul_zero, add_zero]

/-- One step of the sum of rows: the state is the sum of the rows before this one and the power of
the challenge for this one. -/
def stepM (x : E) (s : MRow × E) (R : MRow) : MRow × E :=
  (⟨axpyL .two s.1.main s.2 R.main, axpyL .two s.1.mask s.2 R.mask,
    Fmt.Fld.two.addE s.1.t (Fmt.Fld.two.mulE s.2 R.t)⟩, Fmt.Fld.two.mulE s.2 x)

/-- The sum of rows, as steps from the row without members and the power 1. -/
theorem sumM_eq (x : E) (rows : List MRow) :
    sumM .two x rows = (rows.foldl (stepM x) (noM, Fmt.Fld.oneE)).1 := rfl

/-- A sum with term number k under c x^k: the first term taken off. -/
theorem sum_shift (c x : GE) (n : ℕ) (F : ℕ → GE) :
    ∑ k ∈ Finset.range (n + 1), c * x ^ k * F k =
      c * F 0 + ∑ k ∈ Finset.range n, c * x * x ^ k * F (k + 1) := by
  rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ]
  ring

/-- Steps from any state s: the form on member j's main table. -/
theorem foldl_main (x : E) : ∀ (rows : List MRow) (s : MRow × E) (j e : ℕ),
    vec ((rows.foldl (stepM x) s).1.main.getD j #[]) e = vec (s.1.main.getD j #[]) e +
      ∑ k ∈ Finset.range rows.length,
        toE s.2 * toE x ^ k * vec ((rows.getD k noM).main.getD j #[]) e
  | [], s, j, e => by simp
  | R :: rows, s, j, e => by
    rw [List.foldl_cons, foldl_main x rows, List.length_cons, sum_shift]
    show vec ((axpyL .two s.1.main s.2 R.main).getD j #[]) e +
      ∑ k ∈ Finset.range rows.length, toE (Fmt.Fld.two.mulE s.2 x) * toE x ^ k * _ = _
    rw [vec_axpyL, toE_mulE, add_assoc]
    rfl

/-- Steps from any state s: the form on member j's mask table. -/
theorem foldl_mask (x : E) : ∀ (rows : List MRow) (s : MRow × E) (j e : ℕ),
    vec ((rows.foldl (stepM x) s).1.mask.getD j #[]) e = vec (s.1.mask.getD j #[]) e +
      ∑ k ∈ Finset.range rows.length,
        toE s.2 * toE x ^ k * vec ((rows.getD k noM).mask.getD j #[]) e
  | [], s, j, e => by simp
  | R :: rows, s, j, e => by
    rw [List.foldl_cons, foldl_mask x rows, List.length_cons, sum_shift]
    show vec ((axpyL .two s.1.mask s.2 R.mask).getD j #[]) e +
      ∑ k ∈ Finset.range rows.length, toE (Fmt.Fld.two.mulE s.2 x) * toE x ^ k * _ = _
    rw [vec_axpyL, toE_mulE, add_assoc]
    rfl

/-- Steps from any state s: the target. -/
theorem foldl_t (x : E) : ∀ (rows : List MRow) (s : MRow × E),
    toE (rows.foldl (stepM x) s).1.t = toE s.1.t +
      ∑ k ∈ Finset.range rows.length, toE s.2 * toE x ^ k * toE (rows.getD k noM).t
  | [], s => by simp
  | R :: rows, s => by
    rw [List.foldl_cons, foldl_t x rows, List.length_cons, sum_shift]
    show toE (Fmt.Fld.two.addE s.1.t (Fmt.Fld.two.mulE s.2 R.t)) +
      ∑ k ∈ Finset.range rows.length, toE (Fmt.Fld.two.mulE s.2 x) * toE x ^ k * _ = _
    rw [toE_addE, toE_mulE, toE_mulE, add_assoc]
    rfl

/-- The sum of rows: the form on member j's main table. -/
theorem vec_sumM_main (x : E) (rows : List MRow) (j e : ℕ) :
    vec ((sumM .two x rows).main.getD j #[]) e =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * vec ((rows.getD k noM).main.getD j #[]) e := by
  rw [sumM_eq, foldl_main]
  show vec #[] e + _ = _
  rw [vec_noEntries, zero_add, toE_oneE]
  simp only [one_mul]

/-- The sum of rows: the form on member j's mask table. -/
theorem vec_sumM_mask (x : E) (rows : List MRow) (j e : ℕ) :
    vec ((sumM .two x rows).mask.getD j #[]) e =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * vec ((rows.getD k noM).mask.getD j #[]) e := by
  rw [sumM_eq, foldl_mask]
  show vec #[] e + _ = _
  rw [vec_noEntries, zero_add, toE_oneE]
  simp only [one_mul]

/-- The sum of rows: the target. -/
theorem toE_sumM_t (x : E) (rows : List MRow) :
    toE (sumM .two x rows).t =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * toE (rows.getD k noM).t := by
  rw [sumM_eq, foldl_t]
  show toE Fmt.Fld.zeroE + _ = _
  rw [toE_zeroE, zero_add, toE_oneE]
  simp only [one_mul]

/-! ## From the members' tables to the group's table -/

/-- Entry i of the table that `layAll` makes: an entry of the form of the member whose block holds
row i % 2 ^ w, or 0. -/
theorem vec_layAll (w n : ℕ) (L : List (Option ℕ × ℕ)) (parts : List (Array E)) (i : ℕ) :
    vec (layAll w n L parts) i =
      if i < n then
        match pickRow L (i % 2 ^ w) 0 with
        | some (j, st, b) => vec (parts.getD j #[]) ((i % 2 ^ w - st) + 2 ^ b * (i / 2 ^ w))
        | none => 0
      else 0 := by
  unfold layAll
  rw [vec_ofFn]
  by_cases h : i < n
  · rw [dif_pos h, if_pos h]
    show toE (match pickRow L (i % 2 ^ w) 0 with
      | some (j, st, b) => ent (parts.getD j #[]) ((i % 2 ^ w - st) + 2 ^ b * (i / 2 ^ w))
      | none => Fmt.Fld.zeroE) = _
    cases pickRow L (i % 2 ^ w) 0 with
    | none => exact toE_zeroE
    | some t => rfl
  · rw [dif_neg h, if_neg h]

/-- Two blocks of 2 ^ a rows take a + 1 binary digits. -/
theorem clog_double (a : ℕ) : clog (2 ^ a + 2 ^ a) = a + 1 := by
  have h1 : 0 < 2 ^ a := Nat.two_pow_pos a
  unfold clog
  rw [if_neg (by omega)]
  congr 1
  refine (Nat.log2_eq_iff (by omega)).2 ⟨by omega, ?_⟩
  rw [Nat.pow_succ]
  omega

/-- Two blocks of one size are placed one after the other. -/
theorem layBlocks_two (a : ℕ) :
    layBlocks [some a, some a] = ([some 0, some (2 ^ a)], 2 ^ a + 2 ^ a) := by
  have hord : ((List.range (a + 1)).reverse.flatMap fun e =>
      ([(0, a), (1, a)] : List (ℕ × ℕ)).filter fun x => x.2 == e) = [(0, a), (1, a)] := by
    have h0 : ((List.range a).reverse.flatMap fun e =>
        ([(0, a), (1, a)] : List (ℕ × ℕ)).filter fun x => x.2 == e) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro e he
      have hlt : e < a := by simpa using he
      have hne : (a == e) = false := by simpa using (Nat.ne_of_gt hlt)
      simp [hne]
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons, h0, List.append_nil]
    simp
  have htop : ([(0, a), (1, a)] : List (ℕ × ℕ)).foldl (fun m x => max m x.2) 0 = a := by simp
  -- The definition, with the list of (member, size) written out.
  show ((List.range 2).map fun i =>
      ((((List.range (([(0, a), (1, a)] : List (ℕ × ℕ)).foldl (fun m x => max m x.2) 0
          + 1)).reverse.flatMap
        fun e => ([(0, a), (1, a)] : List (ℕ × ℕ)).filter fun x => x.2 == e).foldl
        (fun (s : List (ℕ × ℕ) × ℕ) x => ((x.1, s.2) :: s.1, s.2 + 2 ^ x.2)) ([], 0)).1.find?
        fun y => y.1 == i).map (·.2),
    (((List.range (([(0, a), (1, a)] : List (ℕ × ℕ)).foldl (fun m x => max m x.2) 0
          + 1)).reverse.flatMap
        fun e => ([(0, a), (1, a)] : List (ℕ × ℕ)).filter fun x => x.2 == e).foldl
        (fun (s : List (ℕ × ℕ) × ℕ) x => ((x.1, s.2) :: s.1, s.2 + 2 ^ x.2)) ([], 0)).2) = _
  rw [htop, hord]
  simp [List.range_succ]

/-- The layout of the link's group: two blocks of 2 ^ aR rows, at the rows 0 and 2 ^ aR. -/
theorem starts_mems (P : Fmt.M3.Par) (hR : 0 < P.R) :
    starts P.mems = ([some 0, some (2 ^ P.aR)], 2 ^ P.aR + 2 ^ P.aR) := by
  have h0 : (P.R == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 hR
  have h1 : (P.mems.map fun m => if m.kept || m.rows == 0 then none else some (clog m.rows))
      = [some P.aR, some P.aR] := by
    show [if (false || P.R == 0) = true then none else some (clog P.R),
      if (false || P.R == 0) = true then none else some (clog P.R)] = _
    rw [h0]
    rfl
  unfold starts
  rw [h1]
  exact layBlocks_two P.aR

/-- The rows of the group's table have aR + 1 binary digits. -/
theorem kOf_mems (P : Fmt.M3.Par) (hR : 0 < P.R) : kOf P.mems = P.aR + 1 := by
  unfold kOf
  rw [starts_mems P hR, clog_double]
  show max (P.aR + 1) (max 0 1) = P.aR + 1
  omega

/-- The group's mask rows take 0 binary digits: it has none. -/
theorem hOf_mems (P : Fmt.M3.Par) : hOf P.mems = 0 := rfl

/-- The row on the link's group, main part. Row r of the group's table is row r of the first
member's table if r < 2 ^ aR, else row r - 2 ^ aR of the second's. -/
theorem vec_toK_c (P : Fmt.M3.Par) (hR : 0 < P.R) (l lz : ℕ) (R : MRow) (i : ℕ) :
    vec (toK P.mems l lz R).c i =
      if i < 2 ^ (P.aR + 1) * l then
        (if i % 2 ^ (P.aR + 1) < 2 ^ P.aR
          then vec (R.main.getD 0 #[]) (i % 2 ^ (P.aR + 1) + 2 ^ P.aR * (i / 2 ^ (P.aR + 1)))
          else vec (R.main.getD 1 #[])
            (i % 2 ^ (P.aR + 1) - 2 ^ P.aR + 2 ^ P.aR * (i / 2 ^ (P.aR + 1))))
      else 0 := by
  show vec (layAll (kOf P.mems) (2 ^ kOf P.mems * l)
    ((starts P.mems).1.zip (P.mems.map fun m => clog m.rows)) R.main) i = _
  rw [kOf_mems P hR, starts_mems P hR, vec_layAll]
  by_cases h : i < 2 ^ (P.aR + 1) * l
  · rw [if_pos h, if_pos h]
    have hr : i % 2 ^ (P.aR + 1) < 2 ^ P.aR + 2 ^ P.aR := by
      have := Nat.mod_lt i (Nat.two_pow_pos (P.aR + 1))
      rw [Nat.pow_succ] at this
      omega
    show (match (if (0 ≤ i % 2 ^ (P.aR + 1) && i % 2 ^ (P.aR + 1) < 0 + 2 ^ P.aR) = true
        then some (0, 0, P.aR)
        else if (2 ^ P.aR ≤ i % 2 ^ (P.aR + 1) && i % 2 ^ (P.aR + 1) < 2 ^ P.aR + 2 ^ P.aR) = true
          then some (0 + 1, 2 ^ P.aR, P.aR) else none : Option (ℕ × ℕ × ℕ)) with
      | some (j, st, b) =>
        vec (R.main.getD j #[]) ((i % 2 ^ (P.aR + 1) - st) + 2 ^ b * (i / 2 ^ (P.aR + 1)))
      | none => 0) = _
    by_cases h1 : i % 2 ^ (P.aR + 1) < 2 ^ P.aR
    · rw [if_pos (by simpa using h1), if_pos h1]
      rfl
    · rw [if_neg (by simpa using h1), if_pos (by simp; omega), if_neg h1]
  · rw [if_neg h, if_neg h]

/-- The row on the link's group has no kept part. -/
theorem toK_kp (P : Fmt.M3.Par) (l lz : ℕ) (R : MRow) : (toK P.mems l lz R).kp = #[] := rfl

/-- The row on the link's group has no mask part but zeros. -/
theorem vec_toK_d (P : Fmt.M3.Par) (l lz : ℕ) (R : MRow) (i : ℕ) :
    vec (toK P.mems l lz R).d i = 0 := by
  show vec (layAll (hOf P.mems) (2 ^ hOf P.mems * lz) [(none, 0), (none, 0)] R.mask) i = 0
  rw [vec_layAll]
  split <;> rfl

/-- Putting a row on the group's table keeps its target. -/
theorem toK_t (P : Fmt.M3.Par) (l lz : ℕ) (R : MRow) : (toK P.mems l lz R).t = R.t := rfl

/-! ## The rows of the link -/

/-- A draw's vector at position x. The message's entries have the powers of x's point from the
exponent r on; the tail's entries, from t0 on, have the powers from the exponent 0 on. -/
theorem vec_colVec_gen (P : Fmt.M3.Par) (x e : ℕ) :
    vec (colVecG (opsOf P.fld) P.t0 P.nTab ((genM P.T x).map Fmt.Fld.ofF)
        ((genT P.T x).map Fmt.Fld.ofF)) e =
      if e < P.nTab then
        (if e < P.T.l then algebraMap GF GE (toF (point P.T.a x) ^ (P.T.r + e))
          else if P.t0 ≤ e then
            (if e - P.t0 < P.T.r then algebraMap GF GE (toF (point P.T.a x) ^ (e - P.t0)) else 0)
          else 0)
      else 0 := by
  show vec (colVecG (opsOf .two) P.t0 P.nTab ((genM P.T x).map Fmt.Fld.ofF)
    ((genT P.T x).map Fmt.Fld.ofF)) e = _
  rw [vec_colVec, List.length_map, length_genM, lst_map_ofF, lst_map_ofF, toF_genM, toF_genT]
  by_cases h : e < P.nTab
  · rw [if_pos h, if_pos h]
    by_cases h1 : e < P.T.l
    · rw [if_pos h1, if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : P.t0 ≤ e
      · rw [if_pos h2, if_pos h2]
        by_cases h3 : e - P.t0 < P.T.r
        · rw [if_pos h3, if_pos h3]
        · rw [if_neg h3, if_neg h3, map_zero]
      · rw [if_neg h2, if_neg h2]
  · rw [if_neg h, if_neg h]

/-- The form of a draw's row is 0 on the member of the other table. On the member of the table that
the draw belongs to, it is the draw's vector, put on that member's table. -/
theorem vec_colRow_main (P : Fmt.M3.Par) (gamma : List E) (which x : ℕ) (col : List UInt64)
    (j i : ℕ) :
    vec ((colRow P gamma which x col).main.getD j #[]) i =
      if j < 2 ∧ j = which then
        vec (layHi P (colVecG (opsOf P.fld) P.t0 P.nTab ((genM P.T x).map Fmt.Fld.ofF)
          ((genT P.T x).map Fmt.Fld.ofF))) i
      else 0 :=
  vec_oneAt 2 which _ j i

/-- A draw's row has no part on a mask table. -/
theorem colRow_mask (P : Fmt.M3.Par) (gamma : List E) (which x : ℕ) (col : List UInt64) :
    (colRow P gamma which x col).mask = [] := rfl

/-- A draw's target is the fold of the opened column. -/
theorem colRow_t (P : Fmt.M3.Par) (gamma : List E) (which x : ℕ) (col : List UInt64) :
    (colRow P gamma which x col).t = foldCol P.fld gamma col := rfl

/-- The equality row on the first member. -/
theorem eqRow_main_zero (P : Fmt.M3.Par) (phi : List E) :
    (eqRow P phi).main.getD 0 #[] = layHi P (eqVecG (opsOf P.fld) P.cut P.nTab phi) := rfl

/-- The equality row on the second member: the negative of its form on the first. -/
theorem vec_eqRow_main_one (P : Fmt.M3.Par) (hf : P.fld = .two) (phi : List E) (i : ℕ) :
    vec ((eqRow P phi).main.getD 1 #[]) i =
      -vec (layHi P (eqVecG (opsOf P.fld) P.cut P.nTab phi)) i := by
  show vec (layHi P (negVG (opsOf P.fld) (eqVecG (opsOf P.fld) P.cut P.nTab phi))) i = _
  rw [vec_layHi, vec_layHi, hf]
  by_cases h : i < 2 ^ (P.aR + P.aP)
  · rw [if_pos h, if_pos h, vec_negV]
  · rw [if_neg h, if_neg h, neg_zero]

/-- The equality row has a form on two members. -/
theorem eqRow_main_length (P : Fmt.M3.Par) (phi : List E) : (eqRow P phi).main.length = 2 := rfl

/-- The equality row has no part on a mask table. -/
theorem eqRow_mask (P : Fmt.M3.Par) (phi : List E) : (eqRow P phi).mask = [] := rfl

/-- The equality row's target is 0. -/
theorem toE_eqRow_t (P : Fmt.M3.Par) (phi : List E) : toE (eqRow P phi).t = 0 := toE_zeroE

/-- The form of member m's sample row is 0 on the other member. -/
theorem vec_smpRow_main (P : Fmt.M3.Par) (z : List E) (beta : E) (m : ℕ) (y : E) (j i : ℕ) :
    vec ((smpRow P z beta m y).main.getD j #[]) i =
      if j < 2 ∧ j = m then vec (sampleOf P.fld P.C.l P.Z.l P.mem z beta y).1 i else 0 :=
  vec_oneAt 2 m _ j i

/-- A sample row of the link has no part on a mask table. -/
theorem smpRow_mask (P : Fmt.M3.Par) (z : List E) (beta : E) (m : ℕ) (y : E) :
    (smpRow P z beta m y).mask = [] := rfl

/-- A sample row's target is the answer. -/
theorem smpRow_t (P : Fmt.M3.Par) (z : List E) (beta : E) (m : ℕ) (y : E) :
    (smpRow P z beta m y).t = y := rfl

/-- If the draws' rows are there, each drawn column was opened and has 2 ^ v words, and row number k
is the row of draw number k. -/
theorem colRows_some (P : Fmt.M3.Par) (V : Fmt.M3.View) (gamma : List E) :
    ∀ (ds : List (ℕ × ℕ)) (rs : List MRow), colRows P V gamma ds = some rs →
      rs.length = ds.length ∧ ∀ k, k < ds.length →
        ∃ col, storedAt V (ds.getD k (0, 0)).1 (ds.getD k (0, 0)).2 = some col ∧
          col.length = 2 ^ P.v ∧
          rs.getD k noM = colRow P gamma (ds.getD k (0, 0)).1 (ds.getD k (0, 0)).2 col
  | [], rs, h => by
    obtain rfl : [] = rs := Option.some.inj h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | (w, x) :: ds, rs, h => by
    rw [colRows] at h
    cases hs : storedAt V w x with
    | none => simp [hs] at h
    | some col =>
      cases hr : colRows P V gamma ds with
      | none => simp [hs, hr] at h
      | some rs' =>
        simp only [hs, hr] at h
        by_cases hl : (col.length == 2 ^ P.v) = true
        · rw [if_pos hl] at h
          obtain rfl := Option.some.inj h
          obtain ⟨h1, h2⟩ := colRows_some P V gamma ds rs' hr
          refine ⟨by rw [List.length_cons, List.length_cons, h1], fun k hk => ?_⟩
          cases k with
          | zero => exact ⟨col, hs, by simpa using hl, rfl⟩
          | succ k => exact h2 k (by simpa using hk)
        · rw [if_neg hl] at h
          cases h

/-! ## Against the library's forms, at the sizes of an entry file -/

/-- The tail begins after the message's end, or at it. -/
theorem le_t0 (P : Fmt.M3.Par) : P.T.l ≤ P.t0 := by
  show P.T.l ≤ (P.T.l + 2 ^ clog P.T.r - 1) / 2 ^ clog P.T.r * 2 ^ clog P.T.r
  have hd : 0 < 2 ^ clog P.T.r := Nat.two_pow_pos _
  generalize 2 ^ clog P.T.r = d at hd ⊢
  have h1 := Nat.div_add_mod (P.T.l + d - 1) d
  have h2 := Nat.mod_lt (P.T.l + d - 1) hd
  rw [Nat.mul_comm] at h1
  omega

/-- A coefficient is at row r, place p exactly if its entry is r * l + p. -/
theorem putAt_eq_iff (S : Sz) (k : S.Co) (r : Fin S.P.R) (p : Fin S.P.C.l) :
    S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val := by
  unfold Sz.putAt
  constructor
  · intro h
    have h' := Sum.inl.inj h
    have h1 : S.entryOf k / S.P.C.l = r.val := congrArg (fun z => z.1.val) h'
    have h2 : S.entryOf k % S.P.C.l = p.val := congrArg (fun z => z.2.val) h'
    have h3 := Nat.div_add_mod (S.entryOf k) S.P.C.l
    rw [h1, h2, Nat.mul_comm] at h3
    exact h3.symm
  · intro h
    refine congrArg Sum.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · show S.entryOf k / S.P.C.l = r.val
      rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ S.hl, Nat.div_eq_of_lt p.isLt, Nat.zero_add]
    · show S.entryOf k % S.P.C.l = p.val
      rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]

/-- Row r, place p lies within the member's table: r is below 2 ^ aR, the index r + 2 ^ aR * p is
below 2 ^ (aR + aP), and the entry r * l + p is below the number of the table's entries. -/
theorem idx_facts (S : Sz) (hl2 : S.P.C.l = 2 ^ S.P.aP) (r : Fin S.P.R) (p : Fin S.P.C.l) :
    r.val < 2 ^ S.P.aR ∧ r.val + 2 ^ S.P.aR * p.val < 2 ^ (S.P.aR + S.P.aP) ∧
      r.val * S.P.C.l + p.val < S.P.nTab := by
  have hr : r.val < 2 ^ S.P.aR := lt_of_lt_of_le r.isLt (le_two_pow_clog S.P.R)
  have hp : p.val < 2 ^ S.P.aP := hl2 ▸ p.isLt
  refine ⟨hr, ?_, ?_⟩
  · calc r.val + 2 ^ S.P.aR * p.val < 2 ^ S.P.aR + 2 ^ S.P.aR * p.val := Nat.add_lt_add_right hr _
      _ = 2 ^ S.P.aR * (p.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm
  · show r.val * S.P.C.l + p.val < 2 ^ (S.P.aR + S.P.aP)
    calc r.val * S.P.C.l + p.val = r.val * 2 ^ S.P.aP + p.val :=
          congrArg (fun n => r.val * n + p.val) hl2
      _ < r.val * 2 ^ S.P.aP + 2 ^ S.P.aP := Nat.add_lt_add_left hp _
      _ = (r.val + 1) * 2 ^ S.P.aP := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_right _ hr
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm

/-- A draw's row. The library's form of a column at the location x, on the entries of a member's
message, is the written row's form on the member's table. -/
theorem colF_eq (S : Sz) (hh : S.P.high = true) (hl2 : S.P.C.l = 2 ^ S.P.aP) (i : Bool) (x : S.Pos)
    (j : S.MJ) :
    S.lk.colF i S.putAt x j =
      vec (layHi S.P (colVecG (opsOf S.P.fld) S.P.t0 S.P.nTab ((genM S.P.T x.val).map Fmt.Fld.ofF)
        ((genT S.P.T x.val).map Fmt.Fld.ofF))) (S.idxJ j) := by
  rcases j with ⟨r, p⟩ | y
  swap
  · exact y.1.elim
  obtain ⟨hr, hlt, hn⟩ := idx_facts S hl2 r p
  have ht0 := le_t0 S.P
  have key : ∀ k : S.Co, S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val :=
    fun k => putAt_eq_iff S k r p
  have hent : ∀ k : S.Co,
      S.entryOf k = if k.val < S.P.T.r then S.P.t0 + k.val else k.val - S.P.T.r := fun _ => rfl
  show _ = vec _ (r.val + 2 ^ S.P.aR * p.val)
  rw [vec_layHi, if_pos hlt, hh, loAt_idx _ _ _ _ hr, ← hl2, vec_colVec_gen, if_pos hn]
  unfold Cb.LdLkP.colF Cb.Slf.push
  generalize r.val * S.P.C.l + p.val = e at key ⊢
  by_cases h1 : e < S.P.T.l
  · rw [if_pos h1, Finset.sum_eq_single (Fin.natAdd S.P.T.r ⟨e, h1⟩)]
    · rw [if_pos ((key _).2 (by
        rw [hent]
        show (if S.P.T.r + e < S.P.T.r then _ else S.P.T.r + e - S.P.T.r) = e
        rw [if_neg (by omega)]
        omega))]
      rfl
    · intro k _ hk
      refine if_neg fun h => hk (Fin.ext ?_)
      have h2 := (key k).1 h
      rw [hent] at h2
      show k.val = S.P.T.r + e
      split at h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h1]
    by_cases h2 : S.P.t0 ≤ e ∧ e - S.P.t0 < S.P.T.r
    · rw [if_pos h2.1, if_pos h2.2, Finset.sum_eq_single (Fin.castAdd S.P.T.l ⟨e - S.P.t0, h2.2⟩)]
      · rw [if_pos ((key _).2 (by
          rw [hent]
          show (if e - S.P.t0 < S.P.T.r then S.P.t0 + (e - S.P.t0) else _) = e
          rw [if_pos h2.2]
          omega))]
        rfl
      · intro k _ hk
        refine if_neg fun h => hk (Fin.ext ?_)
        have h3 := (key k).1 h
        have h4 := k.isLt
        rw [hent] at h3
        show k.val = e - S.P.t0
        split at h3 <;> omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hz : (if S.P.t0 ≤ e then (if e - S.P.t0 < S.P.T.r
          then algebraMap GF GE (toF (point S.P.T.a x.val) ^ (e - S.P.t0)) else 0) else 0) = 0 := by
        by_cases h3 : S.P.t0 ≤ e
        · rw [if_pos h3, if_neg fun h4 => h2 ⟨h3, h4⟩]
        · rw [if_neg h3]
      rw [hz]
      refine Finset.sum_eq_zero fun k _ => if_neg fun h => ?_
      have h3 := (key k).1 h
      have h4 := k.isLt
      rw [hent] at h3
      split at h3 <;> omega

/-- The equality row. The library's form of the layout at the point phi, on the entries of a
member's message, is the written row's form on the member's table. -/
theorem layF_eq (S : Sz) (hh : S.P.high = true) (hl2 : S.P.C.l = 2 ^ S.P.aP) (i : Bool)
    (phi : List E) (hphi : phi.length = S.P.aPhi) (j : S.MJ) :
    S.lk.layF i S.putAt (fun t => lst phi t.val) j =
      vec (layHi S.P (eqVecG (opsOf .two) S.P.cut S.P.nTab phi)) (S.idxJ j) := by
  rcases j with ⟨r, p⟩ | y
  swap
  · exact y.1.elim
  obtain ⟨hr, hlt, hn⟩ := idx_facts S hl2 r p
  have key : ∀ k : S.Co, S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val :=
    fun k => putAt_eq_iff S k r p
  have hent : ∀ a : S.Lay, S.entryOf (S.lk.D.X.pl (S.lk.D.lay a)) = a.val := fun a => by
    show (if S.P.T.r + a.val < S.P.T.r then _ else S.P.T.r + a.val - S.P.T.r) = a.val
    rw [if_neg (by omega)]
    omega
  have hcut : S.P.cut ≤ 2 ^ S.P.aPhi :=
    le_trans (Nat.sub_le _ _) (le_two_pow_clog S.P.T.l)
  show _ = vec _ (r.val + 2 ^ S.P.aR * p.val)
  rw [vec_layHi, if_pos hlt, hh, loAt_idx _ _ _ _ hr, ← hl2, vec_eqVec, if_pos hn, hphi]
  unfold Cb.LdLkP.layF Cb.Slf.push
  generalize r.val * S.P.C.l + p.val = e at key ⊢
  by_cases h1 : e < S.P.cut
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hcut), Finset.sum_eq_single (⟨e, h1⟩ : S.Lay)]
    · rw [if_pos ((key _).2 (hent _))]
      rfl
    · intro a _ ha
      refine if_neg fun h => ha (Fin.ext ?_)
      have h2 := (key _).1 h
      rw [hent] at h2
      exact h2
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h1]
    refine Finset.sum_eq_zero fun a _ => if_neg fun h => h1 ?_
    have h2 := (key _).1 h
    rw [hent] at h2
    exact h2 ▸ a.isLt

/-- A draw's target. The library's fold of a symbol read in the first table is the written fold
of its column. -/
theorem foldSym₀_eq (S : Sz) (gamma : List E) (hg : gamma.length = S.P.v) (s : Run.PQ.SgX) :
    S.lk.foldSym₀ (fun t => lst gamma t.val) (some (.inl (.inl s))) =
      toE (foldCol .two gamma s.2) := by
  rw [toE_foldCol, hg, sum_range_cube]
  show (∑ r, Alg.eqk (fun t : Fin S.P.v => lst gamma t.val) r * S.lk.up s r) = _
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqW_rowNo]

/-- The same for a symbol read in the copy. -/
theorem foldSym₁_eq (S : Sz) (gamma : List E) (hg : gamma.length = S.P.v) (s : Run.PQ.SgX) :
    S.lk.foldSym₁ (fun t => lst gamma t.val) (some (.inl (.inr s))) =
      toE (foldCol .two gamma s.2) := by
  rw [toE_foldCol, hg, sum_range_cube]
  show (∑ r, Alg.eqk (fun t : Fin S.P.v => lst gamma t.val) r * S.lk.up s r) = _
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqW_rowNo]

end OnBytes.Slice

#print axioms OnBytes.Slice.toE_foldCol
#print axioms OnBytes.Slice.vec_colVec
#print axioms OnBytes.Slice.vec_colVec_gen
#print axioms OnBytes.Slice.vec_eqVec
#print axioms OnBytes.Slice.vec_negV
#print axioms OnBytes.Slice.vec_layHi
#print axioms OnBytes.Slice.loAt_idx
#print axioms OnBytes.Slice.vec_oneAt
#print axioms OnBytes.Slice.vec_axpyL
#print axioms OnBytes.Slice.vec_sumM_main
#print axioms OnBytes.Slice.vec_sumM_mask
#print axioms OnBytes.Slice.toE_sumM_t
#print axioms OnBytes.Slice.vec_layAll
#print axioms OnBytes.Slice.starts_mems
#print axioms OnBytes.Slice.kOf_mems
#print axioms OnBytes.Slice.vec_toK_c
#print axioms OnBytes.Slice.vec_toK_d
#print axioms OnBytes.Slice.vec_colRow_main
#print axioms OnBytes.Slice.vec_eqRow_main_one
#print axioms OnBytes.Slice.vec_smpRow_main
#print axioms OnBytes.Slice.colRows_some
#print axioms OnBytes.Slice.colF_eq
#print axioms OnBytes.Slice.layF_eq
#print axioms OnBytes.Slice.foldSym₀_eq
#print axioms OnBytes.Slice.foldSym₁_eq
