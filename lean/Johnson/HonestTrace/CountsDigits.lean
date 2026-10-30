-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsDigits.lean

The lookup on the digits of a sub-proof's smallness test: its two key vectors and the array BZ of
the bits of its counts, as terms of the array ZZ of digits; and the relation Cb.Lkp.MidP at them.

A smallness test (OnBytes/Model/Tail.lean; docs/format/11-1-machinery.md, "The lookup on the
digits") writes each combination of cells, plus 2^17, as a low and a high digit in an array ZZ, and
looks the digits up in two range tables, of 2^10 and of 2^8 rows. The bits of the counts stand in an
array BZ of 32 rows, at an address rule of its own. ZZ depends on a sampled matrix. Here it is an
argument: zz, a function of row and column.

The places are the library's own. DgP.digInCall tl q kn (OnBytes/Tie/Pv/Lookup/Digits/PortKeys.lean)
says which cell of ZZ place kn of call q reads, or that it reads none. DgP.bcP tl t c j is the
address in BZ of bit j of the count of row t of call c. The public numbers are tl.f9. The premise on
tl is Fo.ZPlan.FromPieces tl (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean): tl has, in the fields
that are read here, what HTailF2.piecesF has returned. Where Verify.publicOf returns X, that file
shows FromPieces at hp.tl for every member hp of X.G, at a.seam.tl for every member a of X.A, and at
X.H.tl (public_G_from, public_A_from, public_H_from).

Main definitions:
* "padZ tl q kn": place kn of call q is a padding place. "kvZ tl zz q": the key vector of call q.
* "DigitsIn tl zz": every digit is in its range. It is a premise of what follows.
* "hitsZ", "bzOf tl zz row col": BZ as a function of row and column, with values 0 and 1.
* "virtZ tl bz r col": an array of BZ's form, read as the matrix with one row a plane, which is how
  the library reaches BZ by FoNums.cellRC at lm = 5 (DgP.digL5,
  OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean).
* "LaidBZ tl zz bz": the array bz holds bzOf tl zz.

Main theorems:
* "pubFits_Z": under FromPieces tl, tl.f9.pub counts the padding places tree by tree (PubFits tl.f9
  (padZ tl)).
* "nums_Z", "tabOf_Z", "tailOK_Z": under FromPieces tl: FoNums.ok; two calls; 2^10 and 2^8 rows;
  padding row 0; row t below 2^64 of either call has the value t; DgP.TailOK.
* "kvZ_eq_Kp", "kvZ_key": kvZ is the library's DgP.Kp; what it holds at the place of a digit.
* "kvZ_padRow", "inTable_Z": what law_bits (Johnson/HonestTrace/CountsLaw.lean) asks of the keys.
* "bzOf_at", "virtZ_bzOf", "bz_plane", "virtZ_plane": from BZ's addresses to plane at lm = 5 and
  back.
* "lawZ": under FromPieces tl, DigitsIn tl zz and LaidBZ tl zz bz, Cb.Lkp.MidP for all θ and al.

How pubFits_Z is proved (namespace Dig). "walk_Z" follows the three loops of piecesF and says what
they add to one tree's count: an overlap of a run of places with the tree, for each run
(Att.pubRun_getD, Johnson/HonestTrace/CountsAttention.lean). "due_sum" turns the overlaps into a sum
over the tree's places of the number of runs that hold the place. "point_lay" shows that this number
is 1 at a padding place below 2^n and 0 elsewhere: placeZ lays one piece or two from place 0 on, one
behind the other ("lay_placeZ"), so the runs behind the columns, and the run behind the last piece,
are apart and leave no padding place out.

Limits. DigitsIn is assumed: that the digits of a run are in range is not shown here. zz and bz are
arguments. hitsOf counts a key at the first row below 2^(k_c) that holds it, so, where the numbers
below 2^10 are distinct in K, bzOf counts a high digit in the first of the four rows that the format
allows, and the other three have the count 0. The proof uses that piecesF returns only with one
block of ZZ's rows or two (Fo.PiecesF.piecesF_tail_cnt_walk,
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailCnt.lean). pubFits_Z, nums_Z, tabOf_Z, tailOK_Z, kvZ_padRow,
inTable_Z, virtZ_plane and lawZ say nothing of a tl that does not meet FromPieces.

Not claimed: that a prover's arrays ZZ and BZ are zz and bzOf; that a verifier accepts; anything on
what the arrays show of the cells.

-/
import Johnson.HonestTrace.CountsLaw
import Johnson.HonestTrace.CountsRect
import Johnson.HonestTrace.CountsAttention
import OnBytes.Tie.Pv.Lookup.Digits.PortKeys
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTail

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open OnBytes.DgP (digInCall Kp bcP portQ keyNo TailOK piecesL cut)
open Fo.ZPlan (FromPieces)

/-! ## 1 · The padding places -/

/-- Place kn of call q of the lookup on the digits is a padding place: no cell of ZZ is read
there. -/
def padZ (tl : HTailF2) (q kn : ℕ) : Bool := (digInCall tl q kn).isNone

namespace Dig

open Att (ov)
open Fo.PiecesF

/-! ## 2 · Runs of places, place by place -/

/-- 1 if X is one of the count places from first on; 0 if not. -/
def ind (first count X : ℕ) : ℕ := if first ≤ X ∧ X < first + count then 1 else 0

/-- The overlap of a run of places with block b of D places is the number of the block's places
that lie in the run. -/
theorem ov_sum (D first count b : ℕ) :
    ov D first count b = ∑ x ∈ range D, ind first count (x + D * b) := by
  unfold ind
  rw [← Finset.card_filter]
  have e : ((range D).filter fun x => first ≤ x + D * b ∧ x + D * b < first + count) =
      Ico (first - D * b) (min D (first + count - D * b)) := by
    ext x
    simp only [mem_filter, mem_range, mem_Ico, lt_min_iff]
    omega
  rw [e, Nat.card_Ico]
  unfold ov
  have e1 : (b + 1) * D = D * b + D := by ring
  have e2 : b * D = D * b := Nat.mul_comm _ _
  rw [e1, e2]
  omega

/-- A sum over a list of sums over a finite set, in the other order. -/
theorem sum_list_swap {α : Type} (s : Finset ℕ) (l : List α) (f : α → ℕ → ℕ) :
    (l.map fun a => ∑ x ∈ s, f a x).sum = ∑ x ∈ s, (l.map fun a => f a x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- For Cp ≤ CP and 0 < CP: X is one of the places behind the first Cp places of row R of rows of
CP places that begin at off, if and only if off ≤ X, (X - off) / CP = R and Cp ≤ (X - off) % CP. -/
theorem ind_row {off CP Cp : ℕ} (hC : Cp ≤ CP) (h0 : 0 < CP) (R X : ℕ) :
    ind (off + R * CP + Cp) (CP - Cp) X =
      if off ≤ X ∧ (X - off) / CP = R ∧ Cp ≤ (X - off) % CP then 1 else 0 := by
  unfold ind
  have hdm := Nat.div_add_mod (X - off) CP
  have hlt := Nat.mod_lt (X - off) h0
  have e : (R + 1) * CP = R * CP + CP := Nat.succ_mul _ _
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · have hd : (X - off) / CP = R := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, Nat.mul_comm] at hdm
    exact ⟨by omega, hd, by omega⟩
  · obtain ⟨h1, h2, h3⟩ := h
    rw [h2, Nat.mul_comm] at hdm
    omega

/-- How many of the runs behind the columns in the rows of the piece p hold the place X. -/
def rowsAt (p : Piece) (X : ℕ) : ℕ :=
  ((List.range p.Rp).map fun rr => ind (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp) X).sum

/-- For Cp ≤ CP and 0 < CP that number is 1 if off ≤ X, (X - off) / CP < Rp and
Cp ≤ (X - off) % CP, and 0 if not. -/
theorem rowsAt_eq (p : Piece) (hC : p.Cp ≤ p.CP) (h0 : 0 < p.CP) (X : ℕ) :
    rowsAt p X =
      if p.off ≤ X ∧ (X - p.off) / p.CP < p.Rp ∧ p.Cp ≤ (X - p.off) % p.CP then 1 else 0 := by
  unfold rowsAt
  generalize p.Rp = R
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton, ind_row hC h0]
    split_ifs <;> omega

/-- What is used of a piece: at most CP columns; its range is its rows times CP; it ends at or below
2^n. -/
structure Fair (n : ℕ) (p : Piece) : Prop where
  le : p.Cp ≤ p.CP
  sq : p.CP * p.Rp = 2 ^ p.b
  top : p.off + 2 ^ p.b ≤ 2 ^ n

/-- A piece that meets Fair has 0 < CP. -/
theorem Fair.pos {n : ℕ} {p : Piece} (F : Fair n p) : 0 < p.CP :=
  Nat.pos_of_ne_zero fun h => by
    have h1 := F.sq
    rw [h, Nat.zero_mul] at h1
    exact (Nat.two_pow_pos p.b).ne h1

/-- For a piece that meets Fair: (X - off) / CP < Rp if and only if X - off < 2^b. -/
theorem Fair.div {n : ℕ} {p : Piece} (F : Fair n p) (X : ℕ) :
    (X - p.off) / p.CP < p.Rp ↔ X - p.off < 2 ^ p.b := by
  rw [Nat.div_lt_iff_lt_mul F.pos, Nat.mul_comm, F.sq]

/-- For a piece that meets Fair: the number is 1 if X lies in the piece's range and
Cp ≤ (X - off) % CP, and 0 if not. -/
theorem rowsAt_in {n : ℕ} {p : Piece} (F : Fair n p) (X : ℕ) :
    rowsAt p X =
      if (p.off ≤ X ∧ X < p.off + 2 ^ p.b) ∧ p.Cp ≤ (X - p.off) % p.CP then 1 else 0 := by
  rw [rowsAt_eq p F.le F.pos]
  have hd := F.div X
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · have h1 := hd.1 h.2.1
    exact ⟨⟨h.1, by omega⟩, h.2.2⟩
  · exact ⟨h.1.1, hd.2 (by omega), h.2⟩

/-- For a piece that meets Fair and a place X in its range: DgP.cut finds no cell at X if and only
if Cp ≤ (X - off) % CP. -/
theorem cut_none {n : ℕ} {p : Piece} (F : Fair n p) (q : ℕ) {X : ℕ}
    (hin : p.off ≤ X ∧ X < p.off + 2 ^ p.b) :
    (cut p q X).isNone = decide (p.Cp ≤ (X - p.off) % p.CP) := by
  have hd : (X - p.off) / p.CP < p.Rp := (F.div X).2 (by omega)
  unfold OnBytes.DgP.cut
  by_cases hB : p.Cp ≤ (X - p.off) % p.CP
  · have hc : ¬((X - p.off) / p.CP < p.Rp ∧ (X - p.off) % p.CP < p.Cp) := fun k => by omega
    rw [if_neg hc, decide_eq_true hB]
    rfl
  · have hc : (X - p.off) / p.CP < p.Rp ∧ (X - p.off) % p.CP < p.Cp := ⟨hd, by omega⟩
    rw [if_pos hc, decide_eq_false hB]
    rfl

/-! ## 3 · One place: the runs against DgP.digInCall -/

/-- The end of the last range of key places. -/
def stopL (l : List Piece) : ℕ := l.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0

/-- How many of the runs that HTailF2.piecesF counts for a call with the pieces l and 2^n places
hold the place X. -/
def cntL (l : List Piece) (n X : ℕ) : ℕ :=
  (l.map fun p => rowsAt p X).sum + ind (stopL l) (2 ^ n - stopL l) X

/-- DgP.digInCall finds no cell at X, on a list of pieces. -/
def noneL (l : List Piece) (q X : ℕ) : Bool :=
  ((l.find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)).bind
    fun p => cut p q X).isNone

/-- How one piece or two lie: from place 0 on, one behind the other. -/
def Lay (l : List Piece) : Prop :=
  (∃ P, l = [P] ∧ P.off = 0) ∨
    ∃ P Q, l = [P, Q] ∧ ((P.off = 0 ∧ Q.off = 2 ^ P.b) ∨ (Q.off = 0 ∧ P.off = 2 ^ Q.b))

/-- One piece that meets Fair at n and begins at place 0: the place X lies in exactly one of the
counted runs if X < 2^n and no cell is found at X, and in none if not. -/
theorem point_one {n q : ℕ} {P : Piece} (F : Fair n P) (h0 : P.off = 0) (X : ℕ) :
    cntL [P] n X = if X < 2 ^ n ∧ noneL [P] q X = true then 1 else 0 := by
  have hs : stopL [P] = max 0 (P.off + 2 ^ P.b) := rfl
  have ht := F.top
  unfold cntL noneL ind
  rw [hs, List.map_singleton, List.sum_singleton, rowsAt_in F]
  by_cases hin : P.off ≤ X ∧ X < P.off + 2 ^ P.b
  · have hf : ([P].find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
        some P := by
      simp [hin]
    rw [hf]
    show _ = if X < 2 ^ n ∧ (cut P q X).isNone = true then 1 else 0
    rw [cut_none F q hin]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · have hf : ([P].find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
        none := by
      simp only [List.find?_eq_none, List.mem_singleton, forall_eq, Bool.and_eq_true,
        decide_eq_true_eq]
      exact hin
    rw [hf]
    show _ = if X < 2 ^ n ∧ true = true then 1 else 0
    simp only [eq_self, and_true]
    split_ifs <;> omega

/-- Two pieces that meet Fair at n, one at place 0 and the other behind it: the place X lies in
exactly one of the counted runs if X < 2^n and no cell is found at X, and in none if not. -/
theorem point_two {n q : ℕ} {P Q : Piece} (FP : Fair n P) (FQ : Fair n Q)
    (ha : (P.off = 0 ∧ Q.off = 2 ^ P.b) ∨ (Q.off = 0 ∧ P.off = 2 ^ Q.b)) (X : ℕ) :
    cntL [P, Q] n X = if X < 2 ^ n ∧ noneL [P, Q] q X = true then 1 else 0 := by
  have hs : stopL [P, Q] = max (max 0 (P.off + 2 ^ P.b)) (Q.off + 2 ^ Q.b) := rfl
  have h1 := FP.top
  have h2 := FQ.top
  unfold cntL noneL ind
  rw [hs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [rowsAt_in FP, rowsAt_in FQ]
  by_cases hP : P.off ≤ X ∧ X < P.off + 2 ^ P.b
  · have hf : ([P, Q].find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
        some P := by
      simp [hP]
    rw [hf]
    show _ = if X < 2 ^ n ∧ (cut P q X).isNone = true then 1 else 0
    rw [cut_none FP q hP]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · have hPb : (decide (P.off ≤ X) && decide (X < P.off + 2 ^ P.b)) = false := by
      rw [Bool.eq_false_iff]
      simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
      exact hP
    by_cases hQ : Q.off ≤ X ∧ X < Q.off + 2 ^ Q.b
    · have hf : ([P, Q].find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
          some Q := by
        simp [hPb, hQ]
      rw [hf]
      show _ = if X < 2 ^ n ∧ (cut Q q X).isNone = true then 1 else 0
      rw [cut_none FQ q hQ]
      simp only [decide_eq_true_eq]
      split_ifs <;> omega
    · have hQb : (decide (Q.off ≤ X) && decide (X < Q.off + 2 ^ Q.b)) = false := by
        rw [Bool.eq_false_iff]
        simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
        exact hQ
      have hf : ([P, Q].find? fun p => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
          none := by
        simp [hPb, hQb]
      rw [hf]
      show _ = if X < 2 ^ n ∧ true = true then 1 else 0
      simp only [eq_self, and_true]
      split_ifs <;> omega

/-- **One place.** If the pieces l lie as Lay says and each meets Fair at n, then the place X lies
in exactly one of the counted runs if X < 2^n and no cell is found at X, and in none if not. -/
theorem point_lay {n q : ℕ} {l : List Piece} (hl : Lay l) (hF : ∀ p ∈ l, Fair n p) (X : ℕ) :
    cntL l n X = if X < 2 ^ n ∧ noneL l q X = true then 1 else 0 := by
  rcases hl with ⟨P, rfl, h0⟩ | ⟨P, Q, rfl, ha⟩
  · exact point_one (hF P (by simp)) h0 X
  · exact point_two (hF P (by simp)) (hF Q (by simp)) ha X

/-- The pieces that placeZ makes of one block or two lie as Lay says. -/
theorem lay_placeZ (bz : Array (ℕ × ℕ)) (hsz : bz.size = 1 ∨ bz.size = 2)
    (f : ℕ → ℕ × ℕ → Piece) (name : String) (k lid : ℕ) :
    Lay (placeZ ((Array.range bz.size).map fun i => f i (bz.getD i (0, 0)))
      name k lid).pieces.toList := by
  obtain ⟨l⟩ := bz
  rcases hsz with hsz | hsz
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hsz
    have ep : ((Array.range (Array.mk [x]).size).map fun i => f i ((Array.mk [x]).getD i (0, 0))) =
        #[f 0 x] := by
      apply Array.ext'
      simp [List.range_succ]
    rw [ep]
    obtain ⟨e1, -⟩ := piecesF_tail_cnt_placeZ #[f 0 x] name k lid
    have es : piecesF_tail_cnt_sized #[f 0 x] = #[piecesF_tail_cnt_size1 (f 0 x)] := by
      simp [piecesF_tail_cnt_sized]
    rw [es, show (#[piecesF_tail_cnt_size1 (f 0 x)] : Array Piece).size = 1 from rfl,
      piecesF_tail_cnt_order1] at e1
    rw [e1, (piecesF_tail_cnt_laid1 _).1]
    exact Or.inl ⟨_, rfl, rfl⟩
  · obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hsz
    have ep : ((Array.range (Array.mk [x, y]).size).map
        fun i => f i ((Array.mk [x, y]).getD i (0, 0))) = #[f 0 x, f 1 y] := by
      apply Array.ext'
      simp [List.range_succ]
    rw [ep]
    obtain ⟨e1, -⟩ := piecesF_tail_cnt_placeZ #[f 0 x, f 1 y] name k lid
    have es : piecesF_tail_cnt_sized #[f 0 x, f 1 y] =
        #[piecesF_tail_cnt_size1 (f 0 x), piecesF_tail_cnt_size1 (f 1 y)] := by
      simp [piecesF_tail_cnt_sized]
    rw [es, show (#[piecesF_tail_cnt_size1 (f 0 x), piecesF_tail_cnt_size1 (f 1 y)] :
      Array Piece).size = 2 from rfl] at e1
    rcases piecesF_tail_cnt_order2 (fun i =>
      (((#[piecesF_tail_cnt_size1 (f 0 x), piecesF_tail_cnt_size1 (f 1 y)] :
        Array Piece)[i]?).map (·.b)).getD 0) with ho | ho
    · rw [ho] at e1
      rw [e1, (piecesF_tail_cnt_laid01 _ _).1]
      exact Or.inr ⟨_, _, rfl, Or.inl ⟨rfl, Nat.zero_add _⟩⟩
    · rw [ho] at e1
      rw [e1, (piecesF_tail_cnt_laid10 _ _).1]
      exact Or.inr ⟨_, _, rfl, Or.inr ⟨rfl, Nat.zero_add _⟩⟩

/-! ## 4 · The walk through piecesF, tree by tree -/

/-- What Forest.pubRun adds to the count of tree y for a run of call q. -/
def shr (h : Forest.Shape) (y q first count : ℕ) : ℕ :=
  if FoNums.fst h q ≤ y then ov (2 ^ h.dT) first count (y - FoNums.fst h q) else 0

/-- What the loops of piecesF add to the count of tree y for the call z with the number q. -/
def dueZ (h : Forest.Shape) (y q : ℕ) (z : CallZ) : ℕ :=
  (z.pieces.toList.map fun p =>
      ((List.range p.Rp).map fun rr =>
        shr h y q (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum).sum +
    shr h y q (stopL z.pieces.toList) (2 ^ z.call.n - stopL z.pieces.toList)

/-- Where piecesF returns tl': for a tree y below NT, entry y of tl'.f9.pub is what the loops add
for the two calls. -/
theorem walk_Z {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') {y : ℕ} (hy : y < tl'.f9.NT) :
    tl'.f9.pub.getD y 0 = dueZ tl'.f9 y 0 tl'.z1 + dueZ tl'.f9 y 1 tl'.z2 := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hbz, h1⟩ := Ends.ok_of_bind h
  clear h
  obtain ⟨hsz, h2⟩ := Ends.ok_of_jp h1
  clear h1
  obtain ⟨-, h3⟩ := Ends.ok_of_jp h2
  clear h2
  obtain ⟨f9, hs, h4⟩ := Ends.ok_of_bind h3
  clear h3
  obtain ⟨pub, hl, h5⟩ := Ends.ok_of_bind h4
  clear h4
  obtain ⟨u, hp, h⟩ := Ends.ok_of_bind h5
  clear h5
  generalize hz1 : placeZ _ _ t2D0 _ = z1 at hs hl h
  generalize hz2 : placeZ _ _ t2D1 _ = z2 at hs hl h
  have e := (Except.ok.inj h).symm
  subst e
  clear h
  have hy' : y < f9.NT := hy
  show pub.getD y 0 = dueZ f9 y 0 z1 + dueZ f9 y 1 z2
  clear hz1 hz2 hs hp hbz hsz hy
  have K : pub.getD y 0 = ([0, 1].map fun q =>
      dueZ f9 y q (if (q == 0) = true then z1 else z2)).sum :=
    Ends.forIn_keeps _ [0, 1]
    (fun pre (s : Array ℕ) => s.getD y 0 =
      (pre.map fun q => dueZ f9 y q (if (q == 0) = true then z1 else z2)).sum)
    (fun pre a rest e s s' hI hs => by
      clear hl
      obtain ⟨r, hmid, hs1⟩ := Ends.ok_of_bind hs
      clear hs
      obtain ⟨pub1, stop1⟩ := r
      obtain ⟨pub2, hrun, hs2⟩ := Ends.ok_of_bind hs1
      clear hs1
      refine ⟨pub2, (Except.ok.inj hs2).symm, ?_⟩
      clear hs2
      dsimp only at hI ⊢
      rw [List.map_append, List.sum_append, ← hI, List.map_singleton, List.sum_singleton]
      generalize (if (a == 0) = true then z1 else z2) = c at hmid hrun ⊢
      rw [← Array.forIn_toList] at hmid
      have M : pub1.getD y 0 = s.getD y 0 + (c.pieces.toList.map fun p =>
            ((List.range p.Rp).map fun rr =>
              shr f9 y a (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum).sum ∧
          stop1 = c.pieces.toList.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0 :=
        Ends.forIn_keeps _ c.pieces.toList
        (fun pre' (st : MProd (Array ℕ) ℕ) => st.1.getD y 0 = s.getD y 0 + (pre'.map fun p =>
            ((List.range p.Rp).map fun rr =>
              shr f9 y a (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum).sum ∧
          st.2 = pre'.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0)
        (fun pre' p _ _ st st' hI' hst => by
          clear hmid hrun
          obtain ⟨pb, sp⟩ := st
          obtain ⟨i1, i2⟩ := hI'
          dsimp only at i1 i2 hst
          by_cases hc : p.Cp < p.CP
          · rw [if_pos hc] at hst
            obtain ⟨pb1, hrows, hst1⟩ := Ends.ok_of_bind hst
            clear hst
            refine ⟨⟨pb1, max sp (p.off + 2 ^ p.b)⟩, (Except.ok.inj hst1).symm, ?_, ?_⟩
            · clear hst1
              have R : pb1.getD y 0 = pb.getD y 0 + ((List.range p.Rp).map fun rr =>
                  shr f9 y a (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum :=
                Ends.forIn_keeps _ (List.range p.Rp)
                (fun pre'' (t : Array ℕ) => t.getD y 0 = pb.getD y 0 + (pre''.map fun rr =>
                  shr f9 y a (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum)
                (fun pre'' rr _ _ t t' hI'' ht => by
                  clear hrows
                  obtain ⟨t1, hr1, ht1⟩ := Ends.ok_of_bind ht
                  refine ⟨t1, (Except.ok.inj ht1).symm, ?_⟩
                  dsimp only at hI'' ⊢
                  rw [(Att.pubRun_getD hr1).2.2 y hy', hI'', List.map_append, List.sum_append,
                    List.map_singleton, List.sum_singleton, Nat.add_assoc]
                  rfl)
                (List.range p.Rp) [] _ _ rfl (by simp) hrows
              dsimp only
              rw [R, i1, List.map_append, List.sum_append, List.map_singleton,
                List.sum_singleton, Nat.add_assoc]
            · dsimp only
              rw [List.foldl_append, ← i2]
              rfl
          · rw [if_neg hc] at hst
            refine ⟨⟨pb, max sp (p.off + 2 ^ p.b)⟩, (Except.ok.inj hst).symm, ?_, ?_⟩
            · dsimp only
              have hz : ((List.range p.Rp).map fun rr =>
                  shr f9 y a (p.off + rr * p.CP + p.Cp) (p.CP - p.Cp)).sum = 0 := by
                rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hc)]
                simp [shr, Att.ov_zero]
              rw [i1, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                hz, Nat.add_zero]
            · dsimp only
              rw [List.foldl_append, ← i2]
              rfl)
        c.pieces.toList [] _ _ rfl ⟨by simp, rfl⟩ hmid
      obtain ⟨n1, n2⟩ := M
      rw [(Att.pubRun_getD hrun).2.2 y hy', n1]
      unfold dueZ stopL
      rw [← n2, Nat.add_assoc]
      rfl)
    [0, 1] [] _ _ rfl (by
      show (Array.replicate f9.NT 0 : Array ℕ).getD y 0 = 0
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hy']
      rfl) hl
  rw [K]
  show dueZ f9 y 0 z1 + (dueZ f9 y 1 z2 + 0) = _
  rw [Nat.add_zero]

/-- What the loops add for a call, as a sum over the places of tree y. -/
theorem due_sum (h : Forest.Shape) (y q : ℕ) (z : CallZ) :
    dueZ h y q z = if FoNums.fst h q ≤ y then
      ∑ x ∈ range (2 ^ h.dT), cntL z.pieces.toList z.call.n (x + 2 ^ h.dT * (y - FoNums.fst h q))
      else 0 := by
  unfold dueZ shr
  by_cases hq : FoNums.fst h q ≤ y
  · simp only [if_pos hq, ov_sum, sum_list_swap, cntL, rowsAt, Finset.sum_add_distrib]
  · simp [if_neg hq]

/-! ## 5 · The public numbers count the padding places -/

/-- Where piecesF returns tl, the pieces of either call lie as Lay says. -/
theorem lay_Z {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) {q : ℕ} (hq : q < 2) :
    Lay (piecesL tl q) := by
  obtain ⟨bz, -, hsz, -, -, ez1, ez2, -⟩ := piecesF_tail_cnt_walk h
  have hq' : q = 0 ∨ q = 1 := by omega
  rcases hq' with rfl | rfl
  · show Lay tl.z1.pieces.toList
    rw [ez1]
    exact lay_placeZ bz hsz _ _ _ _
  · show Lay tl.z2.pieces.toList
    rw [ez2]
    exact lay_placeZ bz hsz _ _ _ _

/-- Where piecesF returns tl, call q of tl.f9 has as many key bits as the call's own field n. -/
theorem nOf_Z {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) {q : ℕ} (hq : q < 2) :
    FoNums.nOf tl.f9 q = (tl.zOf q).call.n := by
  obtain ⟨bz, -, -, -, -, -, -, -, hcalls, -⟩ := piecesF_tail_cnt_walk h
  have hq' : q = 0 ∨ q = 1 := by omega
  unfold FoNums.nOf
  rw [hcalls]
  rcases hq' with rfl | rfl <;> rfl

/-- Where piecesF returns tl: what the loops add to tree y for call q is the number of the padding
places of tree y if q is the tree's call, and 0 if not. -/
theorem due_card {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) (hok : FoNums.ok tl.f9 = true)
    {y : ℕ} (hy : y < tl.f9.NT) {q : ℕ} (hq : q < 2) :
    dueZ tl.f9 y q (tl.zOf q) = if FoNums.co tl.f9 y = q then
      ((range (2 ^ tl.f9.dT)).filter fun x =>
        padZ tl q (x + 2 ^ tl.f9.dT * (y % 2 ^ FoNums.io tl.f9 q)) = true).card else 0 := by
  have hT : TailOK tl := piecesF_tailOK tl0 tl h
  have hqN : q < tl.f9.NC := by rw [hT.nc]; exact hq
  obtain ⟨-, hB, hC, -⟩ := Cb.Fo.ok_parts hok
  obtain ⟨-, -, hn, hb⟩ := hC q hqN
  have hnz := nOf_Z h hq
  have hFair : ∀ p ∈ (tl.zOf q).pieces.toList, Fair (tl.zOf q).call.n p := fun p hp => by
    obtain ⟨-, a2, a3, a4, -⟩ := hT.pc q hqN p hp
    refine ⟨a2, a3, ?_⟩
    rw [← hnz]
    exact a4
  have hpt : ∀ X, cntL (tl.zOf q).pieces.toList (tl.zOf q).call.n X =
      if X < 2 ^ (tl.zOf q).call.n ∧ padZ tl q X = true then 1 else 0 :=
    fun X => point_lay (q := q) (lay_Z h hq) hFair X
  have hpow : 2 ^ (tl.zOf q).call.n = 2 ^ tl.f9.dT * 2 ^ FoNums.io tl.f9 q := by
    rw [← hnz, hn, Nat.add_comm, pow_add]
  rw [due_sum]
  simp only [hpt, hpow]
  by_cases hco : FoNums.co tl.f9 y = q
  · obtain ⟨-, lo, hi⟩ := hB y hy
    rw [hco] at lo hi
    have hbl : y - FoNums.fst tl.f9 q < 2 ^ FoNums.io tl.f9 q := by omega
    have hmod : y % 2 ^ FoNums.io tl.f9 q = y - FoNums.fst tl.f9 q := by
      have := (hb _ hbl).2.2
      rwa [Nat.add_sub_cancel' lo] at this
    rw [if_pos lo, if_pos hco, hmod, Finset.card_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x < 2 ^ tl.f9.dT := Finset.mem_range.1 hx
    have hlt : x + 2 ^ tl.f9.dT * (y - FoNums.fst tl.f9 q) <
        2 ^ tl.f9.dT * 2 ^ FoNums.io tl.f9 q := by
      have h1 : 2 ^ tl.f9.dT * (y - FoNums.fst tl.f9 q + 1) ≤
          2 ^ tl.f9.dT * 2 ^ FoNums.io tl.f9 q := Nat.mul_le_mul_left _ hbl
      rw [Nat.mul_succ] at h1
      omega
    exact if_congr ⟨fun k => k.2, fun k => ⟨hlt, k⟩⟩ rfl rfl
  · rw [if_neg hco]
    split_ifs with hz
    · have hge : 2 ^ FoNums.io tl.f9 q ≤ y - FoNums.fst tl.f9 q := by
        by_contra hlt
        have := (hb (y - FoNums.fst tl.f9 q) (by omega)).2.1
        rw [Nat.add_sub_cancel' hz] at this
        exact hco this
      refine Finset.sum_eq_zero fun x _ => ?_
      have h1 : 2 ^ tl.f9.dT * 2 ^ FoNums.io tl.f9 q ≤
          2 ^ tl.f9.dT * (y - FoNums.fst tl.f9 q) := Nat.mul_le_mul_left _ hge
      exact if_neg fun k => by omega
    · rfl

/-- Where piecesF returns tl: PubFits tl.f9 (padZ tl). -/
theorem pubFits_pieces {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    PubFits tl.f9 (padZ tl) := by
  intro y hy
  have hok : FoNums.ok tl.f9 = true :=
    (Fo.ZPlan.shapeZ_from ⟨tl0, tl, h, Fo.SameP.refl tl⟩).ok
  have hc : FoNums.co tl.f9 y < 2 := by
    have := ((Cb.Fo.ok_parts hok).2.1 y hy).1
    rwa [(piecesF_tailOK tl0 tl h).nc] at this
  have d0 := due_card h hok hy (q := 0) (by norm_num)
  have d1 := due_card h hok hy (q := 1) (by norm_num)
  rw [walk_Z h hy, show tl.z1 = tl.zOf 0 from rfl, show tl.z2 = tl.zOf 1 from rfl, d0, d1]
  have hc' : FoNums.co tl.f9 y = 0 ∨ FoNums.co tl.f9 y = 1 := by omega
  rcases hc' with e | e
  · rw [e, if_pos rfl, if_neg (by norm_num), Nat.add_zero]
  · rw [e, if_neg (by norm_num), if_pos rfl, Nat.zero_add]

end Dig

/-! ## 6 · The public numbers where piecesF has returned -/

/-- Under FromPieces tl: TailOK tl. -/
theorem tailOK_Z {tl : HTailF2} (hF : FromPieces tl) : TailOK tl := by
  obtain ⟨tl0, tlp, h1, h2⟩ := hF
  refine OnBytes.DgP.tailOK_of_test ?_
  rw [h2.eq]
  exact Fo.PiecesF.piecesF_tailTest tl0 tlp h1

/-- Under FromPieces tl: FoNums.ok tl.f9; two calls; tables of 2^10 and 2^8 rows; padding row 0. -/
theorem nums_Z {tl : HTailF2} (hF : FromPieces tl) :
    FoNums.ok tl.f9 = true ∧ tl.f9.NC = 2 ∧ FoNums.kOf tl.f9 0 = 10 ∧ FoNums.kOf tl.f9 1 = 8 ∧
      FoNums.t0Of tl.f9 0 = 0 ∧ FoNums.t0Of tl.f9 1 = 0 := by
  have hok := (Fo.ZPlan.shapeZ_from hF).ok
  obtain ⟨tl0, tlp, h1, h2⟩ := hF
  obtain ⟨bz, -, -, -, -, ez1, ez2, -, hcalls, hNC, -⟩ := Fo.PiecesF.piecesF_tail_cnt_walk h1
  refine ⟨hok, ?_⟩
  rw [h2.f9]
  have k0 : FoNums.kOf tlp.f9 0 = tlp.z1.call.k := by
    unfold FoNums.kOf
    rw [hcalls]
    rfl
  have k1 : FoNums.kOf tlp.f9 1 = tlp.z2.call.k := by
    unfold FoNums.kOf
    rw [hcalls]
    rfl
  have t0 : FoNums.t0Of tlp.f9 0 = tlp.z1.call.t0 := by
    unfold FoNums.t0Of
    rw [hcalls]
    rfl
  have t1 : FoNums.t0Of tlp.f9 1 = tlp.z2.call.t0 := by
    unfold FoNums.t0Of
    rw [hcalls]
    rfl
  rw [k0, k1, t0, t1, ez1, ez2]
  exact ⟨hNC, rfl, rfl, rfl, rfl⟩

/-- Under FromPieces tl, for c < 2 and t < 2^64: row t of call c's table has the value t. -/
theorem tabOf_Z (K : Type) [Field K] {tl : HTailF2} (hF : FromPieces tl) {c t : ℕ} (hc : c < 2)
    (ht : t < 2 ^ 64) : tabOf K tl.f9 c t = (t : K) := by
  obtain ⟨tl0, tlp, h1, h2⟩ := hF
  obtain ⟨bz, -, -, -, -, ez1, ez2, -, hcalls, -, -⟩ := Fo.PiecesF.piecesF_tail_cnt_walk h1
  have hw : t.toUInt64.toNat = t := by
    show (UInt64.ofNat t).toNat = t
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt ht
  have e : FoNums.tauN tl.f9 c t = t := by
    rw [h2.f9]
    unfold FoNums.tauN
    rw [hcalls]
    have hc' : c = 0 ∨ c = 1 := by omega
    rcases hc' with rfl | rfl
    · show (tlp.z1.call.tauAt t).toNat = t
      rw [ez1]
      exact hw
    · show (tlp.z2.call.tauAt t).toNat = t
      rw [ez2]
      exact hw
  unfold tabOf
  rw [e]

/-- **The public numbers of padding keys count the padding places, tree by tree.** Under
FromPieces tl: for every tree y below NT, entry y of tl.f9.pub is the number of the places x below
2^dT of tree y at which padZ tl says true of the tree's call. -/
theorem pubFits_Z {tl : HTailF2} (hF : FromPieces tl) : PubFits tl.f9 (padZ tl) := by
  obtain ⟨tl0, tlp, h1, h2⟩ := hF
  rw [h2.eq]
  show PubFits tlp.f9 (padZ tlp)
  exact Dig.pubFits_pieces h1

/-! ## 7 · The key vectors -/

section Keys
variable {K : Type} [Field K]

/-- The key vector of call q of the lookup on the digits, of the array ZZ as a function zz of row
and column: at the place of combination u and cell row c the entry zz u (q mz + c); 0 at a padding
place. -/
def kvZ (tl : HTailF2) (zz : ℕ → ℕ → K) (q kn : ℕ) : K :=
  match digInCall tl q kn with
  | some t => zz t.2.2 (q * tl.mz + t.2.1)
  | none => 0

/-- It is the library's key vector DgP.Kp at the reading that takes ZZ's entries from zz. -/
theorem kvZ_eq_Kp (tl : HTailF2) (zz : ℕ → ℕ → K) :
    kvZ tl zz = Kp tl fun e => zz e.2.1 e.2.2 := by
  funext q kn
  unfold kvZ Kp
  cases digInCall tl q kn <;> rfl

/-- Under TailOK tl, for q < 2, c < mz and u < tau: at place DgP.keyNo tl q c u the key vector of
call q holds zz u (q mz + c). -/
theorem kvZ_key {tl : HTailF2} (hT : TailOK tl) (zz : ℕ → ℕ → K) {q c u : ℕ} (hq : q < 2)
    (hc : c < tl.mz) (hu : u < tl.tau) : kvZ tl zz q (keyNo tl q c u) = zz u (q * tl.mz + c) := by
  rw [kvZ_eq_Kp]
  exact OnBytes.DgP.Kp_key hT _ hq hc hu

/-- At a padding place the key vector holds 0. -/
theorem kvZ_pad (tl : HTailF2) (zz : ℕ → ℕ → K) {q kn : ℕ} (hp : padZ tl q kn = true) :
    kvZ tl zz q kn = 0 := by
  unfold kvZ
  rw [Option.isNone_iff_eq_none.1 hp]

/-- **The premise on the digits.** Every entry of ZZ in the rows below tau is in its range: in the
columns below mz a number below 2^(k_0), in the columns mz, .., 2 mz - 1 a number below 2^(k_1),
cast into K. k_0 and k_1 are the two calls' numbers FoNums.kOf. -/
def DigitsIn (tl : HTailF2) (zz : ℕ → ℕ → K) : Prop :=
  ∀ q < 2, ∀ u < tl.tau, ∀ c < tl.mz,
    ∃ a : ℕ, a < 2 ^ FoNums.kOf tl.f9 q ∧ zz u (q * tl.mz + c) = (a : K)

/-- Under FromPieces tl a padding place holds the value of its call's padding row. -/
theorem kvZ_padRow {tl : HTailF2} (hF : FromPieces tl) (zz : ℕ → ℕ → K) :
    ∀ c < tl.f9.NC, ∀ i < 2 ^ FoNums.nOf tl.f9 c, padZ tl c i = true →
      kvZ tl zz c i = tabOf K tl.f9 c (FoNums.t0Of tl.f9 c) := by
  obtain ⟨-, hNC, -, -, t0, t1⟩ := nums_Z hF
  intro c hc i _ hp
  rw [hNC] at hc
  have ht : FoNums.t0Of tl.f9 c = 0 := by
    have hc' : c = 0 ∨ c = 1 := by omega
    rcases hc' with rfl | rfl
    · exact t0
    · exact t1
  rw [kvZ_pad tl zz hp, ht, tabOf_Z K hF hc (by norm_num), Nat.cast_zero]

/-- Under FromPieces tl and DigitsIn tl zz every key of either call is the value of a row of the
call's table. -/
theorem inTable_Z {tl : HTailF2} (hF : FromPieces tl) {zz : ℕ → ℕ → K} (hd : DigitsIn tl zz) :
    ∀ c < tl.f9.NC, Cb.Lkp.InTable (FoNums.nOf tl.f9 c) (FoNums.kOf tl.f9 c) (kvZ tl zz c)
      (tabOf K tl.f9 c) := by
  obtain ⟨-, hNC, k0, k1, -, -⟩ := nums_Z hF
  have hT := tailOK_Z hF
  intro c hc b _
  rw [hNC] at hc
  have hk : (2 : ℕ) ^ FoNums.kOf tl.f9 c ≤ 2 ^ 64 := by
    have hc' : c = 0 ∨ c = 1 := by omega
    rcases hc' with rfl | rfl
    · rw [k0]
      norm_num
    · rw [k1]
      norm_num
  cases hdc : digInCall tl c b with
  | none =>
    refine ⟨0, Nat.two_pow_pos _, ?_⟩
    rw [kvZ_pad tl zz (by unfold padZ; rw [hdc]; rfl), tabOf_Z K hF hc (by norm_num),
      Nat.cast_zero]
  | some t =>
    obtain ⟨q', cc, u⟩ := t
    obtain ⟨-, hcc, hu, -⟩ := OnBytes.DgP.inCall_bwd hT hc hdc
    obtain ⟨a, ha, e⟩ := hd c hc u hu cc hcc
    refine ⟨a, ha, ?_⟩
    unfold kvZ
    rw [hdc, tabOf_Z K hF hc (lt_of_lt_of_le ha hk)]
    exact e

end Keys

/-! ## 8 · BZ as a term, at its own addresses -/

/-- At lm = 5 the cell of (t, c, j) is row j, column c 2^kT + t. -/
theorem cellRC_5 (h : Forest.Shape) (t c j : ℕ) :
    FoNums.cellRC h 5 (t, c, j) = (j, c * 2 ^ h.kT + t) := by
  show ((t % 2 ^ (5 - FoNums.w)) * FoNums.planes + j,
    c * 2 ^ (h.kT + FoNums.w - 5) + t / 2 ^ (5 - FoNums.w)) = _
  have h1 : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
  have h2 : h.kT + FoNums.w - 5 = h.kT := Nat.add_sub_cancel h.kT 5
  rw [h1, h2, Nat.mod_one, Nat.zero_mul, Nat.zero_add, Nat.div_one]

section Law
variable {K : Type} [Field K]

/-- An array bz of BZ's form, read as the matrix with one row a plane: row r, column
c 2^kT + t is bz at the address DgP.bcP tl t c r. -/
def virtZ (tl : HTailF2) (bz : ℕ → ℕ → K) (r col : ℕ) : K :=
  bz (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.1
    (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.2

variable [DecidableEq K]

/-- The padding places and the chosen rows of the lookup on the digits. -/
def hitsZ (tl : HTailF2) (zz : ℕ → ℕ → K) : Hits :=
  hitsOf tl.f9 (tabOf K tl.f9) (kvZ tl zz) (padZ tl)

/-- **BZ as a function of row and column**, with values 0 and 1. The entry number
X = row * bzColumns + col is bit j = X % 32 of the count of row t = X / 32 / 2^cK of the table of
call c = X / 32 % 2^cK. -/
def bzOf (tl : HTailF2) (zz : ℕ → ℕ → K) (row col : ℕ) : ℕ :=
  plane tl.f9 5 (hitsZ tl zz) ((row * tl.bzColumns + col) % 32)
    ((row * tl.bzColumns + col) / 32 % 2 ^ tl.f9.cK * 2 ^ tl.f9.kT +
      (row * tl.bzColumns + col) / 32 / 2 ^ tl.f9.cK)

/-- For c < 2^cK and j < 32: bzOf at the address DgP.bcP tl t c j is the cell of plane at
FoNums.cellRC tl.f9 5 (t, c, j). -/
theorem bzOf_at (tl : HTailF2) (zz : ℕ → ℕ → K) (t : ℕ) {c j : ℕ} (hc : c < 2 ^ tl.f9.cK)
    (hj : j < 32) :
    bzOf tl zz (bcP tl t c j).2.1 (bcP tl t c j).2.2 =
      plane tl.f9 5 (hitsZ tl zz) (FoNums.cellRC tl.f9 5 (t, c, j)).1
        (FoNums.cellRC tl.f9 5 (t, c, j)).2 := by
  have hX : (bcP tl t c j).2.1 * tl.bzColumns + (bcP tl t c j).2.2 =
      (t * 2 ^ tl.f9.cK + c) * 32 + j := Nat.div_add_mod' _ _
  have e1 : ((t * 2 ^ tl.f9.cK + c) * 32 + j) % 32 = j := by omega
  have e2 : ((t * 2 ^ tl.f9.cK + c) * 32 + j) / 32 = t * 2 ^ tl.f9.cK + c := by omega
  have e3 : (t * 2 ^ tl.f9.cK + c) % 2 ^ tl.f9.cK = c := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  have e4 : (t * 2 ^ tl.f9.cK + c) / 2 ^ tl.f9.cK = t := by
    rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hc, Nat.add_zero]
  unfold bzOf
  rw [hX, cellRC_5, e1, e2, e3, e4]

/-- For r < 32 and col < 2^cK 2^kT: bzOf, read as the matrix with one row a plane, is plane. -/
theorem virtZ_bzOf (tl : HTailF2) (zz : ℕ → ℕ → K) {r col : ℕ} (hr : r < 32)
    (hcol : col < 2 ^ tl.f9.cK * 2 ^ tl.f9.kT) :
    virtZ tl (fun a b => (bzOf tl zz a b : K)) r col = (plane tl.f9 5 (hitsZ tl zz) r col : K) := by
  have hc : col / 2 ^ tl.f9.kT < 2 ^ tl.f9.cK :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  show ((bzOf tl zz (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.1
    (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.2 : ℕ) : K) = _
  rw [bzOf_at tl zz _ hc hr, cellRC_5, Nat.div_add_mod']

/-- The array bz holds bzOf tl zz, cast into K, in its 32 rows and bzColumns columns. -/
def LaidBZ (tl : HTailF2) (zz bz : ℕ → ℕ → K) : Prop :=
  ∀ row < 32, ∀ col < tl.bzColumns, bz row col = (bzOf tl zz row col : K)

/-- Under LaidBZ tl zz bz, for u < 2^d and j < 32: bz at the address (DgP.portQ tl).bAt u j is the
cell of plane at FoNums.cellRC tl.f9 5 (u / 2^cK, u % 2^cK, j), cast into K. -/
theorem bz_plane {tl : HTailF2} {zz bz : ℕ → ℕ → K} (hb : LaidBZ tl zz bz) {u j : ℕ}
    (hu : u < 2 ^ tl.f9.d) (hj : j < 32) :
    bz ((portQ tl).bAt u j).2.1 ((portQ tl).bAt u j).2.2 =
      (plane tl.f9 5 (hitsZ tl zz)
        (FoNums.cellRC tl.f9 5 (u / 2 ^ tl.f9.cK, u % 2 ^ tl.f9.cK, j)).1
        (FoNums.cellRC tl.f9 5 (u / 2 ^ tl.f9.cK, u % 2 ^ tl.f9.cK, j)).2 : K) := by
  have hX : u * 32 + j < tl.bzColumns * 32 := Att.radix hu hj
  have hpos : 0 < tl.bzColumns := Nat.two_pow_pos _
  have h1 : ((portQ tl).bAt u j).2.1 < 32 := Nat.div_lt_of_lt_mul hX
  have h2 : ((portQ tl).bAt u j).2.2 < tl.bzColumns := Nat.mod_lt _ hpos
  have h3 := bzOf_at tl zz (u / 2 ^ tl.f9.cK) (c := u % 2 ^ tl.f9.cK)
    (Nat.mod_lt _ (Nat.two_pow_pos _)) hj
  rw [OnBytes.DgP.dgP_bc] at h3
  rw [hb _ h1 _ h2, h3]

/-- Under FromPieces tl and LaidBZ tl zz bz: for r < 2^5 and col < NC 2^(kT + 5 - 5), bz read as the
matrix with one row a plane is plane, cast into K. -/
theorem virtZ_plane {tl : HTailF2} (hF : FromPieces tl) {zz bz : ℕ → ℕ → K}
    (hb : LaidBZ tl zz bz) :
    ∀ r < 2 ^ 5, ∀ col < tl.f9.NC * 2 ^ (tl.f9.kT + 5 - 5),
      virtZ tl bz r col = (plane tl.f9 5 (hitsZ tl zz) r col : K) := by
  intro r hr col hcol
  have hNC : tl.f9.NC ≤ 2 ^ tl.f9.cK := (Cb.Fo.ok_parts (nums_Z hF).1).1.2.2.1
  rw [Nat.add_sub_cancel] at hcol
  have hcol' : col < 2 ^ tl.f9.cK * 2 ^ tl.f9.kT :=
    lt_of_lt_of_le hcol (Nat.mul_le_mul_right _ hNC)
  have hr' : r < 32 := hr
  have hc : col / 2 ^ tl.f9.kT < 2 ^ tl.f9.cK :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol')
  have ht : col % 2 ^ tl.f9.kT < 2 ^ tl.f9.kT := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hY : col % 2 ^ tl.f9.kT * 2 ^ tl.f9.cK + col / 2 ^ tl.f9.kT <
      2 ^ tl.f9.kT * 2 ^ tl.f9.cK := Att.radix ht hc
  rw [← pow_add] at hY
  have hX : (col % 2 ^ tl.f9.kT * 2 ^ tl.f9.cK + col / 2 ^ tl.f9.kT) * 32 + r <
      tl.bzColumns * 32 := Att.radix hY hr'
  have h1 : (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.1 < 32 :=
    Nat.div_lt_of_lt_mul hX
  have h2 : (bcP tl (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) r).2.2 < tl.bzColumns :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold virtZ
  rw [hb _ h1 _ h2]
  exact virtZ_bzOf tl zz hr' hcol'

/-! ## 9 · The relation after the challenge -/

/-- **The relation of the lookup on the digits.** Under FromPieces tl, DigitsIn tl zz and
LaidBZ tl zz bz, for all θ and al: Cb.Lkp.MidP holds of the joint key vector of kvZ tl zz, the joint
table, the public padding, and the bits that bz holds at the addresses (DgP.portQ tl).bAt u j. -/
theorem lawZ {tl : HTailF2} (hF : FromPieces tl) {zz bz : ℕ → ℕ → K} (hd : DigitsIn tl zz)
    (hb : LaidBZ tl zz bz) (θ al : K) :
    Cb.Lkp.MidP tl.f9.v tl.f9.d 5 32 (Ends.jointKey tl.f9 (kvZ tl zz) θ) (Ends.jointTab tl.f9 θ)
      (FoNums.pads tl.f9)
      (fun u j => bz ((portQ tl).bAt u j).2.1 ((portQ tl).bAt u j).2.2) al :=
  law_bits tl.f9 (kvZ tl zz) (padZ tl) (nums_Z hF).1 (inTable_Z hF hd) (kvZ_padRow hF zz)
    (pubFits_Z hF) (le_refl 5) (Nat.le_add_left 5 _) _ (fun _ hu _ hj => bz_plane hb hu hj) θ al

end Law

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.Dig.ov_sum
#print axioms OnBytes.HonestTrace.Dig.sum_list_swap
#print axioms OnBytes.HonestTrace.Dig.ind_row
#print axioms OnBytes.HonestTrace.Dig.rowsAt_eq
#print axioms OnBytes.HonestTrace.Dig.Fair.pos
#print axioms OnBytes.HonestTrace.Dig.Fair.div
#print axioms OnBytes.HonestTrace.Dig.rowsAt_in
#print axioms OnBytes.HonestTrace.Dig.cut_none
#print axioms OnBytes.HonestTrace.Dig.point_one
#print axioms OnBytes.HonestTrace.Dig.point_two
#print axioms OnBytes.HonestTrace.Dig.point_lay
#print axioms OnBytes.HonestTrace.Dig.lay_placeZ
#print axioms OnBytes.HonestTrace.Dig.walk_Z
#print axioms OnBytes.HonestTrace.Dig.due_sum
#print axioms OnBytes.HonestTrace.Dig.lay_Z
#print axioms OnBytes.HonestTrace.Dig.nOf_Z
#print axioms OnBytes.HonestTrace.Dig.due_card
#print axioms OnBytes.HonestTrace.Dig.pubFits_pieces
#print axioms OnBytes.HonestTrace.tailOK_Z
#print axioms OnBytes.HonestTrace.nums_Z
#print axioms OnBytes.HonestTrace.tabOf_Z
#print axioms OnBytes.HonestTrace.pubFits_Z
#print axioms OnBytes.HonestTrace.kvZ_eq_Kp
#print axioms OnBytes.HonestTrace.kvZ_key
#print axioms OnBytes.HonestTrace.kvZ_pad
#print axioms OnBytes.HonestTrace.kvZ_padRow
#print axioms OnBytes.HonestTrace.inTable_Z
#print axioms OnBytes.HonestTrace.cellRC_5
#print axioms OnBytes.HonestTrace.bzOf_at
#print axioms OnBytes.HonestTrace.virtZ_bzOf
#print axioms OnBytes.HonestTrace.bz_plane
#print axioms OnBytes.HonestTrace.virtZ_plane
#print axioms OnBytes.HonestTrace.lawZ
