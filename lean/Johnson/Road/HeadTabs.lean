-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadTabs.lean: the tables of the output head's lookup calls, the verifier's beside the
library's.

The verifier looks the head's keys up in four tables: the numbers below 2^16, the numbers below 2^8,
the table of the clamp and the table of exponentials. A call's record (Call in
OnBytes/Model/Frame.lean) holds a table as an array of words of the base field, or holds none, and
then row t has the value t. The library has the same four as functions from the row to an integer
(R16, R8, FC, FE in Inst/Model/Tables.lean). This file says that they are the same tables.

The sense (IsLut c T). The call c has as many rows as T; the word in row u of c is the residue of a
natural number that, as an integer, is T.row u; the word in c's padding row is in the same sense
T.pad. From this, for every reading of the verifier's field elements that takes numerals to numbers:
the reading of a row of c is an entry of T in the library's sense (IsLut.inLut), every entry of T is
the reading of a row of c (IsLut.of_inLut), and the padding key reads as T.pad (IsLut.pad_value).

Main definitions: IsLut; tauFCw (the array of the clamp's table, in the letters of the layers'
layout); rowFE; lutOfKind (the library's table for a kind of call); famsH, nameH (the nine families
and their names in the parameter file).
Main theorems: rowFC_eq (for every t), rowFE_eq, tauFELoop_toList, tauFE_getD; isLut_R16, isLut_R8,
isLut_FC, isLut_FE; isLut_lookups, cl_of_layoutH, isLut_of_layout; tauFC_of_layout; IsLut.inLut,
IsLut.of_inLut, IsLut.pad_value; inLut_R23.

Where the hypotheses are met. The four theorems isLut_R16 to isLut_FE ask what a call's record
holds (tau, k, t0). isLut_lookups gives this for the records that the function lookups makes from
the array tauFCw and the table of exponentials at 24, 8, 4, and isLut_of_layout for the records of
a layout that the head's function layout returns on the array tauFCw at these three numbers.
tauFC_of_layout: the layers' layout has that array in the field which the verifier hands to the
head's layout. That the two layouts return, and that the three numbers are 24, 8, 4, is held by
runs at two examples (Johnson/Road/HeadRunK.lean), which also compare the tables row by row.
From that file's head, word for word: «What comes out. - At the full-size example every line holds
but one. The matrix of the lookup's counts has 384 columns for the verifier, 64 for each of six
calls, and n2 .b = 576 in the library, 64 for each of nine trees. In the library n2 .b and placeB
are used in Index.lean alone. - At the small example the library has no head: the lines that compare
a size fail, and they are listed (smallFails). What holds there: no filler entry; 120 ledger bytes;
NormPar.OK; the digit forms; each family in its call; the calls' families, tables' rows and padding
keys; the columns of five families (HD1, HD2, HE0, HE1, CNF), where the library's pos begins as the
identity. - No row of a table differs, at either example.»

lutOfKind is this file's own. That the table of the kind of a family's call is the table which the
library's relation gives the family is not stated here; for the family HD0 it is not so to the
letter (see below).

What is not claimed. Nothing on what the lookup shows. The table of exponentials is treated at F =
24, sh = 8, sT = 4 alone, the numbers of both examples and of the library. The family HD0: the
verifier divides its key by 2^23 and looks it up among the numbers below 2^16; two forms of the
library's relation look the undivided key up among the multiples of 2^23; inLut_R23 is the step from
the first to the second, given that the division is one. The program does not import this file.
-/
import Johnson.Road.FormsKeysLaid
import OnBytes.Model.HeadLayout
import OnBytes.Field.WordEq
import Cm.TargetPHead
import Inst.Model.Head.Trace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading Call CallD)
open Inst.Model

/-! ## The families' names -/

/-- The nine families, in the order of the library's type. -/
def famsH : List Head.Fam := [.NF, .NFH, .HD0, .HD1, .ROW, .HD2, .HE0, .HE1, .CNF]

/-- A family's name in the parameter file. -/
def nameH : Head.Fam → String
  | .NF => "NF" | .NFH => "NFH" | .HD0 => "HD0" | .HD1 => "HD1" | .ROW => "ROW" | .HD2 => "HD2"
  | .HE0 => "HE0" | .HE1 => "HE1" | .CNF => "CNF"

/-! ## Words and numbers -/

/-- A number below the prime, made a word, is its residue. -/
theorem word_eq_fOfNat {n : ℕ} (h : n < 18446744069414584321) :
    n.toUInt64 = Model.fOfNat n := by
  show n.toUInt64 = (n % 18446744069414584321).toUInt64
  rw [Nat.mod_eq_of_lt h]

/-- A row of a call without a written table. -/
theorem tauAt_none {c : Call} (h : c.tau = none) (t : ℕ) : c.tauAt t = t.toUInt64 := by
  simp [Call.tauAt, h]

/-- A row of a call with a written table. -/
theorem tauAt_some {c : Call} {a : Array UInt64} (h : c.tau = some a) (t : ℕ) :
    c.tauAt t = a.getD t 0 := by
  simp [Call.tauAt, h]

/-- An entry of an array that is made from the first n numbers. -/
theorem getD_map_rangeT {α : Type} (f : ℕ → α) (n t : ℕ) (d : α) (h : t < n) :
    ((Array.range n).map f).getD t d = f t := by
  simp [Array.getD, h]

/-- An entry of an array, read in its list. -/
theorem getD_of_toListT {α : Type} (a : Array α) (l : List α) (h : a.toList = l) (i : ℕ) (d : α) :
    a.getD i d = l.getD i d := by
  subst h
  cases a
  simp

/-- An entry of a list that is made from n numbers in a row. -/
theorem getD_map_range'T {α : Type} (f : ℕ → α) (s n i : ℕ) (d : α) (h : i < n) :
    ((List.range' s n).map f).getD i d = f (s + i) := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## The sense -/

/-- The call c has the library's table T: see the head comment. -/
structure IsLut (c : Call) (T : Lut) : Prop where
  /-- as many rows -/
  rows : 2 ^ c.k = T.rows
  /-- row by row -/
  row : ∀ u < T.rows, ∃ n : ℕ, c.tauAt u = Model.fOfNat n ∧ (n : ℤ) = T.row u
  /-- the padding key -/
  pad : ∃ n : ℕ, c.tauAt c.t0 = Model.fOfNat n ∧ (n : ℤ) = T.pad

section Readings

variable {K : Type} [Field K] {ρ : Reading K}

/-- The reading of a row of the verifier's table is an entry of the library's. -/
theorem IsLut.inLut (hρ : Numerals ρ) {c : Call} {T : Lut} (h : IsLut c T) {u : ℕ}
    (hu : u < 2 ^ c.k) : Head.InLut T (ρ.val (ofF (c.tauAt u))) := by
  rw [h.rows] at hu
  obtain ⟨n, hn, hr⟩ := h.row u hu
  refine ⟨u, hu, ?_⟩
  rw [hn, ← hr]
  show ρ.val (Model.ofNat n) = _
  rw [hρ.ofNat, Int.cast_natCast]

/-- An entry of the library's table is the reading of a row of the verifier's. -/
theorem IsLut.of_inLut (hρ : Numerals ρ) {c : Call} {T : Lut} (h : IsLut c T) {a : K}
    (ha : Head.InLut T a) : ∃ u < 2 ^ c.k, a = ρ.val (ofF (c.tauAt u)) := by
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨n, hn, hr⟩ := h.row u hu
  refine ⟨u, by rw [h.rows]; exact hu, ?_⟩
  rw [hn, ← hr]
  show _ = ρ.val (Model.ofNat n)
  rw [hρ.ofNat, Int.cast_natCast]

/-- The verifier's padding key reads as the library's. -/
theorem IsLut.pad_value (hρ : Numerals ρ) {c : Call} {T : Lut} (h : IsLut c T) :
    ρ.val (ofF (c.tauAt c.t0)) = (T.pad : K) := by
  obtain ⟨n, hn, hr⟩ := h.pad
  rw [hn, ← hr]
  show ρ.val (Model.ofNat n) = _
  rw [hρ.ofNat, Int.cast_natCast]

/-- 2^23 times a number below 2^16 is an entry of the table of the multiples of 2^23. -/
theorem inLut_R23 {a : K} (h : Head.InLut R16 a) : Head.InLut Cm.Plain.TP.R23 (2 ^ 23 * a) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨u, hu, ?_⟩
  show (2 : K) ^ 23 * (((u : ℕ) : ℤ) : K) = ((2 ^ 23 * ((u : ℕ) : ℤ) : ℤ) : K)
  push_cast
  ring

end Readings

/-! ## The two tables of consecutive numbers -/

/-- A call without a written table, with 2^16 rows and the padding row 0, has the table R16. -/
theorem isLut_R16 {c : Call} (hτ : c.tau = none) (hk : c.k = 16) (h0 : c.t0 = 0) :
    IsLut c R16 where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 2 ^ 16 := hu
    exact ⟨u, by rw [tauAt_none hτ]; exact word_eq_fOfNat (by omega), rfl⟩
  pad := ⟨0, by rw [tauAt_none hτ, h0]; exact word_eq_fOfNat (by omega), rfl⟩

/-- A call without a written table, with 2^8 rows and the padding row 0, has the table R8. -/
theorem isLut_R8 {c : Call} (hτ : c.tau = none) (hk : c.k = 8) (h0 : c.t0 = 0) :
    IsLut c R8 where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 2 ^ 8 := hu
    exact ⟨u, by rw [tauAt_none hτ]; exact word_eq_fOfNat (by omega), rfl⟩
  pad := ⟨0, by rw [tauAt_none hτ, h0]; exact word_eq_fOfNat (by omega), rfl⟩

/-! ## The table of the clamp -/

/-- The array of the clamp's table, in the letters of the layers' layout
(OnBytes/Model/LayerLayout.lean, the field tauFC). -/
def tauFCw : Array UInt64 := (Array.range 65536).map fun t => (Model.Layer.rowFC t).toUInt64

/-- Row t of the verifier's table of the clamp is row t of the library's, for every t. -/
theorem rowFC_eq (t : ℕ) : ((Model.Layer.rowFC t : ℕ) : ℤ) = FC.row t := by
  have e : Model.Layer.rowFC t =
      t + ((if t + 2047 < 32768 then 0 else min (t + 2047 - 32768) (2 * 2047)) + 1) * 2 ^ 28 := rfl
  have r : FC.row t =
      (t : ℤ) + 2 ^ 28 * (min (max ((t : ℤ) - 2 ^ 15) (-2047)) 2047 + 2 ^ 11) := rfl
  rw [e, r]
  by_cases h : t + 2047 < 32768
  · rw [if_pos h, max_eq_right (by omega), min_eq_left (by norm_num)]
    push_cast
    ring
  · rw [if_neg h, max_eq_left (by omega)]
    by_cases h2 : t + 2047 - 32768 ≤ 2 * 2047
    · rw [min_eq_left h2, min_eq_left (by omega)]
      omega
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
      push_cast
      ring

/-- A row of the clamp's table is below 2^41. -/
theorem rowFC_lt {t : ℕ} (ht : t < 65536) : Model.Layer.rowFC t < 2 ^ 41 := by
  have e : Model.Layer.rowFC t =
      t + ((if t + 2047 < 32768 then 0 else min (t + 2047 - 32768) (2 * 2047)) + 1) * 2 ^ 28 := rfl
  rw [e]
  split_ifs <;> omega

/-- A call with the array of the clamp's table, 2^16 rows and the padding row 2^15 has the table
FC. -/
theorem isLut_FC {c : Call} (hτ : c.tau = some tauFCw) (hk : c.k = 16) (h0 : c.t0 = 32768) :
    IsLut c FC where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    have hb := rowFC_lt hu'
    refine ⟨Model.Layer.rowFC u, ?_, rowFC_eq u⟩
    rw [tauAt_some hτ]
    unfold tauFCw
    rw [getD_map_rangeT _ _ _ _ hu']
    exact word_eq_fOfNat (by omega)
  pad := by
    have hb := rowFC_lt (t := 32768) (by norm_num)
    refine ⟨Model.Layer.rowFC 32768, ?_, ?_⟩
    · rw [tauAt_some hτ, h0]
      unfold tauFCw
      rw [getD_map_rangeT _ _ _ _ (by norm_num)]
      exact word_eq_fOfNat (by omega)
    · have e : Model.Layer.rowFC 32768 = 549755846656 := by decide
      rw [e]
      show ((549755846656 : ℕ) : ℤ) = 2 ^ 15 + 2 ^ 39
      norm_num

/-! ## The table of exponentials -/

/-- Row u of the verifier's table of exponentials as a natural number, in the letters of tauFELoop
(OnBytes/Model/HeadLayout.lean), with the library's G_u for the running value. -/
def rowFE (u : ℕ) : ℕ := u + (((exG u + 131071) >>> 17) <<< 16)

/-- It is row u of the library's table. -/
theorem rowFE_eq (u : ℕ) : ((rowFE u : ℕ) : ℤ) = FE.row u := by
  have e : (exG u + (2 ^ 17 - 1)) / 2 ^ 17 = (exG u + 131071) / 2 ^ 17 := by norm_num
  unfold rowFE
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  show ((u + (exG u + 131071) / 2 ^ 17 * 2 ^ 16 : ℕ) : ℤ) =
    (u : ℤ) + 2 ^ 16 * (((exG u + (2 ^ 17 - 1)) / 2 ^ 17 : ℕ) : ℤ)
  rw [e]
  generalize (exG u + 131071) / 2 ^ 17 = q
  push_cast
  ring

/-- The library's running value never exceeds its first value. -/
theorem exG_le (u : ℕ) : exG u ≤ 2 ^ 41 := by
  induction u with
  | zero => exact le_refl _
  | succ n ih =>
    show (exG n * 484 + (2 ^ 32 - 1)) / 2 ^ 32 ≤ 2 ^ 41
    omega

/-- A row of the table of exponentials is below 2^41. -/
theorem rowFE_lt {u : ℕ} (hu : u < 65536) : rowFE u < 2 ^ 41 := by
  have h := exG_le u
  unfold rowFE
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- The verifier's step of the recurrence is the library's. -/
theorem exG_step (u : ℕ) : (exG u * 484 + 0xFFFFFFFF) >>> 32 = exG (u + 1) := by
  rw [Nat.shiftRight_eq_div_pow]
  show _ = (exG u * 484 + (2 ^ 32 - 1)) / 2 ^ 32
  norm_num

/-- The verifier's loop, begun at row u with the library's running value of row u, appends the rows
u, u + 1, … -/
theorem tauFELoop_toList (left : ℕ) : ∀ (u : ℕ) (a : Array UInt64),
    (Model.Head.tauFELoop 484 left u (exG u) a).toList =
      a.toList ++ (List.range' u left).map fun v => UInt64.ofNat (rowFE v) := by
  induction left with
  | zero =>
    intro u a
    show a.toList = _
    simp
  | succ n ih =>
    intro u a
    have step : Model.Head.tauFELoop 484 (n + 1) u (exG u) a =
        Model.Head.tauFELoop 484 n (u + 1) ((exG u * 484 + 0xFFFFFFFF) >>> 32)
          (a.push (UInt64.ofNat (rowFE u))) := rfl
    rw [step, exG_step, ih (u + 1)]
    simp [List.range'_succ]

/-- An entry of the array that the loop makes from the empty array. -/
theorem tauFELoop_getD (n cap : ℕ) {u : ℕ} (hu : u < n) :
    (Model.Head.tauFELoop 484 n 0 (exG 0) (Array.mkEmpty cap)).getD u 0 =
      UInt64.ofNat (rowFE u) := by
  rw [getD_of_toListT _ _ (tauFELoop_toList n 0 (Array.mkEmpty cap))]
  have e : (Array.mkEmpty cap : Array UInt64).toList = [] := rfl
  rw [e, List.nil_append, getD_map_range'T _ _ _ _ _ hu, Nat.zero_add]

/-- The verifier's table at F = 24, sh = 8, sT = 4 is that loop. -/
theorem tauFEOf_eq : Model.Head.tauFEOf 24 8 4 =
    Model.Head.tauFELoop 484 65536 0 (exG 0) (Array.mkEmpty 65536) := rfl

/-- Row u of the verifier's table of exponentials. -/
theorem tauFE_getD {u : ℕ} (hu : u < 65536) :
    (Model.Head.tauFEOf 24 8 4).getD u 0 = UInt64.ofNat (rowFE u) := by
  rw [tauFEOf_eq]
  exact tauFELoop_getD 65536 65536 hu

/-- A call with the verifier's table of exponentials, 2^16 rows and the padding row 0 has the table
FE. -/
theorem isLut_FE {c : Call} (hτ : c.tau = some (Model.Head.tauFEOf 24 8 4)) (hk : c.k = 16)
    (h0 : c.t0 = 0) : IsLut c FE where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    have hb := rowFE_lt hu'
    refine ⟨rowFE u, ?_, rowFE_eq u⟩
    rw [tauAt_some hτ, tauFE_getD hu']
    exact word_eq_fOfNat (by omega)
  pad := by
    have hb := rowFE_lt (u := 0) (by norm_num)
    refine ⟨rowFE 0, ?_, ?_⟩
    · rw [tauAt_some hτ, h0, tauFE_getD (by norm_num)]
      exact word_eq_fOfNat (by omega)
    · have e : rowFE 0 = 1099511627776 := by decide
      rw [e]
      show ((1099511627776 : ℕ) : ℤ) = 2 ^ 40
      norm_num

/-! ## The records that the head's layout makes -/

/-- The library's table for a kind of call. -/
def lutOfKind (kind : String) : Lut :=
  if kind == "FC" then FC else if kind == "FE" then FE else if kind == "R8" then R8 else R16

/-- Every record that lookups (OnBytes/Model/HeadLayout.lean) makes, from the array tauFCw and the
table of exponentials at 24, 8, 4, has the library's table for the kind of its call. -/
theorem isLut_lookups (h : Model.Head.Shape) (calls : List CallD) (c : Call)
    (hc : c ∈ (Model.Head.lookups h tauFCw (Model.Head.tauFEOf 24 8 4) calls).toList) :
    ∃ cd ∈ calls, c.name = cd.name ∧ IsLut c (lutOfKind cd.kind) := by
  unfold Model.Head.lookups at hc
  simp only [List.mem_map] at hc
  obtain ⟨cd, hcd, rfl⟩ := hc
  refine ⟨cd, hcd, ?_, ?_⟩
  · by_cases e1 : cd.kind = "FC" <;> by_cases e2 : cd.kind = "FE" <;> simp [e1, e2]
  · by_cases e1 : cd.kind = "FC"
    · have hl : lutOfKind cd.kind = FC := by simp [lutOfKind, e1]
      rw [hl]
      refine isLut_FC ?_ ?_ ?_ <;> simp [e1]
    · by_cases e2 : cd.kind = "FE"
      · have hl : lutOfKind cd.kind = FE := by simp [lutOfKind, e2]
        rw [hl]
        refine isLut_FE ?_ ?_ ?_ <;> simp [e2]
      · by_cases e3 : cd.kind = "R8"
        · have hl : lutOfKind cd.kind = R8 := by simp [lutOfKind, e3]
          rw [hl]
          refine isLut_R8 ?_ ?_ ?_ <;> simp [e3]
        · have hl : lutOfKind cd.kind = R16 := by simp [lutOfKind, e1, e2, e3]
          rw [hl]
          refine isLut_R16 ?_ ?_ ?_ <;> simp [e1, e2, e3]

/-- A record keeps its table if the number of its trees is set. -/
theorem IsLut.iota {c : Call} {T : Lut} (h : IsLut c T) (i : ℕ) : IsLut { c with iota := i } T :=
  ⟨h.rows, h.row, h.pad⟩

/-- A record of lookups, by its number: it is the record that lookups makes of the call with that
number alone. -/
theorem lookups_at {h : Model.Head.Shape} {a b : Array UInt64} {calls : List CallD} {q : ℕ}
    {c : Call} (hc : (Model.Head.lookups h a b calls)[q]? = some c) :
    ∃ cd, calls[q]? = some cd ∧ c ∈ (Model.Head.lookups h a b [cd]).toList := by
  unfold Model.Head.lookups at hc
  simp at hc
  obtain ⟨cd, hcd, rfl⟩ := hc
  refine ⟨cd, hcd, ?_⟩
  simp [Model.Head.lookups]

/-- The records of the calls in a layout that the verifier's function returns: those that lookups
makes of the layout's calls, each with the number of its trees set. -/
theorem cl_of_layoutH {h : Model.Head.Shape} {tauFC : Array UInt64} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : ∃ fs : Model.Forest.Shape,
      L.cl = (Model.Head.lookups h tauFC (Model.Head.tauFEOf h.famF h.digSh h.tabS)
        L.calls.toList).mapIdx fun q c => { c with iota := fs.iota.getD q 0 } := by
  unfold Model.Head.layout at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨calls, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  exact ⟨fs, rfl⟩

/-- In a layout that the verifier's function returns on the array tauFCw, at F = 24, sh = 8, sT = 4,
the record of call number q has the library's table for the kind of call number q. -/
theorem isLut_of_layout {h : Model.Head.Shape} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFCw = .ok L) (hF : h.famF = 24) (hs : h.digSh = 8)
    (hT : h.tabS = 4) {q : ℕ} {c : Call} (hc : L.cl[q]? = some c) :
    ∃ cd, L.calls[q]? = some cd ∧ c.name = cd.name ∧ IsLut c (lutOfKind cd.kind) := by
  obtain ⟨fs, e⟩ := cl_of_layoutH hy
  rw [e, hF, hs, hT] at hc
  simp only [Array.getElem?_mapIdx, Option.map_eq_some_iff] at hc
  obtain ⟨c0, h0, rfl⟩ := hc
  obtain ⟨cd, hcd, hm⟩ := lookups_at h0
  obtain ⟨cd', hcd', hn, hl⟩ := isLut_lookups h [cd] c0 hm
  have e' : cd' = cd := by simpa using hcd'
  subst e'
  refine ⟨cd', ?_, hn, hl.iota _⟩
  simpa using hcd

/-! ## The array that the layers' layout hands to the head -/

/-- The first half of the layers' layout writes the array tauFCw into the field tauFC. -/
theorem tauFC_of_base {h : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hy : Model.Layer.layoutBase h pc = .ok y) : y.tauFC = tauFCw := by
  unfold Model.Layer.layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  rfl

/-- Every layout of the layers that the verifier's function returns has the array tauFCw in the
field tauFC, which is what the verifier hands to the head's layout. -/
theorem tauFC_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hy : Model.Layer.layout h pc = .ok y) : y.tauFC = tauFCw := by
  unfold Model.Layer.layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  have k := tauFC_of_base h0
  exact k

#print axioms IsLut.inLut
#print axioms IsLut.of_inLut
#print axioms IsLut.pad_value
#print axioms inLut_R23
#print axioms isLut_R16
#print axioms isLut_R8
#print axioms isLut_FC
#print axioms isLut_FE
#print axioms isLut_lookups
#print axioms cl_of_layoutH
#print axioms isLut_of_layout
#print axioms tauFC_of_layout

end OnBytes.Road.Hd
