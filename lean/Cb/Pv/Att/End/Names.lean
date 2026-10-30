-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Names.lean: the names that the ten records on names of this folder call good, as
lists; the record of names whose late entries are these names and no others.

Definitions, statements and proofs. The reading forms of this folder read late entries by name: a
table's name and the entry's first cell. Ten records (Good8, LinGood and so on) say which names must
be names of late entries. This file lists these names, table by table, takes the listed names
themselves as the late entries, and shows that the ten records hold. So every late entry is an entry
of one of the 21 tables, and has a name that one of the ten records calls good. The records ask a
little more than the forms read: in the tables tVM and tVD they name all five planes of a region,
and the forms read the planes 3 and 4 there.

Main names:
  idx3, idx4: the lists of all triples and quadruples of numbers below given bounds.
  namesOf D ls lmS T: the names listed for the table T. allNames D ls lmS: all of them, with their
  tables. NameJ D ls lmS: the type of the late entries: the members of allNames. It is finite.
  lateN D ls lmS: the record of names. Every late entry's name is good (lateN_good).
  names8, names6d, names6b, names11, names12, namesM, names16, names18, namesH, names_lin: the ten
    records hold of lateN.
  mem_col, mem_row, mem_long, of_mem_col, of_mem_row, of_mem_long: what a listed name looks like.
  name_valid: a listed name is the name of a valid cell.

Limits: the tables on the softmax weights of one region (tVM, tVD) are listed with that region's
names alone, as the records ask. Nothing is said on a verifier's vector of tables: whether it
has more entries than these is not looked at.


-/
import Cb.Pv.Att.End.LastOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Inst.Model.AttSeg

/-! ### Lists of indices -/

/-- All triples of numbers below a, b, c. -/
def idx3 (a b c : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range a).flatMap fun x => (List.range b).flatMap fun y =>
    (List.range c).map fun z => (x, y, z)

theorem mem_idx3 {a b c x y z : ℕ} (hx : x < a) (hy : y < b) (hz : z < c) :
    (x, y, z) ∈ idx3 a b c :=
  List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, List.mem_flatMap.mpr ⟨y, List.mem_range.mpr hy,
    List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩⟩⟩

theorem of_mem_idx3 {a b c : ℕ} {p : ℕ × ℕ × ℕ} (h : p ∈ idx3 a b c) :
    p.1 < a ∧ p.2.1 < b ∧ p.2.2 < c := by
  obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp h
  obtain ⟨y, hy, h⟩ := List.mem_flatMap.mp h
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
  exact ⟨List.mem_range.mp hx, List.mem_range.mp hy, List.mem_range.mp hz⟩

/-- All quadruples of numbers below a, b, c, d. -/
def idx4 (a b c d : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range a).flatMap fun x => (idx3 b c d).map fun p => (x, p)

theorem mem_idx4 {a b c d x y z w : ℕ} (hx : x < a) (hy : y < b) (hz : z < c) (hw : w < d) :
    (x, y, z, w) ∈ idx4 a b c d :=
  List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ⟨_, mem_idx3 hy hz hw, rfl⟩⟩

theorem of_mem_idx4 {a b c d : ℕ} {p : ℕ × ℕ × ℕ × ℕ} (h : p ∈ idx4 a b c d) :
    p.1 < a ∧ p.2.1 < b ∧ p.2.2.1 < c ∧ p.2.2.2 < d := by
  obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact ⟨List.mem_range.mp hx, of_mem_idx3 hq⟩

/-! ### The names -/

variable (D : Dim) (ls lmS : ℕ)

/-- The first cells of the entries of a region's five planes. -/
def colNames (reg : Reg) : List Raw :=
  (idx3 5 D.nb (2 ^ (D.lReg reg - lmS))).map fun p => (Raw.c reg p.1 p.2.1 0).addX (p.2.2 * 2 ^ lmS)

/-- The first cells of the entries for a number in n limbs, a pair and a head. -/
def rowNames (n : ℕ) (mk : ℕ → ℕ → ℕ → Raw) : List Raw :=
  (idx3 n D.nb D.nG).map fun p => mk p.1 p.2.1 p.2.2

/-- The first cells of the entries for a tensor in n limbs. cnt: the pairs, or the layers. -/
def longNames (n cnt : ℕ) (mk : ℕ → ℕ → ℕ → Raw) : List Raw :=
  (idx4 n cnt D.nG (2 ^ (D.ln - ls))).map fun p => (mk p.1 p.2.1 p.2.2.1).addN (p.2.2.2 * 2 ^ ls)

/-- The names listed for a table. -/
def namesOf : AttTab → List Raw
  | .tA => colNames D lmS .M ++ colNames D lmS .D
  | .tVM => colNames D lmS .M
  | .tVD => colNames D lmS .D
  | .tMm => rowNames D 4 fun k b g => .mx k b g 0
  | .tMd => rowNames D 4 fun k b g => .mx k b g 0
  | .hT => rowNames D 4 fun k b g => .mx k b g 0
  | .hW => rowNames D 4 fun k b g => .den k b g 0
  | .hE => rowNames D 4 fun k b g => .den k b g 0
  | .hX => rowNames D D.lT fun k b g => .ib k b g 0
  | .hPi => rowNames D D.lT fun k b g => .ib k b g 0
  | .hR2 => rowNames D D.lT fun k b g => .ib k b g 0
  | .tO => longNames D ls 1 D.nb (fun _ b g => .qh b g 0 0) ++
      longNames D ls 1 D.nb fun _ b g => .qh' b g 0 0
  | .qO => longNames D ls 2 D.nb fun k b g => .out k b g 0 0
  | .tQm => longNames D ls 2 D.nb fun k b g => .qry k b g 0 0
  | .tQd => longNames D ls 2 D.nb fun k b g => .qry k b g 0 0
  | .qF => longNames D ls 2 D.nb fun k b g => .qry k b g 0 0
  | .tKm => longNames D ls 2 D.nl fun k l g => .key k l g 0 0
  | .tKd => longNames D ls 2 D.nl fun k l g => .key k l g 0 0
  | .qKx => longNames D ls 2 D.nl fun k l g => .key k l g 0 0
  | .qVM => longNames D ls 2 D.nl fun k l g => .val k l g 0 0
  | .qVD => longNames D ls 2 D.nl fun k l g => .val k l g 0 0

/-- The 21 tables. -/
def allTabs : List AttTab :=
  [.tA, .tVM, .tVD, .tMm, .tQm, .tKm, .tMd, .tQd, .tKd, .hW, .hX, .hE, .hT, .hPi, .hR2, .tO, .qO,
    .qVM, .qVD, .qF, .qKx]

theorem mem_allTabs (T : AttTab) : T ∈ allTabs := by
  cases T <;> simp [allTabs]

/-- All names, with their tables. -/
def allNames : List (AttTab × Raw) :=
  allTabs.flatMap fun T => (namesOf D ls lmS T).map fun r => (T, r)

theorem mem_allNames {T : AttTab} {r : Raw} :
    (T, r) ∈ allNames D ls lmS ↔ r ∈ namesOf D ls lmS T := by
  constructor
  · intro h
    obtain ⟨T', -, h⟩ := List.mem_flatMap.mp h
    obtain ⟨r', hr, e⟩ := List.mem_map.mp h
    cases e
    exact hr
  · intro h
    exact List.mem_flatMap.mpr ⟨T, mem_allTabs T, List.mem_map.mpr ⟨r, h, rfl⟩⟩

/-! ### What a listed name looks like -/

variable {D ls lmS}

theorem mem_col {reg : Reg} {jj b hi : ℕ} (hj : jj < 5) (hb : b < D.nb)
    (hh : hi < 2 ^ (D.lReg reg - lmS)) :
    (Raw.c reg jj b 0).addX (hi * 2 ^ lmS) ∈ colNames D lmS reg :=
  List.mem_map.mpr ⟨(jj, b, hi), mem_idx3 hj hb hh, rfl⟩

theorem of_mem_col {reg : Reg} {r : Raw} (h : r ∈ colNames D lmS reg) :
    ∃ jj b hi, jj < 5 ∧ b < D.nb ∧ hi < 2 ^ (D.lReg reg - lmS) ∧
      r = (Raw.c reg jj b 0).addX (hi * 2 ^ lmS) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2, h3⟩ := of_mem_idx3 hp
  exact ⟨_, _, _, h1, h2, h3, rfl⟩

theorem mem_row {n : ℕ} {mk : ℕ → ℕ → ℕ → Raw} {k b g : ℕ} (hk : k < n) (hb : b < D.nb)
    (hg : g < D.nG) : mk k b g ∈ rowNames D n mk :=
  List.mem_map.mpr ⟨(k, b, g), mem_idx3 hk hb hg, rfl⟩

theorem of_mem_row {n : ℕ} {mk : ℕ → ℕ → ℕ → Raw} {r : Raw} (h : r ∈ rowNames D n mk) :
    ∃ k b g, k < n ∧ b < D.nb ∧ g < D.nG ∧ r = mk k b g := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2, h3⟩ := of_mem_idx3 hp
  exact ⟨_, _, _, h1, h2, h3, rfl⟩

theorem mem_long {n cnt : ℕ} {mk : ℕ → ℕ → ℕ → Raw} {k a g ch : ℕ} (hk : k < n) (ha : a < cnt)
    (hg : g < D.nG) (hc : ch < 2 ^ (D.ln - ls)) :
    (mk k a g).addN (ch * 2 ^ ls) ∈ longNames D ls n cnt mk :=
  List.mem_map.mpr ⟨(k, a, g, ch), mem_idx4 hk ha hg hc, rfl⟩

theorem of_mem_long {n cnt : ℕ} {mk : ℕ → ℕ → ℕ → Raw} {r : Raw}
    (h : r ∈ longNames D ls n cnt mk) :
    ∃ k a g ch, k < n ∧ a < cnt ∧ g < D.nG ∧ ch < 2 ^ (D.ln - ls) ∧
      r = (mk k a g).addN (ch * 2 ^ ls) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2, h3, h4⟩ := of_mem_idx4 hp
  exact ⟨_, _, _, _, h1, h2, h3, h4, rfl⟩

/-- The layer of a pair is a layer. -/
theorem lamOf_lt {b : ℕ} (hb : b < D.nb) : D.lamOf b < D.nl :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)

/-! ### A listed name is the name of a valid cell -/

/-- The first place of a block lies below the whole. -/
theorem blk_lt {l s hi : ℕ} (hs : s ≤ l) (h : hi < 2 ^ (l - s)) : 0 + hi * 2 ^ s < 2 ^ l := by
  have e : 2 ^ l = 2 ^ (l - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  rw [Nat.zero_add, e]
  exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos s)

/-- Every listed name is valid, if there is a position and blocks are not longer than what they
divide. -/
theorem name_valid (hT : 0 < D.T) (hls : ls ≤ D.ln) (hM : lmS ≤ D.lM) (hD : lmS ≤ D.lD)
    {T : AttTab} {r : Raw} (h : r ∈ namesOf D ls lmS T) : r.Valid D := by
  have cM : ∀ {r : Raw}, r ∈ colNames D lmS .M → r.Valid D := by
    intro r hr
    obtain ⟨jj, b, hi, h1, h2, h3, rfl⟩ := of_mem_col hr
    exact ⟨h1, h2, blk_lt hM h3⟩
  have cD : ∀ {r : Raw}, r ∈ colNames D lmS .D → r.Valid D := by
    intro r hr
    obtain ⟨jj, b, hi, h1, h2, h3, rfl⟩ := of_mem_col hr
    exact ⟨h1, h2, blk_lt hD h3⟩
  have mx : ∀ {r : Raw}, r ∈ rowNames D 4 (fun k b g => .mx k b g 0) → r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, h1, h2, h3, rfl⟩ := of_mem_row hr
    exact ⟨h1, h2, h3, hT⟩
  have den : ∀ {r : Raw}, r ∈ rowNames D 4 (fun k b g => .den k b g 0) → r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, h1, h2, h3, rfl⟩ := of_mem_row hr
    exact ⟨h1, h2, h3, hT⟩
  have ib : ∀ {r : Raw}, r ∈ rowNames D D.lT (fun k b g => .ib k b g 0) → r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, h1, h2, h3, rfl⟩ := of_mem_row hr
    exact ⟨h1, h2, h3, hT⟩
  have qry : ∀ {r : Raw}, r ∈ longNames D ls 2 D.nb (fun k b g => .qry k b g 0 0) →
      r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, ch, h1, h2, h3, h4, rfl⟩ := of_mem_long hr
    exact ⟨h1, h2, h3, hT, blk_lt hls h4⟩
  have out : ∀ {r : Raw}, r ∈ longNames D ls 2 D.nb (fun k b g => .out k b g 0 0) →
      r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, ch, h1, h2, h3, h4, rfl⟩ := of_mem_long hr
    exact ⟨h1, h2, h3, hT, blk_lt hls h4⟩
  have key : ∀ {r : Raw}, r ∈ longNames D ls 2 D.nl (fun k l g => .key k l g 0 0) →
      r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, ch, h1, h2, h3, h4, rfl⟩ := of_mem_long hr
    exact ⟨h1, h2, h3, hT, blk_lt hls h4⟩
  have val : ∀ {r : Raw}, r ∈ longNames D ls 2 D.nl (fun k l g => .val k l g 0 0) →
      r.Valid D := by
    intro r hr
    obtain ⟨k, b, g, ch, h1, h2, h3, h4, rfl⟩ := of_mem_long hr
    exact ⟨h1, h2, h3, hT, blk_lt hls h4⟩
  cases T with
  | tA => exact (List.mem_append.mp h).elim cM cD
  | tVM => exact cM h
  | tVD => exact cD h
  | tMm => exact mx h
  | tMd => exact mx h
  | hT => exact mx h
  | hW => exact den h
  | hE => exact den h
  | hX => exact ib h
  | hPi => exact ib h
  | hR2 => exact ib h
  | tO =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨k, b, g, ch, -, h2, h3, h4, rfl⟩ := of_mem_long h
      exact ⟨h2, h3, hT, blk_lt hls h4⟩
    · obtain ⟨k, b, g, ch, -, h2, h3, h4, rfl⟩ := of_mem_long h
      exact ⟨h2, h3, hT, blk_lt hls h4⟩
  | qO => exact out h
  | tQm => exact qry h
  | tQd => exact qry h
  | qF => exact qry h
  | tKm => exact key h
  | tKd => exact key h
  | qKx => exact key h
  | qVM => exact val h
  | qVD => exact val h

/-! ### The record of names -/

variable (D ls lmS)

/-- The late entries: the listed names. -/
abbrev NameJ : Type := { x : AttTab × Raw // x ∈ allNames D ls lmS }

/-- There are finitely many late entries. -/
instance nameJ_fin : Fintype (NameJ D ls lmS) := inferInstance

open Classical in
/-- The record of names: a late entry is its own name. A name that is not listed is sent to j0. -/
noncomputable def lateN (j0 : NameJ D ls lmS) : LateLay AttTab (NameJ D ls lmS) where
  nm := fun j => j.1
  at' := fun x => if h : x ∈ allNames D ls lmS then ⟨x, h⟩ else j0
  good := fun x => x ∈ allNames D ls lmS
  ok := fun x hx => by rw [dif_pos hx]

/-- Every late entry's name is good, and the entry is the late entry of its name. -/
theorem lateN_good (j0 j : NameJ D ls lmS) :
    (lateN D ls lmS j0).good ((lateN D ls lmS j0).nm j) ∧
      (lateN D ls lmS j0).at' ((lateN D ls lmS j0).nm j) = j :=
  ⟨j.2, by
    show (if h : j.1 ∈ allNames D ls lmS then (⟨j.1, h⟩ : NameJ D ls lmS) else j0) = j
    rw [dif_pos j.2]⟩

variable (j0 : NameJ D ls lmS)

/-- A name of a table on single features is a member of the list of all names. T: a table whose
names are those of mk. -/
theorem in_row {T : AttTab} {n : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hT : namesOf D ls lmS T = rowNames D n mk) {k b g : ℕ} (hk : k < n) (hb : b < D.nb)
    (hg : g < D.nG) : (T, mk k b g) ∈ allNames D ls lmS :=
  (mem_allNames D ls lmS).mpr (by rw [hT]; exact mem_row hk hb hg)

theorem in_long {T : AttTab} {n cnt : ℕ} (mk : ℕ → ℕ → ℕ → Raw)
    (hT : namesOf D ls lmS T = longNames D ls n cnt mk) {k a g ch : ℕ} (hk : k < n) (ha : a < cnt)
    (hg : g < D.nG) (hc : ch < 2 ^ (D.ln - ls)) :
    (T, (mk k a g).addN (ch * 2 ^ ls)) ∈ allNames D ls lmS :=
  (mem_allNames D ls lmS).mpr (by rw [hT]; exact mem_long hk ha hg hc)

theorem in_col {T : AttTab} (reg : Reg) (hT : namesOf D ls lmS T = colNames D lmS reg)
    {jj b hi : ℕ} (hj : jj < 5) (hb : b < D.nb) (hh : hi < 2 ^ (D.lReg reg - lmS)) :
    (T, (Raw.c reg jj b 0).addX (hi * 2 ^ lmS)) ∈ allNames D ls lmS :=
  (mem_allNames D ls lmS).mpr (by rw [hT]; exact mem_col hj hb hh)

theorem names8 : Good8 D ls (lateN D ls lmS j0) where
  hE := fun _ hb _ hg _ hk => in_row D ls lmS (fun k b g => .den k b g 0) rfl hk hb hg
  qO := fun _ hb _ hg _ hc _ hk => in_long D ls lmS (fun k b g => .out k b g 0 0) rfl hk hb hg hc

theorem names6d : Good6d D ls (lateN D ls lmS j0) where
  tQ := fun _ hb _ hg _ hc _ hk => in_long D ls lmS (fun k b g => .qry k b g 0 0) rfl hk hb hg hc
  tK := fun _ hb _ hg _ hc _ hk =>
    in_long D ls lmS (fun k l g => .key k l g 0 0) rfl hk (lamOf_lt hb) hg hc

theorem names6b : Good6b D ls (lateN D ls lmS j0) where
  tQ := fun _ hb _ hg _ hc _ hk => in_long D ls lmS (fun k b g => .qry k b g 0 0) rfl hk hb hg hc
  tK := fun _ hb _ hg _ hc _ hk =>
    in_long D ls lmS (fun k l g => .key k l g 0 0) rfl hk (lamOf_lt hb) hg hc

theorem names11 : Good11 D ls lmS (lateN D ls lmS j0) where
  tVM := fun _ hb _ hj _ hh => in_col D ls lmS .M rfl hj hb hh
  qVM := fun _ hb _ hg _ hc _ hk =>
    in_long D ls lmS (fun k l g => .val k l g 0 0) rfl hk (lamOf_lt hb) hg hc

theorem names12 : Good12 D ls lmS (lateN D ls lmS j0) where
  tVD := fun _ hb _ hj _ hh => in_col D ls lmS .D rfl hj hb hh
  qVD := fun _ hb _ hg _ hc _ hk =>
    in_long D ls lmS (fun k l g => .val k l g 0 0) rfl hk (lamOf_lt hb) hg hc

theorem namesM : GoodM D (lateN D ls lmS j0) where
  hT := fun _ hb _ hg _ hk => in_row D ls lmS (fun k b g => .mx k b g 0) rfl hk hb hg

theorem names16 : Good16 D ls (lateN D ls lmS j0) where
  qF := fun _ hb _ hg _ hc _ hk => in_long D ls lmS (fun k b g => .qry k b g 0 0) rfl hk hb hg hc

theorem names18 : Good18 D ls (lateN D ls lmS j0) where
  qKx := fun _ hl _ hg _ hc _ hk => in_long D ls lmS (fun k l g => .key k l g 0 0) rfl hk hl hg hc
  hPi := fun _ hb _ hk _ hg => in_row D ls lmS (fun k b g => .ib k b g 0) rfl hk hb hg

theorem namesH : GoodH D (lateN D ls lmS j0) where
  hR2 := fun _ hb _ hk _ hg => in_row D ls lmS (fun k b g => .ib k b g 0) rfl hk hb hg

theorem names_lin : LinGood D ls lmS (lateN D ls lmS j0) where
  tA := fun u jj b hu hj hb hi hh => by
    refine (mem_allNames D ls lmS).mpr ?_
    cases u with
    | m1 => exact List.mem_append_left _ (mem_col (reg := .M) hj hb hh)
    | m2 => exact List.mem_append_left _ (mem_col (reg := .M) hj hb hh)
    | d1 => exact List.mem_append_right _ (mem_col (reg := .D) hj hb hh)
    | d2 => exact List.mem_append_right _ (mem_col (reg := .D) hj hb hh)
    | w3 => exact hu.elim
    | x3 => exact hu.elim
    | f4 => exact hu.elim
  tMm := fun _ hb _ hg _ hk => in_row D ls lmS (fun k b g => .mx k b g 0) rfl hk hb hg
  tMd := fun _ hb _ hg _ hk => in_row D ls lmS (fun k b g => .mx k b g 0) rfl hk hb hg
  hW := fun _ hb _ hg _ hk => in_row D ls lmS (fun k b g => .den k b g 0) rfl hk hb hg
  hX := fun _ hk _ hb _ hg => in_row D ls lmS (fun k b g => .ib k b g 0) rfl hk hb hg
  tO := fun _ hb _ hg _ hc =>
    ⟨(mem_allNames D ls lmS).mpr (List.mem_append_left _
        (mem_long (mk := fun _ b g => .qh b g 0 0) (k := 0) Nat.one_pos hb hg hc)),
      (mem_allNames D ls lmS).mpr (List.mem_append_right _
        (mem_long (mk := fun _ b g => .qh' b g 0 0) (k := 0) Nat.one_pos hb hg hc))⟩

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.name_valid
#print axioms Cb.Pv.Att.End.lateN_good
#print axioms Cb.Pv.Att.End.names_lin
#print axioms Cb.Pv.Att.End.names18
