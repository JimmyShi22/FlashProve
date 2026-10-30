-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWLay.lean: the verifier's layout of the committed matrix of weights is the
library's.

The model's weights are committed as one matrix W. The verifier lays them out in units, one for each
weight matrix, and gives each index group of a unit some bits of the number of a column
(WsLay.place, add, addLayer, build and wsLayOf in OnBytes/Model/Weights.lean). The library has a
layout of its own (units, bits, split, off, rows, place in Inst/Model/Layout.lean), through which
its relation reads the weights in W. This file shows that the two are one.

What is compared with what: the verifier's Lean text against the library's Lean text. Neither is
compared with the C++ verifier or with a committed file.

Main statements.
 - unitOK_of_layout: if wsLayOf returns a layout, for a model with or without mixtures of experts,
   every unit of it has the properties of UnitOK (Johnson/Road/FormsKeysWOk.lean) and lies within
   the layout's rows.
 - layout_eq: for a shape of the weights and parameters of the library that agree in nine numbers
   (SizedW), and a model with mixtures of experts: if wsLayOf returns a layout, its list of units is
   the library's, unit by unit and group by group, and cellOf (Johnson/Road/FormsKeysWm.lean) is the
   library's place, for every digit and every list of indices.
 - unitOf_eq: under the same hypotheses, the number under which the verifier finds the unit of a
   kind and a layer is the number that the library's order gives it.
 - z_of_layout: in a layout that wsLayOf returns, the number z of a group of class 'E' is the
   library's number sOf of low bits of the group's size.
 - unit_at: under the hypotheses of layout_eq, the unit at a number, written out: an ask of the list
   layerAsks, placed.
 - unit_groups, unit_names, unit_cls: under the hypotheses of layout_eq, the names and the classes
   of the groups of the unit of a kind and a layer. The verifier's claims pick a factor by a group's
   name; the library's coordinates have no names.

How. placeP, unitP and unitsFrom write what place and add return without their refusals (place_ok,
add_ok). Adds says that a layout comes from another by adding a list of asked units; addLayer, the
fold over the layers and build are walked once (addLayer_adds, foldl_adds, build_ok). What build's
tests leave is BuildOK: from it every group of class 'E' has a size from 1 to 2^24, for which the
verifier's loop oddPart counts the factors two as the library's sOf does (oddPart_eq, sAux_fuel,
raw_E). grp_lib compares one placed group with the library's coordinate.

The hypotheses can be met: sized_made, with a #guard that wsLayOf returns for the made-up shape. A
"#guard" is evaluated when the file is compiled; it is a run and no theorem. Runs of both layouts
side by side at other made-up numbers are in Johnson/Road/FormsKeysRunW.lean.

What is not claimed. Nothing is said for a model without mixtures of experts but unitOK_of_layout:
the library's list of units has experts in every odd layer. cellOf is a definition of
Johnson/Road/FormsKeysWm.lean: that the verifier's settling of a claim (wsGamma, wsEpsT) reaches the
cell cellOf is not shown here. Nothing is said on how W is committed, opened or decoded, on the
ranges of its entries, or on any claim. The program does not import this file.
-/
import Johnson.Road.FormsKeysWOk
import Johnson.Road.FormsKeysPos

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (WsShape WsGrp WsUnit WsLay wsLayOf wsSetMoe clog2 wsRowsLog tokenFactorUnits)
open Inst.Model (Params hasExperts)
open Inst.Model.Layout (Kind Coord UnitS sAux sOf tOf lOf hU uQK uV uO uGU uD uGUr uDr uR uEmb uH)
open Inst.Model.Layout renaming bits → bitsLib, col → colLib, row → rowLib, rows → rowsLib,
  off → offLib, units → unitsLib, first → firstLib, place → placeLib, layerUnits → layerUnitsLib,
  split → splitLib

/-! ## Steps that may refuse -/

/-- If a step and what follows it return a value, the step has returned one, and what follows
returns the value from it. -/
theorem okBind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- If a test that refuses under the condition c, and what follows it, return a value, then c does
not hold, and what follows returns the value. -/
theorem okGuard {β : Type} {c : Prop} [Decidable c] {e : String} {jp : PUnit → Except String β}
    {y : β} (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-! ## The low bits of a size -/

/-- The library's count of the factors two of a size does not depend on the bound of its steps, as
soon as two to the bound is above the size. -/
theorem sAux_fuel : ∀ (a b R : ℕ), 0 < R → R < 2 ^ a → R < 2 ^ b → sAux a R = sAux b R
  | 0, _, R, h0, ha, _ => by
    rw [pow_zero] at ha
    omega
  | _ + 1, 0, R, h0, _, hb => by
    rw [pow_zero] at hb
    omega
  | a + 1, b + 1, R, h0, ha, hb => by
    rw [pow_succ] at ha hb
    simp only [sAux]
    by_cases h : R % 2 = 0 ∧ R ≠ 0
    · rw [if_pos h, if_pos h, sAux_fuel a b (R / 2) (by omega) (by omega) (by omega)]
    · rw [if_neg h, if_neg h]

/-- Two to that count divides the size. -/
theorem two_pow_sAux_dvd : ∀ n R : ℕ, 2 ^ sAux n R ∣ R
  | 0, R => by simp [sAux]
  | n + 1, R => by
    simp only [sAux]
    by_cases h : R % 2 = 0 ∧ R ≠ 0
    · rw [if_pos h, pow_succ]
      obtain ⟨q, hq⟩ := two_pow_sAux_dvd n (R / 2)
      exact ⟨q, by
        have e : R = R / 2 * 2 := by omega
        rw [e, hq]
        have e2 : 2 ^ sAux n (2 ^ sAux n (R / 2) * q * 2 / 2) = 2 ^ sAux n (R / 2) := by
          rw [Nat.mul_div_cancel _ (by norm_num), ← hq]
        rw [e2]
        ring⟩
    · rw [if_neg h]
      simp

/-- The verifier's loop that takes the factors two out of a size, in the library's count. -/
theorem oddPart_eq : ∀ (k o z : ℕ), o ≠ 0 →
    WsLay.oddPart k o z = (o / 2 ^ sAux k o, z + sAux k o)
  | 0, o, z, _ => by simp [WsLay.oddPart, sAux]
  | k + 1, o, z, h => by
    by_cases he : o % 2 = 0
    · have h1 : (o % 2 == 0) = true := by simp [he]
      have h2 : o % 2 = 0 ∧ o ≠ 0 := ⟨he, h⟩
      have e : sAux (k + 1) o = sAux k (o / 2) + 1 := by
        simp only [sAux]
        rw [if_pos h2]
      rw [WsLay.oddPart, if_pos h1, oddPart_eq k (o / 2) (z + 1) (by omega), e, pow_succ,
        Nat.div_div_eq_div_mul, Nat.mul_comm 2, Nat.add_assoc, Nat.add_comm 1]
    · have h1 : ¬ (o % 2 == 0) = true := by simp [he]
      have h2 : ¬ (o % 2 = 0 ∧ o ≠ 0) := fun x => he x.1
      have e : sAux (k + 1) o = 0 := by
        simp only [sAux]
        rw [if_neg h2]
      rw [WsLay.oddPart, if_neg h1, e]
      simp

/-! ## A group before it is placed -/

/-- A group as the layout's list of units writes it: of class 'E' with z the library's number of low
bits of the size and o the size without its factors two; or of class 'A'. -/
def Raw (x : WsGrp) : Prop :=
  (x.cls = 'E' ∧ x.z = sOf x.R ∧ x.o = x.R / 2 ^ sOf x.R) ∨ x.cls = 'A'

/-- A group that E_ makes, of a size from 1 to below 2^64. -/
theorem raw_E (n : String) {R : ℕ} (high : Bool) (h0 : 0 < R) (h : R < 2 ^ 64) :
    Raw (WsLay.E_ n R high) := by
  have e : WsLay.oddPart 64 R 0 = (R / 2 ^ sOf R, sOf R) := by
    rw [oddPart_eq 64 R 0 (by omega), Nat.zero_add, sAux_fuel 64 R R h0 h Nat.lt_two_pow_self]
    rfl
  refine Or.inl ⟨rfl, ?_, ?_⟩
  · show (WsLay.oddPart 64 R 0).2 = sOf R
    rw [e]
  · show (WsLay.oddPart 64 R 0).1 = R / 2 ^ sOf R
    rw [e]

/-- A group that A_ makes. -/
theorem raw_A (n : String) (R : ℕ) : Raw (WsLay.A_ n R) := Or.inr rfl

/-- The library's coordinate for a group: its size, and low, high or whole for its class. -/
def coordOf (x : WsGrp) : Coord :=
  ⟨x.R, if x.cls == 'E' then (if x.high then Kind.high else Kind.low) else Kind.whole⟩

/-! ## The placing of a unit's groups, without its refusal -/

/-- The column bits that a group takes if left bits are free. -/
def tP (x : WsGrp) (left : ℕ) : ℕ :=
  if x.cls == 'E' then min x.z left else if clog2 x.R ≤ left then clog2 x.R else 0

/-- What the group then leaves to the rows. -/
def lP (x : WsGrp) (left : ℕ) : ℕ :=
  if x.cls == 'E' then x.R / 2 ^ tP x left
  else if (x.cls == 'A' && decide (0 < tP x left)) then 1 else x.R

/-- The group as it is placed, with cb as its first column bit. -/
def yP (x : WsGrp) (left cb : ℕ) : WsGrp :=
  { name := x.name, R := x.R, o := x.o, left := lP x left, cls := x.cls, high := x.high, z := x.z,
    t := tP x left, cb0 := cb }

/-- The groups of a unit as they are placed. -/
def placeP : List WsGrp → ℕ → ℕ → List WsGrp
  | [], _, _ => []
  | x :: g, left, cb => yP x left cb :: placeP g (left - tP x left) (cb + tP x left)

/-- What the verifier's place returns, if it returns: the groups as placeP places them, the column
bits counted on from cb, and the rows multiplied by what the groups leave. -/
theorem place_ok : ∀ (g : List WsGrp) (left cb rws : ℕ) (r : List WsGrp × ℕ × ℕ),
    WsLay.place g left cb rws = .ok r →
      r.1 = placeP g left cb ∧ r.2.1 = cb + ((placeP g left cb).map (·.t)).sum ∧
        r.2.2 = rws * ((placeP g left cb).map (·.left)).prod
  | [], left, cb, rws, r, h => by
    have e : ([], cb, rws) = r := Except.ok.inj h
    subst e
    simp [placeP]
  | x :: g, left, cb, rws, r, h => by
    have h' : (if 2 ^ wsRowsLog < rws * lP x left then throw "w-shape-mW"
        else WsLay.place g (left - tP x left) (cb + tP x left) (rws * lP x left) >>= fun r' =>
          pure (yP x left cb :: r'.1, r'.2)) = Except.ok r := h
    by_cases hc : 2 ^ wsRowsLog < rws * lP x left
    · rw [if_pos hc] at h'
      cases h'
    · rw [if_neg hc] at h'
      obtain ⟨r', h1, h2⟩ := okBind h'
      obtain ⟨i1, i2, i3⟩ := place_ok g _ _ _ r' h1
      have e : (yP x left cb :: r'.1, r'.2) = r := Except.ok.inj h2
      subst e
      refine ⟨?_, ?_, ?_⟩
      · show yP x left cb :: r'.1 = yP x left cb :: placeP g (left - tP x left) (cb + tP x left)
        rw [i1]
      · show r'.2.1 = cb + ((yP x left cb :: placeP g (left - tP x left) (cb + tP x left)).map
          (·.t)).sum
        rw [i2, List.map_cons, List.sum_cons, Nat.add_assoc]
        rfl
      · show r'.2.2 = rws * ((yP x left cb :: placeP g (left - tP x left) (cb + tP x left)).map
          (·.left)).prod
        rw [i3, List.map_cons, List.prod_cons, Nat.mul_assoc]
        rfl

/-- A group takes no more column bits than are free. -/
theorem tP_le (x : WsGrp) (left : ℕ) : tP x left ≤ left := by
  unfold tP
  split_ifs with h1 h2
  · exact Nat.min_le_right _ _
  · exact h2
  · exact Nat.zero_le _

/-- Nor do all groups of a unit together. -/
theorem sum_t_le : ∀ (g : List WsGrp) (left cb : ℕ), ((placeP g left cb).map (·.t)).sum ≤ left
  | [], _, _ => by simp [placeP]
  | x :: g, left, cb => by
    have h1 := tP_le x left
    have h2 := sum_t_le g (left - tP x left) (cb + tP x left)
    show ((yP x left cb :: placeP g (left - tP x left) (cb + tP x left)).map (·.t)).sum ≤ left
    rw [List.map_cons, List.sum_cons]
    show tP x left + _ ≤ left
    omega

/-- The placed groups' column bits follow each other. -/
theorem runs_placeP : ∀ (g : List WsGrp) (left cb : ℕ), Runs (placeP g left cb) cb
  | [], _, _ => trivial
  | x :: g, left, cb => ⟨rfl, runs_placeP g (left - tP x left) (cb + tP x left)⟩

/-- A placed group's numbers fit each other. -/
theorem grpOK_yP {x : WsGrp} (hx : Raw x) (left cb : ℕ) : GrpOK (yP x left cb) := by
  rcases hx with ⟨hE, hz, ho⟩ | hA
  · have e : (x.cls == 'E') = true := by rw [hE]; rfl
    refine Or.inl ⟨hE, ?_, ?_, ?_⟩
    · show x.R = x.o * 2 ^ x.z
      rw [ho, hz]
      exact (Nat.div_mul_cancel (two_pow_sAux_dvd x.R x.R)).symm
    · show tP x left ≤ x.z
      unfold tP
      rw [if_pos e]
      exact Nat.min_le_left _ _
    · show lP x left = x.R / 2 ^ tP x left
      unfold lP
      rw [if_pos e]
  · have e : ¬ (x.cls == 'E') = true := by rw [hA]; decide
    have e2 : (x.cls == 'A') = true := by rw [hA]; rfl
    refine Or.inr ⟨hA, ?_, ?_⟩
    · show tP x left = clog2 x.R ∨ tP x left = 0
      unfold tP
      rw [if_neg e]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · show lP x left = if 0 < tP x left then 1 else x.R
      unfold lP
      rw [if_neg e, e2]
      simp

/-- So do all placed groups of a unit. -/
theorem grpOK_placeP : ∀ (g : List WsGrp) (left cb : ℕ), (∀ x ∈ g, Raw x) →
    ∀ y ∈ placeP g left cb, GrpOK y
  | [], _, _, _, y, hy => by cases hy
  | x :: g, left, cb, h, y, hy => by
    rcases List.mem_cons.mp hy with e | hy
    · rw [e]
      exact grpOK_yP (h x List.mem_cons_self) left cb
    · exact grpOK_placeP g _ _ (fun z hz => h z (List.mem_cons_of_mem _ hz)) y hy

/-! ## A placed group against the library's coordinate -/

/-- The bits that a group takes, what it leaves to the rows, and how it cuts an index are the
library's for the group's coordinate. -/
theorem grp_lib {x : WsGrp} (hx : Raw x) (left cb : ℕ) :
    tP x left = tOf (coordOf x) left ∧ lP x left = lOf (coordOf x) (tP x left) ∧
      ∀ v, splitG (yP x left cb) v = Inst.Model.Layout.split (coordOf x) (tP x left) v := by
  rcases hx with ⟨hE, hz, _⟩ | hA
  · have e : (x.cls == 'E') = true := by rw [hE]; rfl
    have et : tP x left = min (sOf x.R) left := by
      unfold tP
      rw [if_pos e, hz]
    have el : lP x left = x.R / 2 ^ tP x left := by
      unfold lP
      rw [if_pos e]
    cases hh : x.high with
    | false =>
      have hc : coordOf x = ⟨x.R, Kind.low⟩ := by
        unfold coordOf
        rw [if_pos e, hh]
        rfl
      rw [hc]
      refine ⟨et, el, fun v => ?_⟩
      show (if (x.cls == 'E') = true then
        (if x.high = true then _ else (v % 2 ^ tP x left, v / 2 ^ tP x left)) else _) = _
      rw [if_pos e, if_neg (by rw [hh]; decide)]
      rfl
    | true =>
      have hc : coordOf x = ⟨x.R, Kind.high⟩ := by
        unfold coordOf
        rw [if_pos e, hh]
        rfl
      rw [hc]
      refine ⟨et, el, fun v => ?_⟩
      show (if (x.cls == 'E') = true then
        (if x.high = true then
          (v / 2 ^ (x.z - tP x left) % 2 ^ tP x left,
            v / 2 ^ x.z * 2 ^ (x.z - tP x left) + v % 2 ^ (x.z - tP x left)) else _) else _) = _
      rw [if_pos e, if_pos hh, hz]
      rfl
  · have e : ¬ (x.cls == 'E') = true := by rw [hA]; decide
    have e2 : (x.cls == 'A') = true := by rw [hA]; rfl
    have hc : coordOf x = ⟨x.R, Kind.whole⟩ := by
      unfold coordOf
      rw [if_neg e]
    rw [hc]
    refine ⟨?_, ?_, fun v => ?_⟩
    · unfold tP
      rw [if_neg e]
      show _ = if Nat.clog 2 x.R ≤ left then Nat.clog 2 x.R else 0
      rw [show clog2 x.R = Nat.clog 2 x.R from ceilLog2_eq_clog x.R]
    · unfold lP
      rw [if_neg e, e2]
      show _ = if 0 < tP x left then 1 else x.R
      simp
    · show (if (x.cls == 'E') = true then _ else
        (if (x.cls == 'A' && decide (0 < tP x left)) = true then (v, 0) else (0, v))) =
          if 0 < tP x left then (v, 0) else (0, v)
      rw [if_neg e, e2]
      simp

/-- The bits that the placed groups take are the library's list of bits. -/
theorem bits_placeP : ∀ (g : List WsGrp) (left cb : ℕ), (∀ x ∈ g, Raw x) →
    (placeP g left cb).map (·.t) = bitsLib (g.map coordOf) left
  | [], _, _, _ => rfl
  | x :: g, left, cb, h => by
    have e1 := (grp_lib (h x List.mem_cons_self) left cb).1
    have ih := bits_placeP g (left - tP x left) (cb + tP x left)
      fun z hz => h z (List.mem_cons_of_mem _ hz)
    show tP x left :: (placeP g (left - tP x left) (cb + tP x left)).map (·.t) =
      tOf (coordOf x) left :: bitsLib (g.map coordOf) (left - tOf (coordOf x) left)
    rw [← e1, ih]

/-- What the placed groups leave to the rows is what the library's coordinates leave. -/
theorem lefts_placeP : ∀ (g : List WsGrp) (left cb : ℕ), (∀ x ∈ g, Raw x) →
    (placeP g left cb).map (·.left) =
      ((g.map coordOf).zip (bitsLib (g.map coordOf) left)).map fun ct => lOf ct.1 ct.2
  | [], _, _, _ => rfl
  | x :: g, left, cb, h => by
    obtain ⟨e1, e2, _⟩ := grp_lib (h x List.mem_cons_self) left cb
    have ih := lefts_placeP g (left - tP x left) (cb + tP x left)
      fun z hz => h z (List.mem_cons_of_mem _ hz)
    show lP x left :: (placeP g (left - tP x left) (cb + tP x left)).map (·.left) =
      lOf (coordOf x) (tOf (coordOf x) left) ::
        ((g.map coordOf).zip (bitsLib (g.map coordOf) (left - tOf (coordOf x) left))).map
          fun ct => lOf ct.1 ct.2
    rw [← e1, ← e2, ih]

/-- The row within the unit is the library's, for every list of indices. -/
theorem rowIn_placeP : ∀ (g : List WsGrp) (left cb : ℕ) (idx : List ℕ) (q : ℕ),
    (∀ x ∈ g, Raw x) →
      rowIn ((placeP g left cb).zip idx) q =
        rowLib q (g.map coordOf) (bitsLib (g.map coordOf) left) idx
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, _, _ => rfl
  | _ :: _, _, _, [], _, _ => rfl
  | x :: g, left, cb, v :: idx, q, h => by
    obtain ⟨e1, e2, e3⟩ := grp_lib (h x List.mem_cons_self) left cb
    have ih := rowIn_placeP g (left - tP x left) (cb + tP x left) idx q
      fun z hz => h z (List.mem_cons_of_mem _ hz)
    show rowIn ((placeP g (left - tP x left) (cb + tP x left)).zip idx) q * lP x left +
        (splitG (yP x left cb) v).2 =
      (splitLib (coordOf x) (tOf (coordOf x) left) v).2 + lOf (coordOf x) (tOf (coordOf x) left) *
        rowLib q (g.map coordOf) (bitsLib (g.map coordOf) (left - tOf (coordOf x) left)) idx
    rw [← e1, ← e2, ← e3 v, ih, Nat.add_comm, Nat.mul_comm]

/-- The column is the library's, moved up by the first column bit, for every list of indices. -/
theorem colIn_placeP : ∀ (g : List WsGrp) (left cb : ℕ) (idx : List ℕ), (∀ x ∈ g, Raw x) →
    colIn ((placeP g left cb).zip idx) =
      2 ^ cb * colLib (g.map coordOf) (bitsLib (g.map coordOf) left) idx
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, _ => rfl
  | _ :: _, _, _, [], _ => rfl
  | x :: g, left, cb, v :: idx, h => by
    obtain ⟨e1, _, e3⟩ := grp_lib (h x List.mem_cons_self) left cb
    have ih := colIn_placeP g (left - tP x left) (cb + tP x left) idx
      fun z hz => h z (List.mem_cons_of_mem _ hz)
    show (splitG (yP x left cb) v).1 * 2 ^ cb +
        colIn ((placeP g (left - tP x left) (cb + tP x left)).zip idx) =
      2 ^ cb * ((splitLib (coordOf x) (tOf (coordOf x) left) v).1 + 2 ^ tOf (coordOf x) left *
        colLib (g.map coordOf) (bitsLib (g.map coordOf) (left - tOf (coordOf x) left)) idx)
    rw [← e1, ← e3 v, ih, pow_add]
    ring

/-! ## The list of units -/

/-- What the layout is asked to add as one unit: the kind, the layer, the digits, the groups. -/
structure AskW where
  /-- the kind of weight matrix -/
  X : ℕ
  /-- the layer -/
  l : ℕ
  /-- the number of digits -/
  nlw : ℕ
  /-- the groups, before they are placed -/
  g : List WsGrp

/-- The library's unit for an ask. -/
def unitS (a : AskW) : UnitS := ⟨a.g.map coordOf, a.nlw⟩

/-- The rows of the unit, with lk column bits. -/
def rowsP (lk : ℕ) (a : AskW) : ℕ := a.nlw * ((placeP a.g lk 0).map (·.left)).prod

/-- The unit as the layout adds it, with o as its first row. -/
def unitP (lk o : ℕ) (a : AskW) : WsUnit :=
  { X := a.X, l := a.l, nlw := a.nlw, ncb := 0 + ((placeP a.g lk 0).map (·.t)).sum,
    g := placeP a.g lk 0, rows := rowsP lk a, off := o }

/-- The units for a list of asks, from row o on. -/
def unitsFrom (lk : ℕ) : ℕ → List AskW → List WsUnit
  | _, [] => []
  | o, a :: as => unitP lk o a :: unitsFrom lk (o + rowsP lk a) as

/-- The first row after them. -/
def endFrom (lk : ℕ) : ℕ → List AskW → ℕ
  | o, [] => o
  | o, a :: as => endFrom lk (o + rowsP lk a) as

/-- What the verifier's add returns, if it returns. -/
theorem add_ok {lay lay' : WsLay} {X l nlw : ℕ} {g : List WsGrp}
    (h : lay.add X l nlw g = .ok lay') :
    lay' = { lk := lay.lk, m0 := lay.m0 + rowsP lay.lk ⟨X, l, nlw, g⟩,
             U := lay.U.push (unitP lay.lk lay.m0 ⟨X, l, nlw, g⟩) } := by
  unfold WsLay.add at h
  obtain ⟨r, hr, h2⟩ := okBind h
  obtain ⟨_, h3⟩ := okGuard h2
  obtain ⟨p1, p2, p3⟩ := place_ok _ _ _ _ r hr
  have e : ({ lk := lay.lk, m0 := lay.m0 + r.2.2,
              U := lay.U.push { X := X, l := l, nlw := nlw, ncb := r.2.1, g := r.1, rows := r.2.2,
                                off := lay.m0 } } : WsLay) = lay' := Except.ok.inj h3
  rw [p1, p2, p3] at e
  exact e.symm

/-- The layout lay' comes from lay by adding the asked units one after the other, none refused. -/
inductive Adds : List AskW → WsLay → WsLay → Prop
  | nil (lay : WsLay) : Adds [] lay lay
  | cons {a : AskW} {as : List AskW} {lay m lay' : WsLay} :
    lay.add a.X a.l a.nlw a.g = .ok m → Adds as m lay' → Adds (a :: as) lay lay'

/-- Two runs of additions, one after the other. -/
theorem Adds.append {as bs : List AskW} {lay m lay' : WsLay} (h1 : Adds as lay m)
    (h2 : Adds bs m lay') : Adds (as ++ bs) lay lay' := by
  induction h1 with
  | nil _ => exact h2
  | cons ha _ ih => exact Adds.cons ha (ih h2)

/-- What a run of additions leaves: the column bits are kept; the units are appended as unitsFrom
lists them; the number of rows is the first row after them. -/
theorem adds_spec {as : List AskW} {lay lay' : WsLay} (h : Adds as lay lay') :
    lay'.lk = lay.lk ∧ lay'.U.toList = lay.U.toList ++ unitsFrom lay.lk lay.m0 as ∧
      lay'.m0 = endFrom lay.lk lay.m0 as := by
  induction h with
  | nil lay => exact ⟨rfl, by simp [unitsFrom], rfl⟩
  | @cons a as lay m lay' ha _ ih =>
    have e := add_ok ha
    subst e
    obtain ⟨i1, i2, i3⟩ := ih
    refine ⟨i1, ?_, i3⟩
    rw [i2]
    show (lay.U.push (unitP lay.lk lay.m0 a)).toList ++
        unitsFrom lay.lk (lay.m0 + rowsP lay.lk a) as =
      lay.U.toList ++ (unitP lay.lk lay.m0 a :: unitsFrom lay.lk (lay.m0 + rowsP lay.lk a) as)
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- Unit number n of the list: the ask number n, placed, from the row after the rows of the asks
before it. -/
theorem unitsFrom_get (lk : ℕ) : ∀ (as : List AskW) (o n : ℕ) (a : AskW), as[n]? = some a →
    (unitsFrom lk o as)[n]? = some (unitP lk (o + ((as.take n).map (rowsP lk)).sum) a)
  | [], _, _, _, h => by simp at h
  | b :: as, o, 0, a, h => by
    have e : b = a := by simpa using h
    subst e
    simp [unitsFrom]
  | b :: as, o, n + 1, a, h => by
    have h' : as[n]? = some a := by simpa using h
    have ih := unitsFrom_get lk as (o + rowsP lk b) n a h'
    show (unitP lk o b :: unitsFrom lk (o + rowsP lk b) as)[n + 1]? = _
    rw [List.getElem?_cons_succ, ih, List.take_succ_cons, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- As many units as asks. -/
theorem unitsFrom_length (lk : ℕ) : ∀ (as : List AskW) (o : ℕ),
    (unitsFrom lk o as).length = as.length
  | [], _ => rfl
  | a :: as, o => by
    show (unitsFrom lk (o + rowsP lk a) as).length + 1 = as.length + 1
    rw [unitsFrom_length lk as]

/-- The first row after the units: the rows of all asks on top of o. -/
theorem endFrom_eq (lk : ℕ) : ∀ (as : List AskW) (o : ℕ),
    endFrom lk o as = o + (as.map (rowsP lk)).sum
  | [], o => by simp [endFrom]
  | a :: as, o => by
    show endFrom lk (o + rowsP lk a) as = _
    rw [endFrom_eq lk as, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The rows of a unit are the library's. -/
theorem rowsP_lib (lk : ℕ) {a : AskW} (h : ∀ x ∈ a.g, Raw x) :
    rowsP lk a = rowsLib lk (unitS a) := by
  show a.nlw * ((placeP a.g lk 0).map (·.left)).prod =
    a.nlw *
      (((a.g.map coordOf).zip (bitsLib (a.g.map coordOf) lk)).map fun ct => lOf ct.1 ct.2).prod
  rw [lefts_placeP a.g lk 0 h]

/-- The rows of the asks before number n are the library's first row of unit number n. -/
theorem sum_rowsP_lib (lk : ℕ) {as : List AskW} (h : ∀ a ∈ as, ∀ x ∈ a.g, Raw x) (n : ℕ) :
    ((as.take n).map (rowsP lk)).sum = offLib lk (as.map unitS) n := by
  show _ = (((as.map unitS).take n).map (rowsLib lk)).sum
  rw [← List.map_take, List.map_map]
  congr 1
  exact List.map_congr_left fun a ha => rowsP_lib lk (h a (List.mem_of_mem_take ha))

/-- The cell of a digit in a placed unit is the library's place, for every digit and every list of
indices. us, n: any list of units and any number for which the unit's first row is the library's. -/
theorem cellOf_lib (lk o : ℕ) {a : AskW} (h : ∀ x ∈ a.g, Raw x) (us : List UnitS) (n : ℕ)
    (ho : o = offLib lk us n) (q : ℕ) (idx : List ℕ) :
    cellOf (unitP lk o a) q idx = placeLib lk us n (unitS a) q idx := by
  show (o + rowIn ((placeP a.g lk 0).zip idx) q, colIn ((placeP a.g lk 0).zip idx)) =
    (offLib lk us n + rowLib q (a.g.map coordOf) (bitsLib (a.g.map coordOf) lk) idx,
      colLib (a.g.map coordOf) (bitsLib (a.g.map coordOf) lk) idx)
  rw [rowIn_placeP a.g lk 0 idx q h, colIn_placeP a.g lk 0 idx h, ho, pow_zero, Nat.one_mul]

/-- A placed unit has the properties of UnitOK. -/
theorem unitOK_unitP (lk o : ℕ) {a : AskW} (h : ∀ x ∈ a.g, Raw x) : UnitOK lk (unitP lk o a) where
  grp := grpOK_placeP a.g lk 0 h
  runs := runs_placeP a.g lk 0
  ncb := Nat.zero_add _
  le := by
    show 0 + ((placeP a.g lk 0).map (·.t)).sum ≤ lk
    rw [Nat.zero_add]
    exact sum_t_le a.g lk 0
  rows := rfl

/-! ## The verifier's list of units -/

/-- The units of layer l, as addLayer asks for them. -/
def layerAsks (s : WsShape) (l : ℕ) : List AskW :=
  [⟨0, l, 2, [WsLay.A_ "hd" 64, WsLay.A_ "cd" s.dh, WsLay.E_ "kk" s.d false]⟩,
   ⟨1, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.dkv true]⟩,
   ⟨2, l, 2, [WsLay.E_ "kk" s.dq false, WsLay.E_ "x" s.d true]⟩] ++
  if s.moe.getD l false = true then
    [⟨5, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.fe true]⟩,
     ⟨6, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.fe true]⟩,
     ⟨7, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "e" s.NE false, WsLay.E_ "x" s.fe true]⟩,
     ⟨8, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "e" s.NE false, WsLay.E_ "x" s.fe true]⟩,
     ⟨9, l, 2, [WsLay.E_ "kk" s.fe false, WsLay.E_ "x" s.d true]⟩,
     ⟨10, l, 2, [WsLay.E_ "kk" s.fe false, WsLay.E_ "e" s.NE false, WsLay.E_ "x" s.d true]⟩,
     ⟨11, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.NE true]⟩]
  else
    [⟨3, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.f true]⟩,
     ⟨4, l, 2, [WsLay.E_ "kk" s.d false, WsLay.E_ "x" s.f true]⟩,
     ⟨9, l, 2, [WsLay.E_ "kk" s.f false, WsLay.E_ "x" s.d true]⟩]

/-- All units: those of the layers, then the embedding's and the head's. -/
def allAsks (s : WsShape) : List AskW :=
  (List.range s.L).flatMap (layerAsks s) ++
    [⟨12, s.L, 4, [WsLay.A_ "v" s.V, WsLay.E_ "x" s.d true]⟩,
     ⟨13, s.L, 2, [WsLay.A_ "x" s.V, WsLay.E_ "kk" s.d false]⟩]

/-- If addLayer returns, it has added the units of layerAsks. -/
theorem addLayer_adds {s : WsShape} {lay lay' : WsLay} {l : ℕ}
    (h : WsLay.addLayer s lay l = .ok lay') : Adds (layerAsks s l) lay lay' := by
  unfold WsLay.addLayer at h
  obtain ⟨a0, h0, h⟩ := okBind h
  obtain ⟨a1, h1, h⟩ := okBind h
  obtain ⟨a2, h2, h⟩ := okBind h
  unfold layerAsks
  by_cases hm : s.moe.getD l false = true
  · rw [if_pos hm] at h ⊢
    obtain ⟨b0, g0, h⟩ := okBind h
    obtain ⟨b1, g1, h⟩ := okBind h
    obtain ⟨b2, g2, h⟩ := okBind h
    obtain ⟨b3, g3, h⟩ := okBind h
    obtain ⟨b4, g4, h⟩ := okBind h
    obtain ⟨b5, g5, h⟩ := okBind h
    exact .cons h0 (.cons h1 (.cons h2 (.cons g0 (.cons g1 (.cons g2 (.cons g3 (.cons g4
      (.cons g5 (.cons h (.nil _))))))))))
  · rw [if_neg hm] at h ⊢
    obtain ⟨b0, g0, h⟩ := okBind h
    obtain ⟨b1, g1, h⟩ := okBind h
    exact .cons h0 (.cons h1 (.cons h2 (.cons g0 (.cons g1 (.cons h (.nil _))))))

/-- The same for the fold over a list of layers. -/
theorem foldl_adds (s : WsShape) : ∀ (ls : List ℕ) (lay lay' : WsLay),
    ls.foldlM (WsLay.addLayer s) lay = .ok lay' → Adds (ls.flatMap (layerAsks s)) lay lay'
  | [], lay, lay', h => by
    have e : lay = lay' := Except.ok.inj h
    subst e
    exact .nil _
  | l :: ls, lay, lay', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := okBind h
    rw [List.flatMap_cons]
    exact (addLayer_adds h1).append (foldl_adds s ls m lay' h2)

/-- What build's tests leave, besides the units. -/
structure BuildOK (s : WsShape) : Prop where
  /-- the multiple to which the number of rows is rounded up -/
  D : s.D = 2048 ∨ s.D = 32
  /-- which layers are mixtures of experts -/
  moe : ∀ l < s.L, s.moe.getD l false = (s.MOE != 0 && l % 2 == 1)
  /-- five sizes are from 1 to 2^24 -/
  five : ([s.d, s.dh, s.dkv, s.dq, s.f].all WsLay.inWords) = true
  /-- so are two more, if a layer is a mixture of experts -/
  two : (s.moe.any id && !([s.fe, s.NE].all WsLay.inWords)) = false

/-- If build returns for a shape with the embedding and the head, it has added the units of allAsks
to the empty layout, rounded the number of rows up, and its tests have passed. -/
theorem build_ok {s : WsShape} {lk : ℕ} {lay : WsLay} (h : WsLay.build s lk = .ok lay)
    (heh : s.eh = 1) :
    ∃ m, Adds (allAsks s) { lk := lk } m ∧
      lay = { lk := m.lk, m0 := (m.m0 + s.D - 1) / s.D * s.D, U := m.U } ∧ BuildOK s := by
  unfold WsLay.build at h
  obtain ⟨_, h⟩ := okGuard h
  obtain ⟨c2, h⟩ := okGuard h
  obtain ⟨_, h⟩ := okGuard h
  obtain ⟨c4, h⟩ := okGuard h
  obtain ⟨c5, h⟩ := okGuard h
  obtain ⟨c6, h⟩ := okGuard h
  obtain ⟨_, h⟩ := okGuard h
  obtain ⟨m1, hf, h⟩ := okBind h
  have he : (s.eh != 0) = true := by rw [heh]; rfl
  dsimp only at h
  rw [if_pos he] at h
  obtain ⟨m2, h12, h⟩ := okBind h
  obtain ⟨m3, h13, h⟩ := okBind h
  obtain ⟨_, h⟩ := okGuard h
  refine ⟨m3, (foldl_adds s _ _ _ hf).append (.cons h12 (.cons h13 (.nil _))),
    (Except.ok.inj h).symm, ?_, ?_, ?_, ?_⟩
  · by_contra hD
    have hD' : s.D ≠ 2048 ∧ s.D ≠ 32 := not_or.mp hD
    exact c2 (by simp [hD'.1, hD'.2])
  · intro l hl
    have a : ((List.range s.L).all fun l => s.moe.getD l false == (s.MOE != 0 && l % 2 == 1)) =
        true := by simpa using c4
    have b := List.all_eq_true.mp a l (List.mem_range.mpr hl)
    exact eq_of_beq b
  · simpa using c5
  · simpa using c6

/-- A size from 1 to 2^24 is above 0 and below 2^64. -/
theorem lt_of_inWords {v : ℕ} (h : WsLay.inWords v = true) : 0 < v ∧ v < 2 ^ 64 := by
  unfold WsLay.inWords at h
  have h' : 1 ≤ v ∧ v ≤ 2 ^ 24 := by simpa using h
  have e : (2 : ℕ) ^ 24 < 2 ^ 64 := by norm_num
  omega

/-- An array of marks that reads true somewhere has a true mark. -/
theorem any_of_getD {a : Array Bool} {l : ℕ} (h : a.getD l false = true) : a.any id = true := by
  by_cases hl : l < a.size
  · rw [Array.any_eq_true]
    exact ⟨l, hl, by simpa [Array.getD, hl] using h⟩
  · simp [Array.getD, hl] at h

/-- All groups of an ask are as the layout's list writes them. -/
def RawAsk (a : AskW) : Prop := ∀ x ∈ a.g, Raw x

theorem rawAsk2 (X l n : ℕ) {x y : WsGrp} (hx : Raw x) (hy : Raw y) : RawAsk ⟨X, l, n, [x, y]⟩ := by
  intro z hz
  have hz' : z = x ∨ z = y := by simpa using hz
  rcases hz' with e | e <;> rw [e] <;> assumption

theorem rawAsk3 (X l n : ℕ) {x y w : WsGrp} (hx : Raw x) (hy : Raw y) (hw : Raw w) :
    RawAsk ⟨X, l, n, [x, y, w]⟩ := by
  intro z hz
  have hz' : z = x ∨ z = y ∨ z = w := by simpa using hz
  rcases hz' with e | e | e <;> rw [e] <;> assumption

/-- So are the groups of all units of a shape that has passed build's tests. -/
theorem raw_all {s : WsShape} (B : BuildOK s) : ∀ a ∈ allAsks s, RawAsk a := by
  have f5 : WsLay.inWords s.d = true ∧ WsLay.inWords s.dh = true ∧ WsLay.inWords s.dkv = true ∧
      WsLay.inWords s.dq = true ∧ WsLay.inWords s.f = true := by simpa using B.five
  obtain ⟨wd, _, wkv, wq, wf⟩ := f5
  have rE (n : String) (hi : Bool) {v : ℕ} (hv : WsLay.inWords v = true) : Raw (WsLay.E_ n v hi) :=
    raw_E n hi (lt_of_inWords hv).1 (lt_of_inWords hv).2
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨l, _, ha⟩ := List.mem_flatMap.mp ha
    unfold layerAsks at ha
    rcases List.mem_append.mp ha with ha | ha
    · have ha' := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with e | e | e <;> rw [e]
      · exact rawAsk3 _ _ _ (raw_A _ _) (raw_A _ _) (rE _ _ wd)
      · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wkv)
      · exact rawAsk2 _ _ _ (rE _ _ wq) (rE _ _ wd)
    · by_cases hm : s.moe.getD l false = true
      · rw [if_pos hm] at ha
        have t2 : WsLay.inWords s.fe = true ∧ WsLay.inWords s.NE = true := by
          have x := B.two
          rw [any_of_getD hm] at x
          simpa using x
        obtain ⟨wfe, wne⟩ := t2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with e | e | e | e | e | e | e <;> rw [e]
        · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wfe)
        · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wfe)
        · exact rawAsk3 _ _ _ (rE _ _ wd) (rE _ _ wne) (rE _ _ wfe)
        · exact rawAsk3 _ _ _ (rE _ _ wd) (rE _ _ wne) (rE _ _ wfe)
        · exact rawAsk2 _ _ _ (rE _ _ wfe) (rE _ _ wd)
        · exact rawAsk3 _ _ _ (rE _ _ wfe) (rE _ _ wne) (rE _ _ wd)
        · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wne)
      · rw [if_neg hm] at ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with e | e | e <;> rw [e]
        · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wf)
        · exact rawAsk2 _ _ _ (rE _ _ wd) (rE _ _ wf)
        · exact rawAsk2 _ _ _ (rE _ _ wf) (rE _ _ wd)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e <;> rw [e]
    · exact rawAsk2 _ _ _ (raw_A _ _) (rE _ _ wd)
    · exact rawAsk2 _ _ _ (raw_A _ _) (rE _ _ wd)

/-- The shape for which wsLayOf calls build. -/
def shapeOf (s : WsShape) (p3 : Bool) : WsShape := wsSetMoe { s with eh := 1 } p3

/-- If wsLayOf returns a layout, build has returned it. -/
theorem wsLayOf_build {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) : WsLay.build (shapeOf s p3) lk = .ok lay := by
  unfold wsLayOf at h
  obtain ⟨_, h⟩ := okGuard h
  obtain ⟨_, h⟩ := okGuard h
  obtain ⟨m, hb, h⟩ := okBind h
  obtain ⟨_, _, h⟩ := okBind h
  have e : m = lay := Except.ok.inj h
  rw [← e]
  exact hb

/-- The layout that wsLayOf returns, written out: the column bits; the units, as unitsFrom lists
them from row 0 on; the rows of the units together are at most the layout's number of rows. -/
theorem wsLayOf_units {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) :
    lay.lk = lk ∧ lay.U.toList = unitsFrom lk 0 (allAsks (shapeOf s p3)) ∧
      endFrom lk 0 (allAsks (shapeOf s p3)) ≤ lay.m0 ∧ BuildOK (shapeOf s p3) := by
  obtain ⟨m, ha, e, B⟩ := build_ok (wsLayOf_build h) rfl
  obtain ⟨a1, a2, a3⟩ := adds_spec ha
  subst e
  refine ⟨a1, ?_, ?_, B⟩
  · show m.U.toList = _
    rw [a2]
    rfl
  · show _ ≤ (m.m0 + (shapeOf s p3).D - 1) / (shapeOf s p3).D * (shapeOf s p3).D
    have a3' : m.m0 = endFrom lk 0 (allAsks (shapeOf s p3)) := a3
    rw [← a3']
    rcases B.D with hD | hD <;> rw [hD] <;> omega

/-- A unit of the list begins at or after row o and ends at or before the first row after all. -/
theorem unitsFrom_in (lk : ℕ) : ∀ (as : List AskW) (o : ℕ), ∀ u ∈ unitsFrom lk o as,
    u.off + u.rows ≤ endFrom lk o as ∧ ∃ a ∈ as, ∃ o', u = unitP lk o' a
  | [], _, u, hu => by cases hu
  | a :: as, o, u, hu => by
    rcases List.mem_cons.mp hu with e | hu
    · refine ⟨?_, a, List.mem_cons_self, o, e⟩
      rw [e]
      show o + rowsP lk a ≤ endFrom lk (o + rowsP lk a) as
      rw [endFrom_eq]
      exact Nat.le_add_right _ _
    · obtain ⟨i1, b, hb, o', e⟩ := unitsFrom_in lk as _ u hu
      exact ⟨i1, b, List.mem_cons_of_mem _ hb, o', e⟩

/-- THE UNITS OF A LAYOUT THAT THE VERIFIER BUILDS HAVE THE PROPERTIES OF UnitOK. If wsLayOf returns
a layout, it has the asked number of column bits, and each of its units has the properties of
UnitOK and lies within the layout's rows. -/
theorem unitOK_of_layout {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) :
    lay.lk = lk ∧ ∀ u ∈ lay.U, UnitOK lk u ∧ u.off + u.rows ≤ lay.m0 := by
  obtain ⟨h1, h2, h3, B⟩ := wsLayOf_units h
  refine ⟨h1, fun u hu => ?_⟩
  have hu' : u ∈ unitsFrom lk 0 (allAsks (shapeOf s p3)) := by
    rw [← h2]
    exact Array.mem_toList_iff.mpr hu
  obtain ⟨i1, a, ha, o', e⟩ := unitsFrom_in lk _ _ u hu'
  refine ⟨?_, le_trans i1 h3⟩
  rw [e]
  exact unitOK_unitP lk o' (raw_all B a ha)

/-! ## The two lists of units are one -/

/-- The verifier's shape of the weights and the library's parameters agree in nine numbers. -/
structure SizedW (s : WsShape) (P : Params) : Prop where
  /-- the layers -/
  L : s.L = P.layers
  /-- the width of the residual stream -/
  d : s.d = P.d
  /-- the width of an attention head -/
  dh : s.dh = P.ch
  /-- the width of all query heads together -/
  dq : s.dq = P.nq * P.ch
  /-- the width of all value heads together -/
  dkv : s.dkv = P.nkv * P.ch
  /-- the inner width of a dense layer's feed-forward part -/
  f : s.f = P.f
  /-- the inner width of an expert -/
  fe : s.fe = P.fe
  /-- the number of experts -/
  NE : s.NE = P.nexp
  /-- the size of the vocabulary -/
  V : s.V = P.V

theorem coordOf_A (n : String) (R : ℕ) : coordOf (WsLay.A_ n R) = ⟨R, Kind.whole⟩ := rfl
theorem coordOf_low (n : String) (R : ℕ) : coordOf (WsLay.E_ n R false) = ⟨R, Kind.low⟩ := rfl
theorem coordOf_high (n : String) (R : ℕ) : coordOf (WsLay.E_ n R true) = ⟨R, Kind.high⟩ := rfl

/-- The units of a layer are the library's. -/
theorem layer_units {s : WsShape} {P : Params} (Z : SizedW s P) {l : ℕ}
    (hm : s.moe.getD l false = (l % 2 == 1)) :
    (layerAsks s l).map unitS = layerUnitsLib P l := by
  unfold layerAsks layerUnitsLib
  by_cases hl : l % 2 = 1
  · have e1 : s.moe.getD l false = true := by rw [hm]; simp [hl]
    have e2 : hasExperts l := hl
    rw [if_pos e1, if_pos e2]
    simp only [List.map_append, List.map_cons, List.map_nil, unitS, coordOf_A, coordOf_low,
      coordOf_high, Z.d, Z.dh, Z.dq, Z.dkv, Z.fe, Z.NE]
    rfl
  · have e1 : ¬ s.moe.getD l false = true := by rw [hm]; simp [hl]
    have e2 : ¬ hasExperts l := hl
    rw [if_neg e1, if_neg e2]
    simp only [List.map_append, List.map_cons, List.map_nil, unitS, coordOf_A, coordOf_low,
      coordOf_high, Z.d, Z.dh, Z.dq, Z.dkv, Z.f]
    rfl

/-- All units are the library's, for a model with layers that are mixtures of experts. -/
theorem all_units {s : WsShape} {P : Params} (Z : SizedW s P) (B : BuildOK s) (hM : s.MOE = 1) :
    (allAsks s).map unitS = unitsLib P := by
  unfold allAsks unitsLib
  rw [List.map_append, List.map_flatMap, ← Z.L]
  congr 1
  · refine List.flatMap_congr fun l hl => layer_units Z ?_
    rw [B.moe l (List.mem_range.mp hl), hM]
    rfl
  · simp only [List.map_cons, List.map_nil, unitS, coordOf_A, coordOf_low, coordOf_high, Z.d, Z.V]
    rfl

/-- Placing a group does not change its coordinate. -/
theorem coords_placeP : ∀ (g : List WsGrp) (left cb : ℕ),
    (placeP g left cb).map coordOf = g.map coordOf
  | [], _, _ => rfl
  | x :: g, left, cb => by
    show coordOf (yP x left cb) :: (placeP g (left - tP x left) (cb + tP x left)).map coordOf =
      coordOf x :: g.map coordOf
    rw [coords_placeP g]
    rfl

/-- THE TWO LAYOUTS ARE ONE. For a shape of the weights and parameters of the library that agree in
the nine numbers of SizedW, and a model with layers that are mixtures of experts: if wsLayOf returns
a layout with lk column bits, then it has as many units as the library's list; the rows of the
library's units together are at most the layout's number of rows; and unit number n of the layout is
the library's unit number n: the digits, the first row, the rows, group by group the size and the
class, the bits given to the columns and what is left to the rows; and THE CELL OF DIGIT q OF THE
WEIGHT WITH THE INDICES idx (cellOf) IS THE LIBRARY'S PLACE, for every q and every list idx. -/
theorem layout_eq {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) :
    lay.lk = lk ∧ lay.U.size = (unitsLib P).length ∧
      offLib lk (unitsLib P) (unitsLib P).length ≤ lay.m0 ∧
      ∀ n U, (unitsLib P)[n]? = some U → ∃ u, lay.U[n]? = some u ∧ UnitOK lk u ∧
        u.nlw = U.nU ∧ u.off = offLib lk (unitsLib P) n ∧ u.rows = rowsLib lk U ∧
        u.g.map coordOf = U.coords ∧ u.g.map (·.t) = bitsLib U.coords lk ∧
        u.g.map (·.left) = (U.coords.zip (bitsLib U.coords lk)).map (fun ct => lOf ct.1 ct.2) ∧
        ∀ q idx, cellOf u q idx = placeLib lk (unitsLib P) n U q idx := by
  obtain ⟨h1, h2, h3, B⟩ := wsLayOf_units h
  have Z' : SizedW (shapeOf s true) P := ⟨Z.L, Z.d, Z.dh, Z.dq, Z.dkv, Z.f, Z.fe, Z.NE, Z.V⟩
  have hu : (allAsks (shapeOf s true)).map unitS = unitsLib P := all_units Z' B rfl
  have hr := raw_all B
  refine ⟨h1, ?_, ?_, fun n U hU => ?_⟩
  · rw [← Array.length_toList, h2, unitsFrom_length, ← hu, List.length_map]
  · refine le_trans (le_of_eq ?_) h3
    rw [endFrom_eq, Nat.zero_add, ← hu, ← sum_rowsP_lib lk hr, List.length_map, List.take_length]
  · rw [← hu, List.getElem?_map] at hU
    obtain ⟨a, ha, e⟩ := Option.map_eq_some_iff.mp hU
    subst e
    have hm : a ∈ allAsks (shapeOf s true) := List.mem_of_getElem? ha
    have ho : 0 + (((allAsks (shapeOf s true)).take n).map (rowsP lk)).sum =
        offLib lk (unitsLib P) n := by
      rw [Nat.zero_add, sum_rowsP_lib lk hr, hu]
    refine ⟨unitP lk (0 + (((allAsks (shapeOf s true)).take n).map (rowsP lk)).sum) a, ?_,
      unitOK_unitP lk _ (hr a hm), rfl, ho, rowsP_lib lk (hr a hm), coords_placeP a.g lk 0,
      bits_placeP a.g lk 0 (hr a hm), lefts_placeP a.g lk 0 (hr a hm),
      fun q idx => cellOf_lib lk _ (hr a hm) _ n ho q idx⟩
    rw [← Array.getElem?_toList, h2]
    exact unitsFrom_get lk _ 0 n a ha

/-! ## The number of a unit -/

/-- A number that rises along the list of units: fourteen times the layer, plus the kind. -/
def codeW (a : AskW) : ℕ := a.l * 14 + a.X

/-- Along the units of a layer it rises, and it stays from 14 l to 14 l + 11. -/
theorem layer_code (s : WsShape) (l : ℕ) :
    (layerAsks s l).Pairwise (fun a b => codeW a < codeW b) ∧
      ∀ a ∈ layerAsks s l, l * 14 ≤ codeW a ∧ codeW a < l * 14 + 12 := by
  unfold layerAsks
  by_cases hm : s.moe.getD l false = true
  · rw [if_pos hm]
    constructor
    · simp [codeW]
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> simp [codeW]
  · rw [if_neg hm]
    constructor
    · simp [codeW]
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with e | e | e | e | e | e <;> rw [e] <;> simp [codeW]

/-- It rises along the whole list of units. -/
theorem all_code (s : WsShape) : (allAsks s).Pairwise (fun a b => codeW a < codeW b) := by
  unfold allAsks
  rw [List.pairwise_append]
  refine ⟨?_, by simp [codeW], ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun l _ => (layer_code s l).1, ?_⟩
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro l1 l2 hl a ha b hb
    have h1 := ((layer_code s l1).2 a ha).2
    have h2 := ((layer_code s l2).2 b hb).1
    omega
  · intro a ha b hb
    obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    have h1 := ((layer_code s l).2 a ha).2
    have h2 := List.mem_range.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with e | e <;> rw [e]
    · show codeW a < s.L * 14 + 12
      omega
    · show codeW a < s.L * 14 + 13
      omega

/-- In a list along which the number rises, the first member with the kind and the layer of member
number i is member number i. -/
theorem findIdx_code {as : List AskW} (hs : as.Pairwise (fun a b => codeW a < codeW b)) {i : ℕ}
    {a : AskW} (h : as[i]? = some a) :
    as.findIdx? (fun b => b.X == a.X && b.l == a.l) = some i := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by rw [e]; simp, fun j hj hp => ?_⟩
  have hlt := List.pairwise_iff_getElem.mp hs j i (lt_trans hj hi) hi hj
  rw [e] at hlt
  have hp' : as[j].X = a.X ∧ as[j].l = a.l := by simpa using hp
  unfold codeW at hlt
  rw [hp'.1, hp'.2] at hlt
  exact lt_irrefl _ hlt

/-- A search by kind and layer finds in the placed units what it finds in the asks. -/
theorem findIdx_unitsFrom (lk : ℕ) (p : ℕ → ℕ → Bool) : ∀ (as : List AskW) (o : ℕ),
    (unitsFrom lk o as).findIdx? (fun u => p u.X u.l) = as.findIdx? fun a => p a.X a.l
  | [], _ => rfl
  | a :: as, o => by
    show (unitP lk o a :: unitsFrom lk (o + rowsP lk a) as).findIdx? (fun u => p u.X u.l) = _
    rw [List.findIdx?_cons, List.findIdx?_cons, findIdx_unitsFrom lk p as]
    rfl

/-- A search in an array finds what the search in its list finds. -/
theorem arr_findIdx {α : Type} (xs : Array α) (p : α → Bool) :
    xs.findIdx? p = xs.toList.findIdx? p := by
  cases xs
  simp

/-- The verifier finds unit number n under that unit's own kind and layer. -/
theorem unitOf_ask {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) {n : ℕ} {a : AskW}
    (ha : (allAsks (shapeOf s p3))[n]? = some a) : lay.unitOf a.X a.l = some n := by
  obtain ⟨_, h2, _, _⟩ := wsLayOf_units h
  unfold WsLay.unitOf
  rw [arr_findIdx, h2, findIdx_unitsFrom lk (fun X l => X == a.X && l == a.l)]
  exact findIdx_code (all_code _) ha

/-- The lists of the layers below L, one after the other, begin with those of the layers below l,
followed by the list of layer l. -/
theorem flat_split {α : Type} (f : ℕ → List α) : ∀ (L l : ℕ), l < L →
    ∃ tail, (List.range L).flatMap f = (List.range l).flatMap f ++ (f l ++ tail)
  | 0, l, h => by omega
  | L + 1, l, h => by
    have e : (List.range (L + 1)).flatMap f = (List.range L).flatMap f ++ f L := by
      rw [List.range_succ, List.flatMap_append]
      simp
    rw [e]
    by_cases hl : l = L
    · subst hl
      exact ⟨[], by simp⟩
    · obtain ⟨t, ht⟩ := flat_split f L l (by omega)
      exact ⟨t ++ f L, by rw [ht]; simp⟩

/-- Unit number i of layer l has, in the whole list, the number i on top of the units of the layers
before. -/
theorem ask_at (s : WsShape) {l i : ℕ} {a : AskW} (hl : l < s.L)
    (h : (layerAsks s l)[i]? = some a) :
    (allAsks s)[((List.range l).map fun l' => (layerAsks s l').length).sum + i]? = some a := by
  obtain ⟨t, ht⟩ := flat_split (layerAsks s) s.L l hl
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  unfold allAsks
  rw [ht, List.append_assoc, List.getElem?_append_right
    (by rw [List.length_flatMap]; exact Nat.le_add_right _ _), List.length_flatMap,
    Nat.add_sub_cancel_left, List.append_assoc, List.getElem?_append_left hi]
  exact h

/-- The kinds of the units of layer l, in order, in a model whose odd layers are mixtures of
experts. -/
def kindsOf (l : ℕ) : List ℕ :=
  if l % 2 = 1 then [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] else [0, 1, 2, 3, 4, 9]

/-- The kinds and layers of the units of a layer. -/
theorem layer_kinds {s : WsShape} {l : ℕ} (hm : s.moe.getD l false = (l % 2 == 1)) :
    (layerAsks s l).map (fun a => (a.X, a.l)) = (kindsOf l).map fun X => (X, l) := by
  unfold layerAsks kindsOf
  by_cases hl : l % 2 = 1
  · have e1 : s.moe.getD l false = true := by rw [hm]; simp [hl]
    rw [if_pos e1, if_pos hl]
    rfl
  · have e1 : ¬ s.moe.getD l false = true := by rw [hm]; simp [hl]
    rw [if_neg e1, if_neg hl]
    rfl

/-- THE NUMBER OF A UNIT. Under the hypotheses of layout_eq: the verifier finds the unit of kind X
of layer l at the library's number of the layer's first unit plus the place of X in the list of the
layer's kinds; the embedding's unit (kind 12) at the number after the last layer's units, and the
head's (kind 13) after it. -/
theorem unitOf_eq {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) :
    (∀ l < P.layers, ∀ i X, (kindsOf l)[i]? = some X →
        lay.unitOf X l = some (firstLib P l + i)) ∧
      lay.unitOf 12 P.layers = some (firstLib P P.layers) ∧
      lay.unitOf 13 P.layers = some (firstLib P P.layers + 1) := by
  obtain ⟨_, _, _, B⟩ := wsLayOf_units h
  have Z' : SizedW (shapeOf s true) P := ⟨Z.L, Z.d, Z.dh, Z.dq, Z.dkv, Z.f, Z.fe, Z.NE, Z.V⟩
  have hmoe : ∀ l < (shapeOf s true).L, (shapeOf s true).moe.getD l false = (l % 2 == 1) :=
    fun l hl => by
      rw [B.moe l hl]
      rfl
  have hfirst : ∀ l ≤ (shapeOf s true).L,
      ((List.range l).map fun l' => (layerAsks (shapeOf s true) l').length).sum = firstLib P l :=
    fun l hl => by
      show _ = ((List.range l).map fun L' => (layerUnitsLib P L').length).sum
      congr 1
      refine List.map_congr_left fun l' hl' => ?_
      rw [← layer_units Z' (hmoe l' (lt_of_lt_of_le (List.mem_range.mp hl') hl)), List.length_map]
  have hL : (shapeOf s true).L = P.layers := Z'.L
  refine ⟨fun l hl i X hX => ?_, ?_, ?_⟩
  · rw [← hL] at hl
    have h1 : ((layerAsks (shapeOf s true) l).map fun a => (a.X, a.l))[i]? = some (X, l) := by
      rw [layer_kinds (hmoe l hl), List.getElem?_map, hX]
      rfl
    rw [List.getElem?_map] at h1
    obtain ⟨a, ha, e⟩ := Option.map_eq_some_iff.mp h1
    have eX : a.X = X := congrArg Prod.fst e
    have el : a.l = l := congrArg Prod.snd e
    have h2 := unitOf_ask h (ask_at (shapeOf s true) hl ha)
    rw [eX, el, hfirst l (le_of_lt hl)] at h2
    exact h2
  · have h1 : (allAsks (shapeOf s true))[firstLib P P.layers]? =
        some ⟨12, (shapeOf s true).L, 4,
          [WsLay.A_ "v" (shapeOf s true).V, WsLay.E_ "x" (shapeOf s true).d true]⟩ := by
      unfold allAsks
      rw [← hL, ← hfirst _ (le_refl _), ← List.length_flatMap,
        List.getElem?_append_right (le_refl _), Nat.sub_self]
      rfl
    have h2 : lay.unitOf 12 (shapeOf s true).L = some (firstLib P P.layers) := unitOf_ask h h1
    rw [hL] at h2
    exact h2
  · have h1 : (allAsks (shapeOf s true))[firstLib P P.layers + 1]? =
        some ⟨13, (shapeOf s true).L, 2,
          [WsLay.A_ "x" (shapeOf s true).V, WsLay.E_ "kk" (shapeOf s true).d false]⟩ := by
      unfold allAsks
      rw [← hL, ← hfirst _ (le_refl _), ← List.length_flatMap,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rfl
    have h2 : lay.unitOf 13 (shapeOf s true).L = some (firstLib P P.layers + 1) :=
      unitOf_ask h h1
    rw [hL] at h2
    exact h2

/-! ## The low bits of a placed group -/

/-- A placed group is one of the asked groups, placed. -/
theorem mem_placeP : ∀ (g : List WsGrp) (left cb : ℕ), ∀ y ∈ placeP g left cb,
    ∃ x ∈ g, ∃ l c, y = yP x l c
  | [], _, _, y, hy => by cases hy
  | x :: g, left, cb, y, hy => by
    rcases List.mem_cons.mp hy with e | hy
    · exact ⟨x, List.mem_cons_self, left, cb, e⟩
    · obtain ⟨z, hz, l, c, e⟩ := mem_placeP g _ _ y hy
      exact ⟨z, List.mem_cons_of_mem _ hz, l, c, e⟩

/-- In a layout that wsLayOf returns, a group of class 'E' has as z the library's number of low bits
of its size, and as o the size without its factors two. -/
theorem z_of_layout {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) :
    ∀ u ∈ lay.U, ∀ g ∈ u.g, g.cls = 'E' → g.z = sOf g.R ∧ g.o = g.R / 2 ^ sOf g.R := by
  obtain ⟨_, h2, _, B⟩ := wsLayOf_units h
  intro u hu g hg hE
  have hu' : u ∈ unitsFrom lk 0 (allAsks (shapeOf s p3)) := by
    rw [← h2]
    exact Array.mem_toList_iff.mpr hu
  obtain ⟨_, a, ha, o', e⟩ := unitsFrom_in lk _ _ u hu'
  rw [e] at hg
  obtain ⟨x, hx, l, c, e2⟩ := mem_placeP a.g lk 0 g hg
  rw [e2] at hE ⊢
  rcases raw_all B a ha x hx with ⟨_, hz, ho⟩ | hA
  · exact ⟨hz, ho⟩
  · have hE' : x.cls = 'E' := hE
    rw [hA] at hE'
    exact absurd hE' (by decide)

/-! ## The names and classes of a unit's groups -/

/-- The names and classes of the groups of a unit of kind X of a layer, in order. -/
def groupsOf (X : ℕ) : List (String × Char) :=
  if X = 0 then [("hd", 'A'), ("cd", 'A'), ("kk", 'E')]
  else if X = 7 ∨ X = 8 ∨ X = 10 then [("kk", 'E'), ("e", 'E'), ("x", 'E')]
  else [("kk", 'E'), ("x", 'E')]

/-- The names alone: hd, cd, kk for kind 0; kk, e, x for the kinds 7, 8, 10; kk, x for the
others. -/
def namesOf (X : ℕ) : List String := (groupsOf X).map (·.1)

/-- Placing a group changes neither its name nor its class. -/
theorem names_placeP : ∀ (g : List WsGrp) (left cb : ℕ),
    (placeP g left cb).map (fun y => (y.name, y.cls)) = g.map fun y => (y.name, y.cls)
  | [], _, _ => rfl
  | x :: g, left, cb => by
    show (x.name, x.cls) ::
        (placeP g (left - tP x left) (cb + tP x left)).map (fun y => (y.name, y.cls)) =
      (x.name, x.cls) :: g.map fun y => (y.name, y.cls)
    rw [names_placeP g]

/-- The groups of the units that a layer asks for have the names and classes of groupsOf. -/
theorem layer_groups (s : WsShape) (l : ℕ) : ∀ a ∈ layerAsks s l,
    a.g.map (fun y => (y.name, y.cls)) = groupsOf a.X := by
  intro a ha
  unfold layerAsks at ha
  by_cases hm : s.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> rfl
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> rw [e] <;> rfl

/-- The ask behind the unit of kind X of layer l: it stands in the whole list at the library's
number, it is one of the layer's asks, and it has that kind and layer. -/
theorem ask_of_kind {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) {l i X : ℕ} (hl : l < P.layers)
    (hX : (kindsOf l)[i]? = some X) :
    ∃ a, (allAsks (shapeOf s true))[firstLib P l + i]? = some a ∧
      a ∈ layerAsks (shapeOf s true) l ∧ a.X = X ∧ a.l = l := by
  obtain ⟨_, _, _, B⟩ := wsLayOf_units h
  have Z' : SizedW (shapeOf s true) P := ⟨Z.L, Z.d, Z.dh, Z.dq, Z.dkv, Z.f, Z.fe, Z.NE, Z.V⟩
  have hmoe : ∀ l < (shapeOf s true).L, (shapeOf s true).moe.getD l false = (l % 2 == 1) :=
    fun l hl => by
      rw [B.moe l hl]
      rfl
  have hL : (shapeOf s true).L = P.layers := Z'.L
  rw [← hL] at hl
  have hfirst :
      ((List.range l).map fun l' => (layerAsks (shapeOf s true) l').length).sum = firstLib P l := by
    show _ = ((List.range l).map fun L' => (layerUnitsLib P L').length).sum
    congr 1
    refine List.map_congr_left fun l' hl' => ?_
    rw [← layer_units Z' (hmoe l' (lt_trans (List.mem_range.mp hl') hl)), List.length_map]
  have h1 : ((layerAsks (shapeOf s true) l).map fun a => (a.X, a.l))[i]? = some (X, l) := by
    rw [layer_kinds (hmoe l hl), List.getElem?_map, hX]
    rfl
  rw [List.getElem?_map] at h1
  obtain ⟨a, ha, e⟩ := Option.map_eq_some_iff.mp h1
  refine ⟨a, ?_, List.mem_of_getElem? ha, congrArg Prod.fst e, congrArg Prod.snd e⟩
  rw [← hfirst]
  exact ask_at (shapeOf s true) hl ha

/-- The units of the layers before layer l are as many as the library counts. -/
theorem first_eq {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) {l : ℕ} (hl : l ≤ P.layers) :
    ((List.range l).map fun l' => (layerAsks (shapeOf s true) l').length).sum = firstLib P l := by
  obtain ⟨_, _, _, B⟩ := wsLayOf_units h
  have Z' : SizedW (shapeOf s true) P := ⟨Z.L, Z.d, Z.dh, Z.dq, Z.dkv, Z.f, Z.fe, Z.NE, Z.V⟩
  have hL : (shapeOf s true).L = P.layers := Z'.L
  show _ = ((List.range l).map fun L' => (layerUnitsLib P L').length).sum
  congr 1
  refine List.map_congr_left fun l' hl' => ?_
  have h1 : l' < (shapeOf s true).L := by
    rw [hL]
    exact lt_of_lt_of_le (List.mem_range.mp hl') hl
  have h2 : (shapeOf s true).moe.getD l' false = (l' % 2 == 1) := by
    rw [B.moe l' h1]
    rfl
  rw [← layer_units Z' h2, List.length_map]

/-- THE UNIT AT A NUMBER, WRITTEN OUT. Under the hypotheses of layout_eq: at the library's number of
the first unit of layer l plus i stands ask number i of the layer's list layerAsks, placed with lk
column bits (unitP), from some first row on. -/
theorem unit_at {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) {l i : ℕ} {a : AskW} (hl : l < P.layers)
    (ha : (layerAsks (shapeOf s true) l)[i]? = some a) :
    ∃ o, lay.U[firstLib P l + i]? = some (unitP lk o a) := by
  obtain ⟨_, h2, _, _⟩ := wsLayOf_units h
  have hl' : l < (shapeOf s true).L := by
    have hL : (shapeOf s true).L = P.layers := Z.L
    rw [hL]
    exact hl
  have h3 := ask_at (shapeOf s true) hl' ha
  rw [first_eq Z h (le_of_lt hl)] at h3
  exact ⟨_, by rw [← Array.getElem?_toList, h2]; exact unitsFrom_get lk _ 0 _ a h3⟩

/-- THE NAMES AND CLASSES OF A UNIT'S GROUPS. Under the hypotheses of layout_eq: the unit that
stands at the library's number of the unit of kind X of layer l has groups with the names and
classes of groupsOf X, in order. -/
theorem unit_groups {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) :
    ∀ l < P.layers, ∀ i X, (kindsOf l)[i]? = some X → ∀ u, lay.U[firstLib P l + i]? = some u →
      u.g.map (fun y => (y.name, y.cls)) = groupsOf X := by
  intro l hl i X hX u hu
  obtain ⟨a, ha, hm, eX, _⟩ := ask_of_kind Z h hl hX
  obtain ⟨_, h2, _, _⟩ := wsLayOf_units h
  rw [← Array.getElem?_toList, h2, unitsFrom_get lk _ 0 _ a ha] at hu
  rw [← Option.some.inj hu, ← eX]
  show (placeP a.g lk 0).map (fun y => (y.name, y.cls)) = groupsOf a.X
  rw [names_placeP]
  exact layer_groups _ l a hm

/-- The names alone. -/
theorem unit_names {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) :
    ∀ l < P.layers, ∀ i X, (kindsOf l)[i]? = some X → ∀ u, lay.U[firstLib P l + i]? = some u →
      u.g.map (·.name) = namesOf X := by
  intro l hl i X hX u hu
  unfold namesOf
  rw [← unit_groups Z h l hl i X hX u hu, List.map_map]
  rfl

/-- In groupsOf the groups kk, e and x have class 'E', and hd and cd have class 'A'. -/
theorem groupsOf_cls {X : ℕ} {n : String} {c : Char} (h : (n, c) ∈ groupsOf X) :
    (c = 'E' ∧ (n = "kk" ∨ n = "e" ∨ n = "x")) ∨ (c = 'A' ∧ (n = "hd" ∨ n = "cd")) := by
  unfold groupsOf at h
  split_ifs at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e2, Or.inl e1⟩
    · exact Or.inr ⟨e2, Or.inr e1⟩
    · exact Or.inl ⟨e2, Or.inl e1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e2, Or.inl e1⟩
    · exact Or.inl ⟨e2, Or.inr (Or.inl e1)⟩
    · exact Or.inl ⟨e2, Or.inr (Or.inr e1)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e2, Or.inl e1⟩
    · exact Or.inl ⟨e2, Or.inr (Or.inr e1)⟩

/-- So in such a unit every group is of class 'E' with one of the names kk, e, x, or of class 'A'
with one of the names hd, cd. -/
theorem unit_cls {s : WsShape} {P : Params} (Z : SizedW s P) {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s true lk = .ok lay) :
    ∀ l < P.layers, ∀ i X, (kindsOf l)[i]? = some X → ∀ u, lay.U[firstLib P l + i]? = some u →
      ∀ g ∈ u.g, (g.cls = 'E' ∧ (g.name = "kk" ∨ g.name = "e" ∨ g.name = "x")) ∨
        (g.cls = 'A' ∧ (g.name = "hd" ∨ g.name = "cd")) := by
  intro l hl i X hX u hu g hg
  refine groupsOf_cls (X := X) ?_
  rw [← unit_groups Z h l hl i X hX u hu]
  exact List.mem_map.mpr ⟨g, hg, rfl⟩

/-! ## The hypotheses can be met -/

/-- A made-up shape of the weights: two layers, the second a mixture of experts. -/
def sMade : WsShape :=
  { D := 32, L := 2, d := 8, dh := 4, dkv := 4, dq := 8, f := 32, fe := 16, NE := 4, V := 16 }

/-- The library's parameters with the same nine numbers. The other fields are the reference's and
are not read by the layout. -/
def pMade : Params :=
  { Inst.Model.ppref with
    layers := 2, d := 8, ch := 4, nq := 2, nkv := 1, f := 32, fe := 16, nexp := 4, V := 16 }

/-- The two agree. -/
theorem sized_made : SizedW sMade pMade := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- wsLayOf returns for the made-up shape, with and without mixtures of experts, at 4, 6 and 11
column bits: a run, no theorem -/
#guard [4, 6, 11].all fun lk => (wsLayOf sMade true lk).isOk && (wsLayOf sMade false lk).isOk

#print axioms oddPart_eq
#print axioms place_ok
#print axioms build_ok
#print axioms unitOK_of_layout
#print axioms layout_eq
#print axioms unitOf_eq
#print axioms z_of_layout
#print axioms unit_at
#print axioms unit_groups
#print axioms unit_names
#print axioms unit_cls
#print axioms sized_made

end OnBytes.Road
