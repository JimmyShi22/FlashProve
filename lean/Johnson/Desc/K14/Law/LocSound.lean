-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LocSound.lean: the law of the constraints (loc_x) in the linear claim's shared
rounds, with its count, and the law tried on two functions that are no verifier's.

For words and a table of columns that are fixed before the locations are drawn: the lists of c
locations at which "LOC" can say yes with all constraints on G_u holding of the words are no more
than g ^ c, where g is the number of locations x at which the equation LocEq holds: at which the
code word of (u, r_u) is the fold of the table's column.
Main names: LocAt, LocSoundOf, YesLocOf, LocLawOf, locSound, loc_yes, locLaw, not_locLawOf_yes,
not_locLawOf_no.

What is not claimed. Nothing on how many such locations there are: that is a matter of the code's
distance and of the table. Nothing on how the locations are drawn, or on the columns handed being
the table's: it is asked as a premise here. The small instance is no instance of a release.

-/
import Johnson.Desc.K14.Law.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (addRowP addRowsP addRowsFrom ok rowL rowsL)

variable {K : Type} [Field K] (ρ : Reading K)

/-- (loc_x)'s equation at the location x, off the table's column there. -/
def LocAt (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64) (x : Nat) : Prop :=
  LocEq ρ p.S.fold (generatorAt p.S.fold.index.code x)
    (fun r => ρ.val ((weights p.S d.loc).getD r zeroE)) (weights p.S d.loc).size
    (fun r => ρ.val (ofF ((tab x).toArray.getD r 0)))
    (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k))

open Classical in
/-- The law of (loc_x), of any function in the place of "LOC". d: the state in front of the round in
which the locations are drawn; tab: the table's columns; c: the number of locations. -/
def LocSoundOf
    (lc : Par → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Option St) : Prop :=
  ∀ (p : Par) (d : St) (T : Statement) (m : Words K) (tab : Nat → List UInt64) (c : Nat),
    p.S.fold.index.ok = true → PlacedU T p.S.fold d.loc.oU →
    (Finset.univ.filter fun Q : Fin c → Fin (2 ^ p.S.fold.index.code.logN) =>
      ∃ (r : Fmt.RoundView) (cols : List (Nat × List UInt64)) (d' : St),
        r.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
        (∀ x col, cols.lookup x = some col → col = tab x) ∧
        lc p d [r] [cols] = some d' ∧ Means.AllSay ρ T (rowsOn d' d.loc.gU) m).card ≤
    (Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
      LocAt ρ p d m tab x.val).card ^ c

/-- Where the constraints can be made and added, the function says yes. -/
def YesLocOf
    (lc : Par → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Option St) : Prop :=
  ∀ (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64)) (rows : List Row),
    locRows p d.loc r cols = some rows → addRowsP d d.loc.gU rows = some d' →
    lc p d [r] [cols] = some d'

/-- The joined law of (loc_x), of any function in the place of "LOC". -/
def LocLawOf
    (lc : Par → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Option St) : Prop :=
  LocSoundOf ρ lc ∧ YesLocOf lc

/-- **The law of (loc_x)**: LAYS and MEANS joined, with the count. -/
theorem locSound : LocSoundOf ρ loc := by
  classical
  intro p d T m tab c hi hP
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Fintype.card_piFinset_const _ c))
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  obtain ⟨_, r, cols, d', hr, htab, hl, hs⟩ := hQ
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hx : (Q i).val ∈ locations p r := by
    unfold locations
    rw [hr, List.mem_map]
    exact ⟨(Q i).val, by simp [List.mem_ofFn], Nat.mod_eq_of_lt (Q i).isLt⟩
  obtain ⟨col, hcol, hE⟩ := locSays ρ p d d' d' r cols T m hl ⟨[], by simp⟩ hs hi hP _ hx
  rw [htab _ _ hcol] at hE
  exact hE

/-- "LOC" says yes where its constraints can be made and added. -/
theorem loc_yes : YesLocOf loc := by
  intro p d d' r cols rows h1 h2
  have e : loc p d [r] [cols] =
      (locRows p d.loc r cols).bind fun rows => addRowsP d d.loc.gU rows := rfl
  rw [e, h1]
  exact h2

/-- **The joined law of (loc_x).** -/
theorem locLaw : LocLawOf ρ loc := ⟨locSound ρ, loc_yes⟩

/-! ## A small instance -/

/-- A code of length 2 with one message entry and no tail; a table of one row. -/
def tinyLS : LinShape :=
  { tinyS with fold := { tinyS.fold with
      index := { code := ⟨1, 1, 0⟩, v := 0, answers := 0, saltBytes := 40 }, columns := 1 } }

@[inherit_doc tinyLS]
def tinyLP : Par := { samples := 0, firstTree := 0, S := tinyLS, key := {}, entries := [] }

/-- The small table's shape meets its conditions. -/
theorem tinyL_ok : tinyLP.S.fold.index.ok = true := by decide

/-- At the small instance o_u has its table. -/
theorem tinyL_placed : PlacedU tinyT tinyLP.S.fold tinyD.loc.oU :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- One row: one weight, 1. -/
theorem tinyL_weights : weights tinyLP.S tinyD.loc = #[oneE] := rfl

/-- A state without a group. -/
def tinyD0 : St := { tinyD with st := { tinyT with groups := #[] } }

/-- At words that are 0 and a table of ones the equation holds at no location. -/
theorem tinyL_never (x : Nat) : ¬ LocAt ρ tinyLP tinyD0 (fun _ _ _ => 0) (fun _ => [1]) x := by
  have hw : weights tinyLP.S tinyD0.loc = #[oneE] := rfl
  have h1 : ρ.val (ofF 1) = 1 := ρ.one
  unfold LocAt LocEq
  rw [hw]
  simp [ρ.one, h1]

/-- A function that says yes to all and lays nothing does not meet the law's first half. -/
theorem not_locSoundOf_yes : ¬ LocSoundOf ρ fun _ d _ _ => some d := by
  classical
  intro h
  have h1 := h tinyLP tinyD0 tinyT (fun _ _ _ => 0) (fun _ => [1]) 1 tinyL_ok tinyL_placed
  have h2 : (Finset.univ.filter fun x : Fin (2 ^ tinyLP.S.fold.index.code.logN) =>
      LocAt ρ tinyLP tinyD0 (fun _ _ _ => 0) (fun _ => [1]) x.val) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun x _ => tinyL_never ρ x.val
  rw [h2, Finset.card_empty, Nat.zero_pow (by decide), Nat.le_zero, Finset.card_eq_zero] at h1
  refine Finset.filter_eq_empty_iff.1 h1
    (Finset.mem_univ fun _ => ⟨0, Nat.two_pow_pos _⟩)
    ⟨⟨[], ⟨[], [0], [], none⟩⟩, [], _, by simp, ?_, rfl, ?_⟩
  · intro x col hc
    simp at hc
  · intro r hr
    simp [rowsOn, tinyD0, tinyD] at hr

/-- The round and the columns of the small instance: one location, 0. -/
def tinyLR : Fmt.RoundView := ⟨[], ⟨[], [0], [], none⟩⟩

/-- (loc_x) at the small instance. -/
def tinyLRow : Row :=
  { kind := .generator, terms := #[⟨1, .main, tinyV (ofF 1)⟩], target := maddS zeroE 1 oneE }

/-- The one constraint of the small instance. -/
theorem tinyL_rows : locRows tinyLP tinyD.loc tinyLR [(0, [1])] = some [tinyLRow] := rfl

/-- It can be added. -/
theorem tinyL_add : (addRowsP tinyD 0 [tinyLRow]).isSome = true := by
  have h0 : ok (rowsL tinyD.st 0) = true := by
    simp [ok, rowsL, VerifiableInference.Desc.Ground.on,
      VerifiableInference.Desc.Ground.has, tinyD, tinyT]
  have h : ok (rowL tinyD.st 0 tinyLRow) = true := by
    simp [ok, rowL, VerifiableInference.Desc.Ground.on,
      VerifiableInference.Desc.Ground.has, tinyD, tinyT, tinyV, tinyLRow,
      VerifiableInference.Desc.Own.placeFits, VerifiableInference.Desc.Own.tableThere,
      VerifiableInference.Desc.Own.tensorInOrder, Statement.tableBits, Statement.rowBits,
      Statement.placeBits, OracleShape.rows, ceilLog2, Tensor.vars]
    try rfl
  unfold addRowsP
  rw [if_pos h0]
  simp only [addRowsFrom, addRowP]
  rw [if_pos h]
  rfl

/-- A function that says no to all does not meet the law's second half. -/
theorem not_yesLocOf_no : ¬ YesLocOf fun _ _ _ _ => none := by
  intro h
  obtain ⟨d', hd⟩ := Option.isSome_iff_exists.1 tinyL_add
  have := h tinyLP tinyD d' tinyLR [(0, [1])] [tinyLRow] tinyL_rows hd
  cases this

/-- Neither function meets the joined law. -/
theorem not_locLawOf_yes : ¬ LocLawOf ρ fun _ d _ _ => some d :=
  fun h => not_locSoundOf_yes ρ h.1

@[inherit_doc not_locLawOf_yes]
theorem not_locLawOf_no : ¬ LocLawOf ρ fun _ _ _ _ => none :=
  fun h => not_yesLocOf_no h.2

end Desc.K14.Law
