-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3Full.lean: WHAT THE ENTRY TESTS' ROWS ON THE LOOKUPS' DIGITS AND ON
ATTENTION's CALLERS' READING READ, AT THE FULL SIZE, WRITTEN DOWN, as narrowed terms
(Johnson/AtFull/ProofRows/K3Views.lean); AND THE SECOND ROW DECIDED AT THEM BY LEAN's KERNEL, with
a negative test. Definitions with code and two theorems. The first row's decision stands alone in
Johnson/AtFull/ProofRows/K3DigFull.lean.
  `treesOfSort`, `callOfSort`, `pieceOfSort` and six small tables of numbers; `pFull i`: the
    narrowed place of the lookup on segment i's digits, by the segment's sort (`sortAt`,
    Johnson/AtFull/Made/LinksFull.lean): four values but for the segment's own number. `tFull i`:
    the narrowed structure: 128 combinations; one piece a call; no table.
  `cFull i`, `mFull`: the narrowed place of attention's lookup on the calls and the narrowed
    structure: one value but for the segment's number.
  `sentFull`: what the tests read beside the public parameters: the written codes, shape and
    layout, and the written views' lists of arrays. `setFull`: the plan's setting at the parameter
    file's written lines.
  `attFull`: the twelve attention segments' numbers. `reads_full`: `readsB` says yes at them.
    `reads_bend`: with every list of arrays one shorter it says no at the first.
WHENCE THE VALUES: two runs (prints of the planner's own values at `VerifierAndGoals.storedPublicFiles`, by name: no
theorem). THAT THEY ARE THE PLANNER's IS PROVED NOWHERE HERE: it is a hypothesis of
Johnson/AtFull/ProofRows/K3Rows.lean.
Limits. Closed facts at written values. No soundness is claimed.

-/
import Johnson.AtFull.ProofRows.K3Views
import Johnson.AtFull.Made.LinksFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3Asks
open VerifiableInference.Desc.First.Look (Place P)
open Johnson.AtFull.Made (sortAt nsOfSort viewFull)

/-! ## 1 The values -/

/-- The arrays' numbers of rows and columns, by the segment's sort. -/
def treesOfSort : Nat → List (Nat × Nat)
  | 0 => [(1, 407626), (21846, 5990), (21846, 5990), (21846, 5990), (10923, 3200), (2731, 324),
      (21846, 256), (21846, 400), (21846, 1536), (21846, 400), (128, 999424), (32, 2048)]
  | 1 => [(1, 60640), (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368),
      (32, 2048), (21846, 1536)]
  | 2 => [(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990), (10923, 3200), (2731, 324),
      (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32, 2048), (21846, 400)]
  | _ => [(1, 61680), (21846, 4816), (21846, 4816), (21846, 4816), (21846, 4816), (5462, 640),
      (2731, 15), (10923, 384), (128, 770048), (32, 2048), (21846, 400)]

/-- The logarithm of a call's number of keys. -/
def nOfSort : Nat → Nat
  | 1 => 25
  | _ => 26

/-- A tree's number of padding keys. -/
def padOfSort : Nat → Nat
  | 0 => 3145728
  | 1 => 5242880
  | 2 => 3145728
  | _ => 17825792

/-- The lookup's first slot. -/
def nextOfSort : Nat → Nat
  | 0 => 2696
  | 1 => 2884
  | 2 => 2695
  | _ => 2168

/-- The half's number of columns. -/
def mzOfSort : Nat → Nat
  | 1 => 221184
  | 3 => 385024
  | _ => 499712

/-- The columns' number rounded up to a power of two. -/
def cpOfSort : Nat → Nat
  | 1 => 262144
  | _ => 524288

/-- The number of the digits' array; the counts' array follows it. -/
def zzOfSort : Nat → Nat
  | 0 => 10
  | 1 => 5
  | 2 => 9
  | _ => 8

/-- The call of the low digits (k = 10), of the high digits (k = 8). -/
def callOfSort (s : Nat) (name : String) (k : Nat) : Call :=
  { name := name, n := nOfSort s, iota := 0, k := k, kappa := 5, fn := 0, t0 := 0, tau := none,
    pub := #[padOfSort s], heavy := [] }

/-- A sort's word in a place's name. -/
def wordOfSort : Nat → String
  | 1 => "attention"
  | 3 => "head"
  | _ => "layers"

/-- **The narrowed place of the lookup on segment i's digits.** -/
def pFull (i : Nat) : Place :=
  { name := "LINK " ++ toString i ++ " (" ++ wordOfSort (sortAt i) ++ ") digits", link := i,
    calls := #[callOfSort (sortAt i) "R10z" 10, callOfSort (sortAt i) "R8d" 8],
    pub := #[padOfSort (sortAt i), padOfSort (sortAt i)], lid := 28,
    base := { trees := ((treesOfSort (sortAt i)).map fun x => { R := x.1, K := x.2 }).toArray },
    F := { next := nextOfSort (sortAt i) }, fs := {}, ns := nsOfSort (sortAt i), lm := 5 }

/-- The one piece of a call: q = 0 the low digits, 1 the high. -/
def pieceOfSort (s q : Nat) : Piece :=
  { tree := zzOfSort s, row := q, r0 := 0, Rp := 128, c0 := q * mzOfSort s, Cp := mzOfSort s,
    CP := cpOfSort s, off := 0, a := 7, b := nOfSort s }

/-- **The narrowed structure of segment i's approximate range proof.** f9 stands at its default:
`digOne` lays it anew. -/
def tFull (i : Nat) : HTailF2 :=
  { tau := 128, mz := mzOfSort (sortAt i),
    z1 := { call := callOfSort (sortAt i) "R10z" 10, pieces := #[pieceOfSort (sortAt i) 0] },
    z2 := { call := callOfSort (sortAt i) "R8d" 8, pieces := #[pieceOfSort (sortAt i) 1] },
    f9 := {}, ix := { ZZ := zzOfSort (sortAt i), BZ := zzOfSort (sortAt i) + 1 } }

/-- The narrowed place of attention's lookup on the calls at segment i. -/
def cFull (i : Nat) : Place :=
  { name := "", link := i, calls := #[], pub := #[], lid := 0, base := {}, F := { next := 0 },
    fs := { dT := 25, rK := 4, kT := 16, cK := 2 }, ns := 0, lm := 0 }

/-- The narrowed structure at an attention segment. -/
def mFull : HTailF2 :=
  { NM := 5, gtTree := #[1, 2, 3, 4, 7],
    mats := #[{ m := 65536, k := 7200 }, { m := 8192, k := 360 }, { m := 65536, k := 640 },
      { m := 16384, k := 512 }, { m := 65536, k := 1536 }] }

/-- **What the tests read beside the public parameters.** -/
def sentFull : Sent :=
  ⟨Johnson.G.proofCodesWritten, VerifiableInference.Desc.ReqLit.shapeFull, Johnson.G.layoutFull,
    (viewFull.map (·.2.2.2)).toArray⟩

/-- The plan's setting at the parameter file's written lines. -/
def setFull : Params.Setting := Params.settingOf Params.recordLines

/-- The attention segments' numbers. -/
def attFull : List Nat := (List.range 12).map (2 * · + 1)

/-! ## 2 The second row -/

set_option maxRecDepth 1000000 in
/-- **`readsB` at the twelve attention segments.** -/
theorem reads_full : (attFull.all fun i => readsB (cFull i) mFull sentFull) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with every list of arrays one shorter. -/
theorem reads_bend :
    readsB (cFull 1) mFull { sentFull with arrayOf := sentFull.arrayOf.map fun a => a.pop } =
      false := by
  decide +kernel

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.reads_full
#print axioms Johnson.AtFull.ProofRows.K3.reads_bend
