-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/FoldPriced.lean: a stage of a proximity test that is folded, in numbers: from two
tests on natural numbers: what the fold asks of its codes, with no hypothesis on codes; so the fold
is taken off; and each of its rounds' error counts is at most 2^-128 of the round's written verifier
messages, without the planner.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

The like of Johnson/Bridge/BaseCodesAt.lean and Johnson/Bridge/BasePriced.lean for a fold.
Definitions, statements and proofs.

Main names:
  `FoldedPlace`: a stage with its radius and the brackets of its two counts (`Br`).
  `FoldedPlace.bC`, `bZ`, `lst`: the count of a main row, the count of a table of mask rows (with
    the Johnson bound's list at the repeated mask code's own distance), the Johnson bound's list at
    the stage's distance: numbers that can be evaluated.
  `FoldedPlace.cntPlain`, `cntMask`: the library's count of a fold's round in which no mask row is
    folded: bC + 2 lst; and of one in which mask rows are folded too: bC + 2 bZ + 2 lst.
  `FoldedPlace.good`, `FoldedPlace.priced`: the two tests. The second asks the comparison of
    `below_of_num` at `cntPlain`, and at `cntMask` where the stage has a mask variable.
  `FoldedPlace.radius_lt`, `listIn`: the radius is below the distance; the lists of the stage's
    tables.
  `FoldedPlace.counts`, `nums`, `holds`: `Sg.CountsAt`; `SumPar.ErrOK`; `FoldHolds` at written
    rounds that are the format's own (`Fmt.M1.rEps`, `Fmt.M1.rTwo`).
  `FoldedPlace.below_eps`, `below_plain`, `below_mask`: the clause `RoundBelow` of the three counts.
  `FoldedPlace.below`: so every count of `foldErr` at the place's numbers meets the clause
    (`fold_below_at`, OnBytes/Slice/ManyAtLetters.lean).

Limits: NO PLACE IS WRITTEN HERE: that the two tests say yes is shown of no place
(Johnson/Bridge/FoldAtWritten.lean has sixty). No work is counted: these rounds have none. That a
place's numbers are those of a file's plan is not said here. In which of a fold's rounds mask rows
are folded is the library's matter (`SumPar.err`). No sum over rounds. Nothing on a verifier or a
file.

-/
import Johnson.Bridge.BasePriced
import OnBytes.Slice.BlocksJohnson
import OnBytes.Slice.ManyAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb Iop _root_.Run
open scoped ENNReal

/-- The typed values of a written round that draws one element and nothing else. -/
theorem nVals_one {d : PQ.RD} (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0)
    (hP : d.entry.poss = 0) (hT : d.entry.trits = 0) (hk1 : d.kind ≠ .seeds)
    (hk2 : d.kind ≠ .sealed) : nVals (Fmt.dsOf d.entry d.kind) = Fintype.card GE := by
  rw [nVals_dsOf _ _ hk1 hk2, hE, hZ, hP, hT, card_GE]
  simp

/-- A count in a written round that is a round of the format which draws one element and nothing
else, without work. -/
theorem below_isOne (count : ℕ)
    (h : count * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)) {d : PQ.RD}
    {r : Fmt.Round} (hd : IsRd d r) (hL : r.entry.logN ≤ 64) (hE : r.entry.drawE = 1)
    (hZ : r.entry.drawNZ = 0) (hW : r.entry.work = 0) (hP : r.entry.poss = 0)
    (hT : r.entry.trits = 0) (hk1 : r.kind ≠ .seeds) (hk2 : r.kind ≠ .sealed) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have e := hd.entry
  have k := hd.kind
  exact LastPlace.below_one count (Cb.Gl.p ^ 3) (Cb.Gl.gl_card.2.1 ▸ card_GE_pos) h d
    (by rw [e]; exact hL) (by rw [e]; exact hE) (by rw [e]; exact hZ) (by rw [e]; exact hW)
    ((nVals_one (by rw [e]; exact hE) (by rw [e]; exact hZ) (by rw [e]; exact hP)
      (by rw [e]; exact hT) (by rw [k]; exact hk1) (by rw [k]; exact hk2)).trans
        Cb.Gl.gl_card.2.1)

/-- A stage that is folded, with its radius and the brackets of its two counts. -/
structure FoldedPlace where
  s : Sg
  e : ℕ
  main : Br
  mask : Br

namespace FoldedPlace
variable (x : FoldedPlace)

/-- The bound on the exceptional points of a line, for a main row. -/
def bC : ℕ := x.main.N

/-- The same for a table of mask rows, with the list at the repeated mask code's own distance. -/
def bZ : ℕ := x.mask.N + listMax (2 ^ x.s.C.a) x.s.dZ x.e

/-- The bound on a list: the Johnson bound's, at the stage's distance. -/
def lst : ℕ := x.s.lstJ x.e

/-- The count of a round in which no mask row is folded. -/
def cntPlain : ℕ := x.bC + x.lst * 2

/-- The count of a round in which mask rows are folded too. -/
def cntMask : ℕ := x.bC + (x.bZ + x.bZ) + x.lst * 2

/-- The test on sizes, radius and brackets. -/
def good : Bool :=
  Johnson.Top.H.stB x.s x.e && x.main.ok (2 ^ x.s.C.a) (x.s.C.r + x.s.C.l - 1) x.e &&
    x.mask.ok (2 ^ x.s.C.a) (2 ^ (x.s.C.a - x.s.Z.a) * (x.s.Z.r + x.s.Z.l - 1)) x.e

/-- The comparison of `below_of_num`, at the count by the kind of round. -/
def priced : Bool :=
  decide (x.cntPlain * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)) &&
    (decide (x.s.h = 0) ||
      decide (x.cntMask * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)))

variable {x}

theorem stageJ (h : x.good = true) : x.s.StageJ x.e := by
  simp only [good, Bool.and_eq_true] at h
  exact Johnson.Top.H.stJ_of h.1.1

/-- The condition on counts, at the place's numbers. No hypothesis on codes. -/
theorem counts (h : x.good = true) : x.s.CountsAt x.e x.bC x.bZ := by
  have hJ := stageJ h
  simp only [good, Bool.and_eq_true] at h
  exact Sg.countsAt_bchks_fl (Cb.Bridge.bchks46At GF GE) hJ.sized hJ.pos hJ.twoC hJ.twoZ hJ.rad
    hJ.joh _ _ (Br.le h.1.2) (Br.le h.2)

/-- The radius is below the stage's distance. -/
theorem radius_lt (h : x.good = true) : x.e < x.s.d := (stageJ h).joh.1

/-- The lists of the stage's tables, which the code switch into the stage asks: the Johnson bound's.
The statement on codes is not used. -/
theorem listIn (h : x.good = true) : x.s.cIn.ListAt x.e x.lst :=
  Sg.listJ_of (Sg.fit_cIn (stageJ h).sized) (stageJ h).joh

/-- The numbers of the fold. -/
theorem nums (h : x.good = true) :
    (x.s.par 0).ErrOK x.e (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ) :=
  OnBytes.Slice.foldNums_joh (stageJ h).sized (stageJ h).joh (counts h)

/-- **The fold is taken off**, at written rounds that are the format's own, with the library's error
counts at the place's numbers. -/
theorem holds (h : x.good = true) (dE dT : PQ.RD) (na nb : String)
    (hdE : IsRd dE (Fmt.M1.rEps na)) (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds x.s x.e dE dT
      (foldErr x.s dE dT (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ)) :=
  fold_holds_joh x.s (stageJ h).sized x.e x.bC x.bZ (stageJ h).joh (counts h) dE dT na nb hdE hdT

theorem priced_plain (h : x.priced = true) :
    x.cntPlain * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65) := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 h).1

theorem priced_mask (h : x.priced = true) (h0 : x.s.h ≠ 0) :
    x.cntMask * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65) := by
  unfold priced at h
  rcases Bool.or_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).2 with h1 | h1
  · exact absurd (of_decide_eq_true h1) h0
  · exact of_decide_eq_true h1

/-- A round in which no mask row is folded. -/
theorem below_plain (h : x.priced = true) {d : PQ.RD} {nb : String}
    (hd : IsRd d (Fmt.M1.rTwo nb)) :
    RoundBelow (x.bC + x.lst * 2) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_isOne _ (priced_plain h) hd (Nat.zero_le 64) rfl rfl rfl rfl rfl
    (by decide : Fmt.Kind.elems ≠ .seeds) (by decide : Fmt.Kind.elems ≠ .sealed)

/-- A round in which mask rows are folded too. -/
theorem below_mask (h : x.priced = true) (h0 : x.s.h ≠ 0) {d : PQ.RD} {nb : String}
    (hd : IsRd d (Fmt.M1.rTwo nb)) :
    RoundBelow (x.bC + (x.bZ + x.bZ) + x.lst * 2) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_isOne _ (priced_mask h h0) hd (Nat.zero_le 64) rfl rfl rfl rfl rfl
    (by decide : Fmt.Kind.elems ≠ .seeds) (by decide : Fmt.Kind.elems ≠ .sealed)

/-- The round before the fold's rounds: the list alone. -/
theorem below_eps (h : x.priced = true) {d : PQ.RD} {na : String}
    (hd : IsRd d (Fmt.M1.rEps na)) : RoundBelow x.lst d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  RoundBelow.mono (n' := x.bC + x.lst * 2)
    (le_trans (Nat.le_mul_of_pos_right _ (by decide)) (Nat.le_add_left _ _))
    (below_isOne _ (priced_plain h) hd (Nat.zero_le 64) rfl rfl rfl rfl rfl
      (by decide : Fmt.Kind.join ≠ .seeds) (by decide : Fmt.Kind.join ≠ .sealed))

/-- **Every count of the fold**, as the library has them at the place's numbers, is at most 2^-128
of its round's written verifier messages. -/
theorem below (h : x.priced = true) {dE dT : PQ.RD} {na nb : String}
    (hdE : IsRd dE (Fmt.M1.rEps na)) (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    Err.Below (foldErr x.s dE dT (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ))
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  fold_below_at x.s dE dT x.bC x.bZ x.bZ x.lst _ (below_eps h hdE) (below_plain h hdT)
    fun h0 => below_mask h h0 hdT

/-- What is said of one place. -/
structure Paid (x : FoldedPlace) : Prop where
  /-- the radius is below the stage's distance -/
  radius : x.e < x.s.d
  /-- the lists of the stage's tables -/
  listIn : x.s.cIn.ListAt x.e x.lst
  /-- what the fold asks of its codes, at the place's numbers -/
  nums : (x.s.par 0).ErrOK x.e (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ)
  /-- so the fold is taken off, with the library's error counts at these numbers -/
  holds : ∀ (dE dT : PQ.RD) (na nb : String), IsRd dE (Fmt.M1.rEps na) →
    IsRd dT (Fmt.M1.rTwo nb) → FoldHolds x.s x.e dE dT
      (foldErr x.s dE dT (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ))
  /-- every one of these error counts is at most 2^-128 of its round's written verifier messages -/
  below : ∀ (dE dT : PQ.RD) (na nb : String), IsRd dE (Fmt.M1.rEps na) →
    IsRd dT (Fmt.M1.rTwo nb) → Err.Below
      (foldErr x.s dE dT (fun _ => x.lst) (fun _ => x.bC) (fun _ => x.bZ) (fun _ => x.bZ))
      ((2 : ℝ≥0∞)⁻¹ ^ 128)
  /-- the three counts by the kind of round -/
  eps : ∀ (d : PQ.RD) (na : String), IsRd d (Fmt.M1.rEps na) →
    RoundBelow x.lst d ((2 : ℝ≥0∞)⁻¹ ^ 128)
  plain : ∀ (d : PQ.RD) (nb : String), IsRd d (Fmt.M1.rTwo nb) →
    RoundBelow (x.bC + x.lst * 2) d ((2 : ℝ≥0∞)⁻¹ ^ 128)
  mask : x.s.h ≠ 0 → ∀ (d : PQ.RD) (nb : String), IsRd d (Fmt.M1.rTwo nb) →
    RoundBelow (x.bC + (x.bZ + x.bZ) + x.lst * 2) d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem paid (hg : x.good = true) (hp : x.priced = true) : x.Paid :=
  ⟨radius_lt hg, listIn hg, nums hg, holds hg, fun _ _ _ _ hE hT => below hp hE hT,
    fun _ _ hd => below_eps hp hd,
    fun _ _ hd => below_plain hp hd,
    fun h0 _ _ hd => below_mask hp h0 hd⟩

end FoldedPlace

end Johnson.Bridge

#print axioms Johnson.Bridge.FoldedPlace.counts
#print axioms Johnson.Bridge.FoldedPlace.holds
#print axioms Johnson.Bridge.FoldedPlace.below
#print axioms Johnson.Bridge.FoldedPlace.paid
