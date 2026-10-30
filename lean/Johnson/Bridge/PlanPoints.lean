-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanPoints.lean: the round «LIN point», the shared point of the test on a stored
table, in numbers and OFF THE PLANS' OWN ENTRIES AND THE PLANNER's RECORDS, at a handed radius,
without the planner's prices: from two tests on natural numbers, the library's condition on the fold
holds at `ptCount`, and the block's error for the records' number of requests, at that count, is at
most 2^-128 of the round's written verifier messages. No numeral of a plan is written here.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/: files
adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Johnson/Bridge/PointAtPlan.lean has the pair at a table of the planner's, the second half as the
planner's cover. Here the second half is a comparison of numbers: `ptCount` holds the integer part
of `Cb.bchksBound`, which no program runs; `brOf` (Johnson/Bridge/BrOf.lean) proposes a bracket of
it and `Cb.CntLe` tests the bracket.

Main names:
  `PointPlace`: a table, a radius, the number of column variables, the number of requests.
  `PointPlace.top`: `ptCount` with the bracket's bound in the place of the integer part.
  `PointPlace.cnt`: `LdLinP.errPtB` (Cb/Ld/LdLinB.lean) at `top`, written out at q = p^3.
  `PointPlace.good`: `Cb.Bridge.foldTest` at the radius, twice, and the bracket's test.
  `PointPlace.priced`: the comparison of `below_of_num`.
  `PointPlace.ptCount_le`, `PointPlace.below`: what each yes gives.
  `PointPlace.block`: THE PAIR, for every test P on a table under that code with both radii the
    place's, the format's matrix and the place's numbers of variables.
  `planLins Z`: the records of the two tests on a stored table: the proof file's, the key file's.
  `planPoints rT M`: each entry «LIN point» of the plans with the place of its number.
  `pointB e x`, `pointB_below`: the entry's form and the place's two tests; what a yes gives.
  `planPointsB rT M`: THE TEST. `planPointsB_two`, `planPointsB_at`, `planPointsB_below`: what its
    yes gives.
  `planRadiusB ρ rT M`: `planAllB` (Johnson/Bridge/PlanTables.lean) and `planPointsB`, at one
    radius. `planRadiusB_parts`.

Limits: THE RADIUS IS WHATEVER THE CALLER SAYS: no statement here ties it to a protocol, and it is
one number for both tables and for both radii of the block. BY READING, A SMALLER RADIUS MAKES BOTH
COUNTS SMALLER; AT THE STORED SETS THE TEST SAID YES FROM THE RADIUS 1 ON; what holds the radius
from below is `planLocB` at the same radius (Johnson/Bridge/PlanLoc.lean): `planRadiusB` takes
`planAllB` with it. `priced` WITHOUT `good` SAYS NOTHING: `cnt` is made of a proposed bracket and of
a list that is 0 beyond the Johnson radius. The test P is a parameter: that its matrix is the
format's and that its numbers of row and column variables are the table's and the sizes' are
hypotheses. The condition speaks of the tables without a collision at the record's seed. WHICH ENTRY
BELONGS TO WHICH TABLE IS BY ORDER ALONE. The number of requests is the records'
(`LinSize.instances`): that no more share a point is not said here. That the records and plans are
those of a file's public files is asked where they are made. That the rounds of a plan are rounds of
the description of the protocol that a verifier runs is not said here. The test has been EVALUATED
at stored sets of public files, in a file that is not in this repository; no theorem says that it
says yes at any plan. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.PlanTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin
open Cb.Bridge
open scoped ENNReal

/-! ## At letters -/

theorem point_num (v B B' Lm Q : ℕ) (h : B ≤ B') :
    v * B * Q ^ (v - 1) + Lm * (v * Q ^ (v - 1)) ≤ v * B' * Q ^ (v - 1) + Lm * (v * Q ^ (v - 1)) :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) _

/-- The typed values of a written round that draws m elements and nothing else. -/
theorem nVals_point {d : PQ.RD} {m : ℕ} (hP : d.entry.poss = 0) (hE : d.entry.drawE = m)
    (hZ : d.entry.drawNZ = 0) (hT : d.entry.trits = 0) (hk1 : d.kind ≠ .seeds)
    (hk2 : d.kind ≠ .sealed) (Q : ℕ) (hq : Fintype.card GE = Q) :
    nVals (Fmt.dsOf d.entry d.kind) = Q ^ m := by
  rw [nVals_dsOf _ _ hk1 hk2, hP, hE, hZ, hT, ← hq, card_GE]
  simp

/-! ## The round in numbers -/

/-- A table, a radius, the number of column variables, the number of requests. -/
structure PointPlace where
  T : TableSize
  e : ℕ
  klo : ℕ
  N : ℕ

namespace PointPlace
variable (x : PointPlace)

/-- The code's length. -/
def n : ℕ := 2 ^ x.T.code.logN

/-- The code's dimension. -/
def k : ℕ := x.T.code.r + x.T.code.ell - 1

/-- The bracket of `Cb.bchksBound` at the code and the radius, by `brOf`. -/
def br : Br := brOf x.n x.k x.e

/-- `ptCount` with the bracket's bound in the place of the integer part. -/
def top : ℕ :=
  x.T.v * x.br.N * (Cb.Gl.p ^ 3) ^ (x.T.v - 1) +
    listMax x.n (x.n - x.k) x.e * (x.T.v * (Cb.Gl.p ^ 3) ^ (x.T.v - 1))

/-- The block's error at `top`, for N requests. -/
def cnt : ℕ :=
  x.top * (Cb.Gl.p ^ 3) ^ x.klo +
    x.N * ((x.T.v + x.klo) * (Cb.Gl.p ^ 3) ^ (x.T.v + x.klo - 1))

/-- The number of all points. -/
def all : ℕ := (Cb.Gl.p ^ 3) ^ (x.T.v + x.klo)

/-- The test on the code's sizes and the radius, and the bracket's test. -/
def good : Bool := foldTest x.T x.e x.e && x.br.ok x.n x.k x.e

/-- The comparison of `below_of_num`. -/
def priced : Bool :=
  decide (x.cnt * 2 ^ 193 + 3 * (x.T.v + x.klo + 0) * x.all ≤ x.all * 2 ^ (0 + 65))

variable {x}

/-- The planner's count is at most `top`. -/
theorem ptCount_le (h : x.good = true) : ptCount x.T x.e (Cb.Gl.p ^ 3) ≤ x.top := by
  simp only [good, Bool.and_eq_true] at h
  obtain ⟨hn, hw, _⟩ := foldTest_sound h.1
  rw [ptCount_eq x.T x.n x.k (x.n - x.k) x.T.v (Cb.Gl.p ^ 3) x.e hn hw rfl rfl]
  unfold top
  exact point_num _ _ _ _ _ (Br.le h.2)

/-- **The count against 2^-128**, in every written round that draws one element for each coordinate
of the point and nothing else, without work (of a kind other than seeds and sealed; its entry's logN
at most 64). -/
theorem below (h : x.priced = true) (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hP : d.entry.poss = 0) (hE : d.entry.drawE = x.T.v + x.klo) (hZ : d.entry.drawNZ = 0)
    (hT : d.entry.trits = 0) (hW : d.entry.work = 0) (hk1 : d.kind ≠ .seeds)
    (hk2 : d.kind ≠ .sealed) : RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog (by rw [hZ]; exact Nat.zero_le _) (fun _ => by rw [hW]; decide)
    x.cnt x.all (nVals_point hP hE hZ hT hk1 hk2 _ Cb.Gl.gl_card.2.1)
    (Nat.pow_pos (Cb.Gl.gl_card.2.1 ▸ card_GE_pos)) ?_
  simp only [hE, hZ, hW]
  exact of_decide_eq_true h

/-- **The condition on the fold at `ptCount`, and the block's error at that count against 2^-128**,
from a yes of the two tests. -/
theorem block (hg : x.good = true) (hp : x.priced = true) {J Y : Type} [Fintype J]
    (P : LdLinP GE (Fin (2 ^ (codeOfSize x.T.code).a))
      (Fin ((codeOfSize x.T.code).r + (codeOfSize x.T.code).l)) J Y)
    (he : P.e' = x.e) (hM : P.D.X.eM = x.e) (hG : P.D.X.G = genOf (codeOfSize x.T.code))
    (hv : P.D.X.v = x.T.v) (hkl : P.D.klo = x.klo) :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1) (ptCount x.T x.e (Fintype.card GE)) ∧
      ∀ d : PQ.RD, d.entry.logN ≤ 64 → d.entry.poss = 0 → d.entry.drawE = x.T.v + x.klo →
        d.entry.drawNZ = 0 → d.entry.trits = 0 → d.entry.work = 0 → d.kind ≠ .seeds →
        d.kind ≠ .sealed →
        RoundBelow (P.errPtB (ptCount x.T x.e (Fintype.card GE)) x.N) d
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hg' := hg
  simp only [good, Bool.and_eq_true] at hg'
  have h1 : foldTest x.T P.e' P.D.X.eM = true := by
    rw [he, hM]
    exact hg'.1
  obtain ⟨hn, hw, ha, hk, hr, he0, hle, hM', hJ⟩ := foldTest_sound h1
  refine ⟨?_, fun d hlog hP hE hZ hT hW hk1 hk2 => ?_⟩
  · have := foldErr_lin_ptCount (codeOfSize x.T.code) P x.T hn hw hv ha hk hr hG he0 hle hM' hJ
    rwa [he] at this
  · refine RoundBelow.mono ?_ (below hp d hlog hP hE hZ hT hW hk1 hk2)
    unfold LdLinP.errPtB cnt
    rw [hv, hkl, Cb.Gl.gl_card.2.1]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (ptCount_le hg)) _

end PointPlace

/-! ## Off the plans' entries and the records -/

/-- The records of the two tests on a stored table: the proof file's, the key file's. -/
def planLins (Z : Params.Sized) : List (TableSize × Option LinSize) :=
  [(Z.proof.batch.table, linSizeOf Z.proof.codes Z.proof.batch),
    (Z.key.once.table, linSizeOf Z.key.codes Z.key.once)]

/-- The plans' entries «LIN point», in the plans' order. -/
def pointEntries (M : Configured) : List Fmt.Entry :=
  (M.proof ++ M.key ++ [M.entry]).flatMap fun P =>
    P.plan.entries.filter fun e => e.name == "LIN point"

/-- **Every entry «LIN point»**, with the place of its number. -/
def planPoints (rT : ℕ) (M : Configured) : List (Fmt.Entry × PointPlace) :=
  (pointEntries M).zipWith
    (fun e p => (e, ⟨p.1, rT, (p.2.map (·.kLo)).getD 0, (p.2.map (·.instances)).getD 0⟩))
    (planLins M.sized)

/-- The entry draws one element for each coordinate of the place's point and nothing else, without
work; there is a request; the place's two tests say yes. -/
def pointB (e : Fmt.Entry) (x : PointPlace) : Bool :=
  decide (e.logN ≤ 64) && Nat.beq e.poss 0 && Nat.beq e.drawE (x.T.v + x.klo) &&
    Nat.beq e.drawNZ 0 && Nat.beq e.trits 0 && Nat.beq e.work 0 && decide (1 ≤ x.N) && x.good &&
    x.priced

/-- A yes: the count against 2^-128, in every written round with that entry (of a kind other than
seeds and sealed). -/
theorem pointB_below {e : Fmt.Entry} {x : PointPlace} (h : pointB e x = true) (d : PQ.RD)
    (hd : d.entry = e) (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    RoundBelow x.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  subst hd
  simp only [pointB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlog, hP⟩, hE⟩, hZ⟩, hT⟩, hW⟩, _⟩, _⟩, hp⟩ := h
  exact PointPlace.below hp d hlog (Nat.eq_of_beq_eq_true hP) (Nat.eq_of_beq_eq_true hE)
    (Nat.eq_of_beq_eq_true hZ) (Nat.eq_of_beq_eq_true hT) (Nat.eq_of_beq_eq_true hW) hk1 hk2

/-- **The test on the plans' entries and the planner's records, at a radius.** -/
def planPointsB (rT : ℕ) (M : Configured) : Bool :=
  Nat.beq (pointEntries M).length (planLins M.sized).length &&
    ((planLins M.sized).all fun p => p.2.isSome) &&
    ((planPoints rT M).all fun p => pointB p.1 p.2)

/-- A yes of the test: the plans hold two entries «LIN point». -/
theorem planPointsB_two {rT : ℕ} {M : Configured} (h : planPointsB rT M = true) :
    (pointEntries M).length = 2 :=
  Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1

/-- **A yes of the test: both tests of every place**, so that `PointPlace.block` can be spent. -/
theorem planPointsB_at {rT : ℕ} {M : Configured} (h : planPointsB rT M = true) :
    ∀ p ∈ planPoints rT M, p.2.good = true ∧ p.2.priced = true := fun p hp => by
  have := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 p hp
  simp only [pointB, Bool.and_eq_true] at this
  exact ⟨this.1.2, this.2⟩

/-- **A yes of the test: at every entry «LIN point» the count is at most 2^-128 of the round's
written verifier messages** (of a kind other than seeds and sealed). -/
theorem planPointsB_below {rT : ℕ} {M : Configured} (h : planPointsB rT M = true) :
    ∀ p ∈ planPoints rT M, ∀ d : PQ.RD, d.entry = p.1 → d.kind ≠ .seeds → d.kind ≠ .sealed →
      RoundBelow p.2.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun p hp d =>
  pointB_below (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 p hp) d

/-- **The test with `planAllB` as one**: the tables' radius is then held from both sides. -/
def planRadiusB (ρ : Rad) (rT : ℕ) (M : Configured) : Bool := planAllB ρ rT M && planPointsB rT M

theorem planRadiusB_parts {ρ : Rad} {rT : ℕ} {M : Configured} (h : planRadiusB ρ rT M = true) :
    planAllB ρ rT M = true ∧ planPointsB rT M = true := Bool.and_eq_true_iff.1 h

end Johnson.Bridge

#print axioms Johnson.Bridge.PointPlace.ptCount_le
#print axioms Johnson.Bridge.PointPlace.below
#print axioms Johnson.Bridge.PointPlace.block
#print axioms Johnson.Bridge.planPointsB_two
#print axioms Johnson.Bridge.planPointsB_at
#print axioms Johnson.Bridge.planPointsB_below
#print axioms Johnson.Bridge.planRadiusB_parts
