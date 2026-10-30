-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FullEqUnit.lean: HOW MUCH OF "THE TABLE's ARRAY HAS ONE ROW" THE FIELD
fuEq (FullEq.lean) AND ITS SPENDERS USE, AND WHAT A YES OF THE RUN OF SELF TESTS GIVES OF IT.
Theorems. A law file; no running text imports it.

Why. `UnitRow F t` (OnBytes/Tie/Pv/Tail/EndRaw.lean: R = 1, and the first virtual row's first weight
is 1) is taken apart at three places (EndRaw.lean: rawRows_tested's fourth part; EndPortUnit.lean:
portWorld_unit; EntryUnit.lean: unitAt_of_row), each time for one sum: an entry of the virtual row
is the sum, OVER THE ARRAY's R ROWS, of weight times cell. The run of self tests lays the WHOLE list
of weights #[1] on a table's first virtual row, whatever R is (`coefficientsF_unit`, EndCoef.lean):
a weight beyond the list reads 0. So at every R > 0 the sum is the cell of row 0; at R = 0 it is
empty.
  `unitAt_run`      behind the routine that lays the weights, a table's vector WITH A ROW (0 < R)
                    has `UnitAt F2 tU 0` (EntryUnit.lean): unitRow_run (EndChain.lean) with R = 1
                    weakened.
  `hasRow_of_selfTest`   a yes of the first self test: where the plan's number of entries of table n
                    (n < 3) is not 0, its array is there and has a first virtual row.
  `entry_zero`, `not_unitAt_zero`   THE REFUTING VALUE: at R = 0 every entry of every virtual row of
                    the array is 0, and `UnitAt` fails: so "0 < R" cannot be dropped.
  `fuEq_full2`      FullEq.lean's fuEq_full with `UnitAt … 0` in `UnitRow`'s place, and its fourth
                    premise CUT TO TWO CLAUSES: the kind is "table"; 0 < R. The clause "has a first
                    virtual row" is PAID from the run of self tests, under one clause more on the
                    promise: the read's table is one of the FIRST THREE vectors and the plan's
                    number of its entries is not 0 (okApart).
THE CUT PREMISE `shape` IS STILL NOT HAD FROM `Fx9` OR `FullAt`: "goes on" carries the arrays'
widths alone, and the run of self tests reads of a table's array the kind (only to choose whether it
writes), the width and the rows' column weights: not R. Put R := 0, or another kind, in the ledger:
every other hypothesis still holds. SO IT IS TRUE ONLY WHERE IT IS EMPTY, UNTIL SOMETHING PINS THE
KIND AND R. This file narrows what a cure must carry; it pays nothing.
The proof of fuEq_full2 follows fuEq_full's, line by line, but for its third part.

Limits. Implications. Nothing is evaluated. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.FullEq
import Johnson.Desc.First.Link.Law.EntryUnit
import Johnson.Desc.First.TailClaims.EquationsSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU UApart hasRow shapeAt coefAt
  coefficientsF_shape coefficientsF_unit)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (selfTestP rkSelfTestP coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (blank coefBody_all self_tested)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (UnitAt)

/-- Behind the routine that lays the weights, a table's vector with a row is a unit at its first
virtual row. -/
theorem unitAt_run (tl : HTailF2) (n0 tU : Nat) (F1 F2 : Fork) (c c' : Ctx)
    (A : UApart tl n0 tU F1) (hR : 0 < (F1.trees.getD tU {}).R)
    (h : tl.coefficientsF F1 c = .ok (((), F2), c')) : UnitAt F2 tU 0 := by
  have e := (coefficientsF_shape tl F1 F2 c c' h).1 tU
  have eR : (shapeAt F2 tU).2.1 = (shapeAt F1 tU).2.1 := by rw [e]
  have eR' : (F2.trees.getD tU {}).R = (F1.trees.getD tU {}).R := eR
  have ec := coefficientsF_unit tl n0 tU F1 F2 c c' A h
  unfold coefAt at ec
  refine ⟨by rw [eR']; exact hR, fun j _ => ?_⟩
  rw [ec]
  cases j with
  | zero => rfl
  | succ k => rfl

/-- Outside an array the default is returned. -/
theorem getD_beyond {α : Type} (a : Array α) (i : Nat) (d : α) (h : ¬ i < a.size) :
    a.getD i d = d := by
  simp [Array.getD, h]

/-- **A yes of the first self test: a table with entries is there, and has a first virtual row.** -/
theorem hasRow_of_selfTest (tl : HTailF2) (nU : Array Nat) (F : Fork)
    (h : selfTestP tl nU F = .ok ()) (n : Nat) (hn : n < 3) (t : Nat)
    (ht : tl.ix.U.getD n none = some t) (h0 : 0 < nU.getD n 0) : hasRow F t 0 := by
  have hz := (self_tested tl nU F h).2.1.units n hn t ht 0 h0
  rw [Nat.zero_div, Nat.zero_mod] at hz
  unfold weightsOf at hz
  by_contra hc
  have e : ((F.trees.getD t {}).rows.getD 0 {}).L = #[] := by
    by_cases h1 : t < F.trees.size
    · have h2 : ¬ 0 < (F.trees.getD t {}).rows.size := fun h2 => hc ⟨h1, h2⟩
      rw [getD_beyond _ _ _ h2]
    · rw [getD_beyond F.trees t {} h1]
      rfl
  rw [e] at hz
  cases hz

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **The refuting value**: at an array without a row every entry of every virtual row is 0. -/
theorem entry_zero (L : LinkCtx) (F : Fork) (D : Bound K) (t r i : ℕ)
    (h : (F.trees.getD t {}).R = 0) : (worldAt ρ L F D).entry t r i = 0 := by
  rw [worldAt_readsRow ρ L F D t r i, h, Finset.range_zero, Finset.sum_empty]

end

/-- And no virtual row of it is a unit. -/
theorem not_unitAt_zero (F : Fork) (t r : ℕ) (h : (F.trees.getD t {}).R = 0) : ¬ UnitAt F t r :=
  fun u => by
    have := u.1
    omega

variable {β : Type}

/-- **THE FIELD fuEq AT `FullAt nU`, WITH `UnitAt`, ITS FOURTH PREMISE CUT TO TWO CLAUSES.** -/
theorem fuEq_full2 (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (okBlocks : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb →
      tlb.wants.map (·.1) = some tlb.zzBlocks)
    (okPos : ∀ q tlb funs v, Ok q → pi8 q.1 = (some tlb, some funs) → q.2 = some v →
      ∀ x ∈ readsList tlb funs, ∀ d, d < (tlb.mats.getD x.1.mat {}).k →
        posOf tlb x.1 x.2 d < colsU v.F (uOf tlb x.1))
    (okApart : ∀ q tlb funs, Ok q → pi8 q.1 = (some tlb, some funs) →
      ∀ x ∈ readsList tlb funs, ∃ n0, n0 < 3 ∧ 0 < nU.getD n0 0 ∧
        tlb.ix.U.getD n0 none = some (uOf tlb x.1) ∧
        tlb.ix.ZZ ≠ uOf tlb x.1 ∧ tlb.ix.BZ ≠ uOf tlb x.1 ∧
        (∀ mu, mu < tlb.NM → tlb.gtTree.getD mu 0 ≠ uOf tlb x.1) ∧
        ∀ k p, p ∈ (tlb.zOf k).pieces.toList → p.tree ≠ uOf tlb x.1)
    (shape : ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      t.tl? = some ts → t.funs? = some funs → ∀ x ∈ readsList ts funs,
        ((b.F.trees.getD (uOf ts x.1) {}).kind == HKind.table) = true ∧
          0 < (b.F.trees.getD (uOf ts x.1) {}).R) :
    ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      t.tl? = some ts → t.funs? = some funs →
      rkSelfTestP ts b.F = .ok () ∧
        (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
        ∀ x ∈ readsList ts funs, UnitAt b.F (uOf ts x.1) 0 ∧
          ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1) := by
  intro q t b ts funs hf hfull hb hts hfu
  have hsh := shape q t b ts funs hf hfull hb hts hfu
  obtain ⟨e, he⟩ := hfull
  obtain ⟨F, tl, g, hF, htl, hg, hself, h3, rfl⟩ := k8Tests_ok nU e _ he
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (part_back e tl _ b hb)
  obtain ⟨a₁, ha₁, f1, _, _, f4, _, _⟩ := get_put e a ha tl (coefBody tl g F)
  have eb : a₁ = b := Option.some.inj (ha₁.symm.trans hb)
  subst eb
  have et : tl = ts := Option.some.inj (f4.symm.trans hts)
  subst et
  obtain ⟨hOk, hφ, v, b', hv, hb', hgo⟩ := hf
  have eb' : a₁ = b' := Option.some.inj (hb.symm.trans hb')
  subst eb'
  have hq1 : pi8 q.1 = (some (blank u tl), some funs) := by
    rw [← hφ]
    show ((S.tl? _).map (blank u), S.funs? _) = _
    rw [hts, hfu]
    rfl
  have hrk : rkSelfTestP tl a₁.F = .ok () := by
    rw [f1]
    exact h3
  refine ⟨hrk, ?_, fun x hx => ⟨?_, fun d hd => ?_⟩⟩
  · obtain ⟨nbW, W, hw, hr⟩ := rk_rows tl a₁.F hrk
    have e1 : (blank u tl).wants.map (·.1) = some (blank u tl).zzBlocks :=
      okBlocks q _ hOk (by rw [hq1])
    have e2 : tl.wants.map (·.1) = some tl.zzBlocks := e1
    rw [hw] at e2
    have e3 : nbW = tl.zzBlocks := Option.some.inj e2
    rw [hr, e3]
  · obtain ⟨n0, a1, a0, a2, a3, a4, a5, a6⟩ := okApart q _ funs hOk hq1 x hx
    obtain ⟨s2, s3⟩ := hsh x hx
    let c : Ctx := { ch := { dry := false, entries := [] } }
    have hrun := coefF_runs tl g hg F c
    obtain ⟨k1, _⟩ := coefficientsF_shape tl F _ c c hrun
    rw [f1, coefBody_all] at s2 s3 ⊢
    have k := k1 (uOf tl x.1)
    unfold shapeAt at k
    have kk : (((Fo.coefAll tl g F).trees.getD (uOf tl x.1) {}).kind) =
        (F.trees.getD (uOf tl x.1) {}).kind := congrArg (·.1) k
    have kR : (((Fo.coefAll tl g F).trees.getD (uOf tl x.1) {}).R) =
        (F.trees.getD (uOf tl x.1) {}).R := congrArg (·.2.1) k
    exact unitAt_run tl n0 (uOf tl x.1) F _ c c
      ⟨Nat.lt_succ_of_lt a1, a2, hasRow_of_selfTest tl nU F hself n0 a1 _ a2 a0,
        by rw [← kk]; exact s2, a3, a4, a5, a6⟩ (by rw [← kR]; exact s3) hrun
  · rw [colsU_goes hgo]
    exact okPos q _ funs v hOk hq1 hv x hx d hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.unitAt_run
#print axioms VerifiableInference.Desc.LinkJoin.hasRow_of_selfTest
#print axioms VerifiableInference.Desc.LinkJoin.entry_zero
#print axioms VerifiableInference.Desc.LinkJoin.not_unitAt_zero
#print axioms VerifiableInference.Desc.LinkJoin.fuEq_full2
