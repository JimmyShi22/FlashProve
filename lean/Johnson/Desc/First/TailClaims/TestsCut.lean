-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/TestsCut.lean: THE SMALLNESS TEST's THREE STEPS BEHIND A SUB-PROOF's
LAST CLAIM (`testsP`, SelfRows.lean in this folder) RETURN JUST IF THREE OPTIONS ARE `some` AND TWO
BOOLS ACCEPT: `shapeT`, six guards on sizes, counts, names and kinds, and `valsT`, the guards on
field elements: `tests_iff`. Seven definitions, five general theorems, by unfolding; nothing is
evaluated.

Purpose. To show that a step of the verifier returns, one needs "where the guards hold, the step
returns". The library's theorems on these three steps start from a return: `self_all` and `rk_all`
(EquationsSelf.lean) give the guards of the first and the third step; `tests_ok`
(EquationsTests.lean) gives that each of the three has returned; `tests_all` (CoefficientsAll.lean)
gives tl.heard and the ledger behind. All three files are in this folder. Here are the converses,
and the guards sorted by what they read.

The fifteen guards. testsP runs selfTestP (four guards), coefficientsP (it asks for tl.heard) and
rkSelfTestP (eleven guards, by the library's own count: three ask that an Option is `some`, the
first of them tl.heard again; then eight tests): SelfTests.lean and Coefficients.lean, in this
folder. Of the fifteen, three are these options, six go to shapeT, and six go to valsT, where they
are twelve conjuncts.

The three options. tl.heard and tl.joinObj9 are fields of the record; by their own comments
(OnBytes/Model/Tail.lean) the first is what the lookup has received and drawn, the second the index
of the claim on the lookup's key vectors. tl.wants IS NO FIELD: it is a function of tl.tau and tl.mz
(`wants`, the same file). It computes the number of blocks of ZZ's rows and the pieces of the two
calls a second time, and it is none just where tl.tau - 2 ^ Nat.log2 tl.tau is neither 0 nor a power
of two. SO THE THIRD OPTION IS A GUARD ON SIZES, AND IT STANDS OUTSIDE shapeT: shapeT is not all the
guards on sizes.

Main names.
* `self_of`: where selfTestP's four guards hold, it returns. `self_iff`: just if.
* `rk_of`: where rkSelfTestP's three options are `some` and its eight tests hold, it returns. (The
  converse is the library's rk_all.)
* `rowA`, `rowB`: the virtual rows number 2 nbW and 2 nbW + 1 of the array ZZ, which rkSelfTestP
  reads as the reads' row and the ties' row; see Limits. `headT`, `sizesT`: the first and the fifth
  of the eight tests. `rowPowers`: the first conjunct of the sixth.
* `shapeT nU tl g nbW Wn Fc`: nU == tl.nUF; tl.lsTail.size == tl.slotB - tl.slotA (the kept list is
  as long as the window of slots is wide); headT; piecesTile; sizesT; readShapeHeld.
* `valsT nU tl F g jo nbW Wn Fc`: selfUnits, selfDigits, selfLinked, selfPlanes, selfSymbols and
  selfSlots at F; pointsHeld; pieceWeightsHeld, rowPowers, tieWeightsHeld, planesWeightsHeld and
  readWeightsHeld at Fc.
* **`tests_returns`**: where the three options are `some`, shapeT accepts at coefBody tl g F, and
  valsT accepts at F and coefBody tl g F, testsP nU tl F returns coefBody tl g F. **`tests_iff`**:
  testsP nU tl F = .ok Fc just if the three are `some`, Fc = coefBody tl g F, shapeT accepts at Fc,
  and valsT accepts at F and Fc.

Limits. THAT shapeT READS NO FIELD ELEMENT IS A READING OF ITS PARTS' TEXTS, NOT A THEOREM:
forestHeld, callHeld, piecesTile, tieShapeHeld, planesShapeHeld and readShapeHeld
(OnBytes/Model/Tail.lean) compare numbers, names, kinds and the sizes of arrays. THE ROWS: rowA and
rowB take their numbers from nbW, which tl.wants computes; the library's own numbers of the reads'
row and the ties' row are zzRowReads tl = 2 * tl.blocks.size and zzRowTies tl, one more
(OnBytes/Model/Tail.lean), and coefBody sets the weights there (Coefficients.lean). That nbW =
tl.blocks.size is not shown here. shapeT is asked at Fc, the ledger BEHIND the step that sets the
weights: what it says of the ledger in front is not shown here. That either Bool accepts anywhere is
not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.CoefficientsAll
import Johnson.Desc.First.TailClaims.EquationsSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (self_all rk_all tests_ok)
open OnBytes.Tie.Pv.Tail.Port (excBind_ok)

variable {nU : Array Nat} {tl : HTailF2} {F Fc : Fork} {g : Forest.Heard} {jo nbW : Nat}
  {Wn : List Want}

/-! ## 1 The converses -/

/-- Where its four guards hold, the first test (selfTestP, SelfTests.lean) returns. -/
theorem self_of (h1 : (nU == tl.nUF) = true)
    (h2 : (selfUnits tl nU F && selfDigits tl F && selfLinked tl F && selfPlanes tl F &&
      selfSymbols tl F) = true)
    (h3 : (tl.lsTail.size == tl.slotB - tl.slotA) = true) (h4 : selfSlots tl F = true) :
    selfTestP tl nU F = .ok () := by
  unfold selfTestP
  rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
  rfl

/-- The first test returns just if its four guards hold: self_of, with the library's self_all
(EquationsSelf.lean). -/
theorem self_iff : selfTestP tl nU F = .ok () ↔
    (nU == tl.nUF) = true ∧
      (selfUnits tl nU F && selfDigits tl F && selfLinked tl F && selfPlanes tl F &&
        selfSymbols tl F) = true ∧
      (tl.lsTail.size == tl.slotB - tl.slotA) = true ∧ selfSlots tl F = true :=
  ⟨self_all tl nU F, fun ⟨h1, h2, h3, h4⟩ => self_of h1 h2 h3 h4⟩

/-- Virtual row number 2 nbW of the array ZZ: the row that rkSelfTestP reads as the reads' row. That
it is the library's zzRowReads is not shown here (the head's Limits). -/
abbrev rowA (tl : HTailF2) (nbW : Nat) (F : Fork) : HRow :=
  (F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}
/-- Virtual row number 2 nbW + 1 of the array ZZ: the row that rkSelfTestP reads as the ties' row.
That it is the library's zzRowTies is not shown here (the head's Limits). -/
abbrev rowB (tl : HTailF2) (nbW : Nat) (F : Fork) : HRow :=
  (F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}

/-- The first of the eight tests that stand behind the three options of rkSelfTestP
(SelfTests.lean). -/
def headT (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (F : Fork) : Bool :=
  (F.trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
    [0, 1].all (tl.callHeld g nbW)

/-- The fifth of the eight tests: eight conjuncts on sizes and shapes. -/
def sizesT (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (F : Fork) : Bool :=
  (rowA tl nbW F).coef.size == tl.tau && (rowB tl nbW F).coef.size == tl.tau &&
    (rowB tl nbW F).L.size == 2 * tl.mz && tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
    (List.range tl.NM).all (tl.tieShapeHeld F) &&
    tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz && tl.planesShapeHeld F g

/-- The first conjunct of the sixth of the eight tests: the two rows' weights on the rows of their
array are the powers of the batching element. The library's text gives it no name. -/
def rowPowers (tl : HTailF2) (nbW : Nat) (F : Fork) : Bool :=
  (List.range tl.tau).all fun u =>
    (rowA tl nbW F).coef.getD u zeroE == powE F.theta u &&
      (rowB tl nbW F).coef.getD u zeroE == (rowA tl nbW F).coef.getD u zeroE

/-- Where the three options are `some` and the eight tests behind them hold, the test by a second
computation (rkSelfTestP) returns. -/
theorem rk_of (hg : tl.heard = some g) (hjo : tl.joinObj9 = some jo)
    (hw : tl.wants = some (nbW, Wn)) (h5 : headT tl g nbW F = true)
    (h7 : tl.piecesTile F Wn = true) (h8 : tl.pointsHeld g = true)
    (h10 : Wn.all (tl.pieceWeightsHeld F g (t2fKappaByText F.theta jo)) = true)
    (h12 : sizesT tl g nbW F = true)
    (h14 : (rowPowers tl nbW F && (List.range tl.NM).all (tl.tieWeightsHeld F (rowB tl nbW F).L) &&
      tl.planesWeightsHeld F g jo) = true)
    (h16 : tl.readShapeHeld (rowA tl nbW F).L = true)
    (h18 : tl.readWeightsHeld F (rowA tl nbW F).L = true) : rkSelfTestP tl F = .ok () := by
  unfold rkSelfTestP
  simp only [hg, hjo, hw]
  refine (if_pos h5).trans ?_
  refine (if_pos h7).trans ?_
  refine (if_pos h8).trans ?_
  refine (if_pos h10).trans ?_
  refine (if_pos h12).trans ?_
  refine (if_pos h14).trans ?_
  refine (if_pos h16).trans ?_
  exact if_pos h18

/-! ## 2 The guards, sorted -/

/-- **The guards on sizes, counts, names and kinds**: six of the fifteen. -/
def shapeT (nU : Array Nat) (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (Wn : List Want)
    (Fc : Fork) : Bool :=
  nU == tl.nUF && tl.lsTail.size == tl.slotB - tl.slotA && headT tl g nbW Fc &&
    tl.piecesTile Fc Wn && sizesT tl g nbW Fc && tl.readShapeHeld (rowA tl nbW Fc).L

/-- **The guards on field elements**: six of the fifteen, as twelve conjuncts: the five of "no
weight that must not be 0 is 0" and selfSlots, at the ledger in front; pointsHeld; five comparisons
at the ledger behind. -/
def valsT (nU : Array Nat) (tl : HTailF2) (F : Fork) (g : Forest.Heard) (jo nbW : Nat)
    (Wn : List Want) (Fc : Fork) : Bool :=
  selfUnits tl nU F && selfDigits tl F && selfLinked tl F && selfPlanes tl F &&
    selfSymbols tl F && selfSlots tl F && tl.pointsHeld g &&
    Wn.all (tl.pieceWeightsHeld Fc g (t2fKappaByText Fc.theta jo)) && rowPowers tl nbW Fc &&
    (List.range tl.NM).all (tl.tieWeightsHeld Fc (rowB tl nbW Fc).L) &&
    tl.planesWeightsHeld Fc g jo && tl.readWeightsHeld Fc (rowA tl nbW Fc).L

/-- **Where the three options are `some` and both Bools accept, the three steps return.** -/
theorem tests_returns (hg : tl.heard = some g) (hjo : tl.joinObj9 = some jo)
    (hw : tl.wants = some (nbW, Wn)) (hS : shapeT nU tl g nbW Wn (coefBody tl g F) = true)
    (hV : valsT nU tl F g jo nbW Wn (coefBody tl g F) = true) :
    testsP nU tl F = .ok (coefBody tl g F) := by
  simp only [shapeT, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩ := hS
  simp only [valsT, Bool.and_eq_true] at hV
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, v9⟩, v10⟩, v11⟩, v12⟩ := hV
  have a : selfTestP tl nU F = .ok () :=
    self_of s1 (by simp only [v1, v2, v3, v4, v5, Bool.and_self]) s2 v6
  have b : coefficientsP tl F = .ok (coefBody tl g F) := by
    unfold coefficientsP
    rw [hg]
  have c : rkSelfTestP tl (coefBody tl g F) = .ok () :=
    rk_of hg hjo hw s3 s4 v7 v8 s5 (by simp only [v9, v10, v11, Bool.and_self]) s6 v12
  unfold testsP
  rw [a, b]
  show (rkSelfTestP tl (coefBody tl g F) >>= fun _ => pure (coefBody tl g F)) = _
  rw [c]
  rfl

/-- **THE CUT**: the three steps return Fc just if the three options are `some`, Fc is F with the
virtual rows' weights set (coefBody), and shapeT and valsT accept. -/
theorem tests_iff : testsP nU tl F = .ok Fc ↔
    ∃ g jo nbW Wn, tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, Wn) ∧
      Fc = coefBody tl g F ∧ shapeT nU tl g nbW Wn Fc = true ∧
      valsT nU tl F g jo nbW Wn Fc = true := by
  constructor
  · intro h
    obtain ⟨a, b, c⟩ := tests_ok h
    obtain ⟨s1, v15, s2, v6⟩ := self_all tl nU F a
    obtain ⟨g, jo, nbW, Wn, hg, hjo, hw, s3, s4, v7, v8, s5, v911, s6, v12⟩ := rk_all tl Fc c
    have e : Fc = coefBody tl g F := by
      unfold coefficientsP at b
      rw [hg] at b
      exact (Except.ok.inj b).symm
    refine ⟨g, jo, nbW, Wn, hg, hjo, hw, e, ?_, ?_⟩
    · simp only [shapeT, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩
    · simp only [Bool.and_eq_true] at v15 v911
      obtain ⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩ := v15
      obtain ⟨⟨v9, v10⟩, v11⟩ := v911
      simp only [valsT, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, v9⟩, v10⟩, v11⟩, v12⟩
  · rintro ⟨g, jo, nbW, Wn, hg, hjo, hw, rfl, hS, hV⟩
    exact tests_returns hg hjo hw hS hV

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.self_of
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.self_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.rk_of
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_iff
