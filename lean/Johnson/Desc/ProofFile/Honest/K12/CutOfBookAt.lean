-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CutOfBookAt.lean: at the jobs of the shared chain's two proximity
tests (`jobAtU`, `jobAtOmega`, JobShared.lean): where the frame has lent the test's second part its
random values and the book passes a public test, the premises `SameCut` (TreeIsColumnAt.lean) and
`SameFresh` (FreshAtJob.lean) hold at the lent values; and so the column of a tree that the first
round of positions opens is, at every position, the column of the table that the sending built at
the sender's own lent values. It imports Mathlib.

  `bookCutsU`, `bookCutsOmega`   the public test on the book, for each test: `cutFits`
                 (CutOfBook.lean) at each entry by which the test's second part carries: o_u, o_sp
                 and the riding fresh table; o_omega and o_sp
  `cuts_atU`, `cuts_atOmega`   `SameCut` at each member, and `SameFresh` at the test on G_u
  `tree0_lent_U`, `tree1_lent_U`, `tree0_lent_Omega`, `tree1_lent_Omega`   the four statements of
                 TreeIsColumnAt.lean at the lent values

The values. C is `carriedCoins J (stretches _ c.2.2)` (Sim/Row.lean), where c is what `lendPart` has
lent the part `restPart J`. The sender's cs is `(coinsE own).toArray`, where own is the sender's
purse cut from 0 by its count, as `lendPart` cuts it.

By what. `sameCut_of_book` (CutOfBook.lean); `freshDue_atU` (FitSharedLaw.lean); `sameFresh_of`
(FreshAtJob.lean); the four statements of TreeIsColumnAt.lean, called.

Limits.
- No book is shown to pass `bookCutsU` or `bookCutsOmega`, at a small plan or at the real size.
- "The same vector" stays a premise of the two statements on a tree with main rows.
- That the frame lends is a premise: nothing here shows that `lendPart` returns.
- The first part's carried entries are not treated.
- All limits of TreeIsColumnAt.lean but the one on `SameCut` and `SameFresh` stand.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (zeroE)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf takesOf columnOf Ask sendingsFit sendPlace)

variable {V W X : Type}

/-! ## 1 The test on the book -/

/-- **For the test on G_u**: the second part carries o_u, o_sp and the riding fresh table. -/
def bookCutsU (Bk : ProverCoinCounts) (A : SendPub) (p : P12) : Bool :=
  cutFits Bk ⟨p.place, 1⟩ 0 ⟨sendPlace 2, 0⟩ (jobU A) 0 &&
    cutFits Bk ⟨p.place, 1⟩ 1 ⟨sendPlace 5, 0⟩ (jobOmega A) 1 &&
    cutFits Bk ⟨p.place, 1⟩ 2 ⟨sendPlace 2, 0⟩ (jobU A) 1

/-- **For the test on G_omega**: the second part carries o_omega and o_sp. -/
def bookCutsOmega (Bk : ProverCoinCounts) (A : SendPub) (p : P12) : Bool :=
  cutFits Bk ⟨p.place, 1⟩ 0 ⟨sendPlace 5, 0⟩ (jobOmega A) 0 &&
    cutFits Bk ⟨p.place, 1⟩ 1 ⟨sendPlace 5, 0⟩ (jobOmega A) 1

/-! ## 2 The cuts -/

section Lent
variable (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (A : SendPub)
  (p : P12) (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
  (v? : Option (W → Front X → ℕ → OnBytes.E))
  (ownU : Cs (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort))
  (hU : (look ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩
    (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) = some ownU)
  (ownO : Cs (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort))
  (hOm : (look ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
    (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) = some ownO)

include hU hOm in
theorem cuts_atU
    (c : (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsU Bk A p = true) (hfr : freshFitsU A p = true) :
    SameCut (jobU A) 0 (coinsE ownU).toArray
        ((carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)).mem 0) ∧
      SameCut (jobOmega A) 1 (coinsE ownO).toArray
        ((carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)).mem 1) ∧
      SameFresh (stage₀ p) (fun i => (coinsE ownU).toArray.getD
          (offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 + i) zeroE)
        (carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)) := by
  unfold bookCutsU at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨b0, b1⟩, b2⟩ := hb
  refine ⟨sameCut_of_book Bk rows look _ _ c hl _ (jobU A) ownU hU 0 0 b0,
    sameCut_of_book Bk rows look _ _ c hl _ (jobOmega A) ownO hOm 1 1 b1,
    sameFresh_of _ _ _ (fun n hn => ?_) rfl⟩
  exact sameCut_of_book Bk rows look _ _ c hl _ (jobU A) ownU hU 2 1 b2 n
    (by rw [freshDue_atU A p hfr]; exact hn)

include hOm in
theorem cuts_atOmega
    (c : (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsOmega Bk A p = true) :
    SameCut (jobOmega A) 0 (coinsE ownO).toArray
        ((carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)).mem 0) ∧
      SameCut (jobOmega A) 1 (coinsE ownO).toArray
        ((carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)).mem 1) := by
  unfold bookCutsOmega at hb
  simp only [Bool.and_eq_true] at hb
  exact ⟨sameCut_of_book Bk rows look _ _ c hl _ (jobOmega A) ownO hOm 0 0 hb.1,
    sameCut_of_book Bk rows look _ _ c hl _ (jobOmega A) ownO hOm 1 1 hb.2⟩

/-! ## 3 The four trees' columns at the lent values -/

variable (hQ : sendingsFit A.P = true) (w : W) (fr : Front X) (st : State Ask Unit) (x : ℕ)

include hU hOm hQ in
/-- **o_u's tree, with the first fresh table that rides in it.** -/
theorem tree0_lent_U
    (c : (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsU Bk A p = true) (hc : colFitsU A p = true) (hfr : freshFitsU A p = true)
    (hroom : 2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l)
    (hv : vecAt (jobU A) 0 (askOf A weights rand) v? w fr = (jobU A).data st 0) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)))).getD 0
          (0, fun _ => [])).2 x =
      columnOf (jobU A).Q.codes (jobU A).Q.sent ((jobU A).rows st (coinsE ownU).toArray) 0 x := by
  obtain ⟨s0, _, sf⟩ := cuts_atU Bk rows look A p door weights rand v? ownU hU ownO hOm c hl hb hfr
  exact tree0_atU A p door weights rand v? hQ w fr _ st _ x hc hfr hroom s0 sf hv

include hU hOm hQ in
/-- **o_sp's tree, at the test on G_u.** -/
theorem tree1_lent_U
    (c : (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsU Bk A p = true) (hc : colFitsU A p = true) (hfr : freshFitsU A p = true) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)))).getD 1
          (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 1 x := by
  obtain ⟨_, s1, _⟩ := cuts_atU Bk rows look A p door weights rand v? ownU hU ownO hOm c hl hb hfr
  exact tree1_atU A p door weights rand v? hQ w fr _ st _ x hc s1

include hOm hQ in
/-- **o_omega's tree.** -/
theorem tree0_lent_Omega
    (c : (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsOmega Bk A p = true) (hc : colFitsOmega A p = true)
    (hv : vecAt (jobOmega A) 0 (askOf A weights rand) v? w fr = (jobOmega A).data st 0) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)))).getD 0 (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 0 x := by
  obtain ⟨s0, _⟩ := cuts_atOmega Bk rows look A p door weights rand v? ownO hOm c hl hb
  exact tree0_atOmega A p door weights rand v? hQ w fr _ st _ x hc s0 hv

include hOm hQ in
/-- **o_sp's tree, at the test on G_omega.** -/
theorem tree1_lent_Omega
    (c : (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsOmega Bk A p = true) (hc : colFitsOmega A p = true) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)))).getD 1 (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 1 x := by
  obtain ⟨_, s1⟩ := cuts_atOmega Bk rows look A p door weights rand v? ownO hOm c hl hb
  exact tree1_atOmega A p door weights rand v? hQ w fr _ st _ x hc s1

end Lent

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.bookCutsU
#print axioms ProofFile.Honest.K12.Light.bookCutsOmega
#print axioms ProofFile.Honest.K12.Light.cuts_atU
#print axioms ProofFile.Honest.K12.Light.cuts_atOmega
#print axioms ProofFile.Honest.K12.Light.tree0_lent_U
#print axioms ProofFile.Honest.K12.Light.tree1_lent_U
#print axioms ProofFile.Honest.K12.Light.tree0_lent_Omega
#print axioms ProofFile.Honest.K12.Light.tree1_lent_Omega
