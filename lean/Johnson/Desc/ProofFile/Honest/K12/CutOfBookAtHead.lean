-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CutOfBookAtHead.lean: the four statements `tree0_lent_U`,
`tree1_lent_U`, `tree0_lent_Omega`, `tree1_lent_Omega` (CutOfBookAt.lean) under the library's head
(`P5J.AtMg`, Johnson/P5J/AtMg.lean), at the real plan's sendings and at the seated places of the two
shared tests: their public premises on the plan are paid there. A join: nothing new is shown.

  `tree0_lent_head_U`, `tree1_lent_head_U`, `tree0_lent_head_Omega`, `tree1_lent_head_Omega`
                 A is `⟨qAt Zp Np, n⟩` at every n, and p the seated place: both stay letters, each
                 with its equation as a premise, so that the statements keep the text of
                 CutOfBookAt.lean

Paid: `sendingsFit` (`sendingsFit_head`), `colFitsU` and `colFitsOmega` (`colFits_head`),
`freshFitsU` (`fits_at_head`, `freshFitsU_plan`), and the room for the riding table
(`room_head_U`): SendFitAtHead.lean and TreeIsColumnAtHead.lean.

Premises that stay. On the book, a public test: `bookCutsU` or `bookCutsOmega`. On the frame: that
`lendPart` has lent the second part its values, and that the senders' own values are cut as
`lendPart` cuts them. On the values: "the same vector", at the two trees with main rows.

Limits. All limits of CutOfBook.lean, CutOfBookAt.lean and TreeIsColumnAtHead.lean stand; first
among them: no book is shown to pass `bookCutsU` or `bookCutsOmega`.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (zeroE)
open VerifiableInference.Desc.K1 (qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf takesOf columnOf Ask sendingsFit sendPlace)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {V W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section Lent
variable (h : P5J.AtMg o Z D r Zp Np cF) (n : ℕ) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
  (look : Addr → (d : Due) × Cs d) (A : SendPub) (hA : A = ⟨qAt Zp Np, n⟩)
  (p : P12) (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
  (v? : Option (W → Front X → ℕ → OnBytes.E))
  (ownU : Cs (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort))
  (hU : (look ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩
    (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) = some ownU)
  (ownO : Cs (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort))
  (hOm : (look ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
    (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) = some ownO)
  (w : W) (fr : Front X) (st : State Ask Unit) (x : ℕ)

include h hA hU hOm in
/-- **o_u's tree, with the first fresh table that rides in it.** -/
theorem tree0_lent_head_U (hp : p = (fourOf Np).U)
    (c : (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsU Bk A p = true)
    (hv : vecAt (jobU A) 0 (askOf A weights rand) v? w fr = (jobU A).data st 0) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)))).getD 0
          (0, fun _ => [])).2 x =
      columnOf (jobU A).Q.codes (jobU A).Q.sent ((jobU A).rows st (coinsE ownU).toArray) 0 x := by
  subst hA
  subst hp
  exact tree0_lent_U Bk rows look _ _ door weights rand v? ownU hU ownO hOm (sendingsFit_head h) w
    fr st x c hl hb (colFits_head h n).1
    ((freshFitsU_plan ⟨qAt Zp Np, n⟩ _).trans (fits_at_head h).2.1) (room_head_U h) hv

include h hA hU hOm in
/-- **o_sp's tree, at the test on G_u.** -/
theorem tree1_lent_head_U (hp : p = (fourOf Np).U)
    (c : (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtU A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsU Bk A p = true) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtU A p door weights rand v?).toRun.toTest (stretches _ c.2.2)))).getD 1
          (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 1 x := by
  subst hA
  subst hp
  exact tree1_lent_U Bk rows look _ _ door weights rand v? ownU hU ownO hOm (sendingsFit_head h) w
    fr st x c hl hb (colFits_head h n).1
    ((freshFitsU_plan ⟨qAt Zp Np, n⟩ _).trans (fits_at_head h).2.1)

include h hA hOm in
/-- **o_omega's tree.** -/
theorem tree0_lent_head_Omega (hp : (fourOf Np).O = some p)
    (c : (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsOmega Bk A p = true)
    (hv : vecAt (jobOmega A) 0 (askOf A weights rand) v? w fr = (jobOmega A).data st 0) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)))).getD 0 (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 0 x := by
  subst hA
  obtain ⟨_, q, hq, a⟩ := colFits_head h n
  obtain rfl : q = p := Option.some.inj (hq.symm.trans hp)
  exact tree0_lent_Omega Bk rows look _ _ door weights rand v? ownO hOm (sendingsFit_head h) w fr
    st x c hl hb a hv

include h hA hOm in
/-- **o_sp's tree, at the test on G_omega.** -/
theorem tree1_lent_head_Omega (hp : (fourOf Np).O = some p)
    (c : (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X).Coins)
    (hl : lendPart Bk rows look ⟨p.place, 1⟩
      (restPart (jobAtOmega A p door weights rand v?).toRun.toTest : Part V W X) = .ok c)
    (hb : bookCutsOmega Bk A p = true) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr (stretches _ c.2.2)
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr
        (carriedCoins (jobAtOmega A p door weights rand v?).toRun.toTest
          (stretches _ c.2.2)))).getD 1 (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent
        ((jobOmega A).rows st (coinsE ownO).toArray) 1 x := by
  subst hA
  obtain ⟨_, q, hq, a⟩ := colFits_head h n
  obtain rfl : q = p := Option.some.inj (hq.symm.trans hp)
  exact tree1_lent_Omega Bk rows look _ _ door weights rand v? ownO hOm (sendingsFit_head h) w fr
    st x c hl hb a

end Lent

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tree0_lent_head_U
#print axioms ProofFile.Honest.K12.Light.tree1_lent_head_U
#print axioms ProofFile.Honest.K12.Light.tree0_lent_head_Omega
#print axioms ProofFile.Honest.K12.Light.tree1_lent_head_Omega
