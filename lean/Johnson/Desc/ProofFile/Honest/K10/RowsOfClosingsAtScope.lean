-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/RowsOfClosingsAtScope.lean: the rows of the closings (kind K10) at
the description's own blocks: at every link below 25, in scope, `Good` holds of the side that
`Side.seated` yields at the closing's place, under the block's own test on the plan and the premise
on the book. `Good` is stated at A := B := False and says of `exact` the spender's half alone, as
Honest/K10/RowsOfClosings.lean says.

  `closingJob_is`, `closingPairs_is`   the job and the pairs are `lotJob` and `closeRow`
  `closing_good_at_scope`   the statement

At the chain c of `IM.Open`: that the description's first chain is c is not carried here.
-/
import Johnson.Desc.ProofFile.Honest.K10.RowsOfClosings
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

variable {W₀ Rc Xi Tr X : Type}

theorem closingJob_is (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) :
    closingJob readers rows stAt Z G Q = lotJob readers rows stAt Z G Q := rfl

theorem closingPairs_is {V W Y Pb : Type} (J : CloseJob W) :
    (closingPairs J : List (Part V W Y × Sim Pb)) = closeRow J := rfl

/-- **AT EVERY LINK BELOW 25, IN SCOPE.** -/
theorem closing_good_at_scope (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : ProofFile.Ground) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b ∧
      (b.planOk = true → ∀ fs : List (Fall S),
        ∃ σ : Side S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
          Side.seated c.blocksInOrder (closePlace Q) (closingPairs (closingJob readers rows stAt Z G Q)) fs =
            some σ ∧
          σ.block = b ∧
          (∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (chain firstTree : Nat),
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt Z G Q)) closeBud) ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts) (ord : List Place)
            (chain firstTree : Nat), (∀ q, Bk.spentBy ⟨closePlace Q, 0⟩ q = []) →
            Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt Z G Q)) closeBud) := by
  obtain ⟨p, Q, b, hT, hall⟩ := member_at_scope (V := Local W₀ Rc Xi Tr)
    (W := Local W₀ Rc Xi Tr) (X := X) (Pb := Xi) hS hR O l hl
  refine ⟨p, Q, b, hT, fun hb fs => ?_⟩
  obtain ⟨σ, hσ, hbl, -, hm, hf⟩ := hall (closingJob readers rows stAt Z G Q) rfl fs
  refine ⟨σ, hσ, hbl, fun pre chain firstTree =>
    closing_shows_some pre Face.own chain firstTree _ (hT.plan hb) hm,
    fun pre Bk ord chain firstTree hk => ?_⟩
  have hk' : ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = [] := by
    rw [hbl, hT.2.2.2.2.2.1]
    exact hk
  exact closing_good pre Face.own Bk ord chain firstTree _ (hT.plan hb) hm hf hk'

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closingJob_is
#print axioms ProofFile.Honest.K10.closingPairs_is
#print axioms ProofFile.Honest.K10.closing_good_at_scope
