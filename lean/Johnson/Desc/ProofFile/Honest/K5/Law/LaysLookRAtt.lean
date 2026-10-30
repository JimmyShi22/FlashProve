-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LaysLookRAtt.lean: CONDITIONAL: `k5_lays_lookR`
(Honest/K5/Law/LaysLookR.lean) WITH ITS CLAUSE SAID AS THE TERM `riderAtt`
(Honest/Thread/RidersAtt.lean): the clause "the chain stands in an attention segment, and P holds of
that part", at P := fun v => `lookR` a v.g. One term: the written clause and `riderAtt`'s are one by
unfolding. It proves nothing new.

  `k5_lays_lookR_att`   CONDITIONAL: under h; g below 12; the group's plan a: `LaysAt` at the member
                        number 14 (2 g + 1) + 3, of `riderAtt` (14 (2 g + 1) + 4) (14 (2 g + 1) + 9)
                        fun v => `lookR` a v.g

Why. The two lemmas by which such a clause stays past a member (`staysBy_att_of`,
`staysBy_att_read`, in that file) are typed at `riderAtt`. So whoever joins "laid" and "stays" wants
both at one term.

Limits. As Honest/K5/Law/LaysLookR.lean's. THAT THE CLAUSE STAYS PAST ANY MEMBER IS NOT HERE. h is a
hypothesis of every statement that names it. At the library's full size and the format's second
hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysLookR
import Johnson.Desc.ProofFile.Honest.Thread.RidersAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.Sound (seatTab Mem MsgT)
open H2K5.Honest (lookR)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **THE LOOKUP's MEMBER LAYS `riderAtt` AT `lookR`.** CONDITIONAL: under the hypothesis h; g is
below 12; the group's plan. -/
theorem k5_lays_lookR_att {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    LaysAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
      (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun v => lookR a v.g) :=
  k5_lays_lookR h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg ha

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lays_lookR_att
