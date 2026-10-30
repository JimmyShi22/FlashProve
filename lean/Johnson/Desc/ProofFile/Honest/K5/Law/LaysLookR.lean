-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LaysLookR.lean: CONDITIONAL: AT THE FIRST CHAIN's LETTERS AS
THEY ARE LAID (`lettersHead`, Honest/Thread/FirstHead.lean) THE MEMBER AT AN ATTENTION SEGMENT's
LOOKUP ON THE CALLS LAYS THE RIDER's CLAUSE "an attention link's own part v is open, and `lookR` a
v.g" (`LaysAt`, Honest/Thread/Riders.lean; `lookR`, Johnson/Desc/K5/Honest/Law/LookR.lean). One
term: two folders' texts set together: `lays_att_head` (Honest/K3/Law/Thread/LaysAttHead.lean),
which is general in a sentence R on the field g under a premise hR on R, at R := `lookR` a, with hR
paid by `lookR_of_hearVia` (Honest/K5/Law/LookRHeard.lean). It proves nothing new: it joins.

  `k5_lays_lookR`   CONDITIONAL: under h; g below 12; the group's plan a: **`LaysAt` at the member
                    number 14 (2 g + 1) + 3, of the clause from border 14 (2 g + 1) + 4 to border
                    14 (2 g + 1) + 9**

Limits. Conditional. `LaysAt` is a debt's form: from `Thr` in front of the member and its accepted
step. Where `Thr` has no member the statement says nothing. THAT THE CLAUSE STAYS PAST THE FIVE
MEMBERS BETWEEN ITS TWO BORDERS IS NOT HERE. The clause is written out as a `RiderCl`; that it is
the term `riderAtt` (Honest/Thread/RidersAtt.lean), by unfolding, is
Honest/K5/Law/LaysLookRAtt.lean's. `lookR` is a sentence on three fields of g alone: it ties them to
no round. `lays_att_head` is not this folder's: the Limits in its own file's head hold here too. h
is a hypothesis of every statement that names it. At the library's full size and the format's
second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LookRHeard
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysAttHead

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

/-- **THE LOOKUP's MEMBER LAYS THE CLAUSE ON THE FIELD g AT `lookR`.** CONDITIONAL: under the
hypothesis h; g is below 12; the group's plan. -/
theorem k5_lays_lookR {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    LaysAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
      (14 * (2 * g + 1) + 3)
      ⟨14 * (2 * g + 1) + 4, 14 * (2 * g + 1) + 9,
        fun _ _ s => ∃ v, s.here = .att v ∧ lookR a v.g⟩ :=
  ProofFile.Honest.K3.Law.AtThr.lays_att_head h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w g hg a ha
    (lookR a) (lookR_of_hearVia h hg ha)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lays_lookR
