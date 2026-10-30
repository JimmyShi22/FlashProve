-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormShare.lean: a fourth share of the hypothesis `OwesS`
(PaysS.lean), beside `ExchangeAtS`, `RidesPastAtS` and `LaysAtS` (SharesS.lean): the first part of
`BehindS` at one sub-protocol. `owesS_head_form` (GatherHeadForm.lean) asks it at every number, as
its column `hF`. With a name for it, a lemma that gathers the column from many families of numbers
can be read. `FormKeepsS` (Johnson/Desc/ProofFile/Honest/K14/Debts2.lean) of other authors is kin:
it has this sentence and `keeps` together. Here `keeps` is left out, because the gathering asks it
in a column of its own (`hK`), and because this half does not change when `keeps` changes.

  1  `FormBehindAtS`   the definition
  2  `formBehindAtS_of_behindS`   `BehindS` gives it
  3  `formBehind_column`   at all numbers below the chain's length it is the column `hF`, word for
     word
  4  `head_formBehindAtS_kp`   at the first chain's invariant at the full size it does not depend on
     the argument `Kp`, through which `lettersHead` (FirstHead.lean) takes `keeps`

Limits.
  * A definition and three lemmas on it. Nothing shows that it holds at any sub-protocol.
  * Lemma 4: full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `formBehind_column`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **`BehindS`'s first part at one sub-protocol**: after an accepting step on the honest prover's
messages, the part `Form` of the invariant holds at the next border. It is the column `hF` of
`owesS_head_form` (GatherHeadForm.lean) at one number. It is a definition: the form of a hypothesis.
-/
def FormBehindAtS (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2

variable {T Said}

/-- `BehindS` gives it. -/
theorem formBehindAtS_of_behindS {b : Nat} (h : BehindS T Said b) : FormBehindAtS T Said b :=
  fun blk hblk k s m E ds y cols s' hA hd hS => (h blk hblk k s m E ds y cols s' hA hd hS).1

/-- At all numbers below the chain's length it is the column `hF`, word for word. -/
theorem formBehind_column :
    (∀ b, b < T.bs.length → FormBehindAtS T Said b) ↔
      ∀ b, b < T.bs.length → ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s',
        ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
        T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 := Iff.rfl

end

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Kp' : Place → TS → TS → Prop)

/-- It does not depend on the argument `Kp`. -/
theorem head_formBehindAtS_kp (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat}
    (hc : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b := hc

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.formBehindAtS_of_behindS
#print axioms ProofFile.Honest.formBehind_column
#print axioms ProofFile.Honest.FirstThread.head_formBehindAtS_kp
