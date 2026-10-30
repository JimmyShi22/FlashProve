-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BlockYesClosed.lean: WAY (1) CLOSED AT THE FIRST CHAIN: BlockYesGivesVals at all 25 batchings, and so the
shape of a thread's state at every border from Thr, the run on shapes and the start alone.

  **block_yes_all**     no premise but the head and baseOf's return.
  **shape_at_thr**      shape_of_thr with that premise paid: no family J, no silence of a stop or a fall.

Limits. hyes and hbeg stay premises. It pays what has the member's step in hand (the family J, the carry), not the member's yes
itself. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.BlockYesAll
import Johnson.AtFull.Shape.Scope.CellVHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE ONE PUBLIC LAW: at every weak member a reached state and the member's step give the table's test on values.** -/
theorem block_yes_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    BlockYesGivesVals (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) 0 cF.blocksInOrder (ProofFile.startS Zp)
      (ReqPasses Zp) :=
  blockYes_of_head h hB fun _ _ _ _ _ _ hr hb hs => ProofFile.Honest.K9.vals_of_step_head h hB hb hr hs

/-- **THE SHAPE OF A THREAD's STATE AT EVERY BORDER.** -/
theorem shape_at_thr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (hbeg : ∀ k w hh s₀, T.valid w → T.begun k w hh s₀ →
      ∃ p, s₀ = ProofFile.startS Zp p ∧ ReqPasses Zp p)
    {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hb : b ≤ 358)
    (hA : Thr T b k s m E) :
    shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA b s :=
  shape_of_thr h hB T hbs hft hyes (block_yes_all h hB) hbeg hb hA

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.block_yes_all
#print axioms Johnson.AtFull.Shape.Scope.shape_at_thr
