-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmChainNone.lean: the chain's half of the compiled lax verifier where no instance
is handed to the chain: the interface's late round does not matter.

An interface has one field `late` for all tags: the round behind which the rest of an instance is
named. `chain_at` (OnBytes/TypedOracleCompiler/Run/ArmChain.lean) asks, through `PQ.ReadE`, that it names no written
round of the link. At an interface whose `late` is a proof file's round that may be false. The chain
reads `late` only to choose between the instance and nothing; where no instance is handed over, both
are nothing.

Main theorems.
 `chainP_late_none`   without an instance the evaluable chain is the same at any two late rounds.
 `chain_at_none`      `chain_at` where the instance's way into the chain gives nothing: `PQ.ReadE`
                      is asked at no late round, so its field `noLate` holds trivially.

Not claimed. No field of `PQ.ReadE` is shown at any interface or family. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmChain

set_option autoImplicit false

namespace TypedOracleCompiler.Run.ArmChain
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))

/-- Without an instance the chain does not look at the late round. -/
theorem chainP_late_none (early : X → X) (late late' : Option ℕ) (t : Tag) (cms : List (Dig lam))
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
      (embP : PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains (up S)),
      chainP Lf g early late t cms none salt rtreq S A W embP i ph rts pls =
        chainP Lf g early late' t cms none salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [TypedOracleCompiler.Run.Thin.chainP, ite_self,
        chainP_late_none early late late' t cms salt rtreq S]

end TypedOracleCompiler.Run.ArmChain

namespace TypedOracleCompiler.Run.ArmChain
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- **The chain's half where no instance is handed over.** `PQ.ReadE` is asked at no late round. -/
theorem chain_at_none {I2 X2 X : Type} (L2 : BatchProtocolWithLeafBody I2 X2) (D : XD)
    (dec : X → _root_.Run.PQ.View → Bool) (g : Fam (typedOracleFamily 256 (D.K + 1) L2))
    (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (embP : PlainPart (_root_.Run.Twin.up (PQ.SOf D.C D.ds)) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds)) →
      PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin : X → Option X2) (cms : List (Dig 256)) (x : X) (hx : xin x = none) (S : _root_.Fmt.SpecX)
    (o : _root_.Fmt.ChainOut) (salt : Bits) (pls : Plains (PQ.uL D.C D.ds))
    (hkit : _root_.Run.PQ.KitFits S.base.plan.field D.C D.K (chalP D.base.plan.field D.K))
    (A : PQ.ReadE (fun _ : Unit => L2) D.C D.K g L2.early none .link cms none salt O D.ds embP
      pls S o)
    (π : OneProtocolProof 256 (PSXE D dec).up) (more : List (Dig 256)) (hsalt : π.salt = salt)
    (hroots : π.roots = (_root_.Run.rootsB o).map bytesToDig ++ more)
    (hpl : π.plains = ((), pls)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds))) (v' : Bits),
      (recomputeChainOfProof (L := L2) .link (PSXE D dec).up (wqXE D dec) embP xin cms x π).det g =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true := by
  obtain ⟨ρ, v', e, hd, hp⟩ := PQ.chain_one_read (fun _ : Unit => L2) D.C D.K g L2.early none
    .link cms none salt O D.ds embP π.rtreq hO (chalP D.base.plan.field D.K) pls S o more hkit A
  refine ⟨ρ, v', ?_, hd, hp⟩
  rw [chainP_det, hx, hsalt, hroots, hpl,
    chainP_late_none (fun _ : Unit => L2) g L2.early L2.late none]
  exact e

end TypedOracleCompiler.Run.ArmChain
