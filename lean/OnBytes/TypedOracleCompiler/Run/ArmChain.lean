-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmChain.lean: the chain's half of the compiled lax verifier at the skeleton of the
written link, for any interface, any family of oracle functions and any way of the plain parts.

OnBytes/TypedOracleCompiler/Run/ChainERead.lean (`chain_one_read`) draws the value of the evaluable chain `chainP`
from one yes of the strict reader, for any interface and family, under the record `PQ.ReadE`.
OnBytes/TypedOracleCompiler/Slice/EntryChain.lean (`entry_chain_run`) says the same of the compiled verifier's own
chain `recomputeChainOfProof`, at the entry's own interface and page. Here that last step is said for any
interface.

Main theorem.
 `chain_at`   from `PQ.ReadE`: the chain's half of the compiled lax verifier returns, draws what the
              reader drew, and all tests of work pass; the last phase is local.

Not claimed. No field of `PQ.ReadE` is shown at any interface or family. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ChainERead
import OnBytes.TypedOracleCompiler.Run.LaxThin
import OnBytes.TypedOracleCompiler.Slice.EntryPS

set_option autoImplicit false

namespace TypedOracleCompiler.Run.ArmChain
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- **The chain's half of the compiled lax verifier, for any interface, family and way.** -/
theorem chain_at {I2 X2 X : Type} (L2 : BatchProtocolWithLeafBody I2 X2) (D : XD)
    (dec : X → _root_.Run.PQ.View → Bool) (g : Fam (typedOracleFamily 256 (D.K + 1) L2))
    (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (embP : PlainPart (_root_.Run.Twin.up (PQ.SOf D.C D.ds)) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds)) →
      PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin : X → Option X2) (cms : List (Dig 256)) (x : X) (S : _root_.Fmt.SpecX)
    (o : _root_.Fmt.ChainOut) (salt : Bits) (pls : Plains (PQ.uL D.C D.ds))
    (hkit : _root_.Run.PQ.KitFits S.base.plan.field D.C D.K (chalP D.base.plan.field D.K))
    (A : PQ.ReadE (fun _ : Unit => L2) D.C D.K g L2.early L2.late .link cms (xin x) salt O D.ds embP
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
  obtain ⟨ρ, v', e, hd, hp⟩ := PQ.chain_one_read (fun _ : Unit => L2) D.C D.K g L2.early L2.late
    .link cms (xin x) salt O D.ds embP π.rtreq hO (chalP D.base.plan.field D.K) pls S o more hkit A
  refine ⟨ρ, v', ?_, hd, hp⟩
  rw [chainP_det, hsalt, hroots, hpl]
  exact e

end TypedOracleCompiler.Run.ArmChain
