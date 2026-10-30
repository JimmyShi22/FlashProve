-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/OfWritten.lean: a written protocol whose batch protocol is that of a file is a
written file, and its compiled verifier is the file's verifier, which walks three hash chains.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

A compiled verifier is called at a written protocol (`Written`, OnBytes/TypedOracleCompiler/Joined/Wire.lean): a
tag, a batch protocol, its wire record and the maps into the typed queries. The verifier of a file
(`FileW.verify`, OnBytes/TypedOracleCompiler/Joined/Verifier.lean) is said at a written file (`FileW`), whose batch
protocol is `D.batch` for a description D over the rounds G. Here the first is carried to the second
along an equation between the two batch protocols.

Main names:
  `FileW.ofWritten Z D e`   the written protocol Z as a written file, given e : Z.Q = D.batch; its
                            description is D by unfolding
  `FileW.ofWritten_written` as a written protocol it is Z again
  `Written.verify_eq_file`  Z's compiled verifier at a proof string π is the file's verifier at π,
                            carried along e
  `batch_eq_of_proto`       the equation e from one between the protocols and one between the
                            annotations

Limits: the equation e is a hypothesis. Where the two batch protocols are the same by unfolding, e
is rfl and nothing is carried.
No other file of the library uses `ofWritten_written` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Verifier

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
  {E : ExtSpec}

/-- A written protocol whose batch protocol is that of the description D, as a written file. -/
def FileW.ofWritten (Z : Written W Y E) (D : Desc G Y E) (e : Z.Q = D.batch) : FileW W G Y E where
  D := D
  t := Z.t
  wq := cast (congrArg (fun Q : BatchInteractiveOracleProof Y E => ProtocolQueryLayout lam W.K Q) e) Z.wq
  embS := cast (congrArg
    (fun Q : BatchInteractiveOracleProof Y E => (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) e) Z.embS
  embP := cast (congrArg
    (fun Q : BatchInteractiveOracleProof Y E => PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L Z.t) (annOf L Z.t)) e) Z.embP
  xin := Z.xin
  embE := Z.embE

/-- as a written protocol it is Z again -/
theorem FileW.ofWritten_written (Z : Written W Y E) (D : Desc G Y E) (e : Z.Q = D.batch) :
    (FileW.ofWritten Z D e).written = Z := by
  obtain ⟨t, Q, wq, embS, embP, xin, embE⟩ := Z
  have e' : Q = D.batch := e
  subst e'
  rfl

/-- The compiled verifier at a written protocol whose batch protocol is that of a file is the file's
verifier, which walks the three chains one after the other. -/
theorem Written.verify_eq_file (Z : Written W Y E) (D : Desc G Y E) (e : Z.Q = D.batch)
    (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Z.Q) :
    Z.verify sMT sFS cms x π =
      (FileW.ofWritten Z D e).verify sMT sFS cms x
        (cast (congrArg (fun Q : BatchInteractiveOracleProof Y E => OneProtocolProof lam Q) e) π) := by
  obtain ⟨t, Q, wq, embS, embP, xin, embE⟩ := Z
  have e' : Q = D.batch := e
  subst e'
  exact (FileW.verify_eq (⟨D, t, wq, embS, embP, xin, embE⟩ : FileW W G Y E) sMT sFS cms x π).symm

/-- A protocol that is the file's, with an annotation that is the file's, is the file's batch
protocol. -/
theorem batch_eq_of_proto (D : Desc G Y E) :
    ∀ (P : InteractiveOracleProof Y E) (_ : P = D.proto) (a : RoundSplits P.shape), HEq a G.ann →
      (⟨P, a⟩ : BatchInteractiveOracleProof Y E) = D.batch := by
  rintro _ rfl a h
  cases h
  rfl

end TypedOracleCompiler.Joined
