-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkRd.lean: the read leaves of a skeleton's own trees as lists, round by round
and tree by tree, made of the protocol's own set of read positions: what the listed strict verifier verifyBSL
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean) wants as `mkRd`. One definition, after checksRQ's pattern
(OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean:168-183): each tree's list is that file's placesAt.
NO LAW: that these lists meet verifyBSL_eq's premise (LeavesOK) is shown nowhere:
(Where this and lean/THEOREM.md differ, the page holds.) A PIECE OF THE PROBE StrictLinkB.lean.

-/
import OnBytes.TypedOracleCompiler.Run.LaxPlaces
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifier

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

/-- Round by round: the read leaves of the trees over the shared component, and of those over the slot's. -/
def rdOfR {lam K : ℕ} :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → Finset (OPos (up S)) → Leaves
  | [], _, _, _ => []
  | r :: S, (_, A), (w, W), R =>
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      (w.depth0.zipIdx.map (fun d => placesAt w false R0 d.2 d.1),
        w.depthJ.zipIdx.map (fun d => placesAt w true R0 d.2 d.1)) ::
        rdOfR S A W (tailR (α := r.Pos) (β := OPos (up S)) R)

end TypedOracleCompiler.Run.Thin
