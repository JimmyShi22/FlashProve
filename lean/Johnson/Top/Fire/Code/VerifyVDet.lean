-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/VerifyVDet.lean: the first half of the fast twin of `verifyV`: the verifier's
answer at a hash function, as a plain function with code in which a typed query's blocks are handed
on as a function of their number, and are not asked of the hash one after the other.

Why. `verifyV v` (Johnson/Top/InputV.lean) is a tree of queries to one hash function: `overOneV`
turns every typed query o into `askAll`: the hash asked at all `v.m.blocks o` strings, one after the
other (Rom/Family.lean). Evaluated as it stands, the tree of these queries is built and walked whole
at every typed query (measured: quadratic in the number of blocks, before any hash).
Main names. `readBlocksV m g`: the typed family that is read off one hash function through the
writing side m of a coding: the text of `Rom.readBlocks` (Rom/Prefix.lean) at `ImplV`. `verifyVDet v
hash commitment prompt output proof : Bool`: build; the code of the key; the test of the commitment
ID at the hash; then `VRAV`'s result over `readBlocksV v.m`. `VerifyVDetIs`: THE STATEMENT, a
proposition, not proved in this file (VerifyVDetProbe.lean proves it): at every v, hash function,
commitment, prompt, output and proof, `verifyV`'s evaluation is `verifyVDet`.
Limits. No theorem. Whether a block is computed once, many times or never is the compiler's and the
coding's matter: nothing on time or memory is said. The three arms are still `verifyOneProtocol` at the whole
wire records, with their lists of all positions: the second half of the twin is not here. Nothing on
soundness.

-/
import Johnson.Top.InputV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

/-- The typed family that is read off one hash function through the writing side of a coding. -/
def readBlocksV {S : OSpec} {lam : ℕ} (m : ImplV S lam) (g : Fam (rom lam)) : Fam S :=
  fun o q => (m.rng o).symm fun j => g () (m.code o q j)

/-- The verifier's answer at a hash function. -/
def verifyVDet (v : InputV) (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)) : Bool :=
  match v.build (prompt, output) proof.1 with
  | some x =>
    match v.enc proof.2.1 with
    | some code =>
      if hash code = commitment then
        (VRAV v.W v.Sd v.cA v.r₀ v.p proof.2.1 x proof.2.2).det (readBlocksV v.m fun _ => hash)
      else false
    | none => false
  | none => false

/-- **The statement**: the evaluation of `verifyV` is `verifyVDet`, at all inputs. -/
def VerifyVDetIs : Prop :=
  ∀ (v : InputV) (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)),
    (verifyV v commitment prompt output proof).evaluate hash =
      verifyVDet v hash commitment prompt output proof

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.readBlocksV
#print axioms VerifiableInference.OnPublicFiles.verifyVDet
#print axioms VerifiableInference.OnPublicFiles.VerifyVDetIs
