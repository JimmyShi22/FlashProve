-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/LinkWireWithListsOfTrees.lean: Link's wiring (Johnson/EntryRec/Laws.lean, `wLG`) as a wire record
with lists of trees (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean), and its laws.

OnBytes/TypedOracleCompiler/Tagged.lean turns every wire record of the library into one with lists of trees (`ofQB`:
a component has its one tree, or none) and carries the laws (`ofQB_okg`). Here that is applied to
Link's wiring at an object `LrG T`.

  `wLG2`: the wire record. `wLG2_okg`: its laws, from the laws of the wiring of the description's
  rounds and "own trees have numbers below 2^16".

Limits. Nothing on a verifier: that the verifier over wire records with lists of trees, at `wLG2`,
and the library's, at `wLG`, accept the same strings is not said (OnBytes/TypedOracleCompiler/Tagged.lean's head).

-/
import Johnson.EntryRec.Laws
import OnBytes.TypedOracleCompiler.Tagged

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Compile Compile.Batch

variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List RD} {xs : List XO}
  {acc : (Seed × Ans) × (Seed × Ans) → (twoExternalStrings (2 ^ a) SgX).Str → Iop.Tr (Twin.up (SOf C ds)) → Bool}
  (T : RestR I X RI Seed Ans a (protoR (Seed × Ans) C ds a xs acc))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)

/-- Link's wiring as a wire record with lists of trees. -/
noncomputable def wLG2 :
    TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (LrG T).link) :=
  TypedOracleCompiler.Tagged.ofQB (wLG T K chal dec)

/-- Its laws. -/
theorem wLG2_okg (dec₀ : View → Bool) (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (h0 : (wqS C K chal ds dec₀).OKG) : (wLG2 T K chal dec).OKG :=
  TypedOracleCompiler.Tagged.ofQB_okg (wLG_okg T K chal dec dec₀ hown h0)

end OnBytes.RunA
