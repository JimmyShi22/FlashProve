-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/CutCode.lean: what string the writing side of the coding of typed queries lays at
a leaf query and at a chain query under the key file's tag, where the page's own spelling writes.
Two small statements with proofs, general in the page. No definition.
Why. The coding of typed queries into strings (`W4M.mVOf`, Johnson/PV/MvAny.lean) takes, at a real
point, what `cutAll` (Johnson/PV/CutAll.lean) writes there, and else an escape string. At a leaf
`cutAll` writes what the page's field `leafX` writes; at a chain query under the key file's tag,
first what the page's field `seeds` writes. The two statements say so in the form in which a caller
needs it.
  `code_leaf`: where `leafX` writes s at a leaf query, the coding's string there is s.
  `code_seed`: where `seeds` writes s at a chain query with a block, the coding's string there is s.
Limits. Equations between strings of this library's own terms. Nothing on any hash function, on any
program, on soundness, on a binding of the commitment (the opening form, `BindsWith`), on
correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.PV.MvAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Spell
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run OnBytes.K.Arm OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : BothCut L K) (bk : AllPts 256 K L → List Bool)

/-- Where the page's spelling of leaves writes, the coding's string is what it writes. -/
theorem code_leaf (q : LeafIn L) (s : List Bool) (h : C.P.leafX q = some s) (j : Fin 1) :
    (W4M.mVOf C bk).code .leaf q j = s := by
  have e : cutAll C (.inl q) = some s := by
    show (match C.P.leafX q with
      | some s => some s
      | none => _) = _
    rw [h]
  show (match cutAll C (.inl q) with
    | some s => s
    | none => _) = s
  rw [e]

/-- Where the page's spelling of the seed's queries writes, the coding's string is what it writes.
    -/
theorem code_seed (q : FbIn 256 L .test) (j : Fin (K + 1)) (s : List Bool)
    (h : C.P.seeds (q, j) = some s) : (W4M.mVOf C bk).code (.fb .test) q j = s := by
  have e : cutAll C (.inr (.inr (.inr (.inr (.inl ⟨.test, q, j⟩))))) = some s := by
    show (match C.P.seeds (q, j) with
      | some s => some s
      | none => _) = _
    rw [h]
  show (match cutAll C (.inr (.inr (.inr (.inr (.inl ⟨.test, q, j⟩))))) with
    | some s => s
    | none => _) = s
  rw [e]

end Bind.Spell

#print axioms Bind.Spell.code_leaf
#print axioms Bind.Spell.code_seed
