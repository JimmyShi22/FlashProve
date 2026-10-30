-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofTrees.lean: what the encoding of the proof file's part (`mProof`,
OnBytes/K/Arm/ProofInj.lean) reads out of a hash function at the leaves and the vertices of the
trees: the digest of that function's answer at the string of the format's call. For a leaf this is
said only where the page's taken spelling of leaves writes, and if what it writes there is the bits
of the call's string (`Spells`).

The laws on the walks of a proof file's trees (`CodeOwes`, OnBytes/Maker/WalksOf.lean) follow from
two laws on a family of typed oracles (`codeOwes_rows`, OnBytes/Maker/Page/CodeRows.lean):
`LeafRow`, at the leaf queries that meet a condition Ql, and `NodeIs` (OnBytes/Maker/RecNodes.lean),
at two digests. Here both are shown of what `mProof C H back` reads out of any g. For proofs only;
the program does not import this file.

`Spells put bd` (OnBytes/K/Arm/KeyTrees.lean): whatever `put` writes at a leaf query that has a call
(`leafOf bd`, OnBytes/Maker/Page/Trees.lean) is the bits of that call's string.

Main theorems.
 `leafRowQ_proof` `LeafRow` at what `mProof C H back` reads out of g, at O the function on bytes
                  made of g, and at Ql := "the page's taken spelling of leaves writes at q". Asked:
                  `Spells` of that spelling.
 `leafRowQ_proofV` so `LeafRow` holds where the page's taken spelling is the code of leaf queries
                  `KeyLeaves.leavesAt L0 nb cfg` (OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean), carried along a
                  pair that keeps the typed salt and reads the body by bd; nb = 8 k (`spells_along`,
                  OnBytes/K/Arm/KeyTrees.lean).
 `node_proof` at two strings of 256 bits: the digest of the answer at the string of the call 166
                  under the page's digest.
 `nodeIs_proof` `NodeIs` at the format's hash over that function and the page's digest.
 `leafRow_proof_oBits`, `nodeIs_proof_oBits` the two laws at g := `oBits` (Run/OracleBits.lean),
                  with the format's own oracle `Fmt.oracle` in the place of the function made of g.

Not claimed. That Ql holds at any leaf query: where the carried code writes is said in
OnBytes/K/Arm/LeafWrites.lean, for strings of bits. That any page's taken spelling of leaves is that
carried code. At a leaf query that does not meet Ql nothing is said. Nothing on the request tree's
two oracles or on chain queries. Nothing on any hash function; nothing on soundness. That the
carried code writes at the leaf queries of a file's own trees and of a stored table is said in
OnBytes/K/Arm/LeafWritesAt.lean. The two laws at `oBits` name the format's own oracle (`Fmt.oracle`,
Fmt/Rules23.lean): they say what is read out of it, and nothing of how it behaves. The
configuration's digest stands in four places: the start of a stored table's leaf queries, the digest
of `NodeIs`, the page's field `cfg`, and the carried code's own cfg. Nothing here ties the page's
cfg to the carried code's.

Where the page's first statement holds a request through the format's item, which is made of digests
of the request, `ProofLaws` cannot hold at a test of fitness that lets the first query of every
request through: there are more requests than items, so two such queries would have one call.
Nothing here shows that it holds at any test; what this cause leaves open is a test that lets
through a set of instances on which the item is one to one. That it is so on a given set is a
hypothesis on the hash that makes the digests. The set stands in the encoding. Whoever lays it has
to name it without knowledge of the hash function and before any run; nothing here enforces that.
For a request outside the set nothing is tied here.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyTrees
import OnBytes.K.Arm.ProofCoding

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker OnBytes.Maker.Page TypedOracleCompiler.Run.LinkAlong
open TypedOracleCompiler.Strings
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-! ## At the proof file's encoding -/

variable (C : ProofCut L K) (H : ProofLaws C) (back : StrCode (AllPts 256 K L)) (g : Fam (rom 256))

/-- **The law on the leaves at the proof file's encoding.** -/
theorem leafRowQ_proof (bd : L.Bd → List Bool) (hS : Spells C.P.leafX bd) :
    LeafRow (readBlocks (mProof C H back) g) (oB (g ())) bd fun q => (C.P.leafX q).isSome := by
  intro q c hq hc
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hq
  refine (proof_leaf C H back g q s hs).trans ?_
  rw [hS q s c hs hc]
  exact (TieTree.bytes_dig _).symm

/-- **The same where the page's taken spelling of leaves is the carried code.** -/
theorem leafRowQ_proofV {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (nb k : ℕ) (hn : nb = 8 * k)
    (cfg : ByteArray) (G : LeafPair (strung L0) L) (bd : L.Bd → List Bool)
    (hG : ∀ q2 q1, G.sel q2 = some q1 → q1.body = bd q2.body ∧ q1.salt = q2.salt)
    (hX : C.P.leafX = (leavesAlong G (KeyLeaves.leavesAt L0 nb cfg)).lf.put) :
    LeafRow (readBlocks (mProof C H back) g) (oB (g ())) bd fun q => (C.P.leafX q).isSome :=
  leafRowQ_proof C H back g bd (hX ▸ spells_along L0 nb k hn cfg G bd hG)

/-- At two strings of 256 bits. -/
theorem node_proof (q : Bits × Bits) (h1 : q.1.length = 256) (h2 : q.2.length = 256) :
    (readBlocks (mProof C H back) g OracleName.node q : Dig 256) =
      bytesToDig (oB (g ())
        (Fmt.oStr 0 166 0 0 C.P.cfg (bitsToBytes q.1 ++ bitsToBytes q.2))) := by
  refine (proof_node C H back g q _ (by
    rw [← pNodeAt_166]
    exact pNodeAt_put 166 C.P.cfg q.1 q.2 h1 h2)).trans ?_
  exact (TieTree.bytes_dig _).symm

/-- **The law on the vertices at the proof file's encoding.** -/
theorem nodeIs_proof : NodeIs (readBlocks (mProof C H back) g) (Fmt.HO (oB (g ()))) C.P.cfg := by
  intro l r hl hr
  have n1 : (List.ofFn (bytesToDig l)).length = 256 := by rw [List.length_ofFn]
  have n2 : (List.ofFn (bytesToDig r)).length = 256 := by rw [List.length_ofFn]
  -- `node_proof` once more, at two letters: handed the two long terms at once, Lean unfolds them
  -- while it compares the lengths' statements, and runs out of its depth of recursion.
  have key : ∀ a b : Bits, a.length = 256 → b.length = 256 →
      (readBlocks (mProof C H back) g OracleName.node (a, b) : Dig 256) = bytesToDig (oB (g ())
                (Fmt.oStr 0 166 0 0 C.P.cfg (bitsToBytes a ++ bitsToBytes b))) :=
    fun a b ha hb => node_proof C H back g (a, b) ha hb
  have h := key _ _ n1 n2
  have el : bitsToBytes (List.ofFn (bytesToDig l)) = l := digToBytes_bytesToDig l hl
  have er : bitsToBytes (List.ofFn (bytesToDig r)) = r := digToBytes_bytesToDig r hr
  rw [el, er] at h
  exact h

/-! ## At the oracle on bits that is made of the format's own -/

/-- **The law on the leaves, at `oBits` and the format's own oracle.** A leaf's call has the half 0.
-/
theorem leafRow_proof_oBits (bd : L.Bd → List Bool) (hS : Spells C.P.leafX bd) :
    LeafRow (readBlocks (mProof C H back) oBits) Fmt.oracle bd
      fun q => (C.P.leafX q).isSome := by
  intro q c hq hc
  rw [leafRowQ_proof C H back oBits bd hS q c hq hc]
  have hc' : (readBody (bd q.body)).map (fun z => (⟨0, z.1, z.2.1, z.2.2.1,
      bitsToBytes (q.salt.take 256), z.2.2.2 ++ bitsToBytes (q.salt.drop 256)⟩ : Fmt.OQ)) =
      some c := hc
  obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 hc'
  exact congrArg bytesToDig (ph_oStr 0 _ _ _ _ _ (Or.inl rfl))

/-- **The law on the vertices, at `oBits` and the format's own oracle.** -/
theorem nodeIs_proof_oBits :
    NodeIs (readBlocks (mProof C H back) oBits) (Fmt.HO Fmt.oracle) C.P.cfg := by
  have e : Fmt.HO (oB (oBits ())) = Fmt.HO Fmt.oracle := ph_hI
  rw [← e]
  exact nodeIs_proof C H back oBits

end OnBytes.K.Arm
