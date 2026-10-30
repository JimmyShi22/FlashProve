-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofRequest.lean: what the proof file's encoding `mProof`
(OnBytes/K/Arm/ProofInj.lean) reads out of a hash function at the vertices and the leaves of the
tree that binds a batch's requests is the format's own hash of that vertex and of that leaf, if the
hash function induces the hash that the format's realised oracle induces.

OnBytes/TypedOracleCompiler/Joined/K/Request.lean asks two laws of typed oracle functions: `NodeCoded` and
`LeafCoded`. OnBytes/Maker/Page/Request.lean shows them of `gJ P Fmt.oracle`, which is a function of
the typed query and no encoding. Here they are shown of what is read through an encoding, from
`proof_rnode` and `proof_rleaf` (OnBytes/K/Arm/ProofCoding.lean), by that file's lemmas on the two
calls. For proofs only; the program does not import this file.

Main names.
 `nodeCoded_proof` `NodeCoded (readBlocks (mProof C H back) g) C.P.cfg`.
 `leafCoded_proof` `LeafCoded (readBlocks (mProof C H back) g) d C.P.cfg C.P.sR (rsOf d)`.
 `nodeCoded_proof_oBits`, `leafCoded_proof_oBits` both at g := `oBits`, by `hoKey_oBits`
                      (OnBytes/K/Arm/KeyRequest.lean).

Asked: `Fmt.HO (oB (g ())) = Fmt.HO Fmt.oracle`; the page's cfg has 32 bytes; for the leaves: the
page's `sR` is a salt's length as the format has it (`Fmt.saltLenOK`), and the tree's depth is below
63. That the page's cfg has 32 bytes is a field of `ProofLaws` too (`ProofLaws.cfg`): beside H that
premise asks nothing new.

Not claimed. `ProofLaws` at any cut. That a total code `back` exists at any interface. Nothing on
any other hash function; nothing on soundness. The premise on g fixes the hash that g induces at
every call of the format: so this is a tie at one hash function, and no bound over a drawn function.

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
import OnBytes.K.Arm.KeyRequest
import OnBytes.K.Arm.ProofCoding

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : ProofCut L K) (H : ProofLaws C)
  (back : StrCode (AllPts 256 K L)) (g : Fam (rom 256))

/-- The vertices of the request tree. -/
theorem nodeCoded_proof (hH : Fmt.HO (oB (g ())) = Fmt.HO Fmt.oracle) (hc : C.P.cfg.size = 32) :
    TypedOracleCompiler.Joined.K.NodeCoded (readBlocks (mProof C H back) g) C.P.cfg := by
  intro x y hx hy
  have ex : bitsToBytes (List.ofFn (bytesToDig x)) = x := TieTree.dig_bytes x hx
  have ey : bitsToBytes (List.ofFn (bytesToDig y)) = y := TieTree.dig_bytes y hy
  have hf : fitTree (List.ofFn (bytesToDig x), List.ofFn (bytesToDig y)) = true := by
    unfold fitTree
    rw [List.length_ofFn, List.length_ofFn]
    rfl
  have hcall : rnodeCall C.P.cfg (List.ofFn (bytesToDig x), List.ofFn (bytesToDig y)) =
      some ⟨0, 178, 0, 0, C.P.cfg, x ++ y⟩ := by
    unfold rnodeCall
    rw [ex, ey]
  have hd : inDom ⟨0, 178, 0, 0, C.P.cfg, x ++ y⟩ = true := by
    show (((0 : UInt8) == 0 || (0 : UInt8) == 1) && Fmt.hDom 178 0 0 C.P.cfg (x ++ y)) = true
    rw [dom178 C.P.cfg x y hc hx hy]
    rfl
  show (readBlocks (mProof C H back) g .rnode
    (List.ofFn (bytesToDig x), List.ofFn (bytesToDig y)) : Dig 256) = _
  rw [proof_rnode C H back g _ _ hf hcall hd]
  show bytesToDig (hO (oB (g ())) 178 0 0 C.P.cfg (x ++ y)) = _
  rw [hO_eq_HO (oB (g ())) 178 0 0 _ _ (by decide), hH,
    Fmt.HO_oracle _ _ _ _ _ (dom178 C.P.cfg x y hc hx hy)]
  rfl

/-- The leaves of the request tree. -/
theorem leafCoded_proof (hH : Fmt.HO (oB (g ())) = Fmt.HO Fmt.oracle) (d : ℕ) (hd : d < 63)
    (hc : C.P.cfg.size = 32) (hR : Fmt.saltLenOK C.P.sR = true) :
    TypedOracleCompiler.Joined.K.LeafCoded (readBlocks (mProof C H back) g) d C.P.cfg C.P.sR (rsOf d) := by
  intro place closing salt hp hcl hs
  have h1 : (2 : ℕ) ^ d ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) (by omega)
  have hR' : Fmt.saltLenOK salt.size = true := by rw [hs]; exact hR
  have hle : salt.size ≤ 64 := by
    simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hR'
    exact hR'.2
  have l4 : ((List.range 4).map fun i => Fmt.wordAt closing (8 * i)).length = 4 := rfl
  have hf : Fmt.fillLen 4 salt.size = 0 := by
    unfold Fmt.fillLen
    rw [if_pos (by omega)]
  have z : Fmt.zeroBytes 0 = ByteArray.empty := rfl
  have eb : closing ++ salt =
      Fmt.leafBytes ((List.range 4).map fun i => Fmt.wordAt closing (8 * i)) salt := by
    unfold Fmt.leafBytes
    rw [words32 closing hcl, l4, hf, z, ByteArray.append_empty]
  have hdm := dom173 (2 ^ d + place) C.P.cfg
    ((List.range 4).map fun i => Fmt.wordAt closing (8 * i)) salt (by omega) hc (by rw [l4]; decide)
    (by rw [l4]; decide) hR'
  rw [l4] at hdm
  have hcall : rleafCall C.P.cfg C.P.sR (List.ofFn (bytesToDig closing) ++ rsOf d place salt) =
      some ⟨0, 173, Fmt.leafPlace 0 4 (salt.size / 8), 2 ^ d + place, C.P.cfg,
        closing ++ salt⟩ := by
    rw [← hs]
    exact rleafCall_at C.P.cfg d place closing salt hcl (by omega)
  have hin : inDom ⟨0, 173, Fmt.leafPlace 0 4 (salt.size / 8), 2 ^ d + place, C.P.cfg,
      closing ++ salt⟩ = true := by
    show (((0 : UInt8) == 0 || (0 : UInt8) == 1) &&
      Fmt.hDom 173 (Fmt.leafPlace 0 4 (salt.size / 8)) (2 ^ d + place) C.P.cfg
        (closing ++ salt)) = true
    rw [eb, hdm]
    rfl
  rw [proof_rleaf C H back g _ _ hcall hin]
  show bytesToDig (hO (oB (g ())) 173 (Fmt.leafPlace 0 4 (salt.size / 8)) (2 ^ d + place) C.P.cfg
    (closing ++ salt)) = _
  rw [eb, hO_eq_HO (oB (g ())) 173 _ _ _ _ (by decide), hH, Fmt.HO_oracle _ _ _ _ _ hdm]
  rfl

/-- The vertices, at the realised oracle on bits. -/
theorem nodeCoded_proof_oBits (hc : C.P.cfg.size = 32) :
    TypedOracleCompiler.Joined.K.NodeCoded (readBlocks (mProof C H back) oBits) C.P.cfg :=
  nodeCoded_proof C H back oBits hoKey_oBits hc

/-- The leaves, at the realised oracle on bits. -/
theorem leafCoded_proof_oBits (d : ℕ) (hd : d < 63) (hc : C.P.cfg.size = 32)
    (hR : Fmt.saltLenOK C.P.sR = true) :
    TypedOracleCompiler.Joined.K.LeafCoded (readBlocks (mProof C H back) oBits) d C.P.cfg C.P.sR (rsOf d) :=
  leafCoded_proof C H back oBits hoKey_oBits d hd hc hR

end OnBytes.K.Arm
