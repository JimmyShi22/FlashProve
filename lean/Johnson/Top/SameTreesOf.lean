-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SameTreesOf.lean: two encodings of pages that give every leaf query and every vertex
query the same string (`AgreeTrees`, OnBytes/K/Arm/AgreeTrees.lean) agree on the leaf and node
oracles in the sense of Johnson/TypedOracleCompiler/RecCompile/WordCodings.lean (`SameTrees`); and that at the entry
file's, the key file's and the proof file's encodings, pair by pair.

`SameTrees W m m'` has four clauses: a leaf query and a node query are written as the same string,
at any two blocks; a block is read as the same answer of these two oracles. At the encoding of a
page (`implG`, OnBytes/TypedOracleCompiler/Run/PageG.lean) an answer of these two oracles has one block, and a block
is read as an answer in the same way at every page. `extEnc_codings` there then has: the word under
a root, read off a log of strings, is the same at both. For proofs only; the program does not import
this file.

Main theorems.
 `sameTrees_of_agree`    `AgreeTrees (implG C) (implG C') → SameTrees W (implG C) (implG C')`.
 `sameTrees_key_proof`   at `mKey C H back` and `mProof C' H' back`, for two cuts of one page.
 `sameTrees_entry_key`   at `implL2 … W.K back` and `mKey C H back`.
 `sameTrees_entry_proof` at `implL2 … W.K back` and `mProof C H back`.

Asked in the last two: the page's taken spelling of leaves is the entry's code of leaves, carried;
the page's digest is the entry's. In all three: one interface, one number W.K of blocks, one total
code `back`. `sameTrees_key_proof` asks one whole page of the two cuts; one spelling of leaves and
one digest are enough (`sameTrees_of_agree` over `agree_key_proof`, OnBytes/K/Arm/AgreeProof.lean).

Not claimed. `KeyLaws` or `ProofLaws` at any cut. That any page meets the two equations. That one
code of leaves spells the leaf calls of all three files and of the stored tables as the programs do.
Nothing on the other oracles. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.AgreeProof
import OnBytes.K.Arm.KeyInj
import Johnson.TypedOracleCompiler.RecCompile.WordCodings

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL))

/-- Two pages' encodings that agree on the trees' strings agree on the leaf and node oracles. -/
theorem sameTrees_of_agree (C C' : Page (typedOracleCarrier L Bd aT aL) W.K)
    (h : AgreeTrees (implG C) (implG C')) : SameTrees W (implG C) (implG C') where
  leaf q j j' := h.1 q j j'
    ((Nat.lt_one_iff.1 (show j.val < 1 from j.isLt)).trans
      (Nat.lt_one_iff.1 (show j'.val < 1 from j'.isLt)).symm)
  node q j j' := h.2 q j j'
    ((Nat.lt_one_iff.1 (show j.val < 1 from j.isLt)).trans
      (Nat.lt_one_iff.1 (show j'.val < 1 from j'.isLt)).symm)
  ansLeaf _ := rfl
  ansNode _ := rfl

/-- The key file's encoding and the proof file's, for two cuts of one page. -/
theorem sameTrees_key_proof (C : KeyCut (typedOracleCarrier L Bd aT aL) W.K)
    (C' : ProofCut (typedOracleCarrier L Bd aT aL) W.K) (H : KeyLaws C) (H' : ProofLaws C') (hP : C.P = C'.P)
    (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL))) :
    SameTrees W (mKey C H back) (mProof C' H' back) :=
  sameTrees_of_agree W _ _ (agree_mKey_mProof C C' H H' hP back)

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁))
  (pbF : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : (typedOracleCarrier L Bd aT aL).Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- The entry file's encoding and the key file's. -/
theorem sameTrees_entry_key (C : KeyCut (typedOracleCarrier L Bd aT aL) W.K) (H : KeyLaws C)
    (hX : C.P.leafX = (leavesAlong (leafM (Ls D d₁) (typedOracleCarrier L Bd aT aL) bd) V).lf.put)
    (hc : C.P.cfg = cfg) :
    SameTrees W
      (implL2 D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0 p1 isP0 isP1 cfgL sh hp0
        hp1 rest isPL hpL cA tr hinj hlen htr W.K back)
      (mKey C H back) :=
  sameTrees_of_agree W _ _ (agree_entry_key D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0
    p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K back C _ _ hX hc)

/-- The entry file's encoding and the proof file's. -/
theorem sameTrees_entry_proof (C : ProofCut (typedOracleCarrier L Bd aT aL) W.K) (H : ProofLaws C)
    (hX : C.P.leafX = (leavesAlong (leafM (Ls D d₁) (typedOracleCarrier L Bd aT aL) bd) V).lf.put)
    (hc : C.P.cfg = cfg) :
    SameTrees W
      (implL2 D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0 p1 isP0 isP1 cfgL sh hp0
        hp1 rest isPL hpL cA tr hinj hlen htr W.K back)
      (mProof C H back) :=
  sameTrees_of_agree W _ _ (agree_entry_proof D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd
    p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K back C _ _ hX hc)

end OnBytes.K.Arm
