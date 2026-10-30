-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/AgreeProof.lean: the three encodings of the three parts of the compiled verifier, the
entry file's, the key file's and the proof file's, give every leaf query and every vertex query the
same string, if their pages have one spelling of leaves and one digest and they have one total code.

OnBytes/K/Arm/AgreeKey.lean has the entry file's encoding against the key file's. `cutProof`
(OnBytes/K/Arm/ProofCut.lean) writes at a leaf and at a vertex what `cutKey`
(OnBytes/K/Arm/KeyCut.lean) writes: the page's taken spelling of leaves, and the library's code of
vertices under the page's digest. So the same holds of the proof file's encoding, against either.
For proofs only; the program does not import this file.

Main theorems.
 `agree_entry_proof` `AgreeTrees (implL2 … K back) (implOf (cutProof C) inj hd back)`. Asked: the
                  page's taken spelling of leaves is the entry's code of leaves, carried; the page's
                  digest is the entry's; one number K of blocks and one total code `back`.
 `agree_key_proof` `AgreeTrees (implOf (cutKey C) …) (implOf (cutProof C') …)`. Asked: the two cuts'
                  pages have one taken spelling of leaves and one digest; one K and one `back`.
 `agree_mKey_mProof` the same at `mKey C H back` and `mProof C' H' back` (OnBytes/K/Arm/KeyInj.lean,
                  ProofInj.lean), for two cuts of one page; one spelling of leaves and one digest
                  are enough (`agree_key_proof`).

Not claimed. That `cutKey C` or `cutProof C` is one to one where it writes, or that their strings
begin with the byte 0 or 1: in the first two theorems both are hypotheses, as `implOf` takes them;
in the third they come from `KeyLaws` and `ProofLaws`, which are hypotheses. That any page meets the
equations. That one code of leaves spells the leaf calls of all three files and of the stored tables
as the programs do. Nothing on the request tree's two oracles, on chain queries or on the queries
for a slot value. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.AgreeKey
import OnBytes.K.Arm.ProofInj

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Slice.ArmRead TypedOracleCompiler.Slice.ArmLinkCode
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The key file's encoding against the proof file's -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The key file's encoding and the proof file's agree on the trees.** -/
theorem agree_key_proof (C : KeyCut L K) (C' : ProofCut L K)
    (inj : ∀ a b s, cutKey C a = some s → cutKey C b = some s → a = b)
    (hd : ∀ a s, cutKey C a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (inj' : ∀ a b s, cutProof C' a = some s → cutProof C' b = some s → a = b)
    (hd' : ∀ a s, cutProof C' a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (hX : C.P.leafX = C'.P.leafX) (hc : C.P.cfg = C'.P.cfg) (back : StrCode (AllPts 256 K L)) :
    AgreeTrees (implOf (cutKey C) inj hd back) (implOf (cutProof C') inj' hd' back) :=
  agree_of_back (pageOf (cutKey C) inj hd back) (pageOf (cutProof C') inj' hd' back)
    (fun q => (cutKey_leaf C q).trans ((congrFun hX q).trans (cutProof_leaf C' q).symm))
    (fun q => (cutKey_node C q).trans
      ((congrArg (fun c => (pNode c).put q) hc).trans (cutProof_node C' q).symm))
    rfl

/-- **The same at the two encodings under their laws**, for two cuts of one page. -/
theorem agree_mKey_mProof (C : KeyCut L K) (C' : ProofCut L K) (H : KeyLaws C)
    (H' : ProofLaws C') (hP : C.P = C'.P) (back : StrCode (AllPts 256 K L)) :
    AgreeTrees (mKey C H back) (mProof C' H' back) :=
  agree_key_proof C C' _ _ _ _ (congrArg OnBytes.Maker.Page.PageJ.leafX hP)
    (congrArg OnBytes.Maker.Page.PageJ.cfg hP) back

end

/-! ## The entry file's encoding against the proof file's -/

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁))
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (K : ℕ) (back : StrCode (AllPts 256 K L2))

/-- **The entry file's encoding and the proof file's agree on the trees.** -/
theorem agree_entry_proof (C : ProofCut L2 K)
    (inj : ∀ a b s, cutProof C a = some s → cutProof C b = some s → a = b)
    (hd : ∀ a s, cutProof C a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (hX : C.P.leafX = (leavesAlong (leafM (Ls D d₁) L2 bd) V).lf.put) (hc : C.P.cfg = cfg) :
    AgreeTrees (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
      isPL hpL cA tr hinj hlen htr K back)
      (implOf (cutProof C) inj hd back) :=
  agree_implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
    tr hinj hlen htr K back (cutProof C) inj hd (fun q => by rw [cutProof_leaf, hX])
    fun q => by rw [cutProof_node, hc]

end OnBytes.K.Arm
