-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/OwedEntry.lean: AT THE ENTRY's FILE: ALL THAT THE PRINTER ASKS OF THE COMPILED
PROVER's STRING, FROM THE PROVER's OWN EQUATION AND NAMED PREMISES. The twin of
OnBytes/Prover/Print/Owed.lean.

Main names.
  EntryOwes ... τ   ON THE TWO OUTER TREES, at the places read: the kept leaf's salt begins with the
    configuration's digest; the symbol names its place; the stored column, the salt and the path are
    shorter than 2^64.
  entry_prints      THE END: PrintableL and SizesL: what the form's way back asks of the entry
    file's string (Johnson/Prover/Print/FormBack.lean: Fits' clauses prL, szL).

By: printableL_of_prove (Johnson/Prover/Print/HonestEntry.lean) · sizesL_of_prove
(Johnson/Prover/Print/HonestEntrySizes.lean).

Does not show: that a premise is met. The leaf file's reader tests no word against the prime and no
run value against zero: neither is asked. Nothing on acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.HonestEntrySizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open Rom
open _root_.Compile (Tag Opening pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Run.PQ (View SgX CK XO weX)
open OnBytes.Flat (linkSkeletonOfRoundData)
open Johnson.RunOne.StrictW (wqW)
open OnBytes.Prover OnBytes.Prover.Print

variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)
  {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- What the prover does not make: the two outer trees, at the places read. -/
def EntryOwes (x : Y) (y : (twoExternalStrings (2 ^ a) SgX).Str) (xt : ℕ → TreeK 256 L) (cfg : ByteArray)
    (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) : Prop :=
  ∀ p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.extReads x τ.rho,
    (SaltFrom cfg ((xt ((weX a).which p)).inp ((weX a).leaf p)).salt ∧
      ((twoExternalStrings (2 ^ a) SgX).rd y p).1 = p.elim (·.val) (·.val)) ∧
    (((twoExternalStrings (2 ^ a) SgX).rd y p).2.length < 2 ^ 64 ∧
      ((xt ((weX a).which p)).inp ((weX a).leaf p)).salt.length < 2 ^ 64 ∧
      (pathOf (xt ((weX a).which p)).lv ((weX a).leaf p)).length < 2 ^ 64)

variable (L) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) →
    OSym (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape p → Body L)
  (embP : PlainPart (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann →
    PlainPart (shapeOf L t) (annOf L t))
  (xin : Y → Option X) (cms : List (Dig 256)) (x : Y)
  (y : (twoExternalStrings (2 ^ a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (cfg : ByteArray) (salt : ℕ)
  (s : OnBytes.Params.LinBindingShape) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up)
  (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
  (root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
  (answers : List (UInt64 × UInt64 × UInt64))

/-- **ALL THAT THE PRINTER ASKS OF THE ENTRY FILE's STRING.** -/
theorem entry_prints
    (hp : (proveX t (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) embS embP xin cms x y xt σ
      (coinsOf (ds.length + 1) (ds.length + 1) s.logLeaves bc) cap).det g = .ok (π, τ))
    (hfit : bc.Fit salt s) (hs : s.logLeaves = 0) (hsalt : salt ≤ 64) (hcfg : cfg.size = 32)
    (hpub : PublicL ds a) (hw : (wqW C ds a xs dec K chal).OKG) (hcap : ∀ i, cap i < 2 ^ 64)
    (hdep : (wqW C ds a xs dec K chal).maxDepth < 2 ^ 64)
    (hr0 : root0.size = 32) (ha0 : answers0.length < 2 ^ 64) (hr : root.size = 32)
    (ha : answers.length < 2 ^ 64) (ho : EntryOwes C ds a xs dec x y xt cfg τ) :
    PrintableL C ds a xs dec cfg π ∧ SizesL C ds a xs dec root0 answers0 root answers π :=
  ⟨printableL_of_prove C ds a xs dec L K chal t embS embP xin cms x y xt σ bc cap g cfg salt s π τ
      hp hfit hs hcfg hpub.few fun p hp' => (ho p hp').1,
    sizesL_of_prove C ds a xs dec L K chal t embS embP xin cms x y xt σ bc cap g salt s π τ root0
      answers0 root answers hp hfit hsalt hpub hw hcap hdep hr0 ha0 hr ha
      fun p hp' => (ho p hp').2⟩

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.EntryOwes
#print axioms Johnson.Prover.Print.entry_prints
