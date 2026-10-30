-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/HonestEntrySizes.lean: THE COMPILED PROVER's PROOF STRING OF THE ENTRY's FILE
MEETS SizesL (Johnson/Prover/Print/Entry.lean): what the reader of the leaf file's bytes asks beside
PrintableL. The twin of OnBytes/Prover/Print/HonestCanon.lean's canon_of_prove, over its general
lemmas.

Main names.
  nonces_SL          at a stretch of local written rounds each printed round's nonce is below B.
  sizesL_of_prove    THE END.

What it asks. The prover has returned (π, τ); the byte coins' lengths with at most 64 bytes of a
leaf's own salt; the public clauses (PublicL, Johnson/Prover/Print/EntryAtFull.lean: theorems at
dsFull and dsSmall); the wire record's laws (a premise of the prover's own theorem yes_of_prove);
every cap and the wire record's greatest depth are below 2^64; the caller's two roots have 32 bytes
and the two lists of answers are shorter than 2^64; at the outer places read: the stored column, the
kept leaf's salt and the kept tree's path are shorter than 2^64.

Does not show: that any premise is met. The leaf file's reader tests no word against the prime, so
no word is asked here. Nothing on acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.HonestEntry
import OnBytes.Prover.Print.HonestCanon

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

theorem nonces_SL (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (cap : ℕ → ℕ)
    (B : ℕ) (hcap : ∀ i, cap i < B) : ∀ (ds : List PQ.RD) (i : ℕ) (rts : List (Dig 256))
    (pl : Plains (PQ.uL C ds)),
    PutIn cap i (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds) pl →
    ∀ r ∈ roundsOfS C ds rts pl, r.2 < B
  | [], _, _, _, _ => fun _ hr => by cases hr
  | d :: ds, i, rts, (pl, r), h => fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact nonce_of (cap i) B (hcap i) d.entry.work pl h.1
    · exact nonces_SL C K chal cap B hcap ds (i + 1) _ r h.2 x hx

section End
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)
  {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) →
    OSym (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape p → Body L)
  (embP : PlainPart (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann →
    PlainPart (shapeOf L t) (annOf L t))
  (xin : Y → Option X) (cms : List (Dig 256)) (x : Y)
  (y : (twoExternalStrings (2 ^ a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (salt : ℕ)
  (s : OnBytes.Params.LinBindingShape) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up)
  (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
  (root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
  (answers : List (UInt64 × UInt64 × UInt64))

/-- **THE COMPILED PROVER's STRING OF THE ENTRY's FILE MEETS SizesL.** -/
theorem sizesL_of_prove
    (hp : (proveX t (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) embS embP xin cms x y xt σ
      (coinsOf (ds.length + 1) (ds.length + 1) s.logLeaves bc) cap).det g = .ok (π, τ))
    (hfit : bc.Fit salt s) (hsalt : salt ≤ 64) (hpub : PublicL ds a)
    (hw : (wqW C ds a xs dec K chal).OKG) (hcap : ∀ i, cap i < 2 ^ 64)
    (hdep : (wqW C ds a xs dec K chal).maxDepth < 2 ^ 64)
    (hr0 : root0.size = 32) (ha0 : answers0.length < 2 ^ 64) (hr : root.size = 32)
    (ha : answers.length < 2 ^ 64)
    (hX : ∀ p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.extReads x τ.rho,
      ((twoExternalStrings (2 ^ a) SgX).rd y p).2.length < 2 ^ 64 ∧
        ((xt ((weX a).which p)).inp ((weX a).leaf p)).salt.length < 2 ^ 64 ∧
        (pathOf (xt ((weX a).which p)).lv ((weX a).leaf p)).length < 2 ^ 64) :
    SizesL C ds a xs dec root0 answers0 root answers π := by
  have hPL := proveX_putsLe t _ _ embS embP xin cms x y xt σ _ cap g π τ hp
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ _ cap g π τ).1 hp
  have hco := fit_coinsOf bc (ds.length + 1) (ds.length + 1) salt s hfit
  have hA : (linkSkeletonOfRoundData C ds a xs dec).up.ann = RoundSplits.allLocal (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape :=
    _root_.Run.Twin.allLo_eq _
  have hF : (linkSkeletonOfRoundData C ds a xs dec).up.ann.Fmt := by
    rw [hA]
    exact RoundSplits.fmt_allLocal _
  obtain ⟨R, hc⟩ := chain_at g (256 + 8 * salt) t cms (xin x) _ cap hco.leaf _ _ _ embS embP 0
    .first σ z hz hF (fewJ_wqW C ds a xs dec K chal hpub.few) (few0_wqW C ds a xs dec K chal)
    (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
  have hP := putIn_of_putsLe cap 0 _ _ _ _ _ hPL
  have hLen := lens_opensK g (256 + 8 * salt) (wqW C ds a xs dec K chal).maxDepth _ _
    (wqW C ds a xs dec K chal).sh embS z.2.1 R
    (haveI := (wqW C ds a xs dec K chal).decO
     fun p => decide (p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.reads x z.1 (trK _ z.2.1 z.1).plains))
    hc.rounds hw.sh hw.depth
  rw [rho_trK] at hX
  exact
    { root0 := hr0
      answers0 := ha0
      root := hr
      answers := ha
      rounds := hpub.rounds
      items := hpub.items
      trees := hpub.trees
      shapes := hpub.shapes
      depth := hpub.depth
      nonces := nonces_SL C K chal cap _ hcap ds 1 _ _ hP.2
      own := fun q op e => by
        obtain ⟨h1, h2⟩ := hLen (.inr q) op e
        exact ⟨by rw [h1]; omega, Nat.lt_of_le_of_lt h2 hdep⟩
      ext := fun p op e => by
        have e' : (if decide (p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.extReads x z.1) = true then
            some ((xt ((weX a).which p)).opening ((weX a).leaf p) ((twoExternalStrings (2 ^ a) SgX).rd y p))
            else none) = some op := e
        split at e'
        · rename_i hdd
          obtain rfl := Option.some.inj e'
          exact hX p (of_decide_eq_true hdd)
        · cases e' }

end End

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.nonces_SL
#print axioms Johnson.Prover.Print.sizesL_of_prove
