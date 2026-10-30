-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Owed.lean: AT ONE WHOLE FILE: ALL THAT THE PRINTER ASKS OF THE COMPILED
PROVER's STRING, FROM THE PROVER's OWN EQUATION AND TWO RECORDS OF NAMED PREMISES: one on the byte
coins, one on what the prover does not make (the strategy's plain parts and words; the outer tree as
its committer has kept it).

Main names.
  CoinsPrint bc salt s   the byte coins' lengths (ByteCoins.Fit); at most 64 bytes of a leaf's own
    salt; none of the three run values is 32 zero bytes.
  WholeOwes ... π τ      ON THE STRATEGY: it has sent the coins' run2 and run3, and the front's
    answers again; the front's answers' words, their number, the copy's number; the words of each
    round's plain part; the words of each opened column. ON THE OUTER TREE, at the places read: the
    kept leaf's salt begins with the configuration's digest; the symbol names its place; the stored
    column's words and length; the salt's and the path's lengths.
  whole_prints           THE END: Printable, Canon, and the three run values of the string are not
    zero: what the form's way back asks of a whole file's string
    (Johnson/Prover/Print/FormBack.lean: Fits' clauses prT, cnT, runT, and prB, cnB, runB).

By: printable_of_prove (OnBytes/Prover/Print/Honest.lean) · canon_of_prove
(OnBytes/Prover/Print/HonestCanon.lean).

Does not show: that either record is met. Nothing on acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.HonestCanon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined Rom
open _root_.Compile (Tag Opening pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ FewJ Few0)
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover

/-- What is asked of the byte coins. -/
structure CoinsPrint {I X : Type} {L : BatchProtocolWithLeafBody I X} (bc : ByteCoins L) (salt : ℕ)
    (s : Params.LinBindingShape) : Prop where
  fit : bc.Fit salt s
  salt64 : salt ≤ 64
  ok1 : _root_.Fmt.runOk bc.run1 = true
  ok2 : _root_.Fmt.runOk bc.run2 = true
  ok3 : _root_.Fmt.runOk bc.run3 = true

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- What the prover does not make. -/
structure WholeOwes (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (xt : ℕ → TreeK 256 L)
    (bc : ByteCoins L) (cfg : ByteArray) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape) : Prop where
  run2 : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run = bc.run2
  run3 : (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = bc.run3
  again : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.answers =
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers
  answers : ∀ e ∈ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers, Carrier.okE e.triple
  count : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.length < 2 ^ 64
  copy : (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy < 2 ^ 64
  words₁ : WordsP C D.ds₁ (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2
  words₂ : WordsP C D.ds₂ (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2
  words₃ : WordsP C D.ds₃ (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2
  cols₁ : ∀ q op, op₁ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₁ q op.sym, Carrier.okF w
  cols₂ : ∀ q op, op₂ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₂ q op.sym, Carrier.okF w
  cols₃ : ∀ q op, op₃ C D tF tJ t3 silent run π q = some op →
    ∀ w ∈ colOfSym C D.ds₃ q op.sym, Carrier.okF w
  outer : ∀ p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x τ.rho,
    SaltFrom cfg ((xt ((weOne D.a).which p)).inp ((weOne D.a).leaf p)).salt ∧ (y p).1 = p.val ∧
      CanonO (y p).2 ((xt ((weOne D.a).which p)).inp ((weOne D.a).leaf p)).salt
        (pathOf (xt ((weOne D.a).which p)).lv ((weOne D.a).leaf p))

variable (L) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (wholeDesc C D tF tJ t3 silent run).batch.loc.shape) →
    OSym (wholeDesc C D tF tJ t3 silent run).batch.loc.shape p → Body L)
  (embP : PlainPart (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
    (wholeDesc C D tF tJ t3 silent run).batch.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
  (y : (oneExternalString (2 ^ D.a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (wholeDesc C D tF tJ t3 silent run).batch.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (cfg : ByteArray) (salt : ℕ)
  (s : Params.LinBindingShape) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
  (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape)

/-- **ALL THAT THE PRINTER ASKS OF A WHOLE FILE's STRING.** -/
theorem whole_prints
    (hp : (proveX t (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) embS embP xin cms x y xt σ
      (coinsOf (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 s.logLeaves bc) cap).det g =
        .ok (π, τ))
    (hb : CoinsPrint bc salt s)
    (hJ : FewJ (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (h0 : Few0 (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (hw : (wqWhole C K chal D tF tJ t3 silent run).OKG)
    (hcap : ∀ i, cap i < 2 ^ 64) (hdep : maxDepthW D < 2 ^ 64)
    (hwid : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ u ∈ d.trees, u.W < 2 ^ 64)
    (ho : WholeOwes C D tF tJ t3 silent run x y xt bc cfg π τ) :
    Printable C D tF tJ t3 silent run cfg s π ∧ Canon C D tF tJ t3 silent run π ∧
      (_root_.Fmt.runOk (bitsToBytes π.salt) = true ∧
        _root_.Fmt.runOk (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run = true ∧
        _root_.Fmt.runOk (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = true) := by
  refine ⟨printable_of_prove C D tF tJ t3 silent run L K chal t embS embP xin cms x y xt σ bc cap g
      cfg salt s π τ hp hb.fit hJ h0 ho.run2 ho.run3 ho.again
      fun p hp' => ⟨(ho.outer p hp').1, (ho.outer p hp').2.1⟩,
    canon_of_prove C D tF tJ t3 silent run L K chal t embS embP xin cms x y xt σ bc cap g salt s π τ
      hp hb.fit hb.salt64 hJ h0 hw hcap hdep hwid ho.answers ho.count ho.copy ho.words₁ ho.words₂
      ho.words₃ ho.cols₁ ho.cols₂ ho.cols₃ fun p hp' => (ho.outer p hp').2.2, ?_, ?_, ?_⟩
  · obtain ⟨z, -, rfl, -⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ _ cap g π τ).1 hp
    show _root_.Fmt.runOk (bitsToBytes (bytesToBits bc.run1)) = true
    rw [bitsToBytes_bytesToBits]
    exact hb.ok1
  · rw [ho.run2]
    exact hb.ok2
  · rw [ho.run3]
    exact hb.ok3

end

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.CoinsPrint
#print axioms OnBytes.Prover.Print.WholeOwes
#print axioms OnBytes.Prover.Print.whole_prints
