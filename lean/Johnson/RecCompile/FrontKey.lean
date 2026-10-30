-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/FrontKey.lean: (1) countable_keyC: the keys FullKey of the verifier with a record
are countable, for every carrier that has a wire, a wire of the record and a coding m of the typed
oracles in which the oracle for leaves has one block (a twin of countable_key,
VerifiableInference/KeyCode.lean:151-186; that records are countable is read off the coding too: a
first query holds a record). (2) soundForWith_recSystemC: soundForWith_recSystem (Front.lean) with
that lemma filled in and the bound written out:
  t ↦ epsC W c t 0 + (t + 2)² / 2^256 = (t + tVC + 1) · c + 2 (t + tVC + 2)² / 2^256 + (t + 2)² /
    2^256, t the sum of the committer's and the prover's queries to the hash function.

-/
import Johnson.RecCompile.Front

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Rec
open Rom ZKCP Iop Compile Compile.Batch Compile.Batch.Cms

variable {I X ISK : Type} {lam : ℕ} {L : HolographicProtocol I X}

theorem countable_keyC (hlam : 0 < lam) (W : QueryLayout lam L.carrierC) (Sd : OutOfDomainSampleQueryLayout lam W.K L)
    (m : OracleCoding (spec lam W.K L.carrierC) lam) (hleaf : m.blocks OracleName.leaf = 1) :
    Countable (FullKey lam L) := by
  haveI : Countable (LeafIn L.carrierC) := countable_points m OracleName.leaf (by omega)
  have hSg : Countable L.Symbol := Function.Injective.countable
    (f := fun a : L.Symbol => (⟨some (Sum.inl a), []⟩ : LeafIn L.carrierC))
    fun _ _ e => Sum.inl.inj (Option.some.inj (LeafIn.mk.inj e).1)
  have hSym : ∀ t : Tag, Countable (SymAny (shapeOf L.carrierC t)) := fun t =>
    Function.Injective.countable
      (f := fun z : SymAny (shapeOf L.carrierC t) =>
        (⟨some (Sum.inr ⟨t, z⟩), []⟩ : LeafIn L.carrierC))
      fun _ _ e => eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Option.some.inj (LeafIn.mk.inj e).1))).2
  have hFb : ∀ t : Tag, Countable (FbIn lam L.carrierC t) := fun t =>
    countable_points m (OracleName.fb t) (blocks_pos_messages hlam m t)
  have hPlain : ∀ t : Tag, Countable (Plains (shapeOf L.carrierC t)) := fun t =>
    haveI := hFb t
    countable_plains (shapeOf L.carrierC t) (annOf L.carrierC t) (Function.Injective.countable
      (f := fun x : PlainPart (shapeOf L.carrierC t) (annOf L.carrierC t) =>
        (⟨0, Head.f2 none [], none, x⟩ : FbIn lam L.carrierC t))
      fun _ _ e => (FbIn.mk.inj e).2.2.2)
  haveI : Countable (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :=
    countable_argumentString (BatchInteractiveOracleProof.ofProto L.offline) (finite_positions _ _ W.T.sh)
      (hSym Tag.test) (hPlain Tag.test) (inferInstanceAs (Finite (Fin L.wordLength))) hSg
  haveI : Countable (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :=
    countable_argumentString (BatchInteractiveOracleProof.ofProto L.link) (finite_positions _ _ W.Lk.sh)
      (hSym Tag.link) (hPlain Tag.link) (inferInstanceAs (Finite (Fin L.wordLength ⊕ Fin L.wordLength))) hSg
  haveI : Countable L.Rec :=
    haveI := hFb Tag.test
    Function.Injective.countable
      (f := fun r : L.Rec =>
        (⟨0, Head.f1 [] (some (none, r, r)) [], none, Sd.pl Tag.test⟩ : FbIn lam L.carrierC Tag.test))
      fun _ _ e =>
        (Prod.mk.inj (Prod.mk.inj (Option.some.inj (Head.f1.inj (FbIn.mk.inj e).2.1).2.1)).2).1
  exact Function.Injective.countable
    (f := fun k : FullKey lam L => (k.cm, k.rcd, k.piT, k.links))
    fun ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ e => by
      have e' : (a1, a2, a3, a4) = (b1, b2, b3, b4) := e
      cases e'
      rfl

theorem epsC_sum (W : QueryLayout lam L.carrierC) (c : ℝ≥0∞) (tC tP : ℕ) :
    epsC W c tC tP = epsC W c (tC + tP) 0 := by
  simp only [epsC, Nat.add_zero]

/-- The front's soundness for the verifier with a record, the bound written out. This is said under
the hypotheses that stand in the statement itself, which this comment does not list; it is no claim
that they hold. -/
theorem soundForWith_recSystemC {L : HolographicProtocol I X} (W : QueryLayout 256 L.carrierC) (Sd : OutOfDomainSampleQueryLayout 256 W.K L)
    (p : Params) (m : OracleCoding (spec 256 W.K L.carrierC) 256) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1)
    (A : ZKCP.Gen.Arg (spec 256 W.K L.carrierC) I X Unit (FullKey 256 L) ISK (RequestProof 256 L))
    (hA : A.V = VC W Sd p) (tag bound : ℕ)
    (build : List Token × List Token → List Token → Option X) (π₀ : FullKey 256 L × RequestProof 256 L)
    (nextToken : I → List Token → Option Token) {Yes IsTrue : I → X → Prop}
    (sub : ∀ i x, Yes i x → IsTrue i x) (c : ℝ≥0∞)
    (bnd : ZKCP.Gen.HasIndexBindingWith (relPair Yes IsTrue sub) A (extractorC0 W) (epsC W c))
    (claim : I → List Token → List Token → Prop) (x₀ : X)
    (sound : ∀ i (x' : List Token × List Token) a x, build x' a = some x → IsTrue i x →
      claim i x'.1 x'.2) :
    SoundForWith
      (systemOf (schemeOverOneHashFunction m A) (countable_keyC (by norm_num) W Sd m hl) tag bound build π₀
        nextToken)
      (tokenExtractorOf (X := X) (extractorOverOneHashFunction m (extractorC0 W))
        (countable_keyC (by norm_num) W Sd m hl) tag).Ei claim
      fun t => epsC W c t 0 + (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  soundForWith_recSystem W Sd p m hl hn A hA _ tag bound build π₀ nextToken sub bnd claim x₀ sound
    fun tC tP => le_of_eq (congrArg (fun a => a + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)
      (epsC_sum W c tC tP))

end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.countable_keyC
#print axioms VerifiableInference.Rec.soundForWith_recSystemC
