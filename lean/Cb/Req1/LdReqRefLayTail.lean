-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLayTail.lean: under the hypotheses of its statements, the wide fact passes the last
segment of a reference request: so the final batching's own masks are fresh before it if the fact g
is fresh before that segment.

Statements (`Cb.Spec.ldReqRefLay_tail`, `Cb.Spec.ldReqRefLay_tailB`) and proofs: an assembly. The
analogue, for the last segment (entry step; body; exit step: no closing), of
Cb/Req1/LdReqRefLay.lean's `ldReqRefLay_cross`.
T is the last segment (`LdRefT`) of the reference request `ldReqRef` (Cb/Req1/LdReqRef.lean). Facts:
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`. (Cb/Req1/LdSegFresh.lean) Wide facts: `LdStage.wideFact`
(Cb/Req1/LdSegCarry.lean); `After`: Cb/Req1/LdReq.lean.
Cb/Req1/LdReqRefLay.lean's last statement asks: "a fact g laid before the last segment that its
moves hand on as the wide fact of the final batching's own masks". Here that clause is brought down
to the same kind of conditions as for a segment that closes.

Main names:
  `Spec.ldReqRefLay_tail`: under the hypotheses of its statement, for every set Y of facts with Y g:
    `T.tail.After Y ⟨K', kc', Mk, put'⟩`, from:
      the entry step hands g on as the wide fact `W.fact own Mk val` at the body's entry;
      the body does not look (Cb/Req1/LdSegRefTenLook.lean: `ldSegRefX_out`): quiet for the front,
      the two senders of the body do not look, neither late block reads an own entry (each reads
      only entries of the wide reading that are not own);
      the exit step's own condition: overwriting the masks changes neither the new explicit part
      nor, but by the overwriting put', the new reading kc'.
  `Spec.ldReqRefLay_tailB`: the case kc', put' := those of the wide fact of the final batching's own
    masks (`R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk ..`): the clause of
    Cb/Req1/LdReqRefLay.lean, word for word, given that g is laid. (not all hypotheses are named
    here: see its statement)

Limits: this file does not say that an instance meets the conditions.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefLayProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace Spec

/-- Under the hypotheses below, the wide fact passes the last segment. -/
def ldReqRefLay_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (b : LdStage E Kc) (T : LdRefT R b) [Nonempty R.ix.C.E0.Str]
      (W : LdRefW T.A) (Fq : LdRefF T.A) (κ : T.A.Gh → Kc) (own : T.A.Xa.Q.D.S.Ent → Prop)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → T.A.Xa.Q.D.S.Ent → E) (g : MaskFact b.J.W)
      (K' : Type) (kc' : R.X.src.J.W → K') (put' : Mk → K' → K'),
    T.A.OK pp → T.A.Ghost κ → Fq.OK pp → W.PassQ Fq own Mk val → T.A.Xa.A.MaskOK T.A.Xa.Dt →
    (∀ n, T.A.Xa.A.srAll T.A.Xa.Dt n → W.Rd2 n ∧ ¬ T.A.own2 own n) → T.A.X.Own →
    (∀ n, T.A.Rdt n → W.Rd2 n ∧ ¬ T.A.own2 own n) →
    (∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y (W.fact own Mk val)) →
    (∀ x (w w' : (T.A.X.tgt T.St₁ T.Az).W) M,
      ((T.A.X.tgt T.St₁ T.Az).wideFact W.Rd2 W.Rr2 (T.A.own2 own) Mk (T.A.val2 val)).kc w' =
        ((T.A.X.tgt T.St₁ T.Az).wideFact W.Rd2 W.Rr2 (T.A.own2 own) Mk (T.A.val2 val)).put
          M (((T.A.X.tgt T.St₁ T.Az).wideFact W.Rd2 W.Rr2 (T.A.own2 own) Mk (T.A.val2 val)).kc w) →
      (T.m' (x, w')).1 = (T.m' (x, w)).1 ∧ kc' (T.m' (x, w')).2 = put' M (kc' (T.m' (x, w)).2)) →
    ∀ Y : MaskFact b.J.W → Prop, Y g → T.tail.After Y ⟨K', kc', Mk, put'⟩

/-- Under the hypotheses below, the final batching's own masks are fresh behind the last segment if
the fact g is fresh before it. -/
def ldReqRefLay_tailB : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      [CharP E pp] (R : LdORE F E Kc) (b : LdStage E Kc) (T : LdRefT R b)
      [Nonempty R.ix.C.E0.Str] (W : LdRefW T.A) (Fq : LdRefF T.A) (κ : T.A.Gh → Kc)
      (own : T.A.Xa.Q.D.S.Ent → Prop) (val : R.X.mask.Mk → T.A.Xa.Q.D.S.Ent → E)
      (g : MaskFact b.J.W) (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    T.A.OK pp → T.A.Ghost κ → Fq.OK pp → W.PassQ Fq own R.X.mask.Mk val →
    T.A.Xa.A.MaskOK T.A.Xa.Dt → (∀ n, T.A.Xa.A.srAll T.A.Xa.Dt n → W.Rd2 n ∧ ¬ T.A.own2 own n) →
    T.A.X.Own → (∀ n, T.A.Rdt n → W.Rd2 n ∧ ¬ T.A.own2 own n) →
    (∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y (W.fact own R.X.mask.Mk val)) →
    (∀ x (w w' : (T.A.X.tgt T.St₁ T.Az).W) M,
      ((T.A.X.tgt T.St₁ T.Az).wideFact
          W.Rd2 W.Rr2 (T.A.own2 own) R.X.mask.Mk (T.A.val2 val)).kc w' =
        ((T.A.X.tgt T.St₁ T.Az).wideFact W.Rd2 W.Rr2 (T.A.own2 own) R.X.mask.Mk (T.A.val2 val)).put
          M (((T.A.X.tgt T.St₁ T.Az).wideFact
            W.Rd2 W.Rr2 (T.A.own2 own) R.X.mask.Mk (T.A.val2 val)).kc w) →
      (T.m' (x, w')).1 = (T.m' (x, w)).1 ∧
      (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M).kc
          (T.m' (x, w')).2 =
        (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M).put M
          ((R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M).kc
            (T.m' (x, w)).2)) →
    ∀ Y : MaskFact b.J.W → Prop, Y g →
      T.tail.After Y
        (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)

end Spec

theorem ldReqRefLay_tail : Spec.ldReqRefLay_tail := by
  intro F E Kc _ _ _ _ _ pp _ R b T _ W Fq κ own Mk _ _ val g K' kc' put' hA hG hF
    hq hM hL hO hT hE hX Y hY
  unfold LdRefT.tail
  rw [LdProg.after_snoc, LdProg.head_after]
  unfold LdRefT.exit
  exact segCarry_step _ R.X.src _ _ _ _ _
    ((T.A.X.tgt T.St₁ T.Az).wideFact W.Rd2 W.Rr2 (T.A.own2 own) Mk (T.A.val2 val)) K' kc' put'
    (ldSegRefX_out E Kc pp _ T.A W Fq κ _ own Mk val T.St₁ T.fz T.Az hA hG hF
      ⟨hE Y hY, hq.quiet, hq.send1, hq.send3⟩ hM hL hO hT) hX

theorem ldReqRefLay_tailB : Spec.ldReqRefLay_tailB := by
  intro F E Kc _ _ _ _ _ pp _ R b T _ W Fq κ own val g Rd Rr hA hG hF hq hM hL hO hT hE hX Y hY
  exact ldReqRefLay_tail F E Kc pp R b T W Fq κ own R.X.mask.Mk val g _ _ _ hA hG hF
    hq hM hL hO hT hE hX Y hY

end Cb
