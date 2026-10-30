-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefLastLay.lean: a reference request with one pending row: under the hypotheses of
`Spec.ldSegRefLast_layB`, the final batching's own masks are fresh behind the last segment if the
fact g₀ is fresh before it.

A rule on the wide fact (`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean), a statement
(`Cb.Spec.ldSegRefLast_layB`) and proofs: an assembly. Cb/Req1/LdSegRefLast.lean makes the end of
the request and its last segment from the last body's data (`R₀.ofBody ..`, `LdRefT.ofBody ..`: the
exit step is the identity). Cb/Req1/LdReqRefLayTail.lean brings "the last segment's moves hand a
fact on as the wide fact of the final batching's own masks" down to conditions on entry step, body
and exit step. Here the exit step's condition is discharged.

Main names:
  `LdStage.wideFact_ext`: the wide fact depends on "own" as a set, and on the values at own entries
    only.
  `Spec.ldSegRefLast_layB`: for T := LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back and
    R := R₀.ofBody A Z' n' wAt' Rd': for every set Y of facts with Y g₀:
      T.tail.After Y (R.X.src.wideFact W.Rd2 W.Rr2 (R.X.atOwn R.X.wAt) R.X.mask.Mk ..),
    for E of characteristic pp and `R₀.ix.C.E0.Str` nonempty, under `A.OK pp`, `A.Ghost κ`,
    `Fq.OK pp`, `A.Xa.A.MaskOK A.Xa.Dt`, `A.X.Own`, `Function.Injective wAt'`, and from:
      the body does not look (`W.PassQ`; neither late block reads an own entry)
        (∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n; the same for A.Rdt n);
      the own entries are the places wAt': seen at the body's last family, "own" is the set of the
      wAt' i, and the value laid at wAt' i is the i-th mask;
      the entry step hands g₀ on as the wide fact at the body's entry.

Limits: this file does not say that g₀ is fresh behind the first sendings
(Cb/Req1/LdReqStdFresh.lean, Cb/Ld/LdSendStdVis.lean). It says nothing on requests with closed
segments before the last.
This file gives no instance that meets its hypotheses, so as far as this file shows its theorems may
hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefLayTail
import Cb.Req1.LdSegRefLast

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- the wide fact depends on "own" as a set, and on the values at own entries only -/
theorem LdStage.wideFact_ext {E Kc : Type} [Field E] [Fintype E] (a : LdStage E Kc)
    (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own own' : a.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val val' : Mk → a.S.Ent → E) (h1 : ∀ n, own n ↔ own' n)
    (h2 : ∀ M n, own n → val M n = val' M n) :
    a.wideFact Rd Rr own Mk val = a.wideFact Rd Rr own' Mk val' := by
  classical
  have e : (fun (M : Mk) (k : a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp) =>
        (a.S.ow own (val M) k.1, k.2)) =
      fun M k => (a.S.ow own' (val' M) k.1, k.2) := by
    funext M k
    refine Prod.ext (funext fun o => funext fun j => ?_) rfl
    show (if own ⟨o, j⟩ then val M ⟨o, j⟩ else k.1 o j) =
      if own' ⟨o, j⟩ then val' M ⟨o, j⟩ else k.1 o j
    by_cases h : own ⟨o, j⟩
    · rw [if_pos h, if_pos ((h1 _).1 h), h2 M _ h]
    · rw [if_neg h, if_neg fun h' => h ((h1 _).2 h')]
  unfold LdStage.wideFact
  rw [e]

/-- Under the hypotheses below, the final batching's own masks are fresh behind the last segment if
the fact g₀ is fresh before it. -/
def Spec.ldSegRefLast_layB : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R₀ : LdORE F E Kc) (A : LdRefD E Kc R₀.ix) (Z' : Evader E Unit) (n' : ℕ)
      (wAt' : PIdx (List.replicate R₀.k (pfCube E n')) → A.Xa.Q.T.Ent) (Rd' : A.Xa.Q.T.Ent → Prop)
      (b : LdStage E Kc) (f : b.X → Option A.V.Fp.s0.X) (g : ExtMap b.Ex A.V.Fp.s0.Ex)
      (m : b.X × b.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : b.X × b.Ex.Str → A.V.Fp.s0.W → b.W)
      [Nonempty R₀.ix.C.E0.Str] (W : LdRefW A) (Fq : LdRefF A) (κ : A.Gh → Kc)
      (own : A.Xa.Q.D.S.Ent → Prop)
      (val : (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk → A.Xa.Q.D.S.Ent → E) (g₀ : MaskFact b.J.W),
    A.OK pp → A.Ghost κ → Fq.OK pp → W.PassQ Fq own (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk val →
    A.Xa.A.MaskOK A.Xa.Dt → (∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n) → A.X.Own →
    (∀ n, A.Rdt n → W.Rd2 n ∧ ¬ A.own2 own n) → Function.Injective wAt' →
    (∀ n, A.own2 own n ↔ ∃ i, wAt' i = n) →
    (∀ (M : (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk) i, A.val2 val M (wAt' i) = M i) →
    (∀ Y : MaskFact b.J.W → Prop, Y g₀ →
      (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).entry.After
        Y (W.fact own (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk val)) →
    ∀ Y : MaskFact b.J.W → Prop, Y g₀ →
      (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).tail.After Y
        ((R₀.ofBody A Z' n' wAt' Rd').X.src.wideFact W.Rd2 W.Rr2
          ((R₀.ofBody A Z' n' wAt' Rd').X.atOwn (R₀.ofBody A Z' n' wAt' Rd').X.wAt)
          (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk
          fun M => (R₀.ofBody A Z' n' wAt' Rd').X.atVal (R₀.ofBody A Z' n' wAt' Rd').X.wAt M)

theorem ldSegRefLast_layB : Spec.ldSegRefLast_layB := by
  intro F E Kc _ _ _ _ _ pp _ R₀ A Z' n' wAt' Rd' b f g m back _ W Fq κ own val g₀ hA hG hF hq hM
    hL hO hT hi h1 h2 hE Y hY
  have e := LdStage.wideFact_ext (R₀.ofBody A Z' n' wAt' Rd').X.src W.Rd2 W.Rr2 (A.own2 own)
    ((R₀.ofBody A Z' n' wAt' Rd').X.atOwn (R₀.ofBody A Z' n' wAt' Rd').X.wAt)
    (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk
    (A.val2 val)
    (fun M => (R₀.ofBody A Z' n' wAt' Rd').X.atVal (R₀.ofBody A Z' n' wAt' Rd').X.wAt M) h1
    (fun M n hn => by
      obtain ⟨i, rfl⟩ := (h1 n).1 hn
      exact (h2 M i).trans (hi.extend_apply M (fun _ => 0) i).symm)
  have h : (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back).tail.After Y
      ((R₀.ofBody A Z' n' wAt' Rd').X.src.wideFact
        W.Rd2 W.Rr2 (A.own2 own) (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk (A.val2 val)) :=
    ldReqRefLay_tail F E Kc pp (R₀.ofBody A Z' n' wAt' Rd') b
      (LdRefT.ofBody R₀ A Z' n' wAt' Rd' b f g m back) W Fq κ own
      (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk val g₀ _
      ((R₀.ofBody A Z' n' wAt' Rd').X.src.wideFact
        W.Rd2 W.Rr2 (A.own2 own) (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk (A.val2 val)).kc
      ((R₀.ofBody A Z' n' wAt' Rd').X.src.wideFact
        W.Rd2 W.Rr2 (A.own2 own) (R₀.ofBody A Z' n' wAt' Rd').X.mask.Mk (A.val2 val)).put
      hA hG hF hq hM hL hO hT hE (fun _ _ _ _ hh => ⟨rfl, hh⟩) Y hY
  rw [e] at h
  exact h

end Cb
