-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDTail.lean: under the hypotheses of its statement, a pending block passes the last
segment of a reference request, from `T.TailD`: so the final batching's own masks are still fresh
before it in this sense: at the β'' and G of "Why:", some fact g of G is handed on by the last
segment's moves as the wide fact of β'' (of the facts laid: `Spec.ldReqRefLayJ_after`,
Cb/Req1/LdReqRefLayJ.lean: `L.LaidJ base g → L.segs.AfterJ base g`; that the facts in G are fresh,
and that β is pending before the last segment, this file does not say).

In standard terms: book-keeping for the honest prover's side of the last segment of a request's
sub-protocol, up to the final batching: a condition (`T.TailD`) on a set of entries of earlier
oracle messages, and one statement on it. The whole request: Cb/Ld/LdLayD.lean.

One definition and one statement (`Cb.Spec.ldLayD_tail`); the proof is in
Cb/Ld/LdLayDTailProofs.lean.
The records `LdReqRefDS` (Cb/Req1/LdReqRefStd.lean) and `LdReqRefDSA` (Cb/Req1/LdReqStdAny.lean) ask
(clause `layB`): "a fact laid before the last segment that its moves (entry step ; body ; exit
step) hand on as the wide fact of the final batching's own masks".
Cb/Req1/LdReqRefLayTail.lean brings that down to: the entry step hands the fact on, the exit step's
own condition, places, "quiet", and: the body's two senders do not look, beside the body's
conditions (`T.A.OK pp`) (not all hypotheses are named here: see `Spec.ldReqRefLay_tail`). Here in
the form of Cb/Ld/LdLayDKit.lean.

Main names:
  `T.TailD Q pp β β''`: there are a wide reading W over the last body, own entries, a type of masks
    (finite, not empty) and values with: the entry step hands β on as the pending block with these
    fields (`LdPend.StepD T.m`: a condition on the model's map); that block passes the body
    (`T.A.OutD`: places, readings, the two data maps do not look; whole: Cb/Ld/LdLayDKit.lean, the
    row of `A.OutD`: what a closed body is asked so that the wide fact passes it); the exit step
    hands what comes out on as β'' (`LdPend.StepD T.m'`).
  `Spec.ldLayD_tail`: E of characteristic pp; the configuration's further oracles have a string
    (`Nonempty R.ix.C.E0.Str`, an instance binder); G: a set of facts before the last segment,
    closed under join, coarser reading and another type of masks. If β's wide fact lies in G, the
    body has its conditions (`T.A.OK pp`) and `T.TailD Q pp β β''`, then some fact g of G is handed
    on by the last segment's moves as the wide fact of β''.

Why: with β'' := the pending block of the final batching's own masks, and G := the facts laid
before the last segment, this is the clause `layB`.

Notation: `Q`: what is asked of a layout: a parameter (`LdLayQ`, Cb/Ld/LdLayDKit.lean).

Limits: this file does not say that β is pending before the last segment.
This file does not say that the conditions can be met together: a guard's matter.
It says nothing on a splitting.
`T.TailD` is written so as to name no property of an honest prover, link or sender (by reading; no
program's result is reported here).
The two steps are free moves: their conditions are conditions on the model's maps; a write-up
of ours (lean/CREDITS.md) has no such steps and no counterpart of these conditions.
"The configuration's further oracles have a string" stands as an instance binder of the statement:
it is a hypothesis.
`T.A.OK pp` is taken as it stands (the model's side and the protocol's side of the body give it).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLayDKit
import Cb.Req1.LdReqRefLayTail

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- The last segment hands the pending block β on as β'' (exactly: the three conditions below; what
follows from them: `Spec.ldLayD_tail`, under its hypotheses). -/
def LdRefT.TailD {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b) (Q : LdLayQ E) (pp : ℕ)
    (β : LdPend b) (β'' : LdPend R.X.src) : Prop :=
  ∃ (W : LdRefW T.A) (own : T.A.Xa.Q.D.S.Ent → Prop) (Mk : Type) (_ : Fintype Mk)
      (_ : Nonempty Mk) (val : Mk → T.A.Xa.Q.D.S.Ent → E),
    LdPend.StepD T.m β (⟨W.Rd, W.Rr, own, Mk, val⟩ : LdPend T.A.V.Fp.s0) ∧
    T.A.OutD Q pp W own Mk val ∧
    LdPend.StepD T.m'
      (⟨W.Rd2, W.Rr2, T.A.own2 own, Mk, T.A.val2 val⟩ : LdPend (T.A.X.tgt T.St₁ T.Az)) β''

/-- Under the hypotheses below: a pending block passes the last segment. -/
def Spec.ldLayD_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (b : LdStage E Kc) (T : LdRefT R b) [Nonempty R.ix.C.E0.Str] (Q : LdLayQ E)
      (G : MaskFact b.J.W → Prop) (β : LdPend b) (β'' : LdPend R.X.src),
    (∀ h, MaskFact.JCl G h → G h) → T.A.OK pp → G β.fact → T.TailD Q pp β β'' →
    ∃ g, G g ∧ ∀ Y : MaskFact b.J.W → Prop, Y g → T.tail.After Y β''.fact

end Cb
