-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfIdx.lean: a rule that lifts a reduction from fixed messages to statements with oracles,
where the claims also read the message of the encoded index.
It carries blocks on claims that read the encoded index from "for each fixed tuple (message of the
index, messages)" to statements in which the index is decoded by the statement.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdWfIdxProofs.lean. For both
preambles. No protocol occurs here.

Why: a block that reduces claims on messages to claims on the same messages (a sumcheck, a batching
of tensor rows) is written once, with no code in it, and is knowledge sound for each fixed tuple of
messages (Cb/Ld/LdSigLift.lean: `GoodAt`, for any type of tuples). Over a signature S the tuple is
fixed before the block begins: it is the decoding of the statement; that is the lifting rule of that
file.
In a preamble the claims also read the message of the encoded index. The index is no oracle message:
it is a further oracle of the statement, its record is in the explicit part, no extractor hands its
message back, and relaxed relations hold none (Cb/Ld/LdSig.lean, the head, "An encoded index is not
an oracle message"; Cb/Ld/LdWfClose.lean: `idxRels`). But its message, too, is a function of the
statement: the decoding with the record. Hence a second lifting rule, before the first.

`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`. `GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT`
(likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its honest side,
between two joints, at given numbers; among its clauses: completeness between the honest relations,
outside sets of verifier randomness whose probabilities further clauses bound by the numbers;
round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input joint's set
of statements, with a given extractor, at the numbers' list of errors; and one on honest-verifier
zero knowledge. `H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always
empty; the honest prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept
under `D.put`; and where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the
distribution `D.sim xp ρ`. `GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`,
and the clause that every (x, y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here
`GoodAt` is a premise of `Spec.idxLift_goodAt`, `Spec.idxLift_goodB` and `Spec.idxLift_goodM`, and
the conclusion of the first; `GoodB` is the conclusion of the second, `GoodM` of the third; `MM` is
premise and conclusion of `Spec.idxLift_mm`, and a premise of `Spec.idxLift_goodM`. (In the sentence
on `MM`, `M : D.Mk` is the letter of Ior/Masked.lean.)

Main names:
  `idxAt C rc A`: the joint A on tuples (U, m), U a message of the index, read on statements with
    the index as the further oracle; rc reads the record off the explicit part. Its witness is (m,
    (prover encoded index, further witness)). Its four fields:
    exact (`rel`): the index is the encoding of the prover encoded index, with this record, and
      `A.rel` at its message;
    relaxed (`relR`): the statement decodes the index with the record to some U, and `A.relR` at U:
      the prover encoded index in the witness is not read; false where the index does not decode;
    condition (`on`): no collision of the index at the record's seed, and `A.on`;
    `core`: `A.core` at ((message of the prover encoded index, m), further witness).
  `idxExt C ext`: the extractor: the block's. Asked: the block's extractor does not read the index's
    part of the tuple (ext : M → ..; the extractors of a sumcheck, a zerocheck, a batching are the
    identity). So no extractor decodes:
    the messages m come from the later witness;
    the index has no extractor at all;
    the part "prover encoded index" of the later witness is handed back, and nobody reads it.
  `Spec.idxLift_goodAt`: a block R whose oracles are the index alone, which copies the index and
    keeps the record: `GoodAt` for tuples (U, m) gives `GoodAt` for tuples m, between `idxAt C rc A`
    and `idxAt C rc' B`. Same numbers.
  `Spec.idxLift_goodB`: with the first rule on top: `GoodB` (Ior/Masked.lean: `IOR.GoodT` without
    its clause on zero knowledge) of `R.keep S.Smp S.ext` between `S.over (idxAt ..)` and
    `S.over (idxAt ..)`.
  `idxMask C S D`, `Spec.idxLift_mm`: the item "masked messages" goes along: same own masks, same
    closed form, same simulator; of a witness is read what D reads of ((message of the prover
    encoded index, messages), further witness).
  `Spec.idxLift_goodM`: the two together: the bundle of a masked block. Its last hypothesis: every
    (x, y, w) in `A.rel` meets `D.Cl (D.pub x) (D.kc w)`.
    (not all hypotheses are named here: see its statement)

Limits: "no collision" is not used by these rules: the decoder is a function of the statement on all
statements. The condition is carried.
This file says nothing on blocks that read the index's symbols. The test for linear constraints
reads them. This file says nothing on zero knowledge of a chain. It says nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigLift
import Cb.Ld.LdWfClose
import Ior.MaskedMap

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable (C : ConfigurationWithOutOfDomainSample) {K X X' M Wp Wp' : Type}

/-- The joint A on tuples (message of the index, messages), with the index decoded by the statement.
-/
def idxAt (rc : X → C.Rec) (A : IOR.Rels K X C.E0 ((C.Msg × M) × Wp)) :
    IOR.Rels K X C.E0 (M × (C.PIdx × Wp)) where
  rel  := fun x y w => C.Enc (rc x) y w.2.1 ∧ A.rel x y ((w.2.1.1.1, w.1), w.2.2)
  relR := fun a w => ∃ U, C.dcd a.2 (rc a.1) = some U ∧ A.relR a ((U, w.1), w.2.2)
  on   := fun a => ¬ C.coll a.2 (rc a.1).1 ∧ A.on a
  core := fun w => A.core ((w.2.1.1.1, w.1), w.2.2)

/-- what a block on tuples is given of a witness -/
def idxIn (w : M × (C.PIdx × Wp)) : (C.Msg × M) × Wp := ((w.2.1.1.1, w.1), w.2.2)

/-- The honest side. -/
def idxH {R : IOR X C.E0 X' C.E0} (H : R.Honest ((C.Msg × M) × Wp) ((C.Msg × M) × Wp')) :
    R.Honest (M × (C.PIdx × Wp)) (M × (C.PIdx × Wp')) :=
  H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))

/-- The extractor: the block's, which does not read the index's part of the tuple. -/
def idxExt {s : Shape} (ext : M → X × C.E0.Str → Tr s → Wp' → Wp) :
    M → X × C.E0.Str → Tr s → C.PIdx × Wp' → C.PIdx × Wp :=
  fun m a τ w => (w.1, ext m a τ w.2)

/-- The parameters of the item "masked messages", over a signature. -/
def idxMask {E : Type} (S : Sig E) {R : IOR X C.E0 X' C.E0}
    (D : IOR.MaskData R ((C.Msg × S.Msg) × Wp)) :
    IOR.MaskData (R.keep S.Smp S.ext) (S.Wit × (C.PIdx × Wp)) :=
  ((D.mapW (idxIn C)).keep S.Smp S.ext).mapW fun w => (S.msgs w.1, w.2)

end

namespace Spec
open IOR

/-- The index-lifting rule. -/
def idxLift_goodAt : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (K X X' M Wp Wp' : Type) (R : IOR X C.E0 X' C.E0)
      (H : R.Honest ((C.Msg × M) × Wp) ((C.Msg × M) × Wp')) (A : Rels K X C.E0 ((C.Msg × M) × Wp))
      (B : Rels K X' C.E0 ((C.Msg × M) × Wp')) (rc : X → C.Rec) (rc' : X' → C.Rec)
      (ext : M → X × C.E0.Str → Tr R.shape → Wp' → Wp) (P : Nums K R),
    (∀ x y τ x', R.out x y τ = some x' → rc' x' = rc x) → (∀ y τ, R.imp y τ = y) →
    GoodAt R H A B (fun um => ext um.2) P →
    GoodAt R (idxH C H) (idxAt C rc A) (idxAt C rc' B) (idxExt C ext) P

/-- Over a signature. -/
def idxLift_goodB : Prop :=
  ∀ (E : Type) [Field E] (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (K X X' Wp Wp' : Type)
      (R : IOR X C.E0 X' C.E0) (H : R.Honest ((C.Msg × S.Msg) × Wp) ((C.Msg × S.Msg) × Wp'))
      (A : Rels K X C.E0 ((C.Msg × S.Msg) × Wp)) (B : Rels K X' C.E0 ((C.Msg × S.Msg) × Wp'))
      (rc : X → C.Rec) (rc' : X' → C.Rec)
      (ext : S.Msg → X × C.E0.Str → Tr R.shape → Wp' → Wp) (P : Nums K R),
    (∀ x y τ x', R.out x y τ = some x' → rc' x' = rc x) →
    (∀ y τ, R.imp y τ = y) → GoodAt R H A B (fun um => ext um.2) P →
    GoodB (R.keep S.Smp S.ext) (S.liftH (idxH C H)) (S.over (idxAt C rc A)) (S.over (idxAt C rc' B))
      (fun a τ w => (w.1, idxExt C ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) (P.keep S.Smp S.ext)

/-- The item "masked messages" goes along. -/
def idxLift_mm : Prop :=
  ∀ (E : Type) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (X X' Wp Wp' : Type) (R : IOR X C.E0 X' C.E0)
      (H : R.Honest ((C.Msg × S.Msg) × Wp) ((C.Msg × S.Msg) × Wp'))
      (D : MaskData R ((C.Msg × S.Msg) × Wp)),
    H.MM D → (S.liftH (idxH C H)).MM (idxMask C S D)

/-- Under the hypotheses below, a masked block on tuples is a masked block over the signature, with
the index decoded by the statement. -/
def idxLift_goodM : Prop :=
  ∀ (E : Type) [Field E] (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (K X X' Wp Wp' : Type) (R : IOR X C.E0 X' C.E0)
      (H : R.Honest ((C.Msg × S.Msg) × Wp) ((C.Msg × S.Msg) × Wp'))
      (A : Rels K X C.E0 ((C.Msg × S.Msg) × Wp)) (B : Rels K X' C.E0 ((C.Msg × S.Msg) × Wp'))
      (rc : X → C.Rec) (rc' : X' → C.Rec) (ext : S.Msg → X × C.E0.Str → Tr R.shape → Wp' → Wp)
      (P : Nums K R) (D : MaskData R ((C.Msg × S.Msg) × Wp)),
    (∀ x y τ x', R.out x y τ = some x' → rc' x' = rc x) → (∀ y τ, R.imp y τ = y) →
    GoodAt R H A B (fun um => ext um.2) P → H.MM D →
    (∀ x y w, A.rel x y w → D.Cl (D.pub x) (D.kc w)) →
    GoodM (R.keep S.Smp S.ext) (S.liftH (idxH C H)) (S.over (idxAt C rc A))
      (S.over (idxAt C rc' B)) (fun a τ w => (w.1, idxExt C ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2))
      (P.keep S.Smp S.ext) (idxMask C S D)

/-- The base joint of a predicate (Cb/Ld/LdWfClose.lean: `idxRels`) is a case, up to the empty
further witness. -/
def idxAt_pred : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (St M : Type) (P PR : St → C.Rec → C.Msg → M → Prop) (x : St × C.Rec)
    (y : C.E0.Str) (m : M) (p : C.PIdx),
    let A : Rels Unit (St × C.Rec) C.E0 ((C.Msg × M) × Unit) :=
      ⟨fun x _ w => P x.1 x.2 w.1.1 w.1.2, fun a w => PR a.1.1 a.1.2 w.1.1 w.1.2,
        fun _ => True, fun _ => ()⟩
    ((idxAt C Prod.snd A).rel x y (m, (p, ())) ↔ (idxRels C P PR).rel x y (m, p)) ∧
    ((idxAt C Prod.snd A).relR (x, y) (m, (p, ())) ↔ (idxRels C P PR).relR (x, y) (m, p)) ∧
    ((idxAt C Prod.snd A).on (x, y) ↔ (idxRels C P PR).on (x, y))

end Spec
end Cb
