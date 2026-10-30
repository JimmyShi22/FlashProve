-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDBody.lean: what zero knowledge asks of the closed body of a reference segment, beside
its hypotheses, in the form `LdRefD.ZkD`: places, readings, data maps, and memberships in a set of
pending blocks.
(not all kinds of clauses are named here: see `LdRefD.ZkD` below)

In standard terms: book-keeping for the honest prover's side of one body, the part of a segment of
a request's sub-protocol between its entry step and its closing (in the last segment: its exit
step): conditions (on which entries of earlier oracle messages its steps use and read; all the
clauses: `LdRefD.ZkD` below), and two statements that, under further hypotheses, derive a
hypothesis on honest provers from them. The whole request: Cb/Ld/LdLayD.lean.

Definitions and statements (`Cb.Spec.ldLayD_body`, `Cb.Spec.ldLayD_enter`); the proofs, assemblies,
are in Cb/Ld/LdLayDBodyProofs.lean.
For X' closed under "follows after every chain", Cb/Req1/LdReqRefLayWide.lean's `A.ZkW pp X'` brings
what zero knowledge asks of a body (`A.ZkAt`), beside its hypotheses, down to places, nested
readings, and clauses that still speak of more than data, among them two kinds:
  (1) memberships: for each masked block of the body (the front's lookup, the zerocheck's sumcheck,
    each further sumcheck, the digits' lookup, the batching of the tensor rows) the wide fact of
    its own masks lies in the set X' of facts that are fresh at the body's entry;
  (2) the body's two senders do not look at the own entries of the two late blocks (four clauses
    `LdSendD.NoLook`).
Here both are replaced. (not all kinds of clauses are named here: see `LdRefD.ZkW`,
Cb/Req1/LdReqRefLayWide.lean; `A.Ghost κ` and `F.OK pp` stay in `LdRefD.ZkD`)

Main names:
  `P.InD W X`, `A.LateD Q W F RdL X`: the records `P.In`, `A.LateW` with: (1) "the pending block
    (`LdPend`, Cb/Ld/LdMia.lean: what may be seen, the own entries, the type of masks, their values)
    lies in X" (fields `lk`, `s0`, `s`; `pendL`, `pendT`), X a set of pending blocks: a set of data;
    (2) "the sending is the standard one, for some pads' field, layout and data map, and the data
    map does not look" (fields `s1L`, `s3L`, `s1T`, `s3T`) (`LdSendD.StdBl`, Cb/Ld/LdLayDKit.lean;
    Q: what is asked of the layout: a parameter there; `StdBl` also asks: what is read back off the
    data with what is handed on is the further witness).
  `A.ZkD Q pp X`: `A.ZkW` with these two records.
  `Spec.ldLayD_body`: if every pending block of X has its wide fact in X', and X' is closed under
    "follows after every chain", then `A.ZkD Q pp X` → `A.ZkAt pp X'`.
  `Spec.ldLayD_enter`: the form in which it is used: the body stands behind a step without rounds
    with the honest map m; G: a set of facts before the step, closed under join, coarser reading
    and another type of masks; P: a set of pending blocks whose wide facts lie in G. Then `A.ZkD`
    at "the blocks γ that the step hands on from some β in P" (`LdPend.StepD m β γ`: the step's own
    condition) gives `A.ZkAt` at "the facts that the step hands on from some fact of G": the clause
    of `lay` and `layT` in `LdReqRefDS` (Cb/Req1/LdReqRefStd.lean), for a segment of the list and
    for the last segment alike.

Why: the step of the induction along the list of segments, and the last segment's clause, are this
one lemma, at X := the pending blocks that the entry step hands on from those pending before the
segment.

Limits: this file does not say that X holds anything: the matter of the sendings before the segment
and of what crosses a closing.
It does not say that the conditions can be met together: a guard's matter.
The clauses of `A.ZkD` are written so as to name no property of an honest prover, link or sender (by
reading; no program's result is reported here).
Nothing is wired: which sending holds which block's masks is not said here; each of the memberships
stands alone, and X may hold pairs of blocks from different sendings.
A write-up of ours (lean/CREDITS.md) has no entry steps, and no counterpart of
`LdPend.StepD`.
One wide reading W serves all blocks of a body.
The own masks of the two late blocks lie in messages that are open at the entry: a body's own
sendings lay no masks.
This file says nothing on a splitting.
`F.OK` still repeats clauses of the model's side (the lookup's conditions).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLayDKit
import Cb.Req1.LdReqRefLayWide

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- The pending blocks of the front's blocks are in X. -/
structure LdRefP.InD {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
    {F : LdRefF A} (P : LdRefP A F) (W : LdRefW A) (X : LdPend A.V.Fp.s0 → Prop) : Prop where
  lk : X ⟨W.Rd, W.Rr, plOwn P.atL, (A.V.Fp.dm F.RdK F.Cc).Mk,
      plVal P.atL fun M => (LdRefP.plL (F := F)).ve M⟩
  s0 : X ⟨W.Rd, W.Rr, plOwn P.at0, (A.V.Fp.Z.T.own F.Rd0).Mk, plVal P.at0 fun M => Sum.elim M.1 M.2⟩
  s  : ∀ i ≤ A.V.m,
    X ⟨W.Rd, W.Rr, plOwn (P.atS i), ((A.V.T i).own (F.RdS i)).Mk,
        plVal (P.atS i) fun M => Sum.elim M.1 M.2⟩

/-- The late blocks' conditions. -/
structure LdRefD.LateD {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
    (A : LdRefD E Kc I) (Q : LdLayQ E) (W : LdRefW A) (F : LdRefF A)
    (RdL : A.Xa.Q.T.Ent → Prop) (X : LdPend A.V.Fp.s0 → Prop) : Prop where
  /-- the digits' lookup -/
  maskL : A.Xa.A.MaskOK A.Xa.Dt
  rdL   : ∀ j, A.Xa.A.srAll A.Xa.Dt j → RdL j
  inL   : ∀ j, A.Xa.A.swAll j → ∃ n, A.up n = j
  wideL : ∀ n, RdL n → W.Rd2 n
  pendL : X ⟨W.Rd, W.Rr, A.ownL, (A.Xa.dm RdL).Mk, A.valL RdL⟩
  blL   : W.Blind F A.ownL
  s1L   : A.Xa.Q.D.d1.StdBl Q W.Rd W.Rr A.ownL
  s3L   : A.Xa.Q.D.d3.StdBl Q (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N A.ownL fun _ => False)
  /-- the batching -/
  ownT  : A.X.Own
  inT   : ∀ i, ∃ n, A.up n = A.wAt i
  wideT : ∀ n, A.Rdt n → W.Rd2 n
  pendT : X ⟨W.Rd, W.Rr, A.ownT, A.X.mask.Mk, A.valT⟩
  blT   : W.Blind F A.ownT
  s1T   : A.Xa.Q.D.d1.StdBl Q W.Rd W.Rr A.ownT
  s3T   : A.Xa.Q.D.d3.StdBl Q (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N A.ownT fun _ => False)
  /-- the digits' lookup reads entries of the wide reading, and no own mask of the batching -/
  apart : ∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 A.ownT n

/-- What zero knowledge asks of a closed body, beside its hypotheses, in this form; X: the blocks
that are pending at its entry. -/
def LdRefD.ZkD {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)
    (Q : LdLayQ E) (pp : ℕ) (X : LdPend A.V.Fp.s0 → Prop) : Prop :=
  Nonempty I.C.E0.Str ∧
  ∃ (W : LdRefW A) (F : LdRefF A) (P : LdRefP A F) (κ : A.Gh → Kc) (RdL : A.Xa.Q.T.Ent → Prop),
    A.Ghost κ ∧ F.OK pp ∧ P.OKL W ∧ P.OK0 W ∧ (∀ i ≤ A.V.m, P.OKS W i) ∧
    F.Nest ∧ P.InD W X ∧ A.LateD Q W F RdL X

/-- The body's clause, from `A.ZkD`: under the two hypotheses below, `A.ZkD Q pp X` gives
`A.ZkAt pp X'`. -/
def Spec.ldLayD_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (Q : LdLayQ E) (pp : ℕ)
      (X : LdPend A.V.Fp.s0 → Prop) (X' : MaskFact A.V.Fp.s0.J.W → Prop),
    (∀ γ, X γ → X' γ.fact) → A.V.Fp.s0.Closed X' → A.ZkD Q pp X → A.ZkAt pp X'

/-- The same behind an entry step. -/
def Spec.ldLayD_enter : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (Q : LdLayQ E) (pp : ℕ)
      (a : LdStage E Kc) (f : a.X → Option A.V.Fp.s0.X) (g₀ : ExtMap a.Ex A.V.Fp.s0.Ex)
      (m : a.X × a.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : a.X × a.Ex.Str → A.V.Fp.s0.W → a.W)
      (G : MaskFact a.J.W → Prop) (P : LdPend a → Prop),
    (∀ h, MaskFact.JCl G h → G h) → (∀ β, P β → G β.fact) →
    A.ZkD Q pp (fun γ => ∃ β, P β ∧ LdPend.StepD m β γ) →
    A.ZkAt pp fun h =>
      ∃ g, G g ∧ ∀ Y : MaskFact a.J.W → Prop, Y g → (LdMv.step a A.V.Fp.s0 f g₀ m back).After Y h

end Cb
