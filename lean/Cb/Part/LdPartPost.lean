-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPost.lean: the front's last step, for arbitrary parameters: from "what is open after
the last sumcheck" to the first stage of the body ("packing, and claims on the virtual cells",
`readIn`, Cb/Ld/LdRead.lean): the four clauses of a step that only maps the explicit part.

In standard terms: a step of a chain of interactive reductions in which no message is sent. The
verifier only maps its explicit statement, and the claims that the front's sumchecks have left are
regrouped as the input claims of the next sub-protocol, the read stage (Cb/Ld/LdRead.lean).
Definitions and statements (`Cb.Spec`); the proofs are in Cb/Part/LdPartPostProofs.lean.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A segment's front ends in a chain of sumchecks and a last
step `gz`, a map of the explicit part; `LdStepOK` (Cb/Req1/LdSegFrontTab.lean) has the four clauses
that are asked of such a step between two joints (`Rels`, Ior/Chain.lean: an exact relation `rel`, a
relaxed relation `relR`, a condition `on`, a core `core`).
In this file "the body" means the part of a segment's term between the
front and the last list; that term itself begins with the front.
Behind the last sumcheck of a segment's front three kinds of claims are open (by inspection, in
this protocol's technical report (lean/CREDITS.md) as here): (i) rows on the values of maps that are
affine in cells; (ii) rows on entries of messages: each sumcheck's row on its hiding polynomial's
coefficients, the lookup's
rows; (iii) rows on the values of maps which the index enters linearly: the segment's tensor rows.
The body begins with "read": its claims (`ReadCl`) take (i), and, with no read and no constant,
(ii). (iii) rides on, to the tensor list behind the body.

Main names:
  `LdPartRw E St J`, `Rw.toCl p`: rows on names; the rows as claims of the read stage: constant 0,
    no read, mask form co, target tg.
  `LdPartSrt p E St Jb T` (below: Q): the sorting, as data, over the states St after the step: K:
    the claims on cell atoms (Cb/Part/LdPartCells.lean); Rw: the rows on names; Tn s t: what else
    is open, a predicate on the state and on the tuple t = (message of the index, messages).
  `Q.A₀t R`: what rides behind the claims, on tuples: Tn, then the riding relation R (in this
    order).

  `LdPartSeam R R' Pk`: the riding relation may change at the step, from R (through the front) to
    R' (behind the read stage): forth: R's exact relation gives R''s; back: where the messages are
    packed (Pk), R''s relaxed relation gives R's; R''s condition follows from R's; one core.
  `Spec.ldPartPost`: `LdPartSrc A f R Opn`; `LdPartSeam R R'` (packed below 2 D); f keeps the
    index's record; each claim's reading is a reading, the reads are tied
    (Cb/Part/LdPartCells.lean); `Q.Law Opn c nm` (Opn: "what is open"); R's exact relation gives the
    packing (R.rel s y w → PackBy B ϱ (c.yz (R.core w)) (c.pk w.1.2)) ⇒ `LdStepOK` S (A, the index
    decoded by the statement) (Q.Az .. R') f.


Why the seam: a front's riding relation reads all rows of the body's matrix and holds "packed" in
its relaxed part; behind the rows what rides has to be a relation on the kept messages alone.
Why the packing: forth: the exact relation of `readIn` asks it: it comes from R. Back: `readIn`'s
relaxed relation gives "packed below 2 D": it is handed to the seam's clause "back", which may need
it to give R's relaxed relation.

Limits:
This file does not say that a front built from a partition has a sorting with its law.
It does not say that Tn is a family of tensor rows. It does not
say that the names of the entries which the rows of kind (ii) read lie in messages of the segment's
group. The closing will ask it of these claims' mask forms. This file says nothing on
zero knowledge, and nothing on places apart.
This file gives no instance that meets the hypotheses of `Spec.ldPartPost`, `Spec.ldPartPost_plus`,
`Spec.ldPartPost_rows`, so as far as this file shows these theorems may hold of nothing.
A difference of filing (by inspection, on an earlier text of these statements, in which the joint
before the step was the chain's; towards otherwise: the sorting is the report's). The report carries
the rows of kind (ii) beside the claims, through reads and range check, to the
family that the closing batches; here they are claims without reads. No message, round, error or
mask changes: a claim without a read adds nothing to the list of reads, the sender of the reads
looks at the weight vectors and the cells, not at the claims, and behind the body each claim is one
row of the family that the body leaves.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartCells
import Cb.Req2.LdSeg2Step
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Blocks Finset Cb.Rng Cb.RngPk

/-- two families of claims side by side -/
def ReadCl.plus {p : RngPar} {E St J : Type} (cl cl' : ReadCl p E St J) : ReadCl p E St J where
  Jc := cl.Jc ⊕ cl'.Jc
  k0 := fun st => Sum.elim (cl.k0 st) (cl'.k0 st)
  cw := fun st => Sum.elim (cl.cw st) (cl'.cw st)
  ms := fun st => Sum.elim (cl.ms st) (cl'.ms st)
  v  := fun st => Sum.elim (cl.v st) (cl'.v st)

/-- Rows on names. -/
structure LdPartRw (E St J : Type) where
  Jr : Type
  co : St → Jr → J → E
  tg : St → Jr → E

namespace LdPartRw
variable {E St J : Type} [Field E] (Rw : LdPartRw E St J)

def Says [Fintype J] (st : St) (e : J → E) : Prop := ∀ r, ∑ n, Rw.co st r n * e n = Rw.tg st r

/-- the rows as claims of the read stage -/
def toCl (p : RngPar) : ReadCl p E St J := ⟨Rw.Jr, fun _ _ => 0, fun _ _ _ _ => 0, Rw.co, Rw.tg⟩

end LdPartRw

/-- The sorting of what is open after the last sumcheck: the data. -/
structure LdPartSrt (p : RngPar) (E St Jb T : Type) where
  K  : LdPartCl p E St Jb
  Rw : LdPartRw E St Jb
  Tn : St → T → Prop

namespace LdPartSrt
variable {p : RngPar} {E St Jb : Type} [Field E] [Fintype Jb]
  {U M : Type} (Q : LdPartSrt p E St Jb (U × M))

/-- the body's claims -/
def cl (nm : LdPartNm p) : ReadCl p E St Jb := (Q.K.toCl nm).plus (Q.Rw.toCl p)

/-- The one law. -/
def Law {Kc : Type} (Opn : St → U × M → Prop) (c : CellRd p E St M Kc Jb) (nm : LdPartNm p) :
    Prop :=
  ∀ (s : St) (t : U × M),
    Opn s t ↔
    Q.K.Says s (nm.matsE E (cells p.P (2 * p.D) p.rdx (c.pk t.2))) (c.ent t.2) ∧
    Q.Rw.Says s (c.ent t.2) ∧
    Q.Tn s t

omit [Field E] [Fintype Jb] in
/-- what rides behind the claims, on tuples: the rows first -/
def A₀t {Kc Wp : Type} {Ex : ExtSpec} (R : Rels Kc St Ex ((U × M) × Wp)) :
    Rels Kc St Ex ((U × M) × Wp) :=
  ⟨fun s y w => Q.Tn s w.1 ∧ R.rel s y w, fun a w => Q.Tn a.1 w.1 ∧ R.relR a w, R.on, R.core⟩

end LdPartSrt

/-- The body's first stage. -/
def LdPartSrt.Az {p : RngPar} {E St Jb : Type} [Field E] [Fintype Jb] (C : ConfigurationWithOutOfDomainSample)
    {S : Sig E} (Q : LdPartSrt p E St Jb (C.Msg × S.Msg)) {Kc Wp : Type} (rc : St → C.Rec)
    (c : CellRd p E St S.Msg Kc Jb) (nm : LdPartNm p) (R : Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)) :
    Rels Kc St C.E0 (S.Msg × (C.PIdx × Wp)) :=
  readIn p c (Q.cl nm) (idxAt C rc (Q.A₀t R))

/-- What is asked of the joint before the step. -/
structure LdPartSrc {Kc O St T Wp : Type} {Ex : ExtSpec} (A : Rels Kc O Ex (T × Wp)) (f : O → St)
    (R : Rels Kc St Ex (T × Wp)) (Opn : St → T → Prop) : Prop where
  rel  : ∀ o y w, A.rel o y w ↔ R.rel (f o) y w ∧ Opn (f o) w.1
  relR : ∀ o y w, A.relR (o, y) w ↔ R.relR (f o, y) w ∧ Opn (f o) w.1
  on   : ∀ o y, A.on (o, y) → R.on (f o, y)
  core : ∀ w, R.core w = A.core w

/-- The riding relation may change at the step. -/
structure LdPartSeam {Kc St T Wp : Type} {Ex : ExtSpec}
    (R R' : Rels Kc St Ex (T × Wp)) (Pk : T → Prop) : Prop where
  fw   : ∀ s y w, R.rel s y w → R'.rel s y w
  bw   : ∀ a w, Pk w.1 → R'.relR a w → R.relR a w
  on   : ∀ a, R.on a → R'.on a
  core : ∀ w, R'.core w = R.core w

theorem LdPartSeam.refl {Kc St T Wp : Type} {Ex : ExtSpec}
    (R : Rels Kc St Ex (T × Wp)) (Pk : T → Prop) : LdPartSeam R R Pk :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, fun _ h => h, fun _ => rfl⟩

namespace Spec

def ldPartPost_plus : Prop :=
  ∀ (p : RngPar) (E St J : Type) [Field E] [Fintype J] (cl cl' : ReadCl p E St J)
      (W : St → p.Rd → p.Row → E) (st : St) (Y : p.Cells) (e : J → E),
    (cl.plus cl').OnCells W st Y e ↔ cl.OnCells W st Y e ∧ cl'.OnCells W st Y e

def ldPartPost_rows : Prop :=
  ∀ (p : RngPar) (E St J : Type) [Field E] [Fintype J] (Rw : LdPartRw E St J)
      (W : St → p.Rd → p.Row → E) (st : St) (Y : p.Cells) (e : J → E),
    (Rw.toCl p).OnCells W st Y e ↔ Rw.Says st e

/-- The front's last step. -/
def ldPartPost : Prop :=
  ∀ (E : Type) [Field E] (p : RngPar) (O St Jb : Type) [Fintype Jb] (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (Q : LdPartSrt p E St Jb (C.Msg × S.Msg)) (Kc Wp : Type)
      (A : Rels Kc O C.E0 ((C.Msg × S.Msg) × Wp)) (f : O → St)
      (R R' : Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)) (Opn : St → C.Msg × S.Msg → Prop)
      (rcO : O → C.Rec) (rc : St → C.Rec) (c : CellRd p E St S.Msg Kc Jb) (nm : LdPartNm p),
    LdPartSrc A f R Opn → LdPartSeam R R' (fun t => Packed p.P (2 * p.D) p.rdx (c.pk t.2)) →
    (∀ o, rc (f o) = rcO o) → (∀ j, (Q.K.rg j).Of nm.R nm.C (Q.K.v j) (Q.K.f j)) → Q.K.Ties nm c.W →
    Q.Law Opn c nm → (∀ s y w, R.rel s y w → PackBy p.B p.rdx (c.yz (R.core w)) (c.pk w.1.2)) →
    LdStepOK S (idxAt C rcO A) (Q.Az C rc c nm R') f

end Spec
end Cb
