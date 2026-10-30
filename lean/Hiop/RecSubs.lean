-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecSubs.lean: this file states the hypotheses on the building blocks of the holographic
interactive oracle proof: two reductions (`IOR`), a test for linear constraints, and a test that two
oracles encode the same index.

Definitions only.


Main names:
  `SubsR`: the data of the four sub-protocols.
  `PreListR`: the parameter list of the two preambles; `LinListR` and `LinBListR`: of the IOPP for
    the constraint relation (the test for linear constraints; the claims are abstract here) at its
    two settings; `LinkListR`: of the link. Each list is in two parts: the item on knowledge
    soundness, a definition of its own (`PreKnowR`, `LinKnowR`, `LinBKnowR`, `LinkKnowR`), and a
    record of all other items. (So that completeness, formats and honest-verifier zero knowledge of
    the object are proved from hypotheses in which no extractor occurs.)

Of these lists:
  The record stands in every explicit part, by type: weights-formedness runs on rec; a request on
    (x, rec); the link on (rec, rec'); the constraint relation on (claims, rec). A preamble hands
    the record on (`passes`).
  Knowledge soundness of a preamble is "on the statements named, into the collision-free statements
    of the constraint relation" (Ior/KnowColl.lean: `KnowInto`): an output with a collision counts
    as a win of the prover and is counted in the preamble's errors; the item names no round. (Where
    "into" is proved by `Spec.knowInto_of_badFam`, in that file, a collision of an oracle that the
    preamble sends is an event of one of its rounds and is counted in that round's error.)
  Extractors go backwards and may read the statement and the whole transcript (Ior/KnowCollGood.lean
    says why); no extractor produces a prover encoded index: the relaxed relations hold none. For
    weights-formedness and the link there is nothing to extract.
  The IOPP at one instance has one list of errors, on all collision-free statements.

  The IOPP at N instances is asked for each record, with that record in all slots, on collision-free
    statements whose encoded index decodes with the record. (The weaker demand: it is all that a
    session needs.)
  The honest prover hands its prover encoded index on (`hands`); decoders here do not
    return the encoding randomness.

  Of the oracles that a preamble leaves nothing is asked (they may depend on verifier messages) but
    what other items say of them, among them `srcAux`, `isLocal`, of honest runs `acc`, and
    `PreKnowR` through `S.cond` and `S.RlinR`; the encoded index is copied.
  The private input of the shared part of the IOPP's honest prover is the prover encoded index with
    its record.
  The other items: completeness, probabilities of withheld sets, exact zero knowledge with
    budgets of further reads, numbers of positions read in the encoded index, locality, point
    oracles. The simulators are given the record as part of the explicit instance.

Limits: (1) The IOPP's extractor is fixed as "DECODE THE STATEMENT" (LinKnowR, LinBKnowR), although
on paper no extractor of an IOP decodes from errors. In content no loss: the relaxed constraint
relation determines its witness, so any extractor may be replaced by the decoder of the statement
(Ior/KnowColl.lean: `Spec.know_of_det`; Ior/KnowWide.lean: `Spec.sndBKT_of_det`, with
`Spec.sndBKT_conseq` for the two conditions in `LinBKnowR`); running times, and so the item "total
extraction time", are not modelled.
(2) `cellsOf` may read every verifier message. That, on collision-free statements, the cells
extracted are the decoding with their samples of the oracles of cells (what the witness extractor of
a compiled argument can compute) is not an item here.
This file says nothing on whether the lists can be met; nothing on running times, so no time of
extraction.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecConf
import Hiop.ListNums
import Ior.KnowColl
import Ior.KnowWideOnline

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

/-- The four sub-protocols: the data. -/
structure SubsR (C : ConfigurationWithOutOfDomainSample) where
  /-- what the two preambles leave -/
  off : C.Left
  on  : C.Left
  /-- the number of slots: a batch holds at most this many instances -/
  N   : ℕ
  /-- the preamble of weights-formedness; the IOPP at one instance; the link; the preamble of a
  request; the IOPP at N instances. The record stands in every explicit part -/
  wf     : IOR C.Rec C.E0 (off.Xl × C.Rec) off.El
  linOff : IOR (off.Xl × C.Rec) off.El Unit extNone
  link   : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone
  req    : IOR (C.X × C.Rec) C.E0 (on.Xl × C.Rec) on.El
  linOn  : BIOP (on.Xl × C.Rec) on.El
  /-- the extractor of the preamble of a request, backwards: from the message of the oracles left to
  the cells. It may read the statement and the whole transcript of the preamble: oracles, their
  samples (seeds are verifier messages, answers plain parts), every other verifier message -/
  cellsOf : (C.X × C.Rec) × C.E0.Str → Tr req.shape → on.AMsg → C.Cells
  hWf     : wf.Honest C.PIdx (C.PIdx × off.WAux)
  hLinOff : linOff.Honest (C.PIdx × off.WAux) Unit
  hLink   : link.Honest (C.PIdx × C.PIdx) Unit
  hReq    : req.Honest (C.PIdx × C.Cells) (C.PIdx × on.WAux)
  hLinOn  : linOn.Honest C.PIdx on.WAux
  /-- fixed values, where an oracle does not decode -/
  dOff : off.AMsg
  dOn  : on.AMsg

variable {C : ConfigurationWithOutOfDomainSample}

/-- Round-by-round knowledge soundness of a preamble F: relaxation RiR on the statements with `on`,
to the relaxed constraint relation of S, into its collision-free statements: an output with a
collision counts as a win of the prover, and is counted in the errors. `ext` is the extractor. -/
def PreKnowR {Xi Wr : Type} (S : C.Left) (F : IOR Xi C.E0 (S.Xl × C.Rec) S.El)
    (on : Xi × C.E0.Str → Prop) (RiR : Xi × C.E0.Str → Wr → Prop)
    (ext : Xi × C.E0.Str → Tr F.shape → S.AMsg → Wr) (ε : Err F.shape) : Prop :=
  F.red.KnowInto on S.cond RiR S.RlinR ext ε

/-- The parameter list of a preamble F from the relation Ri to the constraint relation of S: all
items but knowledge soundness. `rc` reads the record off the explicit part; `px` the prover encoded
index off the honest witness. -/
structure PreListR {Xi Wi : Type} (S : C.Left) (F : IOR Xi C.E0 (S.Xl × C.Rec) S.El)
    (H : F.Honest Wi (C.PIdx × S.WAux)) (rc : Xi → C.Rec) (px : Wi → C.PIdx)
    (Ri : Xi → C.E0.Str → Wi → Prop) (P : PreNums F) : Prop where
  point   : Nonempty F.shape.IsPoint
  isLocal : F.IsLocal
  acc     : H.Acc Ri S.Rlin
  prBad   : prRho H.Bad ≤ P.pBad
  prHid   : ∀ x y w, Ri x y w → prRho (H.Hid w x) ≤ P.pHid
  exact   : H.Exact Ri P.bud
  noReads : ∀ ρ, F.extReads ρ = ∅
  noTie   : ∀ ρ p, F.tie ρ p = ∅
  /-- the record is handed on -/
  passes  : ∀ x y τ b, F.out x y τ = some b → b.2 = rc x
  /-- the honest prover hands its prover encoded index on: on inputs in the relation, where the
  verifier's randomness is not withheld -/
  hands   : ∀ x y w c ρ, Ri x y w → ρ ∉ H.withheld w x → ((H.strat w x c).run ρ).2.2.1 = px w
  /-- the new implicit instance: the encoded index, unchanged, and oracles of which nothing is asked
  here but `srcAux` (what other items say of them: the head of this file) -/
  copy    : ∀ y τ, (F.imp y τ).1 = y
  srcIdx  : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅
  srcAux  : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅

/-- The numbers of an IOPP at one instance: one list of errors, for all collision-free statements.
-/
structure LinNumsR (s : Shape) where
  err    : Err s
  pBad   : ℝ≥0∞
  q      : ℕ
  bud    : Rho s → Finset (OPos s) → Prop

/-- Round-by-round knowledge soundness of the IOPP for the constraint relation, one instance: on all
collision-free statements, whether the encoded index decodes or not. The extractor decodes the
statement. -/
def LinKnowR (S : C.Left) (Q : IOR (S.Xl × C.Rec) S.El Unit extNone)
    (d0 : S.AMsg) (ε : Err Q.shape) : Prop :=
  Q.red.Know S.cond S.RlinR (fun _ _ => True) (fun a _ (_ : Unit) => S.decA d0 a.1.1 a.2.2) ε

open Classical in
/-- The parameter list of the IOPP for the constraint relation, one instance: all items but
knowledge soundness. -/
structure LinListR (S : C.Left) (Q : IOR (S.Xl × C.Rec) S.El Unit extNone)
    (H : Q.Honest (C.PIdx × S.WAux) Unit) (P : LinNumsR Q.shape) : Prop where
  point   : Nonempty Q.shape.IsPoint
  isLocal : Q.IsLocal
  acc     : H.Acc S.Rlin IOR.triv
  noHid   : ∀ w x, H.Hid w x = ∅
  prBad   : prRho H.Bad ≤ P.pBad
  exact   : H.Exact S.Rlin P.bud
  bud0    : ∀ ρ, P.bud ρ ∅
  tied    : Q.Tied
  idxReads : ∀ ρ, ((Q.extReads ρ).filter fun p => p.isLeft).card ≤ P.q

/-- Round-by-round knowledge soundness of the IOPP for the constraint relation, at most N instances
that share the encoded index and its record: for each record, with that record in all slots, on the
collision-free statements whose encoded index decodes with the record (to a message; it need not
hold an index). One-instance errors in the rounds of an instance, joint errors in the shared rounds;
one list for all records. -/
def LinBKnowR (S : C.Left) (Q : BIOP (S.Xl × C.Rec) S.El) (N : ℕ)
    (d0 : S.AMsg) (ε : Err Q.ior.shape) : Prop :=
  ∀ rec : C.Rec, (Q.comapX fun xl : S.Xl => (xl, rec)).curry.SndBKT N id none
    (fun a y0 w =>
      (C.dcd y0 rec).isSome → S.cond ((a.1, rec), (y0, a.2)) → S.RlinR ((a.1, rec), (y0, a.2)) w)
    (fun a _ _ => S.decA d0 a.1 a.2) ε

open Classical in
/-- The parameter list of the IOPP for the constraint relation, at most N instances: all items but
knowledge soundness. -/
structure LinBListR (S : C.Left) (Q : BIOP (S.Xl × C.Rec) S.El) (H : Q.Honest C.PIdx S.WAux)
    (N : ℕ) (P : LinBNums Q.ior.shape N) : Prop where
  point    : Nonempty Q.ior.shape.IsPoint
  isLocal  : Q.ior.IsLocal
  coherent : Q.ann.Coherent
  acc      : H.Acc S.Rlin
  prBad    : prRho H.withheld ≤ P.pBad
  exact    : H.Exact N S.Rlin P.bud
  bud0     : ∀ J ρs, P.bud J ρs fun _ => ∅
  tied     : Q.ior.Tied
  idxShared : ∀ ρ ρ', Rho.sh Q.ann ρ = Rho.sh Q.ann ρ' →
    (Q.ior.extReads ρ).filter (fun p => p.isLeft) = (Q.ior.extReads ρ').filter (fun p => p.isLeft)
  idxReads  : ∀ ρ, ((Q.ior.extReads ρ).filter fun p => p.isLeft).card ≤ P.q

/-- Round-by-round knowledge soundness of the link: on the statements whose first encoded index
decodes to an index and whose further one has no collision. Nothing is extracted. -/
def LinkKnowR (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone) (ε : Err Q.shape) : Prop :=
  Q.red.Know C.onEq C.ReqR (fun _ _ => True) (fun _ _ (_ : Unit) => ()) ε

open Classical in
/-- The parameter list of the link: all items but knowledge soundness. -/
structure LinkListR (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone)
    (H : Q.Honest (C.PIdx × C.PIdx) Unit) (P : LinkNums Q.shape) : Prop where
  point   : Nonempty Q.shape.IsPoint
  isLocal : Q.IsLocal
  acc     : H.Acc C.Req IOR.triv
  noHid   : ∀ w x, H.Hid w x = ∅
  prBad   : prRho H.Bad ≤ P.pBad
  exact   : H.Exact C.Req P.bud
  bud0    : ∀ ρ, P.bud ρ ∅
  tied    : Q.Tied
  cntPar  : ∀ ρ, ((Q.extReads ρ).filter fun p => p.isLeft).card ≤ P.qpar
  cntCh   : ∀ ρ, ((Q.extReads ρ).filter fun p => p.isRight).card ≤ P.qch

end Hiop
