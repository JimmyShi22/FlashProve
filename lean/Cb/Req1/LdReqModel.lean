-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqModel.lean: what a model has to supply and to prove for the reference request; what is
the protocol's own.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs. The layers, from the inside: Fp
(`LdPreD`, Cb/Req1/LdSegRefLkpPre.lean), the lookup of a front; V (`LdFrontRef`,
Cb/Req1/LdSegFrontRef.lean), a front; A (`LdRefD`, Cb/Req1/LdSegRefAll.lean), a body; S, L, T
(`LdRefS`, `LdRefL`, `LdRefT`, Cb/Req1/LdReqRef.lean), a segment, the list of segments, the last
segment of the reference request `ldReqRef`; D is `A.Xa.Q.D` (`LdRrD`, Cb/Req1/LdSegRefRng.lean), K
a `LdRefC1` (Cb/Req1/LdSegRefAll.lean), R the end (`LdORE`, Cb/Obj/LdObjectReqEnd.lean). The
hypotheses of the reference request are `LdReq.Hyp` (Cb/Req1/LdReq.lean).
Cb/Req1/LdReqRef.lean reduces the hypotheses of the reference request (all of the bundle but zero
knowledge) to bundles "OK" of its parts. Each of these bundles mixes two kinds of clauses. Here they
are sorted, layer by layer, and nothing is added or dropped (`Spec.ldReqModel_pre` to
`Spec.ldReqModel_tail`: OK if and only if Model and Proto).

The model's side ("Model"). A model (the computation that a request claims) supplies, in the data of
the parts:
  for each segment: the key maps, tables and tags of its lookup (Fp.P), the clause on its
  multiplicities (Fp.Mu); the claims that the first block joins and its summand (Fp.Z: for
  identities, a zerocheck); the further sumchecks for maps given by inner sums (T i); what waits
  beside each block (Fp.Rr, Fp.R0z, A0 i);
  the maps of the explicit part between the blocks (Fp.e, g0, g i, gz); how cells are read and which
  claims on cell maps are left (D.c, D.cl); the tensor rows on the index (g, pt, mf, g₀); what is
  claimed beside the rows at the end (St₁, fz, Az / A₀c); the entry step of each segment, the exit
  step of the last
and proves:
  M1 The steps between segments: what one segment's closing leaves says what the next segment takes
      (`IOR.StepT` of the entry steps; of the last segment's exit step).
      In this protocol's technical report (lean/CREDITS.md) there are no such steps: the relation
      behind segment s is defined to hold the next segment's conditions on the cell messages just
      sent and all later segments'
      conditions on cells that are a further part of the witness until sent; consecutive blocks have
      equal relations. What a model supplies and proves there is one definition (a partition of the
      conditions into segments: cells, the earlier matrices still read, summands, key maps with
      tables, over maps of three kinds, of bounded degree, with public coefficients that the
      verifier evaluates) and one equivalence (the constraints hold if and only if for all segments
      the zero and lookup predicates hold). That the steps are free moves with hypotheses here is
      this library's form; Cb/Req1/LdSegNext.lean goes towards the report's. These steps are
      free moves (four free maps, one of them on oracles): renaming or dropping a kept message,
      moving the index among the further oracles happens here; sound, since the step's way back is
      asked, but more than "the model's matter".
      The first entry step holds the arithmetization proper: from the request's relation on
      (instance, cells) at the index that the decoded message holds to the first segment's claims,
      and back; that a message which holds an index agrees with that index's body on the layout has
      to be proved inside it.
      The exit step must turn all that rides into rows of the final family or pending tensor rows:
      nothing rides past the end.
  M2 The steps between blocks: the claims that one block leaves are the claims that the next one
      takes: four clauses each (after the lookup; after each sumcheck; into "packing, and claims on
      the virtual cells").
      They also route protocol rows: the rows that the front's lookup files (on its bits and own
      masks) have no slot of their own among the rows that the closing batches. They are meant to
      leave the front as further claims of D.cl with no coefficient on a read, so that they close
      with the segment (so at the toy: Cb/GlVal/GlJ3SegFrontToySeam.lean). The records do not force
      this: rows that ride on instead force their messages to be kept at every later closing.
      The same for the rows that the closing before left (the folded claim on the cut of the new
      message, the old samples' rows, the symbols read at the locations: claims on the entries of
      the messages that the one sending sent, with public data of that closing): the body's rows
      have no slot of their own for them; they are meant to ride through the front and to leave it
      as further claims of D.cl with no coefficient on a read, so that they join this segment's
      batch (the group of a segment holds what the switch before sent).
  M3 The sum claim of the first block is the combination of its claims (`Link`), and the new state
      gives the old one back (`Back`): for a zerocheck both hold by Cb/Ld/LdZero*.lean.
  M4 The degrees of each summand (`DegX`, `DegY`).
  M5 The honest prover's multiplicities are what the lookup's exact clause asks (`muFrom`). In the
      technical report this is the protocol's: the construction fixes the predicate on the
      multiplicities, a function of the keys alone satisfies it if all keys lie in the table, and
      the sending puts that vector into the cell messages; a model supplies keys and tables only.
      That it stands on the model's side here is this library's form (the clause is a datum of the
      front, Fp.Mu).
  M6 What else is claimed is carried: past the rows (`Rest`), past the tensor batching (`Ends`).
What is shown of M1. Between segments: if what the closing carries is a predicate Cn on (kept
messages, the next segment's data still in the further witness, what is handed on) and the one
sending gives these data back, the relation behind the segment is "the rows on the new messages,
beside Cn at the data read off the messages just sent": an identity, no step
(Cb/Req1/LdSegNext.lean; the step into the next body's first claim keeps a hypothesis there:
`Spec.ldSegNext_step`). This file gives no instance that meets its hypotheses, so as far as this
file shows its theorems may hold of nothing. No model of a computation is given.

The protocol's side ("Proto"): codes, samples, evaders, senders, places, numbers: tags and sizes;
injective names, named places; admissible numbers against the characteristic; the multiplicities'
clause is one that the lookup accepts (`muOK`); the variables of each sumcheck (`VarsOK`, `ValInj`);
the evaders' laws; the range check's parameters; the hypotheses of the sendings; the laws of the
places (`Places`, `Bits`, `Reads`); named places lie in the group; bridge-to-fold.

Main names:
  `Fp.Model`, `Fp.Proto p`; `V.Model`, `V.Proto p`; `A.Model`, `A.Proto pp`; `S.Model`,
    `S.Proto pp`; `L.Model`, `L.Proto pp`; `T.Model`, `T.A.Proto pp`. (T has no closing: so the
    protocol's side of the last segment is its body's, `T.A.Proto`.)
  `LdReqModel L T`: the model's side of a reference request: `L.Model` and `T.Model`.
  `LdReqProto pp R first more L T`: the protocol's side: the first sending's hypotheses; `more.Hyp`;
    `L.Proto pp`; `T.A.Proto pp`; 2 ≤ degree, the evader's law and `R.Tie` of the final batching.
  `Spec.ldReqModel_pre`, `Spec.ldReqModel_front`, `Spec.ldReqModel_body`, `Spec.ldReqModel_seg`,
    `Spec.ldReqModel_tail`: OK ↔ Model ∧ Proto, layer by layer.
  `Spec.ldReqModel_list`: `L.OK pp ↔ L.Model ∧ L.Proto pp`.
  `Spec.ldReqModel_hyp`: for pp the characteristic of E (`[CharP E pp]`) and `hm`: `more` has
    sendings and steps alone:
    `LdReqModel L T → LdReqProto pp R first more L T → (ldReqRef R first a₁ more hm b L T).Hyp`.

Limits:
A warning to whoever supplies a model. The conditions on own masks (zero knowledge: `OwnOur`) are
asked at all states of the state types that the model supplies. They can be met only if states hold
earlier claims as they stand and forms are readers of them, laid at fixed places; a state that files
an incoming form as free data cannot meet them.
The sorting of the records' clauses is this library's own; what the model's side is, the technical
report fixes (see under M1). The encoded index (configuration, rows, column variables, matrix)
is one parameter I of all segments of a request, and it is the request's (`R.ix`); each body still
has its own reader of the record (`A.rc`), tied through the formats' clauses. Zero knowledge,
formats and error bounds ask nothing of a model but through the data that it supplies (which entries
its maps read; the readers of the record; the degrees): not sorted here. This file does not say that
a model exists: none is given.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRef

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

/-! ## The lookup and the step after it -/

namespace LdPreD
variable {E Kc : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp : Type} (F : LdPreD E Kc S E₀ Wp)

structure Model : Prop where
  muFrom : ∀ (x : F.St × E) y w, F.Rr.rel x.1 y w → F.PS.outC x w.1 → F.Mu x (F.msg w.1)
  lastFw : ∀ x y w, F.jT.rel x y w → (F.Z.relsIn F.R0z F.msg0).rel (F.e x) y w
  lastOn : ∀ x y, F.jT.on (x, y) → (F.Z.relsIn F.R0z F.msg0).on (F.e x, y)
  lastCo : ∀ w, (F.Z.relsIn F.R0z F.msg0).core w = F.jT.core w
  lastBw : ∀ x y w,
    F.jT.on (x, y) → (F.Z.relsIn F.R0z F.msg0).relR (F.e x, y) w → F.jT.relR (x, y) w

structure Proto (p : ℕ) : Prop where
  tags   : TagInj F.P.g F.P.tag
  numV   : F.P.g + F.P.v = F.A0.v' + 1
  numD   : F.P.g + F.P.d = F.A0.d
  inj    : Function.Injective F.ι
  places : F.A.PlacesIn fun j => j ∈ Set.range F.ι
  adm    : F.A.H.lkb.Adm p
  muOK   : F.A.H.MuOn F.Mu

end LdPreD

/-! ## The front -/

namespace LdFrontRef
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (V : LdFrontRef E Kc z)

structure Model : Prop where
  pre   : V.Fp.Model
  link  : V.Fp.Z.Link
  back  : V.Fp.Z.Back
  degX0 : V.Fp.Z.T.DegX
  degY0 : V.Fp.Z.T.DegY
  degX  : ∀ i ≤ V.m, (V.T i).DegX
  degY  : ∀ i ≤ V.m, (V.T i).DegY
  step0 : LdStepOK z.S V.tab.t0.A (V.tab.s 0).A V.g0
  step  : ∀ i < V.m, LdStepOK z.S (V.tab.t i).A (V.tab.s (i + 1)).A (V.g i)
  post  : LdStepOK z.S (V.tab.t V.m).A z.A V.gz

structure Proto (p : ℕ) : Prop where
  pre   : V.Fp.Proto p
  ev    : V.Fp.Z.ev.OK
  vars0 : V.Fp.Z.T.VarsOK
  inj0  : V.Fp.Z.T.ValInj
  vars  : ∀ i ≤ V.m, (V.T i).VarsOK
  inj   : ∀ i ≤ V.m, (V.T i).ValInj

end LdFrontRef

/-! ## The body -/

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

structure Model : Prop where
  front : A.V.Model
  rest  : A.Gr.Rest A.Y.St₀ A.Y.g₀ A.Y.Ar

structure Proto (pp : ℕ) : Prop where
  front  : A.V.Proto pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : A.Xa.Q.D.d1.Hyp
  send3  : A.Xa.Q.D.d3.Hyp
  tabQ   : A.Xa.Q.D.p.q ≤ 2 ^ A.Xa.Q.d
  tabH   : A.Xa.Q.D.p.H ≤ 2 ^ A.Xa.Q.d
  keys   : A.Xa.Q.K ≤ 2 ^ A.Xa.Q.v
  tags   : A.Xa.Q.tag 0 ≠ A.Xa.Q.tag 1
  inj    : Function.Injective A.Xa.ι
  named  : A.Xa.A.PlacesIn (fun j => j ∈ Set.range A.Xa.ι)
  adm    : A.Xa.A.H.lkb.Adm pp
  bits   : A.Xa.Bits
  reads  : A.Gr.Reads
  deg    : 2 ≤ A.nt
  ev     : A.Zt.OK

end LdRefD

/-! ## A segment, the list, the last segment -/

namespace LdRefS
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
  {a : LdStage E Kc} (S : LdRefS E Kc I a)

structure Model : Prop where
  entry : S.entry.Hyp
  body  : S.A.Model
  ends  : S.A.X.Ends S.K.St₁ S.K.fz S.K.Az

structure Proto (pp : ℕ) : Prop where
  body  : S.A.Proto pp
  ev    : S.K.Z.OK
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : S.K.R.c1.fold.Hyp S.l
  snd   : S.Qc.snd.Hyp

end LdRefS

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

def Model : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Model ∧ S.Model

def Proto (pp : ℕ) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Proto pp ∧ S.Proto pp

end LdRefL

namespace LdRefT
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b)

structure Model : Prop where
  entry : T.entry.Hyp
  body  : T.A.Model
  ends  : T.A.X.Ends T.St₁ T.fz T.Az
  exit  : T.exit.Hyp

end LdRefT

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The model's side of a reference request. -/
structure LdReqModel {R : LdORE F E Kc} {a₁ b : LdStage E Kc}
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : Prop where
  segs : L.Model
  tail : T.Model

/-- The protocol's side. -/
structure LdReqProto (pp : ℕ) (R : LdORE F E Kc) {a a₁ b : LdStage E Kc} (first : LdSendD a)
    (more : LdProg first.tgt a₁) (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : Prop where
  hFirst : first.Hyp
  hMore  : more.Hyp
  segs   : L.Proto pp
  tail   : T.A.Proto pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie

end

namespace Spec

def ldReqModel_pre : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (F : LdPreD E Kc S E₀ Wp) (p : ℕ),
    F.OK p ↔ F.Model ∧ F.Proto p

def ldReqModel_front : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (V : LdFrontRef E Kc z) (p : ℕ),
    V.OK p ↔ V.Model ∧ V.Proto p

def ldReqModel_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (pp : ℕ),
    A.OK pp ↔ A.Model ∧ A.Proto pp

def ldReqModel_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc)
      (S : LdRefS E Kc I a) (pp : ℕ),
    S.OK pp ↔ S.Model ∧ S.Proto pp

def ldReqModel_list : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (pp : ℕ),
    L.OK pp ↔ L.Model ∧ L.Proto pp

def ldReqModel_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (b : LdStage E Kc) (T : LdRefT R b) (pp : ℕ),
    T.OK pp ↔ T.Model ∧ T.A.Proto pp

/-- States: for pp the characteristic of E and `more` a list of sendings and steps alone (`hm`), the
model's side and the protocol's side give the reference request's `Hyp`. -/
def ldReqModel_hyp : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b),
    LdReqModel L T → LdReqProto pp R first more L T → (ldReqRef R first a₁ more hm b L T).Hyp

end Spec

theorem ldReqModel_pre : Spec.ldReqModel_pre := fun _ _ _ _ _ _ _ _ _ =>
  ⟨fun h =>
      ⟨⟨h.muFrom, h.lastFw, h.lastOn, h.lastCo, h.lastBw⟩,
        ⟨h.tags, h.numV, h.numD, h.inj, h.places, h.adm, h.muOK⟩⟩,
    fun h =>
      ⟨h.2.tags, h.2.numV, h.2.numD, h.1.muFrom, h.2.inj, h.2.places, h.2.adm, h.2.muOK, h.1.lastFw,
        h.1.lastOn, h.1.lastCo, h.1.lastBw⟩⟩

theorem ldReqModel_front : Spec.ldReqModel_front := fun E Kc _ _ _ V p =>
  ⟨fun h =>
      ⟨⟨((ldReqModel_pre E Kc _ _ _ V.Fp p).1 h.pre).1, h.link, h.back, h.psc0.degX, h.psc0.degY,
          fun i hi => (h.psc i hi).degX, fun i hi => (h.psc i hi).degY, h.step0, h.step, h.post⟩,
        ⟨((ldReqModel_pre E Kc _ _ _ V.Fp p).1 h.pre).2, h.ev, h.psc0.vars, h.psc0.inj,
          fun i hi => (h.psc i hi).vars, fun i hi => (h.psc i hi).inj⟩⟩,
    fun h =>
      ⟨(ldReqModel_pre E Kc _ _ _ V.Fp p).2 ⟨h.1.pre, h.2.pre⟩, h.1.link, h.1.back,
        h.2.ev, ⟨h.2.vars0, h.1.degX0, h.1.degY0, h.2.inj0⟩,
        fun i hi => ⟨h.2.vars i hi, h.1.degX i hi, h.1.degY i hi, h.2.inj i hi⟩,
        h.1.step0, h.1.step, h.1.post⟩⟩

theorem ldReqModel_body : Spec.ldReqModel_body := fun E Kc _ _ _ A pp =>
  ⟨fun h =>
      ⟨⟨((ldReqModel_front E Kc _ A.V pp).1 h.front).1, h.rest⟩,
        ⟨((ldReqModel_front E Kc _ A.V pp).1 h.front).2, h.ok, h.places, h.uniq, h.send1, h.send3,
          h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm, h.bits, h.reads, h.deg, h.ev⟩⟩,
    fun h =>
      ⟨(ldReqModel_front E Kc _ A.V pp).2 ⟨h.1.front, h.2.front⟩, h.2.ok, h.2.places, h.2.uniq,
        h.2.send1, h.2.send3, h.2.tabQ, h.2.tabH, h.2.keys, h.2.tags, h.2.inj, h.2.named, h.2.adm,
        h.2.bits, h.2.reads, h.1.rest, h.2.deg, h.2.ev⟩⟩

theorem ldReqModel_seg : Spec.ldReqModel_seg := fun E Kc _ _ _ _ S pp =>
  ⟨fun h =>
      ⟨⟨h.entry, ((ldReqModel_body E Kc _ S.A pp).1 h.body).1, h.ends⟩,
        ⟨((ldReqModel_body E Kc _ S.A pp).1 h.body).2, h.ev, h.named, h.fold, h.snd⟩⟩,
    fun h =>
      ⟨h.1.entry, (ldReqModel_body E Kc _ S.A pp).2 ⟨h.1.body, h.2.body⟩,
        h.1.ends, h.2.ev, h.2.named, h.2.fold, h.2.snd⟩⟩

theorem ldReqModel_list : Spec.ldReqModel_list := by
  intro E Kc _ _ I a b L pp
  induction L with
  | nil => rw [LdRefL.OK, LdRefL.Model, LdRefL.Proto]; exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | snoc L S ih =>
      rw [LdRefL.OK, LdRefL.Model, LdRefL.Proto, ih, ldReqModel_seg E Kc _ _ S pp]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩

theorem ldReqModel_tail : Spec.ldReqModel_tail := fun _ E Kc _ _ _ _ _ _ _ T pp =>
  ⟨fun h =>
      ⟨⟨h.entry, ((ldReqModel_body E Kc _ T.A pp).1 h.body).1, h.ends, h.exit⟩,
        ((ldReqModel_body E Kc _ T.A pp).1 h.body).2⟩,
    fun h => ⟨h.1.entry, (ldReqModel_body E Kc _ T.A pp).2 ⟨h.1.body, h.2⟩, h.1.ends, h.1.exit⟩⟩

theorem ldReqModel_hyp :
    Spec.ldReqModel_hyp := fun F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T hM hP =>
  ldReqRef_hyp F E Kc pp R a first a₁ more hm b L T hP.hFirst hP.hMore
    ((ldReqModel_list E Kc _ _ _ L pp).2 ⟨hM.segs, hP.segs⟩)
    ((ldReqModel_tail F E Kc R b T pp).2 ⟨hM.tail, hP.tail⟩) hP.deg hP.ev hP.tie

end Cb
