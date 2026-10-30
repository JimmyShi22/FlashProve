-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAll.lean: the reference segment as one closed term: no list of moves is left free.

This file puts the sub-protocols of one segment's body together into one term (`A.body`); in the
segment `K.seg l Qc` the link bridge-to-fold l and the data Qc stay parameters; it gathers what is
asked of the body's data in one record (`A.OK`).
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefAllProofs.lean.
Cb/Req1/LdSegRefBody.lean makes the body of a segment from three lists of its own and three
parameters (front, the digits' lookup, tensor). Here the parameters are filled in, over one encoded
index I:
  front: Cb/Req1/LdSegFrontRef.lean: shift; the assembled lookup; zerocheck; sumchecks, again for
    each map that is never sent: a term whose target stage is a parameter: here the first stage of
    "read".
  digits: Cb/Req1/LdSegRefAsm.lean: the assembled lookup on the shifted digits.
  tensor: Cb/Req1/LdSegRefTen.lean: the batching of the segment's tensor rows on the encoded index,
    beside the rows.
The further oracles of every stage are the encoded index (`I.C.E0`); the further witness is (prover
encoded index, (W₁, a ghost Gh)).

Why: the encoded index (`LdRefIx`) is a parameter of the data, not a part of them: all segments of
a request have one, so that their pending tensor rows are rows on one matrix and can meet in one
last batching.
Where the rows of the front's lookup go: the family of rows that is gathered
(Cb/Req1/LdSegRefRows.lean: `G.B`) has slots for the range check's rows, the claims on cell maps,
and the rows and the mask claim of the digits' lookup. The rows that the front's lookup files have
no slot of their own: they are meant to leave the front as further members of the family of claims
(`D.cl`), with no coefficient on a read; the records do not force this (Cb/Req1/LdReqModel.lean).

Main names:
  `LdRefD E Kc I`: the data: W₁, Gh; Xa (read, range check, shift, digits' lookup); the places of
    packed matrix, reads and the claims' mask entries; the batching's data over the oracle messages
    that are then open (state, record; claims; incoming mask forms as coefficients on names;
    evader, degree, places of its own masks; what else is claimed; what it reads); g₀: how the
    state at the reads gives the targets and the state of the tensor rows; V: the front.
  `A.Gr`, `A.X`, `A.Y`: the rows' data, the batching's data with the body's rows as its riding
    rows, the body's data.
  `Spec.ldSegRefAll_meet`: the stage after the rows are gathered is the first stage of the
    batching's list: by definition.
  `A.body St₁ fz Az`: the body, from the entry stage of the front to "rows on all entries, beside
    Az".
  `A.OK pp`: what is asked of the body's data: the front's conditions (`V.OK pp`); numbers; places;
    the hypotheses of the two sendings; the evader's law (`A.Zt.OK`); the law `rest` on "what else
    is claimed".
  `A.Ghost κ`: the core is the ghost, from the start: the core of every witness is κ of its last
    part. (The other way, a step that copies the core into the further witness behind a request's
    first sending, is Cb/Req1/LdSegGhost.lean; here the first is taken.)
  `LdRefC1 A`: one group: the closing's data. `K.seg l Qc : LdSeg ..`: the segment.
  `Spec.ldSegRefAll_body`: `(A.body St₁ fz Az).Hyp` from `A.OK pp` and `A.X.Ends St₁ fz Az`; pp is
    the characteristic of E, here and in `Spec.ldSegRefAll_one`.
  `Spec.ldSegRefAll_kinds`: the body holds sendings, sub-protocols and steps only. No hypothesis
    beside whatever the arguments hold as proofs.
  `Spec.ldSegRefAll_one`: `(K.seg l Qc).Hyp` from `A.OK pp`, what is left goes over into what the
    closing carries, the evader's law (`K.Z.OK`), all named places lie in members of the group, the
    hypotheses of bridge-to-fold and of the one sending.
  `Spec.ldSegRefAll_noLook`: `A.Ghost κ` gives: the integer cells are read without looking at any
    message (Cb/Req1/LdSegRefCarry.lean: `D.NoLook`, for all sets of entries).

Limits: the body is other than a write-up of ours (lean/CREDITS.md) in two places. Two
kinds of digits joined by a shift, where the write-up has one table and no shift: one round
more. The range check's rows go straight to the closing's batching, where the write-up first
batches them into one row: one round and one error term fewer. Cb/Req1/LdSegRefBody.lean says it in
full. So this closed term is not the write-up's segment.







This file says nothing on zero knowledge of the segment's masked blocks: each part's file says what
it asks (facts on fresh masks); they are not put together here. It says nothing on two groups. The
front (Cb/Req1/LdSegFrontRef.lean) has at least one further sumcheck behind the zerocheck's: a
segment all of whose never-sent maps are cell maps is not held by this closed term
(Cb/Req1/LdSegRefBody.lean holds it, with another front). This file does not say that `A.OK pp` can
be met. At a toy: `Cb.GlJ3.Spec.ldSegFront_toySeam`, Cb/GlVal/GlJ3SegFrontToySeam.lean. No theorem
of this library states that the hypotheses of `Spec.ldSegRefAll_one` can be met together.
The order of the parts restates a table of a segment in a write-up of ours that is not in this
repository, with its errata, in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegRefProofs
import Cb.Req1.LdSegRefAsmProofs
import Cb.Req1.LdSegRefTenProofs
import Cb.Req1.LdSegRefCarry
import Cb.Req1.LdSegFrontRef
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- The encoded index of a request: its configuration; its matrix (names of rows, number of column
variables, the entries read off a message). -/
structure LdRefIx (E : Type) where
  C   : ConfigurationWithOutOfDomainSample
  Rw  : Type
  [finRw : Fintype Rw]
  k   : ℕ
  mat : C.Msg → Rw × (Fin k → Bool) → E

attribute [instance] LdRefIx.finRw

/-- The reference segment's body, closed: the data. -/
structure LdRefD (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) : Type 1 where
  /-- the further witness beside the prover encoded index; the ghost -/
  W₁  : Type
  Gh  : Type
  /-- read, range check, shift, the digits' lookup -/
  Xa  : LdDgA E Kc I.C.E0 (I.C.PIdx × (W₁ × Gh))
  [finJc : Fintype Xa.Q.D.cl.Jc]
  pkAt : Xa.Q.D.p.Rp → Xa.Q.D.p.C → Xa.Q.T.Ent
  rdAt : Xa.Q.D.p.Rd → Xa.Q.D.p.C → Xa.Q.T.Ent
  jAt  : Xa.Q.D.J → Xa.Q.T.Ent
  /-- the batching of the tensor rows -/
  Stt : Type
  rc  : Stt → I.C.Rec
  Qt  : Type
  [finQt : Fintype Qt]
  g   : Stt → Qt → I.Rw → E
  pt  : Stt → Qt → Fin I.k → E
  Nm  : Type
  [finNm : Fintype Nm]
  mf  : Stt → Qt → Nm → E
  μAt : Nm → Xa.Q.T.Ent
  Zt  : Evader E Qt
  nt  : ℕ
  wAt : PIdx (List.replicate I.k (pfCube E nt)) → Xa.Q.T.Ent
  A0t : IOR.Rels Kc Stt I.C.E0 ((I.C.Msg × Xa.Q.T.Msg) × (W₁ × Gh))
  Rdt : Xa.Q.T.Ent → Prop
  g₀  : Xa.Q.D.St → (Qt → E) × Stt
  /-- the front -/
  V   : LdFrontRef E Kc Xa.Q.D.s0

attribute [instance] LdRefD.finJc LdRefD.finQt LdRefD.finNm

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

/-- the rows' data -/
@[reducible] def Gr : LdGaP E Kc I.C.E0 (I.C.PIdx × (A.W₁ × A.Gh)) :=
  { Q := A.Xa.Q, n := A.Xa.A.nRows, ent := A.Xa.ent, pkAt := A.pkAt, rdAt := A.rdAt,
    jAt := A.jAt, nAt := A.Xa.ι }

/-- The batching's data, with the body's rows as its riding rows. -/
@[reducible] def X : LdTenD E Kc :=
  { S := A.Xa.Q.T, C := I.C, Wp := A.W₁ × A.Gh, Bn := A.Gr.B, Sb := fun _ => A.Gr.Sx,
    sl := A.Gr.sl, Rw := I.Rw, k := I.k, mat := I.mat, St := A.Stt, rc := A.rc, Q := A.Qt,
    g := A.g, pt := A.pt, Nm := A.Nm, mf := A.mf, μAt := A.μAt, Z := A.Zt, n := A.nt, wAt := A.wAt,
    A0 := A.A0t, Rd := A.Rdt }

/-- The body's data. -/
@[reducible] def Y : LdBodyD E Kc I.C.E0 (I.C.PIdx × (A.W₁ × A.Gh)) :=
  { G := A.Gr, St₀ := (A.Qt → E) × A.Stt, g₀ := A.g₀, Ar := idxAt I.C (fun x => A.rc x.2) A.X.tenA,
    mult := A.Xa.mult, lk := A.Xa.lk, a := A.V.Fp.s0, front := A.V.prog }

/-- The body. -/
def body (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
    (Az : IOR.Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))) :
    LdProg A.V.Fp.s0 (A.X.tgt St₁ Az) :=
  A.Y.body (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az)

/-- What is asked of the body's data. -/
structure OK (pp : ℕ) : Prop where
  front  : A.V.OK pp
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
  rest   : A.Gr.Rest A.Y.St₀ A.Y.g₀ A.Y.Ar
  deg    : 2 ≤ A.nt
  ev     : A.Zt.OK

/-- The core is the ghost, from the start. -/
def Ghost (κ : A.Gh → Kc) : Prop := ∀ w, A.Xa.Q.D.A₀.core w = κ w.2.2.2

end LdRefD

/-- One group closes: the data. -/
structure LdRefC1 {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I) :
    Type 1 where
  Z   : Evader E A.Gr.B
  grp : Grp A.Xa.Q.T
  kp  : A.Xa.Q.T.O → Prop
  [decKp : DecidablePred kp]
  St₁ : Type
  fz  : A.X.bt.par.Mid → St₁
  A₀c : IOR.Rels Kc St₁ I.C.E0 ((A.Xa.Q.T.sub kp).Msg × (I.C.PIdx × (A.W₁ × A.Gh)))
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (A.Xa.Q.T.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (A.Xa.Q.T.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (A.Xa.Q.T.om k.1.1).C.Q → Cf.Q

attribute [instance] LdRefC1.decKp LdRefC1.finPf LdRefC1.decCl

namespace LdRefC1
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I} (K : LdRefC1 A)

/-- the data of the segment with one group -/
@[reducible] def R : LdSegRef E Kc I.C.E0 (I.C.PIdx × (A.W₁ × A.Gh)) :=
  { Y := A.Y, Z := K.Z, grp := K.grp, kp := K.kp, St₁ := K.St₁, A₀c := K.A₀c,
    Pf := K.Pf, Cf := K.Cf, Stf := K.Stf, slf := K.slf, e := K.e, cl := K.cl,
    sW := K.sW, sJ := K.sJ, sQ := K.sQ }

/-- what the closing carries, read off all messages -/
@[reducible] def Az : IOR.Rels Kc K.St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh))) :=
  onMsgRels (A.Xa.Q.T.res (T := OMsg.Msg) K.kp) K.A₀c

/-- the batching's list, up to the stage at which the closing begins -/
def tensor : LdProg K.R.Y.tgt K.R.c1.bat.src := A.X.prog K.St₁ K.fz K.Az

/-- the kinds of the body's moves -/
theorem kinds :
    (K.R.Y.body K.R.c1.bat.src K.tensor).All fun t => t = .send ∨ t = .sub ∨ t = .step :=
  ldSegRef_body_kinds E Kc _ _ A.Y K.R.c1.bat.src K.tensor (ldSegFrontRef_kinds E Kc _ A.V)
    (ldSegRef_tn_kinds E Kc A.X K.St₁ K.fz K.Az)

/-- The segment; l: the link bridge-to-fold, a parameter; Qc: the one sending and the locations. -/
def seg (l : IOR.Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid)
    (Qc : LdCloseD K.R.c1.fold) : LdSeg A.V.Fp.s0 Qc.loc.tgt :=
  K.R.seg K.tensor K.kinds l Qc

end LdRefC1

namespace Spec
open IOR

/-- The stage after the rows are gathered is the first stage of the batching's list. -/
def ldSegRefAll_meet : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I), A.Y.tgt = A.X.src

def ldSegRefAll_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (St₁ : Type)
      (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))),
    (A.body St₁ fz Az).All fun t => t = .send ∨ t = .sub ∨ t = .step

/-- The body's hypotheses. -/
def ldSegRefAll_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))),
    A.OK pp → A.X.Ends St₁ fz Az → (A.body St₁ fz Az).Hyp

/-- The reference segment with one group, closed: its hypotheses. -/
def ldSegRefAll_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      (K : LdRefC1 A) (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid) (Qc : LdCloseD K.R.c1.fold),
    A.OK pp → A.X.Ends K.St₁ K.fz K.Az → K.Z.OK → (∀ n, A.Gr.Named n → K.grp.mem n.1) →
    K.R.c1.fold.Hyp l → Qc.snd.Hyp → (K.seg l Qc).Hyp

/-- States, under `A.Ghost κ`: the integer cells are read without looking at any message
(`D.NoLook`, for all sets of entries). -/
def ldSegRefAll_noLook : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I) (κ : A.Gh → Kc),
    A.Ghost κ → ∀ Rd own, A.Xa.Q.D.NoLook Rd own

end Spec
end Cb
