-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefBody.lean: the body of the reference segment, as a term: from the parts' lists of
moves.

This file puts the sub-protocols of one segment's body in a row as one sequence of reductions (a
list of moves); its first part, the lookup on the digits and its last part are parameters.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefBodyProofs.lean.
Cb/Req1/LdSeg.lean states a segment over arbitrary lists of moves. Here the body is a term, in the
order of a table of a segment in a write-up of ours that is not in this repository; whatever closing
follows (one group: Cb/Req1/LdSegRef.lean)
takes it as it stands.
  front: the segment's lookup; zerocheck and sumchecks, again for each map that is never sent: a
    parameter, any list of moves that ends at "packing, and claims on the virtual cells"
    (Cb/Req1/LdSegRefRng.lean: `D.s0`). All rows that it leaves are meant to be members of the
    family of claims; the records do not force this (Cb/Req1/LdReqModel.lean).
  read: the reads are sent (Cb/Req1/LdSegRefRng.lean).
  range: the ternary matrix; the digits and their multiplicities in one prover message (the same
    file).
  digits: the shift; the digits' lookup (a parameter: any chain between the lookup's two stages;
    Cb/Req1/LdSegRefAsm.lean: the assembled lookup) (Cb/Req1/LdSegRefDig.lean).
  rows: all that is left are rows on all entries, beside what else is claimed
    (Cb/Req1/LdSegRefRows.lean).
  tensor: the batching of the segment's tensor rows on the encoded index: a parameter, any list of
    moves that leads from "the rows, beside what else is claimed" to the stage z at which the
    closing begins (Cb/Req1/LdSegRefTen.lean has the list: its two ends have these forms).

Main names:
  `LdBodyD`: the data: G (Cb/Req1/LdSegRefRows.lean; it holds the data of the three files above),
    St₀, g₀, Ar (what else is claimed after the rows are gathered), mult and lk (the digits'
    lookup), the entry stage a and "front".
  `Y.body z tensor`: the list of moves from `Y.a` to z.
  `Y.Hyp pp`: what is asked beside front, lk and tensor: `p.OK`; the law of the digits' places; the
    two conditions on radix and characteristic; the hypotheses of the two sendings (reads; digits);
    sizes of tables and keys, two different tags; what is derived from the digits meets the
    lookup's exact clause; the laws of the places; what else was claimed goes over into Ar.
  `Spec.ldSegRef_body_hyp`: `(Y.body z tensor).Hyp` from `front.Hyp`, `Y.Hyp pp` (pp the
    characteristic of E), `lk.AllB`, `tensor.Hyp`.
  `Spec.ldSegRef_body_kinds`: the body holds sendings, sub-protocols and steps only, if front and
    tensor do.
  `Spec.ldSegRef_body_zk`: what zero knowledge asks of the body, beside its hypotheses: of "front",
    of the digits' lookup, of "tensor", each given what is fresh before it. Reads, range check,
    shift and steps ask nothing, beside their hypotheses. (not all hypotheses are named here: see
    its statement)
  `Spec.ldSegRef_body_nums`: the body's rounds: front + 5 + 1 + the lookup's + tensor's. Withheld
    in secret: front's + p.pWin + the lookup's + tensor's, in this sense:
    `(Y.body z tensor).pHid = Y.front.pHid + Y.G.Q.D.p.pWin + Y.lk.pHid + tensor.pHid` (on what the
    words rest: `Spec.ldSeg_goodB`, `Spec.ldSeg_nums`, Cb/Req1/LdSeg.lean, each under its
    hypotheses).

Limits: declared: where this body is other than a write-up of ours (lean/CREDITS.md; other,
not wider).
  (1) The digits. Here a combination has two digits of two kinds (low < q, high < H, q · H = 2 D),
      with two tables, joined into one lookup by a shift. The write-up writes a combination
      in a number of digits of one width, with one table and no shift. Neither is a case of the
      other
      (unless q = H; and then the shift is still there). Here: one round more.
  (2) The range check's rows. Here the rows of the range check and the rows and the mask claim of
      the digits' lookup go straight to the closing's batching, beside the claims on cell maps. The
      write-up batches them into one row inside the range check (one verifier message, an
      evader
      of its own, nothing masked). Here: one round fewer, one error term fewer. (That batching, as
      a list of moves of its own: Cb/Req1/LdSegRefPartBat.lean.)
  (3) So the body's list of rounds and of errors is not the write-up's, and a reference
      request made of this body is not the write-up's request as a term.












"front" and "tensor" are parameters here. This file does not say that all hypotheses can be met
together.
The order of the parts restates a table of a segment in a write-up of ours that is not in this
repository, with its errata, in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegRefRows
import Cb.Req1.LdSegRefKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- The body of the reference segment: the data. -/
structure LdBodyD (E Kc : Type) [Field E] [Fintype E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  G     : LdGaP E Kc E₀ Wp
  /-- what else is claimed after the rows are gathered -/
  St₀   : Type
  g₀    : G.Q.D.St → St₀
  Ar    : IOR.Rels Kc St₀ E₀ (G.Q.T.Msg × Wp)
  /-- the digits' lookup -/
  mult  : G.Q.X₄ × E → Ms G.Q.T E₀ → Prop
  lk    : IOR.Chain Kc (G.Q.lkS mult).J (G.Q.lkT G.ent G.n).J
  /-- the entry stage; lookup, zerocheck, sumchecks -/
  a     : LdStage E Kc
  front : LdProg a G.Q.D.s0

namespace LdBodyD
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (Y : LdBodyD E Kc E₀ Wp)

/-- the stage after the rows are gathered; the step that gathers them -/
@[reducible] def tgt : LdStage E Kc := Y.G.tgt Y.St₀ Y.Ar
def step : LdMv (Y.G.Q.lkT Y.G.ent Y.G.n) Y.tgt := Y.G.step Y.St₀ Y.g₀ Y.Ar

/-- The body; z: the stage at which the closing begins; tensor: the batching of the segment's tensor
rows. -/
def body (z : LdStage E Kc) (tensor : LdProg Y.tgt z) : LdProg Y.a z :=
  (((Y.front.app Y.G.Q.D.prog).app (Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk)).snoc Y.step).app tensor

/-- What is asked beside front, the digits' lookup and tensor. -/
structure Hyp (pp : ℕ) : Prop where
  ok     : Y.G.Q.D.p.OK
  places : Y.G.Q.Places
  uniq   : Uniq (2 * Y.G.Q.D.p.D) Y.G.Q.D.p.rdx Y.G.Q.D.p.P pp
  send1  : Y.G.Q.D.d1.Hyp
  send3  : Y.G.Q.D.d3.Hyp
  tabQ   : Y.G.Q.D.p.q ≤ 2 ^ Y.G.Q.d
  tabH   : Y.G.Q.D.p.H ≤ 2 ^ Y.G.Q.d
  keys   : Y.G.Q.K ≤ 2 ^ Y.G.Q.v
  tags   : Y.G.Q.tag 0 ≠ Y.G.Q.tag 1
  mult   : Y.G.Q.Mult Y.mult
  reads  : Y.G.Reads
  rest   : Y.G.Rest Y.St₀ Y.g₀ Y.Ar

end LdBodyD

namespace Spec
open IOR

def ldSegRef_body_kinds : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Y : LdBodyD E Kc E₀ Wp)
      (z : LdStage E Kc) (tensor : LdProg Y.tgt z),
    (Y.front.All fun t => t = .send ∨ t = .sub ∨ t = .step) →
    (tensor.All fun t => t = .send ∨ t = .sub ∨ t = .step) →
    (Y.body z tensor).All fun t => t = .send ∨ t = .sub ∨ t = .step

/-- The body's hypotheses, from the parts'. -/
def ldSegRef_body_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp]
      (Y : LdBodyD E Kc E₀ Wp) (z : LdStage E Kc) (tensor : LdProg Y.tgt z),
    Y.front.Hyp → Y.Hyp pp → Y.lk.AllB → tensor.Hyp → (Y.body z tensor).Hyp

/-- What zero knowledge asks of the body, beside its hypotheses. -/
def ldSegRef_body_zk : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Y : LdBodyD E Kc E₀ Wp)
      (z : LdStage E Kc) (tensor : LdProg Y.tgt z) (base : MaskFact Y.a.J.W → Prop),
    Y.G.Q.D.p.OK → Y.G.Q.tag 0 ≠ Y.G.Q.tag 1 → Y.front.Zk base →
    Y.lk.OkGiven ((Y.G.Q.pre Y.mult).After (Y.G.Q.D.prog.After (Y.front.After base))) →
    tensor.Zk (Y.step.After
        ((Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk).After (Y.G.Q.D.prog.After (Y.front.After base)))) →
    (Y.body z tensor).Zk base

def ldSegRef_body_nums : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Y : LdBodyD E Kc E₀ Wp)
      (z : LdStage E Kc) (tensor : LdProg Y.tgt z),
    (Y.body z tensor).nAll = Y.front.nAll + 5 + (1 + Y.lk.nAll) + tensor.nAll ∧
    (Y.body z tensor).pBad = Y.front.pBad + Y.lk.pBad + tensor.pBad ∧
    (Y.body z tensor).pHid = Y.front.pHid + Y.G.Q.D.p.pWin + Y.lk.pHid + tensor.pHid

end Spec
end Cb
