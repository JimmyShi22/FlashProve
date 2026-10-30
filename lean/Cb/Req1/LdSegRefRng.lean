-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefRng.lean: the part "read, then the range check" of a segment's body, as a list of
moves.

This file composes two sub-protocols of a segment's body into one sequence of reductions (a list of
moves): the prover sends linear combinations (the reads) of integers (the cells) that earlier
oracle messages hold in packed form; then come the range check's draw and the sending of its
digits.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefRngProofs.lean.
What zero knowledge asks of a move, beside its hypotheses: Cb/Req1/LdReq.lean.
The reads are weight vectors times the cells (`ReadBy`); the packing is `PackBy`; the range check's
predicate is `Rng`: all three are in Cb/Ld/LdRngAlg.lean.

Why: the two blocks are stated each between its own joints. Here they are put in a row in the form
in which a segment is stated, so that the composition typechecks from "packing, and claims on the
virtual cells" to "the digits are in their tables, the range check's rows, the claims as rows on
the reads", and, under the hypotheses of `Spec.ldSegRef_rr_hyp`, every hypothesis that a list of
moves asks is discharged from the blocks' theorems and the rule for a change of the base joint
(Cb/Ld/LdBatPeelProofs.lean).

Main names:
  `LdRrD`: the data: the parameters p of the range check; the oracle messages S that are open; some
    other fields have a comment at their place.
  `D.prog`: the five moves.
    step, `D.s0` → `D.s1`, no round: the honest prover computes the reads; they are a further part
      of the witness.
    send, `D.s1` → `D.s2`, two rounds: the family N. The base joint of `D.s2` is the input joint of
      the range check (`Spec.ldSegRef_rr_s2`).
    sub, `D.s2` → `D.s3`, one round: the verifier draws the ternary matrix; the digits are a
      further part of the witness. A reduction on claims about messages, lifted over the oracle
      messages of `D.s2`.
    step, `D.s3` → `D.s3v`, no round: the honest prover derives v = mkV digits; it is a further
      part of the witness. An exact-only clause (`alsoJ`): the relaxed relation does not read v.
    send, `D.s3v` → `D.s4`, two rounds: the family N': digits and v in one prover message.
  `Spec.ldSegRef_rr_hyp`: `D.prog.Hyp` from: `p.OK`; the two conditions on radix and characteristic
    (`Uniq`, Cb/Ld/LdRngAlg.lean, at the characteristic pp of E); the hypotheses of the two
    sendings. Nothing else beside whatever the arguments hold as proofs.
  `Spec.ldSegRef_rr_kinds`: the kinds of the moves are those that a body may hold.
  `Spec.ldSegRef_rr_zk`: under `D.p.OK`: D.prog.Zk base, for every set of facts at the start: no
    move has masks in its input; the one "sub" has the whole bundle.
  `Spec.ldSegRef_rr_nums`: five rounds; nothing is withheld in public, in this sense:
    `D.prog.pBad = 0` (see `GoodB`, Ior/Masked.lean); withheld in secret with probability at most
    p.pWin (the window event: the one term that a range check adds to the completeness error and to
    the zero-knowledge error of a request) in this sense: `D.prog.pHid = D.p.pWin` (on what the
    words rest: `Spec.ldRng_pWin`, Cb/Ld/LdRng.lean, and `Spec.ldSeg_goodB`, `Spec.ldSeg_nums`,
    Cb/Req1/LdSeg.lean, each under its hypotheses).
  `Spec.ldSegRef_rr_s4`: what the base joint of the last stage says. Exact: the range check's
    output on the digits read off the new messages, what rode along, and the part read off the new
    messages is mkV of these digits (the exact input of a lookup asks this of the multiplicities).
    Relaxed: the first two.

Limits: the packed rows (`p.Rp`) and how they are read off the messages (`D.c`) are data: S holds
every oracle message that is open, so the packed matrix may hold, beside the segment's own cells,
the earlier matrices that the segment reads and that are still open. Nothing here asks or forbids
it.
This file says nothing on the lookup on the digits, the batching of the rows, what else a body
holds. It does not say that masks which stand in the oracle messages of S stay fresh through these
moves (the two sendings must not read them: a property of the senders). The core Kc is not fixed to
Unit: c.yz reads the integer cells off it. This file says nothing on how blocks stated at core Unit
stand in one list with these moves.
The order of the moves restates this protocol's technical report
in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReq
import Cb.Ld.LdRead
import Cb.Ld.LdBatPeel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk
open scoped ENNReal

/-- A joint with a further part of the witness that the honest prover derives: a clause of the exact
relation alone. -/
def alsoJ {Kc X M Wp V : Type} {E₀ : ExtSpec}
    (A : IOR.Rels Kc X E₀ (M × Wp)) (ok : M × Wp → V → Prop) :
    IOR.Rels Kc X E₀ (M × (Wp × V)) where
  rel  := fun x y w => A.rel x y (w.1, w.2.1) ∧ ok (w.1, w.2.1) w.2.2
  relR := fun a w => A.relR a (w.1, w.2.1)
  on   := A.on
  core := fun w => A.core (w.1, w.2.1)

/-- "Read", then the range check: the data. -/
structure LdRrD (E Kc : Type) [Field E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  p   : RngPar
  S   : Sig E
  St  : Type
  J   : Type
  [finJ : Fintype J]
  /-- how the cells are read; the claims on cell maps; what else is claimed -/
  c   : CellRd p E St S.Msg Kc J
  cl  : ReadCl p E St J
  A₀  : IOR.Rels Kc St E₀ (S.Msg × Wp)
  /-- the family that holds the reads -/
  N   : Sig E
  get : N.Msg → p.Rds E
  Sd  : N.Seeds
  Dn  : N.Sender (S.Wit × (Wp × p.Rds E)) (S.Wit × Wp)
  L   : N.O → ℕ
  t   : N.O → ℕ
  /-- what the prover derives from the digits and sends with them (the multiplicities of the digits'
  lookups; Unit if nothing) -/
  V    : Type
  mkV  : p.Dg E → V
  /-- the family that holds the digits and that part -/
  N'   : Sig E
  get' : N'.Msg → p.Dg E
  getV : N'.Msg → V
  Sd'  : N'.Seeds
  Dn'  : N'.Sender ((S.sum N).Wit × ((Wp × p.Dg E) × V)) ((S.sum N).Wit × Wp)
  L'   : N'.O → ℕ
  t'   : N'.O → ℕ

attribute [instance] LdRrD.finJ

namespace LdRrD
variable {E Kc : Type} [Field E] {E₀ : ExtSpec} {Wp : Type} (D : LdRrD E Kc E₀ Wp)

/-- packing, and the claims on the virtual cells -/
@[reducible] def s0 : LdStage E Kc := ⟨D.S, D.St, E₀, Wp, readIn D.p D.c D.cl D.A₀⟩
/-- the reads are a further part of the witness -/
@[reducible] def s1 : LdStage E Kc := ⟨D.S, D.St, E₀, Wp × D.p.Rds E, readMid D.p D.c D.cl D.A₀⟩
/-- the sending of the reads -/
@[reducible] def d1 : LdSendD D.s1 := ⟨D.N, D.Sd, Wp, readBk D.p D.N D.get, D.Dn, D.L, D.t⟩
@[reducible] def s2 : LdStage E Kc := D.d1.tgt
/-- how the range check reads; what rides along in it -/
@[reducible] def r : RngRd D.p E D.St (D.S.sum D.N).Msg Kc := D.c.withReads D.p D.S D.N D.get
@[reducible] def A₁ : IOR.Rels Kc D.St E₀ ((D.S.sum D.N).Msg × Wp) :=
  D.S.grow D.N (readRows D.p D.c D.cl D.A₀) (readBk D.p D.N D.get)
/-- after the draw: the digits are a further part of the witness -/
@[reducible] def s3 : LdStage E Kc :=
  ⟨D.S.sum D.N, D.St × D.p.Chal, E₀, Wp × D.p.Dg E, rngOut D.p D.r D.A₁⟩
/-- what is derived from the digits is a further part of the witness -/
@[reducible] def s3v : LdStage E Kc :=
  ⟨D.S.sum D.N, D.St × D.p.Chal, E₀, (Wp × D.p.Dg E) × D.V,
    alsoJ (rngOut D.p D.r D.A₁) fun w v => v = D.mkV w.2.2⟩
/-- the sending of the digits and of what is derived from them -/
@[reducible] def d3 : LdSendD D.s3v :=
  ⟨D.N', D.Sd', Wp, fun m wp => ((wp, D.get' m), D.getV m), D.Dn', D.L', D.t'⟩
@[reducible] def s4 : LdStage E Kc := D.d3.tgt

variable [Fintype E]

/-- The draw of the ternary matrix, lifted over the oracle messages of D.s2. -/
def draw : IOR.Link Kc D.s2.J D.s3.J :=
  D.s2.lift (rngOut D.p D.r D.A₁)
    (rngDraw D.p D.St E₀) (rngDrawH D.p D.r D.A₁) (fun _ _ _ w => w.1) (rngDrawN D.p D.r)

/-- the step in which the honest prover derives v -/
def derive : LdMv D.s3 D.s3v :=
  .step D.s3 D.s3v (sideF (D.S.sum D.N) id) (sideG (D.S.sum D.N) (ExtMap.id E₀))
    (sideM (D.S.sum D.N) id fun _ w => (w.2, D.mkV w.2.2)) (sideB (D.S.sum D.N) fun _ w => w.2.1)

/-- The five moves. -/
def prog : LdProg D.s0 D.s4 :=
  (((((LdProg.nil D.s0).snoc
            (.step D.s0 D.s1 (fun x => some x) (ExtMap.id D.s0.Ex)
              (readM D.p D.S D.c D.A₀) fun _ w => (w.1, w.2.1))).snoc
          (.send D.s1 D.d1)).snoc
        (.sub D.s2 D.s3 (.one D.draw))).snoc D.derive).snoc
    (.send D.s3v D.d3)

end LdRrD

namespace Spec
open IOR

/-- the base joint before the draw is the input joint of the range check -/
def ldSegRef_rr_s2 : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (D : LdRrD E Kc E₀ Wp),
    D.s2.A = rngIn D.p D.r D.A₁

/-- What the last stage claims. -/
def ldSegRef_rr_s4 : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (D : LdRrD E Kc E₀ Wp),
    (∀ x y w,
      D.s4.A.rel x y w ↔
      (Out D.p.D D.p.rdx D.p.q D.p.H (D.r.W x.1) x.2
          (D.r.pk ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1))
          (D.r.rd ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1))
          (D.get' ((D.S.sum D.N).right D.N' (T := OMsg.Msg) w.1)) ∧
        D.A₁.rel x.1 y ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1, w.2)) ∧
      D.getV ((D.S.sum D.N).right D.N' (T := OMsg.Msg) w.1) =
        D.mkV (D.get' ((D.S.sum D.N).right D.N' (T := OMsg.Msg) w.1))) ∧
    ∀ a w,
      D.s4.A.relR a w ↔
      Out D.p.D D.p.rdx D.p.q D.p.H (D.r.W a.1.1) a.1.2
        (D.r.pk ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1))
        (D.r.rd ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1))
        (D.get' ((D.S.sum D.N).right D.N' (T := OMsg.Msg) w.1)) ∧
      D.A₁.relR (a.1.1, a.2) ((D.S.sum D.N).left D.N' (T := OMsg.Msg) w.1, w.2)

/-- All that the list of moves asks. (not all hypotheses are named here: see the statement below) -/
def ldSegRef_rr_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ)
      [CharP E pp] (D : LdRrD E Kc E₀ Wp),
    D.p.OK → Uniq (2 * D.p.D) D.p.rdx D.p.P pp → D.d1.Hyp → D.d3.Hyp → D.prog.Hyp

def ldSegRef_rr_kinds : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (D : LdRrD E Kc E₀ Wp),
    D.prog.All fun t => t = .send ∨ t = .sub ∨ t = .step

/-- What zero knowledge asks of the moves, beside their hypotheses, whatever is fresh at the
start. (not all hypotheses are named here: see the statement below) -/
def ldSegRef_rr_zk : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E]
      (D : LdRrD E Kc E₀ Wp) (base : MaskFact D.s0.J.W → Prop),
    D.p.OK → D.prog.Zk base

def ldSegRef_rr_nums : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (D : LdRrD E Kc E₀ Wp),
    D.prog.nAll = 5 ∧ D.prog.pBad = 0 ∧ D.prog.pHid = D.p.pWin

end Spec
end Cb
