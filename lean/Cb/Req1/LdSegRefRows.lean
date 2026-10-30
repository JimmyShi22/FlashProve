-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefRows.lean: at the end of a segment's body all that is left are rows on all entries,
beside what else is claimed: the step from the digits' lookup to the batching.

Book-keeping at the end of a segment's body: the claims that are left after the lookup on the
digits are written as one family of linear claims (rows) on the entries of all oracle messages,
beside what else is claimed, by a reduction without rounds.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefRowsProofs.lean.
It ends at the stage at which a closing begins (Cb/Req1/LdSegKit.lean: `LdBatD.src`).

Why: what is claimed after the digits' lookup, and in which form:
  the range check's rows: `Cb.RngPk.Rows`, on the packed matrix, the reads, the digits;
  the claims on cell maps, as rows on the reads: `ReadCl.OnReads`, on the reads and on mask
    entries;
  the lookup's output claim: the extension of the (shifted) keys at a point, plus a mask form, is a
    public target (`LdLkp.MCl.Holds`). The keys are the digits: a linear key map;
  the rows that the lookup has recorded: a list of rows in the explicit part (`LdLkp.RowsHold`);
  what else the statement claims: a parameter.
A closing begins with a family of linear forms on all entries of all messages, over a fixed finite
set of names, with public targets, beside what else is claimed.

Main names:
  `LdGaP`: the data: Q (the data of the digits' lookup, but for the lookup itself), n (the number
    of rows that it records), ent; the places of all that is read among the entries of all
    messages: pkAt, rdAt (packed matrix, reads; the digits' places stand in Q), jAt (the mask
    entries of the claims), nAt (the entries that the lookup's rows read).
  St₀, g₀, Ar (variables of the file, no fields): parameters of the last stage and of the step, not
    of the rows: what else is claimed at the end, in the form of whatever comes next.
  `G.Reads`: the laws of the places: what the earlier stages read is what stands at these places.
  `G.Rest St₀ g₀ Ar`: what else was claimed goes over into Ar (`fw`: the exact relation forwards;
    `bw`: the relaxed relation backwards, on statements with `A₀.on`; `on`: the condition; `core`:
    the core).
  `G.B`: the names of the rows: (packed rows and reads) × combinations, the claims, one for the
    lookup's output claim, n for its recorded rows.
  `G.sl`, `G.tg`: the forms (the state of each is the whole explicit part) and the targets.
  `G.step`: the step, without rounds. The verifier rejects unless the list has n rows (a row beyond
    the format would be dropped). An artefact of keeping the rows in a list; this protocol's
    technical report (lean/CREDITS.md) has no such check. The list is made by the verifier from its
    own view; for the assembled lookup it has
    n rows on every transcript (Cb/Ld/LdLkpAsm2Pull.lean: `ldLkpAsm2N_len`), so the branch is dead
    there.
  `Spec.ldSegRef_ga_sum`: if K ≤ 2^v, a weighted sum over the 2^v keys of one kind is the weighted
    sum over the digits of that kind.
  `Spec.ldSegRef_ga_keys`: if `Q.K` ≤ 2^v, the extension of the shifted keys at a point is a linear
    form in the digits plus a public constant.
  `Spec.ldSegRef_ga_all`: if `G.Reads` and the number of digits of a kind is at most 2^v, then for
    a list of n rows: all forms of G.sl hold with the targets G.tg if and only if the four claims
    hold.
  `Spec.ldSegRef_ga_hyp`: the step's Hyp from `G.Reads`, `G.Rest` and: the number of digits of a
    kind is at most 2^v.

Limits: this file does not say that places with these laws exist: a layout is an instance.
Elsewhere, at a toy: `Cb.GlJ3.RefToy.reads`, `Cb.GlJ3.RefToy.rest`, Cb/GlVal/GlJ3SegRefToyAll.lean.
This file does not say which rows vanish outside which group. The honest-only clauses
(multiplicities; digits in their tables; the length) end here: nothing after the lookup reads them,
but that this step tests the length.
The gathering of rows restates this protocol's technical report
in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefDig
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

/-- From the digits' lookup to the batching: the data. -/
structure LdGaP (E Kc : Type) [Field E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Q   : LdDgP E Kc E₀ Wp
  /-- the number of rows that the lookup records; the entries that they read -/
  n   : ℕ
  ent : Ms Q.T E₀ → Q.Nn → E
  [finJc : Fintype Q.D.cl.Jc]
  /-- the places (those of the digits stand in Q) -/
  pkAt : Q.D.p.Rp → Q.D.p.C → Q.T.Ent
  rdAt : Q.D.p.Rd → Q.D.p.C → Q.T.Ent
  jAt : Q.D.J → Q.T.Ent
  nAt : Q.Nn → Q.T.Ent

attribute [instance] LdGaP.finJc

namespace LdGaP
variable {E Kc : Type} [Field E] {E₀ : ExtSpec} {Wp : Type} (G : LdGaP E Kc E₀ Wp)

/-- the explicit part after the lookup -/
abbrev Sx : Type := TX (G.Q.X₄ × E) E G.Q.Nn
/-- The names of the rows. -/
abbrev B : Type := ((G.Q.D.p.Rp ⊕ G.Q.D.p.Rd) × G.Q.D.p.U) ⊕ (G.Q.D.cl.Jc ⊕ (Unit ⊕ Fin G.n))

/-- the places of all that the range check reads -/
def l : RngAt G.Q.D.p G.Q.T.Ent := ⟨G.pkAt, G.rdAt, G.Q.lo, G.Q.hi⟩

/-- the row that holds of every vector -/
def row0 : Row E G.Q.Nn := ⟨fun _ => 0, 0⟩

/-- The forms. -/
def sl : G.B → Slf E G.Sx G.Q.T.Ent
  | .inl b => fun x => rngRow G.Q.D.p G.Q.D.r.W G.l b x.1.1
  | .inr (.inl j) =>
    fun x nn =>
      placed (fun kc : G.Q.D.p.Rd × G.Q.D.p.C => G.l.rd kc.1 kc.2)
          (fun kc => G.Q.D.cl.cw x.1.1.1 j kc.1 kc.2) nn +
        placed G.jAt (G.Q.D.cl.ms x.1.1.1 j) nn
  | .inr (.inr (.inl _)) => fun x nn =>
      placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.l.lo ru.1 ru.2)
        (fun ru => eqN (G.Q.v + 1) 0 x.2.1.pt (G.Q.e ru)) nn
      + placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.l.hi ru.1 ru.2)
          (fun ru => eqN (G.Q.v + 1) 0 x.2.1.pt (2 ^ G.Q.v + G.Q.e ru)) nn +
        placed G.nAt x.2.1.mf nn
  | .inr (.inr (.inr i)) => fun x nn => placed G.nAt (x.2.2.getD i G.row0).cf nn

/-- The targets. -/
def tg (x : G.Sx) : G.B → E
  | .inl b => rngTgt G.Q.D.p G.Q.D.r.W x.1.1.1 b
  | .inr (.inl j) => G.Q.D.cl.v x.1.1.1 j - G.Q.D.cl.k0 x.1.1.1 j
  | .inr (.inr (.inl _)) =>
    x.2.1.tg -
      x.1.2 *
        ∑ X ∈ Finset.range (2 ^ (G.Q.v + 1)), eqN (G.Q.v + 1) 0 x.2.1.pt X * G.Q.tag (X / 2 ^ G.Q.v)
  | .inr (.inr (.inr i)) => (x.2.2.getD i G.row0).tg

/-- The laws of the places. -/
structure Reads : Prop where
  pk : ∀ m, G.Q.D.r.pk (G.Q.old m) = G.l.pkOf G.Q.D.p (G.Q.T.ents m)
  rd : ∀ m, G.Q.D.r.rd (G.Q.old m) = G.l.rdOf G.Q.D.p (G.Q.T.ents m)
  je : ∀ m j,
    G.Q.D.c.ent (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m)) j = G.Q.T.ents m (G.jAt j)
  ne : ∀ y m i, G.ent (y, m) i = G.Q.T.ents m (G.nAt i)

/-! What else is claimed at the end: St₀, g₀, Ar. -/
variable (St₀ : Type) (g₀ : G.Q.D.St → St₀) (Ar : IOR.Rels Kc St₀ E₀ (G.Q.T.Msg × Wp))

/-- Rows on all entries, beside what else is claimed: the stage at which a closing begins. -/
@[reducible] def tgt : LdStage E Kc :=
  ⟨G.Q.T, ((G.B → E) × (G.B → G.Sx)) × St₀, E₀, Wp,
    claimRels (fun x m => Slf.All G.sl x (G.Q.T.ents m)) Ar⟩

/-- the new explicit part -/
def fd (x : G.Sx) : ((G.B → E) × (G.B → G.Sx)) × St₀ := ((G.tg x, fun _ => x), g₀ x.1.1.1)

/-- What else was claimed goes over into Ar. -/
structure Rest : Prop where
  fw : ∀ st y m wp, G.Q.D.A₀.rel st y (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m), wp) →
    Ar.rel (g₀ st) y (m, wp)
  bw : ∀ st y m wp, G.Q.D.A₀.on (st, y) → Ar.relR (g₀ st, y) (m, wp) →
    G.Q.D.A₀.relR (st, y) (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m), wp)
  on : ∀ st y, G.Q.D.A₀.on (st, y) → Ar.on (g₀ st, y)
  core : ∀ m wp,
    Ar.core (m, wp) = G.Q.D.A₀.core (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m), wp)

variable [Fintype E]

/-- The step. -/
def step : LdMv (G.Q.lkT G.ent G.n) (G.tgt St₀ Ar) :=
  .step (G.Q.lkT G.ent G.n) (G.tgt St₀ Ar)
    (fun x => if x.1.2.2.length = G.n then some (G.fd St₀ g₀ x.1, x.2) else none)
    (sideG G.Q.T (ExtMap.id E₀)) (sideM G.Q.T (G.fd St₀ g₀) fun _ w => w.2)
    (sideB G.Q.T fun _ w => w.2)

end LdGaP

namespace Spec
open IOR

/-- A weighted sum over the keys of one kind. -/
def ldSegRef_ga_sum : Prop :=
  ∀ (E : Type) [Field E] (p : RngPar) (K v : ℕ) (e : p.Row × p.U ≃ Fin K)
      (d : p.Row → p.U → E) (c : ℕ → E),
    K ≤ 2 ^ v →
    ∑ b ∈ Finset.range (2 ^ v), c b * rngKeys p e d b = ∑ ru : p.Row × p.U, c (e ru) * d ru.1 ru.2

/-- States, if `Q.K` ≤ 2 ^ `Q.v`: the extension of the shifted keys at a point is linear in the
digits, plus a public constant. -/
def ldSegRef_ga_keys : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (Q : LdDgP E Kc E₀ Wp) (x : Q.X₄ × E)
      (ms : Ms Q.T E₀) (pt : ℕ → E),
    Q.K ≤ 2 ^ Q.v →
    ext Q.L.v (Q.L.key x ms) pt =
      ∑ ru : Q.D.p.Row × Q.D.p.U, eqN (Q.v + 1) 0 pt (Q.e ru) * (Q.dg ms.2).1 ru.1 ru.2 +
        ∑ ru : Q.D.p.Row × Q.D.p.U,
          eqN (Q.v + 1) 0 pt (2 ^ Q.v + Q.e ru) * (Q.dg ms.2).2 ru.1 ru.2 +
        x.2 * ∑ X ∈ Finset.range (2 ^ (Q.v + 1)), eqN (Q.v + 1) 0 pt X * Q.tag (X / 2 ^ Q.v)

/-- States, under the hypotheses below: all forms hold if and only if the four claims hold. -/
def ldSegRef_ga_all : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (G : LdGaP E Kc E₀ Wp) (x : G.Sx)
      (y : E₀.Str) (m : G.Q.T.Msg),
    G.Reads → G.Q.K ≤ 2 ^ G.Q.v → x.2.2.length = G.n →
    (Slf.All G.sl (G.tg x, fun _ => x) (G.Q.T.ents m) ↔
      Rows G.Q.D.p.D G.Q.D.p.rdx G.Q.D.p.q (G.Q.D.r.W x.1.1.1) x.1.1.2 (G.Q.D.r.pk (G.Q.old m))
        (G.Q.D.r.rd (G.Q.old m)) (G.Q.dg m) ∧
      G.Q.D.cl.OnReads x.1.1.1 (G.Q.D.r.rd (G.Q.old m))
        (G.Q.D.c.ent (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m))) ∧
      x.2.1.Holds G.Q.L.v (G.Q.L.key x.1 (y, m)) (G.ent (y, m)) ∧
      RowsHold x.2.2 (G.ent (y, m)))

/-- What the step asks. (not all hypotheses are named here: see the statement below) -/
def ldSegRef_ga_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (G : LdGaP E Kc E₀ Wp)
      (St₀ : Type) (g₀ : G.Q.D.St → St₀) (Ar : Rels Kc St₀ E₀ (G.Q.T.Msg × Wp)),
    G.Reads → G.Rest St₀ g₀ Ar → G.Q.K ≤ 2 ^ G.Q.v → (G.step St₀ g₀ Ar).Hyp

end Spec
end Cb
