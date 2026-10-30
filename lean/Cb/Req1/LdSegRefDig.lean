-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefDig.lean: the digits' lookup of a segment's body, after the range check, as a list
of moves.

This file puts the lookup argument on the range check's digits into the sequence of reductions (a
list of moves) of a segment's body: two lookups, one for each kind of digits, are joined into one
by a random shift; the lookup protocol itself is a parameter.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefDigProofs.lean.
A lookup claims that every key is an entry of the table, and a further clause `more`, which is
`True` here (`Lk.inR`, Cb/Ld/LdLkp.lean); its exact form adds a clause on the multiplicities
(`Lk.inP`).

Why: the range check ends with "the low digits lie in [0, q), the high digits in [0, H)", its rows,
and, on the honest side, "the part sent with the digits is what mkV derives from them". The lookup
is stated in Cb/Ld/LdLkp.lean between joints of another form. Here the joints are made to meet: two
steps without rounds, the shift, and the lookup as a parameter.
A choice of ours. A write-up of ours (lean/CREDITS.md) says "a lookup on the digits" and
has one message of multiplicities for them; how the two tables (low, high) become one lookup it does
not say. Here:
the random shift with two functions. Two small tables could also be joined by a fixed shift.

Main names:
  `LdDgP`: the data: D, the data of "read, then the range check" (p = D.p: the range check's
    parameters, with q, H); lo, hi: the places of the digits among the entries of all messages
    (`Q.Places`: what the range check reads as digits stands there), so that the keys are functions
    of entries, as an assembled lookup needs them; the other fields have a comment at their place.
  ent, mult, lk (variables and a binder, no fields): ent: the entries that the lookup's rows and
    mask forms may read; mult: the lookup's exact clause on the multiplicities; lk: the lookup, any
    chain between its two stages.
  `Q.prog`: the four moves.
    step, `D.s4` → `Q.u0`, no round: "the digits are in their tables" is written as: for each of
      the two kinds, every key is an entry of that kind's table.
    sub, `Q.u0` → `Q.u1`, one round: the verifier draws the shift θ from all of E; one lookup claim
      with 2^(v+1) keys and a table of 2^(1+d) entries that reads θ.
    step, `Q.u1` → `Q.lkS`, no round: that claim in the form of a lookup, beside what rides along;
      on the honest side the clause mult.
    sub, `Q.lkS` → `Q.lkT`, its rounds: the lookup.
  The number n of rows that the lookup records stands in the exact relation of `Q.lkT` alone: the
    step that hands the rows to a batching with a fixed format rejects every other length, and
    completeness needs the honest length.
  `Q.R0`: what rides along: the range check's rows; what rode along in the range check (the claims
    as rows on the reads, and what else the statement claims); on the honest side alone: the part
    sent with the digits is mkV of the digits, and the digits are in their tables (after the shift
    the claim speaks of shifted keys; the clause on the multiplicities is derived from the
    unshifted fact).
  θ comes after the answers of the sample of the digits' oracle messages: they stand in the stage's
    samples. It comes before the lookup's first challenge, in a verifier message of its own.
  `Spec.ldSegRef_dg_allIn`: if `p.OK`, q, H ≤ 2^d and the number of digits of a kind is at most
    2^v, the digits are in their tables if and only if each kind's keys are in that kind's table.
  `Spec.ldSegRef_dg_hyp`: `Q.prog.Hyp` from: `p.OK`; the law of the places; q, H ≤ 2^d; the number
    of digits of a kind ≤ 2^v; the two tags differ; `Q.Mult` (for digits in their tables, what mkV
    derives meets the lookup's exact clause at every shift); every link of the lookup has all of
    the bundle but zero knowledge.
  `Spec.ldSegRef_dg_kinds`: the kinds of the moves are those that a body may hold.
  `Spec.ldSegRef_dg_zk`: under `Q.tag 0 ≠ Q.tag 1`: Q.prog.Zk base from: the lookup's chain is of
    the two kinds, given what is fresh before it (`Chain.OkGiven`, Cb/Req1/LdSegFresh.lean;
    `LdProg.Zk`, `LdProg.After`, Cb/Req1/LdReq.lean).
  `Spec.ldSegRef_dg_sub`: how a lookup stated as `SubR` with `SubR.OK` (Cb/Ld/LdLkp.lean) enters as
    one link: with the fact that every explicit part which its verifier puts out lists n rows.
  `Spec.ldSegRef_dg_nums`: rounds (`nAll`) and the two numbers `pBad`, `pHid` (what pBad and pHid
    bound: `GoodB`, Ior/Masked.lean): one round and nothing more beside the lookup's own.

Limits: this file does not say that a lookup with these properties exists. It does not say that a
function mkV with `Q.Mult` exists. For the assembled lookup (`X : LdDgA`), `X.lk.AllB` and
`X.Q.Mult X.mult` are stated under hypotheses (`Spec.ldSegRef_asm_allB`, `Spec.ldSegRef_asm_mult`,
Cb/Req1/LdSegRefAsm.lean; valid vectors of multiplicities, function by function, at every shift:
Cb/Ld/LdLkpMult.lean). This file says nothing on the closing of the lookup's output claim (the
extension of the keys at a point: a row on the digits) and the batching of all rows.
The order of the moves restates the write-up in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegRefRng
import Cb.Ld.LdRngLkp
import Cb.Ld.LdLkpShift
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- The digits' lookup after the range check: the data, but for the lookup itself. -/
structure LdDgP (E Kc : Type) [Field E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  D   : LdRrD E Kc E₀ Wp
  /-- the places of the digits among the entries of all messages -/
  lo  : D.p.Row → D.p.U → ((D.S.sum D.N).sum D.N').Ent
  hi  : D.p.Row → D.p.U → ((D.S.sum D.N).sum D.N').Ent
  /-- a numbering of the digits of one kind -/
  K   : ℕ
  e   : D.p.Row × D.p.U ≃ Fin K
  /-- 2^v keys and 2^d table entries for each kind; the tags -/
  v   : ℕ
  d   : ℕ
  tag : ℕ → E
  /-- the entries that the lookup's rows and mask forms may read -/
  Nn  : Type
  [finNn : Fintype Nn]

attribute [instance] LdDgP.finNn

namespace LdDgP
variable {E Kc : Type} [Field E] {E₀ : ExtSpec} {Wp : Type} (Q : LdDgP E Kc E₀ Wp)

/-- the oracle messages that are open (`LdStage.S`, Cb/Req1/LdSegKit.lean); the explicit part
without the samples -/
abbrev T : Sig E := (Q.D.S.sum Q.D.N).sum Q.D.N'
abbrev X₄ : Type := Q.D.St × Q.D.p.Chal

/-- the digits: the entries at their places; the part sent with them, read off the messages -/
def dg (m : Q.T.Msg) : Q.D.p.Dg E :=
  (fun r u => Q.T.ents m (Q.lo r u), fun r u => Q.T.ents m (Q.hi r u))
def vv (m : Q.T.Msg) : Q.D.V := Q.D.getV ((Q.D.S.sum Q.D.N).right Q.D.N' (T := OMsg.Msg) m)
/-- the older messages -/
def old (m : Q.T.Msg) : (Q.D.S.sum Q.D.N).Msg := (Q.D.S.sum Q.D.N).left Q.D.N' (T := OMsg.Msg) m

/-- The law of the places: what the range check reads as digits stands there. -/
def Places : Prop :=
  ∀ m : Q.T.Msg, Q.D.get' ((Q.D.S.sum Q.D.N).right Q.D.N' (T := OMsg.Msg) m) = Q.dg m

/-- What rides along. -/
def R0 : IOR.Rels Kc Q.X₄ E₀ (Q.T.Msg × Wp) where
  rel  := fun x y w =>
    Rows Q.D.p.D Q.D.p.rdx Q.D.p.q (Q.D.r.W x.1) x.2 (Q.D.r.pk (Q.old w.1))
      (Q.D.r.rd (Q.old w.1)) (Q.dg w.1) ∧
    Q.D.A₁.rel x.1 y (Q.old w.1, w.2) ∧
    Q.vv w.1 = Q.D.mkV (Q.dg w.1) ∧
    InTabs Q.D.p.q Q.D.p.H (Q.dg w.1)
  relR := fun a w =>
    Rows Q.D.p.D Q.D.p.rdx Q.D.p.q (Q.D.r.W a.1.1) a.1.2 (Q.D.r.pk (Q.old w.1))
      (Q.D.r.rd (Q.old w.1)) (Q.dg w.1) ∧
    Q.D.A₁.relR (a.1.1, a.2) (Q.old w.1, w.2)
  on   := fun a => Q.D.A₁.on (a.1.1, a.2)
  core := fun w => Q.D.A₁.core (Q.old w.1, w.2)

/-- The two kinds of digits as two functions with their tables: 0 the low digits, any other number
the high ones. -/
def sh : ShiftP E Q.X₄ Q.T.Msg :=
  ⟨1, Q.v, Q.d, fun _ m f => rngKeys Q.D.p Q.e (if f = 0 then (Q.dg m).1 else (Q.dg m).2),
    fun _ f => tabMod (if f = 0 then Q.D.p.q else Q.D.p.H), Q.tag⟩

/-- each kind's keys are in that kind's table -/
@[reducible] def u0 : LdStage E Kc := ⟨Q.T, Q.X₄, E₀, Wp, Q.sh.jIn Q.R0⟩
/-- after the shift -/
@[reducible] def u1 : LdStage E Kc := ⟨Q.T, Q.X₄ × E, E₀, Wp, Q.sh.jOut Q.R0⟩

/-- The one lookup claim. -/
def L : Lk E (Q.X₄ × E) (Ms Q.T E₀) :=
  ⟨Q.v + 1, 1 + Q.d, fun x ms => shKey Q.v (Q.sh.key x.1 ms.2) Q.tag x.2,
    fun x => shTab Q.d (Q.sh.tab x.1) Q.tag x.2, fun _ _ => True⟩

/-- what rides along, read at an explicit part that holds the shift -/
def R1 : IOR.Rels Kc (Q.X₄ × E) E₀ (Q.T.Msg × Wp) :=
  ⟨fun x y w => Q.R0.rel x.1 y w, fun a w => Q.R0.relR (a.1.1, a.2) w,
    fun a => Q.R0.on (a.1.1, a.2), Q.R0.core⟩

variable (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E)

/-- The two stages of the lookup, in the form in which Cb/Ld/LdLkp.lean states a lookup. -/
@[reducible] def lkS : LdStage E Kc :=
  ⟨Q.T, Q.X₄ × E, E₀, Wp, rideJ Q.T Q.R1 id (Q.L.inP mult) Q.L.inR⟩
@[reducible] def lkT (n : ℕ) : LdStage E Kc :=
  ⟨Q.T, TX (Q.X₄ × E) E Q.Nn, E₀, Wp,
    rideJ Q.T Q.R1 Prod.fst (fun x ms => Q.L.out id ent x ms ∧ x.2.2.length = n) (Q.L.out id ent)⟩

/-- For digits in their tables, what mkV derives from the digits meets the lookup's exact clause, at
every shift. -/
def Mult : Prop :=
  ∀ (x : Q.X₄ × E) (y : E₀.Str) (m : Q.T.Msg),
    InTabs Q.D.p.q Q.D.p.H (Q.dg m) → Q.vv m = Q.D.mkV (Q.dg m) → mult x (y, m)

variable [Fintype E]

/-- the first step -/
def stepA : LdMv Q.D.s4 Q.u0 :=
  .step Q.D.s4 Q.u0 (sideF Q.T id) (sideG Q.T (ExtMap.id E₀))
    (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)

/-- The shift, lifted over the oracle messages. -/
def shift : IOR.Link Kc Q.u0.J Q.u1.J :=
  Q.u0.lift (Q.sh.jOut Q.R0) (IOR.draw E (Prod.mk : Q.X₄ → E → Q.X₄ × E) E₀)
    (IOR.Honest.draw E Prod.mk E₀ (Q.T.Msg × Wp)) (fun _ _ _ wp => wp)
    (IOR.Nums.draw Kc E Prod.mk E₀ (2 ^ (1 + Q.d)))

/-- the second step -/
def stepB : LdMv Q.u1 (Q.lkS mult) :=
  .step Q.u1 (Q.lkS mult) (sideF Q.T id) (sideG Q.T (ExtMap.id E₀))
    (sideM Q.T id fun _ w => w.2) (sideB Q.T fun _ w => w.2)

/-- the three moves before the lookup -/
def pre : LdProg Q.D.s4 (Q.lkS mult) :=
  (((LdProg.nil Q.D.s4).snoc Q.stepA).snoc (.sub Q.u0 Q.u1 (.one Q.shift))).snoc (Q.stepB mult)

/-- The four moves; lk: the lookup. -/
def prog (n : ℕ) (lk : IOR.Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) :
    LdProg Q.D.s4 (Q.lkT ent n) :=
  (Q.pre mult).snoc (.sub (Q.lkS mult) (Q.lkT ent n) lk)

/-- a lookup that sends no oracle (`SubR`), as a link between the two stages -/
def ofSub (n : ℕ) (B : SubR Q.T E₀ Kc (Q.X₄ × E) Q.Nn Wp) :
    IOR.Link Kc (Q.lkS mult).J (Q.lkT ent n).J :=
  ⟨B.R, B.H, B.ext, B.P⟩

end LdDgP

namespace Spec
open IOR

/-- States, under the hypotheses below: the digits are in their tables if and only if each kind's
keys are in that kind's table. -/
def ldSegRef_dg_allIn : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (Q : LdDgP E Kc E₀ Wp)
      (x : Q.X₄) (m : Q.T.Msg),
    Q.D.p.OK → Q.D.p.q ≤ 2 ^ Q.d → Q.D.p.H ≤ 2 ^ Q.d → Q.K ≤ 2 ^ Q.v →
    (Q.sh.inC x m ↔ InTabs Q.D.p.q Q.D.p.H (Q.dg m))

/-- All that the list of moves asks. -/
def ldSegRef_dg_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J),
    Q.D.p.OK → Q.Places → Q.D.p.q ≤ 2 ^ Q.d → Q.D.p.H ≤ 2 ^ Q.d → Q.K ≤ 2 ^ Q.v →
    Q.tag 0 ≠ Q.tag 1 → Q.Mult mult → lk.AllB → (Q.prog mult ent n lk).Hyp

def ldSegRef_dg_kinds : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J),
    (Q.prog mult ent n lk).All fun t => t = .send ∨ t = .sub ∨ t = .step

/-- What zero knowledge asks, beside its hypotheses (`Q.prog.Hyp`): of the lookup alone.
(not all hypotheses are named here: see the statement below) -/
def ldSegRef_dg_zk : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (base : MaskFact Q.D.s4.J.W → Prop),
    Q.tag 0 ≠ Q.tag 1 → lk.OkGiven ((Q.pre mult).After base) → (Q.prog mult ent n lk).Zk base

/-- A lookup stated as `SubR` enters: from `SubR.OK`, and: every explicit part that its verifier
puts out lists n rows. -/
def ldSegRef_dg_sub : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (B : SubR Q.T E₀ Kc (Q.X₄ × E) Q.Nn Wp),
    B.OK Q.L mult Q.R1 ent → (∀ x y τ xo, B.R.out x y τ = some xo → xo.1.2.2.length = n) →
    (Q.ofSub mult ent n B).GoodB

def ldSegRef_dg_nums : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (Q : LdDgP E Kc E₀ Wp)
      (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
      (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J),
    (Q.prog mult ent n lk).nAll = 1 + lk.nAll ∧
    (Q.prog mult ent n lk).pBad = lk.pBad ∧
    (Q.prog mult ent n lk).pHid = lk.pHid

end Spec
end Cb
