-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRng2.lean: the approximate range check with packing as an interactive oracle reduction, with
a number of digits of one width and one table.

The file has the approximate range check as a three-round reduction in which each entry of each
random combination, plus D, is written in nd digits of wd bits, all claimed to be in one table
[0, 2^wd). (What is checked, and against which bounds: the first paragraph of the head of
Cb/Ld/LdRng.lean.)

Definitions and statements (Cb.Spec.ldRng2_*); the proofs are in Cb/Ld/LdRng2Proofs.lean.
The mathematics is Cb/Ld/LdRng2Alg.lean. The block is that of Cb/Ld/LdRng.lean; all that does not
mention digits is that file's, unchanged: the predicate and the input joint (`rngIn`), the reduction
of round 1 (`rngDraw`: the verifier draws the ternary matrix), its numbers (`rngDrawN`: the error
`p.one.err`, the window event, its bound `p.one.pWin`), how the check reads (`RngRd`), the sending
that follows.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Main names:
  `RngPar2`: the parameters: as `RngPar`, with wd (the width of a digit) and nd (their number) in
    the place of the sizes of two tables.
  `p.OK`: 1 ≤ B ≤ 2 D, 2 D = 2^(wd · nd).
  `p.one : RngPar`: the same parameters as a `RngPar`;
    its two sizes of tables are 2^wd and 2^(wd (nd - 1)); they are read by nothing that is used
    here, but for `p.one.OK`.
  `p.Dg E`: the digits: one for each row of cells, each combination, each i < nd.
  `rngOut2`: the joint after the draw, at the base: all digits are in the one table, and the rows
    hold, beside the base joint A₀; the digits are a further part of the witness. At the base: on
    messages as such, before `Sig.over` (Cb/Ld/LdSig.lean) puts codes and samples over them.
  `rngDrawH2`: the honest side of round 1: the digits of the integer combinations; the window event
    is withheld in secret (`Hid`, Ior/Honest.lean).
  `ldRng p.one ..`, `ldRng2H ..`: all three rounds: the draw, then the sending of the family that
    holds the digits.
  Statements, each under the hypotheses of its statement: `Spec.ldRng2_at` (round 1 for each fixed
  tuple of messages: the bundle `GoodAt`), `Spec.ldRng2_exact` (honest-verifier zero knowledge, in
  the exact form of Ior/Honest.lean: outside the window event, which is withheld in secret
  (`Hid` := `rngEv`), round 1 shows nothing), `Spec.ldRng2_draw` (round 1 over a signature),
  `Spec.ldRng2_goodT` (the three rounds), `Spec.ldRng2_rows` (the rows are linear forms with public
  targets), `Spec.ldRng2_end` (what the relaxed relation of the output joint says).

The errors are those of Cb/Ld/LdRng.lean: round 1: the fraction 2^(-|U|) of the values of the
verifier message; rounds 2, 3: the sending's. The relaxed bound is 2 D = 2^(wd · nd).

Notation: `Rp`, `Rd`, `C`, `U`: packed rows, reads, columns, combinations; `P`: how many rows of
cells are packed into one; `rdx`: the radix; `B`: the honest bound; `D`: the half-width of the
window; `r.W`: the weights of the reads; `r.pk`, `r.rd`: the two components, read off the messages;
`r.yz`: the integer matrix, read off the core (`RngPar`, `RngRd`: Cb/Ld/LdRng.lean); `S`, `N`, `Sd`,
`Dn`, `L`, `t`: see "Notation:" in the head of Cb/Ld/LdRng.lean.

Limits: what the head of Cb/Ld/LdRng.lean lists as not said is not said here either. No lookup is
run here. Its multiplicities are not this block's. The batching of the rows is not run here.
Cb/Req1/LdSegRefPartBat.lean has it as a list of moves (for any rows).

There are three remarks against this protocol's technical report (lean/CREDITS.md).
(1) `p.OK` lets the honest bound B go up to 2 D; the report asks it to be at most D.
    Wider here, and harmless: for B above D the bound on the window event says little.
(2) The two conditions under which the packing determines the cells are not asked by this block.
    They are asked where the cells are read as a virtual matrix: Cb/Ld/LdRead.lean.
    Their name is `Uniq`
    (Cb/Ld/LdRngAlg.lean).
(3) In the report the relation after round 1 already holds, on the exact side only, the
    predicate on the multiplicities of the digits' lookup, and the honest prover puts that vector
    out with the digits. Here that is left to the caller, as a step of its own after the draw: the
    same content at another place.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRng2Alg
import Cb.Ld.LdRng
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk
open scoped ENNReal

/-- The parameters. -/
structure RngPar2 where
  Rp : Type
  Rd : Type
  C : Type
  U : Type
  [finRp : Fintype Rp]
  [finRd : Fintype Rd]
  [finC : Fintype C]
  [decC : DecidableEq C]
  [neC : Nonempty C]
  [finU : Fintype U]
  [decU : DecidableEq U]
  P : ℕ
  rdx : ℤ
  B : ℤ
  D : ℤ
  /-- the width of a digit; the number of digits of a combination -/
  wd : ℕ
  nd : ℕ

attribute [instance] RngPar2.finRp RngPar2.finRd RngPar2.finC RngPar2.decC RngPar2.neC
  RngPar2.finU RngPar2.decU

namespace RngPar2
variable (p : RngPar2)

/-- The same parameters as a `RngPar` (Cb/Ld/LdRng.lean). -/
@[reducible] def one : RngPar :=
  { Rp := p.Rp, Rd := p.Rd, C := p.C, U := p.U, P := p.P, rdx := p.rdx, B := p.B, D := p.D,
    q := 2 ^ p.wd, H := 2 ^ (p.wd * (p.nd - 1)) }

abbrev Dg (E : Type) : Type := Dig2 E p.Rp p.P p.U p.nd

structure OK : Prop where
  B1 : 1 ≤ p.B
  BD : p.B ≤ 2 * p.D
  D2 : 2 * p.D = ((2 ^ (p.wd * p.nd) : ℕ) : ℤ)

end RngPar2

section
variable {E St M Kc Wp : Type} [CommRing E] {E₀ : ExtSpec} (p : RngPar2)
  (r : RngRd p.one E St M Kc) (A₀ : IOR.Rels Kc St E₀ (M × Wp))

/-- The joint after the draw, at the base. -/
def rngOut2 : IOR.Rels Kc (St × p.one.Chal) E₀ (M × (Wp × p.Dg E)) where
  rel  := fun x y w =>
    Out2 p.D p.rdx p.wd (r.W x.1) x.2 (r.pk w.1) (r.rd w.1) w.2.2 ∧ A₀.rel x.1 y (w.1, w.2.1)
  relR := fun a w =>
    Out2 p.D p.rdx p.wd (r.W a.1.1) a.1.2 (r.pk w.1) (r.rd w.1) w.2.2 ∧
    A₀.relR (a.1.1, a.2) (w.1, w.2.1)
  on   := fun a => A₀.on (a.1.1, a.2)
  core := fun w => A₀.core (w.1, w.2.1)

/-- The honest side of round 1. -/
def rngDrawH2 : (rngDraw p.one St E₀).Honest (M × Wp) (M × (Wp × p.Dg E)) where
  Coin := Unit
  strat w x _ := ((((), ()), fun Θ => ((x, Θ), (w.1, (w.2, hdig2 p.D p.wd (r.yz (A₀.core w)) Θ)))) :
    Strat [IOR.drawRound p.one.Chal] ((St × p.one.Chal) × (M × (Wp × p.Dg E))))
  Bad := ∅
  Hid w _ := rngEv p.one (r.yz (A₀.core w))

end

section
variable {E St Kc Wp : Type} [Field E] {E₀ : ExtSpec} (p : RngPar2) (S N : Sig E)
  (r : RngRd p.one E St S.Msg Kc) (A₀ : IOR.Rels Kc St E₀ (S.Msg × Wp))

abbrev ldRng2DrawH : (ldRngDraw p.one S St E₀).Honest (S.Wit × Wp) (S.Wit × (Wp × p.Dg E)) :=
  S.liftH (rngDrawH2 p r A₀)

/-- the digits are read off the new messages -/
def rngBk2 (get : N.Msg → p.Dg E) : N.Msg → Wp → Wp × p.Dg E := fun m wp => (wp, get m)

variable (Sd : N.Seeds)

abbrev ldRng2H (Dn : N.Sender (S.Wit × (Wp × p.Dg E)) (S.Wit × Wp)) :
    (ldRng p.one S N Sd St E₀).Honest (S.Wit × Wp) ((S.sum N).Wit × Wp) :=
  (ldRng2DrawH p S r A₀).seq (ldSendSigHon Sd (St × p.one.Chal) E₀ Dn)

end

/-- The places of the entries of the two components and of the digits in one vector of entries. -/
structure RngAt2 (p : RngPar2) (J : Type) where
  pk : p.Rp → p.C → J
  rd : p.Rd → p.C → J
  dg : p.one.Row → p.U → Fin p.nd → J

section
variable {E St J : Type} [Field E] [DecidableEq J] (p : RngPar2)
  (W : St → p.Rd → p.one.Row → E) (l : RngAt2 p J)

/-- The rows: one for each packed row and each read, for each combination. The state is (st, Θ). -/
def rngRow2 : (p.Rp ⊕ p.Rd) × p.U → Slf E (St × p.one.Chal) J
  | (.inl i, u) =>
    fun s n =>
      placed (l.pk i) (fun c => (((s.2 u c).val : ℤ) : E)) n -
        placed (fun x : Fin p.P × Fin p.nd => l.dg (i, x.1) u x.2)
          (fun x => (p.rdx : E) ^ (x.1 : ℕ) * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E)) n
  | (.inr k, u) =>
    fun s n =>
      placed (l.rd k) (fun c => (((s.2 u c).val : ℤ) : E)) n -
        placed (fun x : p.one.Row × Fin p.nd => l.dg x.1 u x.2)
          (fun x => W s.1 k x.1 * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E)) n

def RngAt2.pkOf (v : J → E) : p.Rp → p.C → E := fun i c => v (l.pk i c)
def RngAt2.rdOf (v : J → E) : p.Rd → p.C → E := fun k c => v (l.rd k c)
def RngAt2.dgOf (v : J → E) : p.Dg E := fun r u i => v (l.dg r u i)

end

namespace Spec
open IOR

def ldRng2_one : Prop := ∀ p : RngPar2, p.OK → p.one.OK

/-- Round 1, for each fixed tuple of messages. The extractor forgets the digits. -/
def ldRng2_at : Prop :=
  ∀ (E St M Kc Wp : Type) [CommRing E] (E₀ : ExtSpec) (p : RngPar2)
      (r : RngRd p.one E St M Kc) (A₀ : Rels Kc St E₀ (M × Wp)),
    p.OK → GoodAt (rngDraw p.one St E₀) (rngDrawH2 p r A₀) (rngIn p.one r A₀) (rngOut2 p r A₀)
      (fun _ _ _ w => w.1) (rngDrawN p.one r)

/-- Honest-verifier zero knowledge, in the exact form of Ior/Honest.lean: outside the window
event, which is withheld in secret (`Hid` := `rngEv`), round 1 shows nothing. -/
def ldRng2_exact : Prop :=
  ∀ (E St M Kc Wp : Type) [CommRing E] (E₀ : ExtSpec) (p : RngPar2) (r : RngRd p.one E St M Kc)
      (A₀ : Rels Kc St E₀ (M × Wp)) (Ri : St → E₀.Str → M × Wp → Prop),
    (rngDrawH2 p r A₀).Exact Ri fun _ _ => True

/-- Round 1 over a signature. -/
def ldRng2_draw : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar2) (S : Sig E)
      (r : RngRd p.one E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    p.OK → GoodT (ldRngDraw p.one S St E₀) (ldRng2DrawH p S r A₀) (S.over (rngIn p.one r A₀))
      (S.over (rngOut2 p r A₀)) (fun _ _ w => (w.1, w.2.1)) (ldRngDrawN p.one S r)

/-- The range check with packing. The statement has eight hypotheses: `p.OK`; for every member a of
N, `(N.om a).C.Laws` (Cb/Ld/LdRel.lean), `ListLE (L a)` and `Evades` (Cb/Ld/LdSig.lean); `Sd.Fair`,
`Dn.Laws` and `Dn.Blind Sd` (Cb/Ld/LdSendFam.lean); `Dn.Nn.Hides (N.budT t)` (Cb/Gen/Code.lean); the
head of Cb/Ld/LdRng.lean tells what the last seven ask.
Under these the three rounds (`ldRng p.one`), with the honest side `ldRng2H`, have the bundle
`GoodT` (Ior/KnowCollGood.lean) from `(S.over (rngIn p.one ..)).cf` to
`((S.sum N).over (S.grow N (rngOut2 ..) ..)).cf`, with the extractor that the head of
Cb/Ld/LdRng.lean tells, at the numbers `ldRngN p.one` (`.cf`: `Rels.cf`, Ior/KnowCollGood.lean: the
condition is moved into the relaxed relation). -/
def ldRng2_goodT : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar2) (S N : Sig E)
      (r : RngRd p.one E St S.Msg Kc) (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (get : N.Msg → p.Dg E)
      (Sd : N.Seeds) (Dn : N.Sender (S.Wit × (Wp × p.Dg E)) (S.Wit × Wp)) (L t : N.O → ℕ),
    p.OK → (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) →
    (∀ a, (N.om a).Evades) → Dn.Laws (S.backN N (rngBk2 p N get)) →
    Dn.Blind Sd → Dn.Nn.Hides (N.budT t) →
    GoodT (ldRng p.one S N Sd St E₀) (ldRng2H p S N r A₀ Sd Dn) (S.over (rngIn p.one r A₀)).cf
      ((S.sum N).over (S.grow N (rngOut2 p r A₀) (rngBk2 p N get))).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, w.2)) (ldRngN p.one S N r Sd L t)

/-- The rows are linear forms with public targets. -/
def ldRng2_rows : Prop :=
  ∀ (E St J : Type) [Field E] [Fintype J] [DecidableEq J] (p : RngPar2)
      (W : St → p.Rd → p.one.Row → E) (l : RngAt2 p J) (st : St) (Θ : p.one.Chal) (v : J → E),
    Rows2 p.D p.rdx p.wd (W st) Θ (l.pkOf p v) (l.rdOf p v) (l.dgOf p v) ↔
    Slf.All (rngRow2 p W l) (rngTgt p.one W st, fun _ => (st, Θ)) v

/-- What the relaxed relation of the output joint says. -/
def ldRng2_end : Prop :=
  ∀ (E St Kc Wp : Type) [Field E] (E₀ : ExtSpec) (p : RngPar2) (S N : Sig E)
      (l : RngAt2 p (S.sum N).Ent) (r : RngRd p.one E St S.Msg Kc)
      (get : N.Msg → p.Dg E) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    (∀ m : (S.sum N).Msg,
      r.pk (S.left N (T := OMsg.Msg) m) = l.pkOf p ((S.sum N).ents m) ∧
      r.rd (S.left N (T := OMsg.Msg) m) = l.rdOf p ((S.sum N).ents m) ∧
      get (S.right N (T := OMsg.Msg) m) = l.dgOf p ((S.sum N).ents m)) →
    ∀ a w,
      ((S.sum N).over (S.grow N (rngOut2 p r A₀) (rngBk2 p N get))).relR a w ↔
      (∀ i, (S.sum N).decs a.1.2 a.2.2 i = some (w.1 i).1) ∧
      InTabs2 p.wd (l.dgOf p ((S.sum N).ents ((S.sum N).msgs w.1))) ∧
      Slf.All (rngRow2 p r.W l) (rngTgt p.one r.W a.1.1.1, fun _ => a.1.1)
        ((S.sum N).ents ((S.sum N).msgs w.1)) ∧
      A₀.relR (a.1.1.1, a.2.1) (S.left N (T := OMsg.Msg) ((S.sum N).msgs w.1), w.2)

end Spec
end Cb
