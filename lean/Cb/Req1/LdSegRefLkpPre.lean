-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefLkpPre.lean: what comes before the zerocheck in the body of a reference segment: the
random shift, the lookup, as a list of moves.

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Req1/LdSegRefLkpPreProofs.lean.
It uses Cb/Ld/LdLkpShift.lean (several lookups into one by a random shift), Cb/Ld/LdLkpAsm2Fmt.lean
(the assembled lookup, its rows filed as a family of fixed size), Cb/Req1/LdSegRefPsc.lean (a block
at the base as a move), Cb/Req1/LdSegClose.lean (`ldStepF`: a step that only maps the explicit
part), Cb/Req1/LdSegFront.lean (`frInS`: the stage at which the front's first block starts).

The data (`LdPreD E Kc S E₀ Wp`). The oracle messages S, the further oracles E₀ and the further
witness Wp of the stage are parameters of the structure, not fields: so that a list built here meets
another file's list at a stage that both see (two stages are the same term only if their parts are).
Fields: the states St of the stage. msg: how the entries J are read off the messages (any function:
virtual cells among them).
    P: the 2^g functions with their keys (functions of state and entries, never sent), tables and
      tags. Rr: whatever else is claimed: it rides along.
    A0 : LkAsm2 E gives the lookup's numbers (v', d, w, n), the entries J, the places of the bits
      and of all own masks. Its fields St, key, tab are not read: the lookup that runs is `F.A`:
      states (state, shift θ), the joint keys and the joint table at θ.
    N, ι: names for the entries that rows and mask form may read. Mu: the lookup's exact clause on
      the multiplicities.
    Z, R0z, msg0, e: the step into a sumcheck that follows (the zerocheck), what rides beside it,
      and the map e of the explicit part into its states.
The four moves (`F.prog`):
    sub: the verifier draws the shift θ from all of E (one round). F.s0 → F.s1.
    step: the one lookup claim in the terms of the lookup; on the honest side the clause Mu (no
      round). F.s1 → F.s2.
    sub: the assembled lookup, one link (its rounds). F.s2 → F.s3.
    step: the explicit part is mapped by e (no round). F.s3 → frInS Kc Z S E₀ Wp R0z msg0.
  All steps are total maps of the explicit part; nothing is filed as a list (the rows are a family
  `Fin A0.nRows → Row`, `FX`); no step rejects.
The conditions, named (`F.OK p`): the tags differ; the numbers fit (g + v = v' + 1, g + d = the
lookup's d); muFrom: what rides along on the honest side, with the joint lookup claim
(`F.PS.outC`), gives Mu at every shift; ι injective, all named places in its range; the lookup's
conditions on numbers; H.MuOn Mu; last: four clauses at the base joints for the map e.

Main names (p: the characteristic of E, in the first and the fourth):
  `Spec.ldSegRef_pre_hyp`: `F.OK p` ⇒ `F.prog.Hyp`.
  `Spec.ldSegRef_pre_kinds`: the kinds are those that a body may hold.
  `Spec.ldSegRef_pre_rounds`: the number of rounds `F.prog.nAll` is 1 + the lookup's rounds.
  `Spec.ldSegRef_pre_zk`: `F.prog.Zk base`, from `F.OK p`, the masked bundle of the lookup's link,
    and: its fact is fresh at the start.
  `Spec.ldSegRef_pre_carry`: under `F.lkBk.SameOn F.msg Rd`: a fact that is fresh at the start and
    changes no entry that the lookup reads (no entry in Rd) (in this sense: the text of `ldQuiet`,
    Cb/Req1/LdSegFrontTabZk.lean) is fresh after the list.
  `Spec.ldSegRef_pre_fmt`: the list has the format (Cb/Req1/LdSegFormat.lean), if e hands on what is
    read off the state.

Limits: this file says nothing on the step from a segment's entry stage to `F.s0` (the caller's). It
does not say that the lookup's link has the masked bundle, or what it reads
(Cb/Req1/LdSegRefLkpPreZk.lean: `Spec.ldSegRef_preZk_goodM`, `baseF_sameOn`: each under its
hypotheses, for the letters `F.dm Rd C` and the entries in `A.srAll Dt`; the item "masked messages":
Cb/Ld/LdLkpMask*.lean). It does not say that `F.OK` can be met (it is met at the toy of
Cb/GlVal/GlJ3SegFrontToy.lean: `preOK`, Cb/GlVal/GlJ3SegFrontToyProofs.lean).
The order of the moves restates a write-up of ours in our own words (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpShift
import Cb.Req1.LdSegFront
import Cb.Req1.LdSegFormatMoves
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

/-- The data. -/
structure LdPreD (E Kc : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) :
    Type 1 where
  St : Type
  /-- numbers, entries and places of the lookup; its fields St, key, tab are not read -/
  A0 : LkAsm2 E
  msg : S.Msg → A0.J → E
  /-- the functions with their keys, tables and tags -/
  P  : ShiftP E St (A0.J → E)
  Rr : Rels Kc St E₀ (S.Msg × Wp)
  N  : Type
  [finN : Fintype N]
  ι  : N → A0.J
  Mu : St × E → (A0.J → E) → Prop
  /-- what follows -/
  Z    : PscIn E
  R0z  : Rels Kc Z.St0 E₀ (S.Msg × Wp)
  msg0 : S.Msg → Z.T.J → E
  e    : FX (St × E) E N A0.nRows → Z.St0

attribute [instance] LdPreD.finN

namespace LdPreD
variable {E Kc : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp : Type} (F : LdPreD E Kc S E₀ Wp)

/-- The lookup that runs: states (state, θ); the joint keys and the joint table at θ. -/
def A : LkAsm2 E :=
  { F.A0 with
    St := F.St × E, key := fun x m => shKey F.P.v (F.P.key x.1 m) F.P.tag x.2,
    tab := fun x => shTab F.P.d (F.P.tab x.1) F.P.tag x.2 }

/-- the functions, read off the messages -/
def PS : ShiftP E F.St S.Msg :=
  ⟨F.P.g, F.P.v, F.P.d, fun st ms => F.P.key st (F.msg ms), F.P.tab, F.P.tag⟩

/-- what rides along, read at an explicit part that holds the shift -/
def R1 : Rels Kc (F.St × E) E₀ (S.Msg × Wp) :=
  ⟨fun x y w => F.Rr.rel x.1 y w, fun a w => F.Rr.relR (a.1.1, a.2) w,
    fun a => F.Rr.on (a.1.1, a.2), F.Rr.core⟩

/-- the base joints of the lookup -/
@[reducible] def jS : Rels Kc (F.St × E) E₀ (S.Msg × Wp) :=
  cj F.R1 F.msg id (F.A.lk.inP F.Mu) F.A.lk.inR
@[reducible] def jT : Rels Kc (FX (F.St × E) E F.N F.A0.nRows) E₀ (S.Msg × Wp) :=
  cj F.R1 F.msg Prod.fst (F.A.lk.outF id (F.A.entN F.ι)) (F.A.lk.outF id (F.A.entN F.ι))

/-- The stages. -/
@[reducible] def s0 : LdStage E Kc := ⟨S, F.St, E₀, Wp, F.PS.jIn F.Rr⟩
@[reducible] def s1 : LdStage E Kc := ⟨S, F.St × E, E₀, Wp, F.PS.jOut F.Rr⟩
@[reducible] def s2 : LdStage E Kc := ⟨S, F.St × E, E₀, Wp, F.jS⟩
@[reducible] def s3 : LdStage E Kc := ⟨S, FX (F.St × E) E F.N F.A0.nRows, E₀, Wp, F.jT⟩
@[reducible] def s4 : LdStage E Kc := frInS Kc F.Z S E₀ Wp F.R0z F.msg0

/-- the shift and the lookup, at the base -/
def shBk : BkA Kc S.Msg F.St (F.St × E) E₀ Wp :=
  ⟨IOR.draw E Prod.mk E₀,
    Honest.draw E Prod.mk E₀ (S.Msg × Wp),
    Nums.draw Kc E Prod.mk E₀ (2 ^ (F.P.g + F.P.d))⟩
def lkBk : BkA Kc S.Msg (F.St × E) (FX (F.St × E) E F.N F.A0.nRows) E₀ Wp :=
  F.A.baseF F.ι E₀ S.Msg Wp Kc F.msg

/-- The four moves. -/
def m1 : LdMv F.s0 F.s1 := F.s0.mvA (F.PS.jOut F.Rr) F.shBk
def m2 : LdMv F.s1 F.s2 := ldStepF S (F.PS.jOut F.Rr) F.jS id
def m3 : LdMv F.s2 F.s3 := F.s2.mvA F.jT F.lkBk
def m4 : LdMv F.s3 F.s4 := ldStepF S F.jT (F.Z.relsIn F.R0z F.msg0) F.e

/-- The list. -/
def prog : LdProg F.s0 F.s4 :=
  ((((LdProg.nil F.s0).snoc F.m1).snoc F.m2).snoc F.m3).snoc F.m4

/-- What is asked of the data. -/
structure OK (p : ℕ) : Prop where
  tags   : TagInj F.P.g F.P.tag
  numV   : F.P.g + F.P.v = F.A0.v' + 1
  numD   : F.P.g + F.P.d = F.A0.d
  muFrom : ∀ (x : F.St × E) y w, F.Rr.rel x.1 y w → F.PS.outC x w.1 → F.Mu x (F.msg w.1)
  inj    : Function.Injective F.ι
  places : F.A.PlacesIn fun j => j ∈ Set.range F.ι
  adm    : F.A.H.lkb.Adm p
  muOK   : F.A.H.MuOn F.Mu
  lastFw : ∀ x y w, F.jT.rel x y w → (F.Z.relsIn F.R0z F.msg0).rel (F.e x) y w
  lastOn : ∀ x y, F.jT.on (x, y) → (F.Z.relsIn F.R0z F.msg0).on (F.e x, y)
  lastCo : ∀ w, (F.Z.relsIn F.R0z F.msg0).core w = F.jT.core w
  lastBw : ∀ x y w,
    F.jT.on (x, y) → (F.Z.relsIn F.R0z F.msg0).relR (F.e x, y) w → F.jT.relR (x, y) w

end LdPreD

namespace Spec
variable (E : Type) [Field E] [Fintype E]

def ldSegRef_pre_hyp : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (S : Sig E) (E₀ : ExtSpec)
      (Wp : Type) (F : LdPreD E Kc S E₀ Wp),
    F.OK p → F.prog.Hyp

def ldSegRef_pre_kinds : Prop :=
  ∀ (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (F : LdPreD E Kc S E₀ Wp),
    F.prog.All fun t => t = .send ∨ t = .sub ∨ t = .step

def ldSegRef_pre_rounds : Prop :=
  ∀ (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (F : LdPreD E Kc S E₀ Wp),
    F.prog.nAll = 1 + F.lkBk.R.shape.nAll

def ldSegRef_pre_zk : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (F : LdPreD E Kc S E₀ Wp)
      (base : MaskFact F.s0.J.W → Prop) (D : MaskData (F.s2.linkA F.jT F.lkBk).R F.s2.J.W),
    F.OK p → (F.s2.linkA F.jT F.lkBk).GoodM D → base D.fact → F.prog.Zk base

def ldSegRef_pre_carry : Prop :=
  ∀ (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (F : LdPreD E Kc S E₀ Wp) (Rd : F.A0.J → Prop),
    F.lkBk.SameOn F.msg Rd →
    ∀ (base : MaskFact F.s0.J.W → Prop) (f : MaskFact F.s0.J.W),
      (∀ w w' m,
        f.kc w' = f.put m (f.kc w) → ∀ j, Rd j → F.msg (S.msgs w'.1) j = F.msg (S.msgs w.1) j) →
      base f → F.prog.After base f

def ldSegRef_pre_fmt : Prop :=
  ∀ (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (F : LdPreD E Kc S E₀ Wp)
      (E0 : ExtSpec) (Rc Pw : Type) (i : IxAt E0 E₀) (rc : F.St → Rc) (rc' : F.Z.St0 → Rc)
      (px : Wp → Pw) (q : Finset F.s0.Ex.Pos → Prop),
    (∀ x, rc' (F.e x) = rc x.1.1) → F.prog.Fmt (F.s0.fmt i rc px q) (F.s4.fmt i rc' px q)

end Spec
end Cb
