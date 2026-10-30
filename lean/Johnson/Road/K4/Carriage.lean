-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Carriage.lean: FROM THE LIBRARY's KNOWLEDGE SOUNDNESS OF A TYPED CHAIN TO THE PLAIN
LAW OF A PIECE OVER WRITTEN ROUNDS, the committed messages outside the game; and the same at the
value of Johnson/Road/K4/Value.lean. Two records of premises, a definition and three theorems.
Bookkeeping: no count is made here and no protocol is read.

Why. The law of the layers' own rounds (the kind K4) is wanted in the form "for each tuple m of
pinned messages the piece's reduction `Leads` to: the promise behind holds, and for every world
whose pinned part is m, what the row opens gives what it closes" (`K04LawAt`,
Johnson/Desc/Plain/K04Plain.lean). The library has the count for the typed chain
(`FullPar.own_knowAt`, Cb/Pv/Lay/At/OwnW.lean). This file says what must be shown to pass from the
second to the first, one field for each thing, so that each can be proved apart.

  `Ties R v A B pc Mp fa part rest on on' Fr Bh`: five premises on a piece pc, a typed reduction R
    whose verifier puts out v, maps Mp from the piece's written rounds to R's, and a reading fa of
    statements. `front_on`: the promise in front gives R's. At every yes of the piece:
    `work`: the tests of work of the rounds that are read pass; `kept`: the promise behind holds;
    `last`: what the row opens (Bh) gives R's relation behind, at what R's verifier puts out on the
    transcript's image; `first`: with Bh, R's relation in front gives what the row closes (Fr).
  `leads_of_ties`: `KnowAt` of R, v is R's output, the maps are as asked, the piece's errors bear
    the carried ones, and `Ties`: the plain law, for each m.
  `noJoint`: the joint that says nothing. `Plan4.pickIs`: at the value the batched sumcheck's pick
    is the library's lawful one, so the chain's verifier refuses nothing.
  `Plan4.Tied`: `Ties` at the value's chain, written out: `last` asks the chain's last claim
    (`Ch.Last`), `first` starts from what is claimed before the first round (`pT`: `own_pT`).
  `Plan4.leads`: the plain law at the value, from `Plan4.Tied`.

Limits. `Ties` and `Plan4.Tied` ARE PREMISES: NOTHING HERE SHOWS THAT THEY CAN BE MET AT K4's BLOCK
OR AT ANY BLOCK. At a promise `on` that holds of nothing, or a piece that refuses all, all is true
and empty. The errors are the piece's own letter: that they are small is not said. The value's
letters are tied to no plan (Value.lean's limits). A sub-proof that is not the first alone. As a
statement of soundness the conclusion says no more than `own_knowAt`.
It leans on Johnson/Desc/Plain/Carry.lean (`leads_carryS`) and FromKnowAt.lean
(`leadsAt_of_knowAt`).
-/
import Johnson.Desc.Plain.Carry
import Johnson.Desc.Plain.FromKnowAt
import Johnson.Desc.Sound.ChainRule
import OnBytes.Flat.CarrySMaps
import Cb.Pv.Lay.OwnTot
import Johnson.Road.K4.Value

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop TWhole TWhole.G9 OnBytes.Flat OnBytes.Maker Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open Inst.Model (Scl)

section General
variable {Kc X Xo Wp Mm S Cl Wt : Type} {Ei Eo : ExtSpec} {F : Frame}

/-- What ties a piece over written rounds to a typed reduction. -/
structure Ties (R : IOR X Ei Xo Eo) (v : X × Ei.Str → Tr R.shape → Xo × Eo.Str)
    (A : IOR.Rels Kc X Ei (Mm × Wp)) (B : IOR.Rels Kc Xo Eo (Mm × Wp))
    (pc : Piece (ckP .two) F S Cl Wt) (Mp : Maps pc.ds R.shape)
    (fa : S × F.E.Str → X × Ei.Str) (part : Wt → Mm) (rest : Wt → Wp)
    (on on' : S × F.E.Str → Prop) (Fr Bh : S × F.E.Str → Wt → Prop) : Prop where
  /-- the promise in front gives the typed reduction's -/
  front_on : ∀ a, on a → A.on (fa a)
  /-- at a yes the tests of work of the rounds that are read pass -/
  work : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b, on a → pc.ior.red.out a τ = some b →
    Mp.pass τ = true
  /-- at a yes the promise behind holds -/
  kept : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b, on a → pc.ior.red.out a τ = some b → on' b
  /-- at a yes, what the row opens gives the typed relation behind -/
  last : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b w, on a → pc.ior.red.out a τ = some b → Bh b w →
    B.relR (v (fa a) (Mp.view τ)) (part w, rest w)
  /-- at a yes, with what the row opens, the typed relation in front gives what the row closes -/
  first : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b w, on a → pc.ior.red.out a τ = some b → Bh b w →
    A.relR (fa a) (part w, rest w) → Fr a w

/-- **From the typed reduction's knowledge soundness to the piece's plain law**, the messages m
outside the game. -/
theorem leads_of_ties {R : IOR X Ei Xo Eo} {v : X × Ei.Str → Tr R.shape → Xo × Eo.Str}
    {A : IOR.Rels Kc X Ei (Mm × Wp)} {B : IOR.Rels Kc Xo Eo (Mm × Wp)} {ε : Err R.shape}
    {pc : Piece (ckP .two) F S Cl Wt} {Mp : Maps pc.ds R.shape}
    {fa : S × F.E.Str → X × Ei.Str} {part : Wt → Mm} {rest : Wt → Wp}
    {on on' : S × F.E.Str → Prop} {Fr Bh : S × F.E.Str → Wt → Prop}
    (hk : KnowAt R A B (fun _ _ _ wp => wp) ε) (hv : Tot R.red v) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ε) pc.err) (T : Ties R v A B pc Mp fa part rest on on' Fr Bh) (m : Mm) :
    pc.ior.red.Leads on (fun a b => on' b ∧ ∀ w, part w = m → Bh b w → Fr a w) pc.err :=
  Reduction.Leads.mono_err
    (leads_carryS pc.ior.red R.red (fun _ => Mp.carry) ε (Mp.err ε) (fun _ => Mp.fits hOK ε) fa on
      A.on (fun a b => on' b ∧ ∀ w, part w = m → Bh b w → Fr a w)
      (fun a b => B.on b ∧ ∀ w : Mm × Wp, w.1 = m → B.relR b w → A.relR a w) T.front_on
      (fun a τ b ha hb => ⟨Mp.view τ, v (fa a) (Mp.view τ), Mp.tr_of_pass τ (T.work a τ b ha hb),
        hv _ _, fun hQ => ⟨T.kept a τ b ha hb, fun w hw hB =>
          T.first a τ b w ha hb hB (hQ.2 (part w, rest w) hw (T.last a τ b w ha hb hB))⟩⟩)
      (VerifiableInference.Desc.Plain.leadsAt_of_knowAt hk m)) herr

end General

/-- The joint that says nothing. -/
def noJoint (Ex : ExtSpec) (Mm : Type) : IOR.Rels Unit Unit Ex (Mm × Unit) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

section AtTheValue
variable [scl : Scl] {Mm X S Cl Wt : Type} {F : Frame}

/-- At the value the batched sumcheck's pick is the library's lawful one. -/
theorem Plan4.pickIs (Q : Plan4 Cb.Gl.E Mm X) : Q.full.own.PickIs := rfl

/-- `Ties` at the value's chain, written out. -/
structure Plan4.Tied (Q : Plan4 Cb.Gl.E Mm X) (Ex : ExtSpec) (pc : Piece (ckP .two) F S Cl Wt)
    (Mp : Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape) (fa : S × F.E.Str → X × Ex.Str)
    (part : Wt → Mm) (on on' : S × F.E.Str → Prop) (Fr Bh : S × F.E.Str → Wt → Prop) : Prop where
  /-- at a yes the tests of work of the rounds that are read pass -/
  work : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b, on a → pc.ior.red.out a τ = some b →
    Mp.pass τ = true
  /-- at a yes the promise behind holds -/
  kept : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b, on a → pc.ior.red.out a τ = some b → on' b
  /-- at a yes, what the row opens gives the chain's last claim, at the chain's own output on the
  transcript's image -/
  last : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b w, on a → pc.ior.red.out a τ = some b → Bh b w →
    Q.full.own.toOwn.ch.Last (fun _ _ => True)
      (Q.full.own.toOwn.ch.val Ex (fa a) (Mp.view τ)).1 (part w)
  /-- at a yes, with what the row opens, what is claimed before the chain's first round gives what
  the row closes -/
  first : ∀ a (τ : Tr (uLT (ckP .two) pc.ds)) b w, on a → pc.ior.red.out a τ = some b → Bh b w →
    Q.full.own.pT (fa a).1 (part w) → Fr a w

/-- **The plain law at the value**, the messages m outside the game. -/
theorem Plan4.leads (Q : Plan4 Cb.Gl.E Mm X) (Ex : ExtSpec) {pc : Piece (ckP .two) F S Cl Wt}
    {Mp : Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape} {fa : S × F.E.Str → X × Ex.Str}
    {part : Wt → Mm} {on on' : S × F.E.Str → Prop} {Fr Bh : S × F.E.Str → Wt → Prop}
    (hOK : Mp.OK) (herr : Err.le (Mp.err (Q.full.own.toOwn.ch.eps Ex)) pc.err)
    (T : Q.Tied Ex pc Mp fa part on on' Fr Bh) (m : Mm) :
    pc.ior.red.Leads on (fun a b => on' b ∧ ∀ w, part w = m → Bh b w → Fr a w) pc.err :=
  leads_of_ties (rest := fun _ => ())
    (Q.full.own_knowAt Ex (noJoint Ex Mm) (fun _ => ()) (fun _ _ => True))
    (Q.full.own.tot Q.pickIs Ex) hOK herr
    { front_on := fun _ _ => trivial
      work := T.work
      kept := T.kept
      last := fun a τ b w ha hb hB => ⟨trivial, T.last a τ b w ha hb hB⟩
      first := fun a τ b w ha hb hB h => T.first a τ b w ha hb hB h.2.2 } m

end AtTheValue
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.leads_of_ties
#print axioms OnBytes.Road.K4.Plan4.pickIs
#print axioms OnBytes.Road.K4.Plan4.leads
