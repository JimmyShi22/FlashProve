-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyReqEnd.lean: a small test instance of the last steps of a request's part of the
protocol: one linear claim on the index's matrix that is still open (a pending tensor row) is
batched, and the data of the test that follows are read off the result. What these last three steps
ask (`lastP.Hyp`; `LdMv.Hyp`, Cb/Req1/LdSeg.lean) is proved for it.

Definitions, statement (`Cb.Gl.Spec.gl_ldORE_toy`) and proof (an assembly). A guard against empty
theorems; no parameter of a protocol.
It builds on Cb/Obj/LdObjectReqEnd.lean (`LdORE`: one record for the end of a request and the test
that follows; `R.O`, the test's data, read off the final batching's last claim) and
Cb/GlVal/GlToyConf.lean (the toy configuration with two different fields, for every index set Mo).
Here F is the integers modulo p = 2^64 - 2^32 + 1 (entries of index messages, the codes' own field),
E is F[x] / (x^3 - 2) (all that is read: claims, masks, points, challenges). The analogue over one
field with 101 elements: Cb/Obj/LdObjectReqEndToy.lean. Of its clauses none needs F = E.

What is fixed here (the index's side, as in the toy of weights-formedness, Cb/Ld/LdWfToy.lean). The
matrix of the index: one row, two columns (one column variable, which names the code row; none
inside a row): the two entries of the index; defined by the equation that `R.Tie` is: the entries of
the index message lie in F and are read over E (`Cf.upM`). One pending tensor row, so one
coefficient, which is 1, and no seed. Degree 2: the batching has 3 own mask entries.
What is a parameter:
  `ReToy.Rq Mo Kc`: what the request's earlier moves leave: the oracle messages S; the rows that
    stay open; the state with its record; row factor and point of the pending row; its mask form as
    coefficients on names laid at fixed entries; the places of the batching's 3 own entries; the
    entries that the batching reads; the ghost and the core.
  `ReToy.Ln Mo`: what the test that follows needs beside (l and py of the layout, radius, locations,
    three families).
  `q.PlOK`: the one condition, on places: the batching's own places are different entries, read by
    the batching; the names' places are read by it too; no own place is a name's place.

Main names:
  `Spec.gl_ldORE_toy`, for every Mo, Kc, q, n:
    `R.Tie`;
    all that the last three moves ask (`R.lastP.Hyp`), nothing assumed beside whatever the arguments
      hold as proofs;
    3 rounds, nothing withheld (`lastP.nAll = 3`, `lastP.pBad = 0`, `lastP.pHid = 0`);
    under `q.PlOK`: the conditions on the batching's own entries (`X.Own`), and, for every `base`,
      what zero knowledge asks of the three moves, beside their hypotheses
      (`(R q n).lastP.Zk base`), from "the batching's fact is fresh before it";
    at all states the mask part of `R.O` is a linear form in the entries that is 0 off the places
      `wAt`, `μAt`;
    "more" of `R.O` says: the rows of the fixed family hold.
  `ReToy.one M`: an instance of the places: the request leaves one oracle message, whose entries
    hold the 3 own entries and one name; `Spec.gl_ldORE_toy_one`: if `pl` is injective, its `q.PlOK`
    holds.
  `ReToy.mW`, `ReToy.mU`, `ReToy.mO`, `ReToy.n84`: the families of the test that follows, standard
    oracle messages under the code that hides 3 long positions (Cb/GlVal/GlToyBase4.lean). Over the
    field with 101 elements these are in Cb/Obj/LdObjectPartBatRe.lean.

Limits: this file says nothing on the moves in front (first sending, ghost step, segment): they end
at `(R q n).X.src`. It does not say that the batching's fact is fresh there. It says nothing on the
size of errors.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndProofs
import Cb.GlVal.GlToyConf
import Cb.GlVal.GlToyBase4

set_option autoImplicit false

namespace Cb.Gl
namespace ReToy
open Iop Prob Hiop Blocks Cb.Ood IOR

noncomputable section

/-- The names of the coefficients of the batching's hiding polynomial. -/
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube E 2))

/-- What the request's earlier moves leave: a parameter. -/
structure Rq (Mo : ToyMo8) (Kc : Type) : Type 1 where
  S   : Sig E
  Bn  : Type
  Sb  : Bn → Type
  sl  : ∀ b, Slf E (Sb b) S.Ent
  St  : Type
  rc  : St → (toyCf8 Mo).conf.Rec
  g   : St → E
  pt  : St → E
  Nm  : Type
  [finNm : Fintype Nm]
  mf  : St → Nm → E
  μAt : Nm → S.Ent
  wAt : WBt → S.Ent
  Rd  : S.Ent → Prop
  G    : Type
  core : ((toyCf8 Mo).conf.Msg × S.Msg) × G → Kc

attribute [instance] Rq.finNm

/-- The condition on places. -/
structure Rq.PlOK {Mo : ToyMo8} {Kc : Type} (q : Rq Mo Kc) : Prop where
  inj : Function.Injective q.wAt
  own : ∀ i, q.Rd (q.wAt i)
  rdM : ∀ a, q.Rd (q.μAt a)
  wM  : ∀ i a, q.wAt i ≠ q.μAt a

/-- What the test that follows needs beside: a parameter. -/
structure Ln (Mo : ToyMo8) : Type 1 where
  l   : ℕ
  py  : Unit → Fin l → Bool
  e' : ℕ
  t  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin (toyCf8 Mo).X.v ⊕ Fin 0) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin (toyCf8 Mo).C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Unit → (NO.om iO).C.J

/-- The end of the toy request and the test that follows. -/
@[reducible] def R {Mo : ToyMo8} {Kc : Type} (q : Rq Mo Kc) (n : Ln Mo) : LdORE F E Kc where
  Cf := toyCf8 Mo
  S := q.S
  Bn := q.Bn
  Sb := q.Sb
  sl := q.sl
  Rw := Unit
  k := 1
  mat := fun U a => (toyCf8 Mo).upM U (a.2, Sum.inl ())
  St := q.St
  rc := q.rc
  Q := Unit
  g := fun st _ _ => q.g st
  pt := fun st _ _ => q.pt st
  Nm := q.Nm
  mf := fun st _ => q.mf st
  μAt := q.μAt
  Z := Evader.one E
  n := 2
  wAt := q.wAt
  Rd := q.Rd
  G := q.G
  core := q.core
  klo := 0
  e := (Equiv.sumEmpty (Fin 1) (Fin 0)).symm
  l := n.l
  lay := fun _ => ()
  py := n.py
  e' := n.e'
  t := n.t
  NW := n.NW
  SdW := n.SdW
  iW := n.iW
  lW := n.lW
  NU := n.NU
  SdU := n.SdU
  iU := n.iU
  lU := n.lU
  NO := n.NO
  SdO := n.SdO
  iO := n.iO
  lO := n.lO

/-- An instance of the places: one oracle message M is left; pl lays the 3 own entries and one name
at entries of its message. -/
@[reducible] def one (Mo : ToyMo8) (M : OMsg E) (pl : WBt ⊕ Unit → M.C.J) : Rq Mo Unit where
  S := Sig.one M
  Bn := Empty
  Sb := fun _ => Unit
  sl := fun b => b.elim
  St := (toyCf8 Mo).conf.Rec × (E × E × E)
  rc := fun st => st.1
  g := fun st => st.2.1
  pt := fun st => st.2.2.1
  Nm := Unit
  mf := fun st _ => st.2.2.2
  μAt := fun a => ⟨(), pl (Sum.inr a)⟩
  wAt := fun i => ⟨(), pl (Sum.inl i)⟩
  Rd := fun _ => True
  G := Unit
  core := fun _ => ()

/-- The three standard oracle messages of the test that follows, under the code that hides 3 long
positions. -/
@[reducible] def mW (Mo : ToyMo8) : StdM E P84 :=
  toyStd84 ((Fin (toyCf8 Mo).X.v ⊕ Fin 0) → Bool) (Fin (toyCf8 Mo).X.v ⊕ Fin 0) id
@[reducible] def mU : StdM E P84 := toyStd84 (Fin C8.k) (Fin 2) plcK8
@[reducible] def mO : StdM E P84 := toyStd84 Unit Empty fun _ e => e.elim

/-- The test's families. -/
@[reducible] def n84 (Mo : ToyMo8) : Ln Mo where
  l := 0
  py := fun _ i => i.elim0
  e' := 1
  t := 1
  NW := Sig.one (mW Mo).om
  SdW := Sig.Seeds.indep _
  iW := ()
  lW := fun c => (mW Mo).place (Sum.inl c)
  NU := Sig.one mU.om
  SdU := Sig.Seeds.indep _
  iU := ()
  lU := fun k => mU.place (Sum.inl k)
  NO := Sig.one mO.om
  SdO := Sig.Seeds.indep _
  iO := ()
  lO := fun y => mO.place (Sum.inl y)

end
end ReToy

namespace Spec
open Iop Hiop IOR ReToy

/-- The end of the toy request. -/
def gl_ldORE_toy : Prop :=
  ∀ (Mo : ToyMo8) (Kc : Type) (q : Rq Mo Kc) (n : Ln Mo),
    (R q n).Tie ∧ (R q n).lastP.Hyp ∧
    ((R q n).lastP.nAll = 3 ∧ (R q n).lastP.pBad = 0 ∧ (R q n).lastP.pHid = 0) ∧
    (q.PlOK → (R q n).X.Own ∧
        ∀ base : MaskFact (R q n).X.src.J.W → Prop,
          (R q n).X.stepIn.After base (R q n).X.mask.fact → (R q n).lastP.Zk base) ∧
    ((∀ z m, (R q n).O.restM z m = ∑ a, (R q n).restC z a * q.S.ents m a) ∧
      ∀ z a, (∀ i, a ≠ q.wAt i) → (∀ b, a ≠ q.μAt b) → (R q n).restC z a = 0) ∧
    ∀ z m, (R q n).O.more z m ↔ Slf.All q.sl ((R q n).X.stOf z).1 (q.S.ents m)

def gl_ldORE_toy_one : Prop :=
  ∀ (Mo : ToyMo8) (M : OMsg E) (pl : WBt ⊕ Unit → M.C.J), Function.Injective pl → (one Mo M pl).PlOK

end Spec

open Iop Hiop IOR ReToy in
theorem gl_ldORE_toy : Spec.gl_ldORE_toy := by
  intro Mo Kc q n
  have hT : (R q n).Tie := fun _ _ _ => rfl
  have hZ : (R q n).Z.OK := ldZero_ok_one E
  obtain ⟨-, k1, k2, k3⟩ := ldORE_kinds F E Kc (R q n)
  refine ⟨hT, ldORE_hyp F E Kc (R q n) (le_refl 2) hZ hT, ⟨k1, k2, k3⟩, fun h => ?_,
    ldORE_rest F E Kc (R q n), ldORE_more F E Kc (R q n)⟩
  have hO : (R q n).X.Own := ⟨h.inj, h.own, h.rdM, h.wM⟩
  exact ⟨hO, fun base hb => ldORE_zk F E Kc (R q n) base (le_refl 2) hZ hO hb⟩

open ReToy in
theorem gl_ldORE_toy_one : Spec.gl_ldORE_toy_one := fun _ _ _ h =>
  { inj := fun _ _ e => Sum.inl_injective (h (eq_of_heq (Sigma.mk.inj e).2))
    own := fun _ => trivial
    rdM := fun _ => trivial
    wM := fun _ _ e => Sum.inl_ne_inr (h (eq_of_heq (Sigma.mk.inj e).2)) }

end Cb.Gl
