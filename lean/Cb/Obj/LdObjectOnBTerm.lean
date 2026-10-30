-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBTerm.lean: the test for linear constraints on the encoded index at N instances,
over the configuration of Cb/Obj/LdObjectConf.lean: the term, and all that is used of it.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation. In a session it runs on a batch of at most N instances that share the encoded
index. This file builds the test for a batch as one term, with honest side, extractor and numbers,
from the test as a chain of reductions; the test's last part, the closing, stays a parameter. It
states under which conditions that term has both items of the object's list.

Definitions and statements (Cb.Spec.ldOnT_*); the proofs are in Cb/Obj/LdObjectOnBTermProofs.lean.
Cb/Obj/LdObjectOnB.lean requires a term `T : O.LinBT N` with `T.OK`, and gives from it, under the
other hypotheses of `Spec.ldOBT_object`, both items of the object's list. Here the term is made from
the test on chains (Cb/Ld/LdLinBHonTop.lean: `P.linCV`) at P := the test over a signature made from
O (Cb/Obj/LdObjectLinFull.lean: `O.toC.P`), after the step without rounds `O.enter`.
The closing is still a parameter: a chain cZ of links with annotations, batch errors and the honest
side of a batch, from the joint after ζ to the trivial statement.

Main names:
  `O.VIn`: the first joint for a batch: the shared witness is the prover encoded index with its
    record; the tie: the statement's index is its encoding, the slot's tables are its full
    messages, the slot's record is its record; the demand: at most t positions of the index through
    all slots, each slot's positions in the oracles left within `O.qaIn qa`.
  `O.termT`: the term: the budget is "no further reads";
    the bound on the withheld set is the closing's (`cZ.pWh`); at most `O.t` positions of the index;
    the bound on what the verifier reads: `O.P.q0 (O.qaIn qa)`.
  `Spec.ldOnT_same`: the term's link and reduction, in the forms of `O.fullB`
    (Cb/Ld/LdBatchBlocksObject.lean) and `O.full` (Cb/Obj/LdObjectLinFull.lean).
  `Spec.ldOnT_ok`: `T.OK`, for any condition on0 on the index that holds wherever the item speaks
    (`O.Fits on0`) and any bound εf on the fold's bad points under it, from: what the three sendings
    ask (`Sn.OK`, `Sn.Apart`), the layout's places are distinct (`Function.Injective O.py`), qa is
    kept by subsets, a value of `O.toC.P.Ea.Str`, and the closing's conditions
    (Cb/Ld/LdLinBHonTop.lean: `Spec.ldLinT_all`):
    behind the core and the budgets' half (one instance) (`OkFrom`, `SidesCT`);
    `KB` from the key after ζ, `O.toC.P.key6` (batch, sound);
    behind the core for sets of slots (`OkFromV`), coherent annotations (`Coh`), nothing follows
    (`∀ Jn, VT.q Jn fun _ => ∅`) (batch, honest).
  `Spec.ldOnT_object`: from these, `HasDist O.Cf.C₀.G O.Cf.C₀.d` and `O.Cf.eM < O.Cf.C₀.d`:
    `Hiop.LinBListR` ∧ `Hiop.LinBKnowR` of one term. `Spec.ldOnT_object_far`: the same in the second
    regime (the index decodes with its record; e' + eM below the distance) with no point bad for
    the fold.
  All four statements require that the index code has a position (`Nonempty (Fin O.Cf.C₀.n)`).

Limits: no closing is given. That the hypotheses can be met together is not said here.


Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectOnB
import Cb.Obj.LdObjectLinFull
import Cb.Ld.LdLinBHonTop
import Cb.Ld.LdStepV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

namespace LdOL
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) [Fintype F]
  [Fintype E] [Nonempty (Fin O.Cf.C₀.n)]

/-- what the test's shared part holds at the start, made from the prover encoded index p: the
encoded index as sent, the rows' full messages read over E, and the record -/
def shIn (p : O.Cf.conf.PIdx) : O.toC.P.Sh0 :=
  ((O.Cf.conf.enc p.1.1 p.1.2, fun r => Code.liftWord E (O.Cf.full p.1.1 p.1.2 r)), p.2)

variable (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop)
  (Sn : O.toC.P.Snd) (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ)

/-- The first joint for a batch. -/
def VIn : JV N (O.P.J0 on0) :=
  ⟨O.Cf.conf.PIdx,
    fun p (x : O.P.X0) (y : O.P.E0.Str) (w : O.P.W0) =>
      (y.1 = (O.shIn p).1.1 ∧ w.1 = (O.shIn p).1.2) ∧ x.2 = (O.shIn p).2,
    O.P.qv0 (O.qaIn qa) N⟩

/-- the step as a link -/
def lkE : Link Unit (O.P.J0 on0) (O.toC.P.J0 on0) :=
  ⟨O.enter, O.hEnter, fun _ _ w => (w.1, w.2.1), Nums.pure Unit some O.enG⟩

/-- the step as a link of a batch -/
def lvE : LinkV Unit N (O.VIn on0 qa N) (O.toC.P.V0 qa N on0) :=
  ⟨⟨O.lkE on0, PUnit.unit, ()⟩,
    stepV some O.enG (fun a => (a.1, (a.2.1, (a.2.2, ())))) O.shIn,
    fun _ _ _ => True⟩

variable {VT : JV N LdLinP.JT}
  (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0)

/-- The step, then the test. -/
def termV : LinkV Unit N (O.VIn on0 qa N) VT :=
  (O.lvE on0 qa N).seq (O.toC.P.linCV Sn qa N on0 εf cZ d) d₀

/-- The value: the term `T : O.LinBT N` that Cb/Obj/LdObjectOnB.lean requires. -/
def termT : O.LinBT N where
  R := (O.termV on0 Sn qa εf N cZ d d₀).a.l.R
  A := (O.termV on0 Sn qa εf N cZ d d₀).a.ann
  Wi := O.P.W0
  W0' := VT.W0
  Wo := Unit
  H := (O.termV on0 Sn qa εf N cZ d d₀).hv
  mkW := fun p a => O.fi (p, a)
  RiV := (O.VIn on0 qa N).rel
  RoV := VT.rel
  P := ⟨(O.termV on0 Sn qa εf N cZ d d₀).a.err, cZ.pWh, O.t, fun _ _ Ts => ∀ j, Ts j = ∅⟩
  on0 := on0
  ext := (O.termV on0 Sn qa εf N cZ d d₀).a.l.ext
  qi := O.P.q0 (O.qaIn qa)

end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States, if the index code has a position (`Nonempty (Fin O.Cf.C₀.n)`): the term's link and
reduction have the forms of `O.fullB` (Cb/Ld/LdBatchBlocksObject.lean) and `O.full`
(Cb/Obj/LdObjectLinFull.lean). -/
def ldOnT_same : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0),
    (O.termV on0 Sn qa εf N cZ d d₀).a =
      (⟨O.lkE on0, PUnit.unit, ()⟩ : LinkA Unit (O.P.J0 on0) (O.toC.P.J0 on0)).seq
        (O.toC.P.linCA on0 Sn εf N cZ.forget d) d₀ ∧
    (O.termT on0 Sn qa εf N cZ d d₀).R = O.enter.seq (O.toC.P.linC on0 Sn εf cZ.forget.forget d).R

/-- All that is used of the value (`LinBT.OK`). -/
def ldOnT_ok : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (kT : JKey LdLinP.JT) (d : O.toC.P.W0)
      (d₀ : O.P.W0) (_ : O.toC.P.Ea.Str),
    O.Fits on0 → O.toC.P.FoldErr on0 εf → Function.Injective O.py → Sn.OK → Sn.Apart →
    (∀ U V, V ⊆ U → qa U → qa V) → cZ.forget.forget.OkFrom (O.toC.P.chain on0 Sn εf) →
    cZ.forget.forget.SidesCT (O.toC.P.q5 Sn qa) → cZ.forget.KB N O.toC.P.key6 kT →
    cZ.OkFromV (O.toC.P.chainV Sn qa N on0 εf) → cZ.forget.Coh →
    (∀ Jn, VT.q Jn fun _ => ∅) → (O.termT on0 Sn qa εf N cZ d d₀).OK

/-- Both items of the object's list, of one term. -/
def ldOnT_object : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (kT : JKey LdLinP.JT) (d : O.toC.P.W0)
      (d₀ : O.P.W0) (_ : O.toC.P.Ea.Str) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.Fits on0 → O.toC.P.FoldErr on0 εf →
    Function.Injective O.py → Sn.OK → Sn.Apart → (∀ U V, V ⊆ U → qa U → qa V) →
    cZ.forget.forget.OkFrom (O.toC.P.chain on0 Sn εf) →
    cZ.forget.forget.SidesCT (O.toC.P.q5 Sn qa) → cZ.forget.KB N O.toC.P.key6 kT →
    cZ.OkFromV (O.toC.P.chainV Sn qa N on0 εf) → cZ.forget.Coh → (∀ Jn, VT.q Jn fun _ => ∅) →
    LinBListR O.left (O.termT on0 Sn qa εf N cZ d d₀).Q (O.termT on0 Sn qa εf N cZ d d₀).hQ
      N (O.termT on0 Sn qa εf N cZ d d₀).P ∧
    LinBKnowR O.left (O.termT on0 Sn qa εf N cZ d d₀).Q N d0 (O.termT on0 Sn qa εf N cZ d d₀).P.err

/-- The second regime: the index decodes with its record; no point is bad for the fold.
(not all hypotheses are named here: see the statement below) -/
def ldOnT_object_far : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (Sn : O.toC.P.Snd) (qa : Finset O.toC.P.Ea.Pos → Prop)
      (N : ℕ) (VT : JV N LdLinP.JT) (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT)
      (kT : JKey LdLinP.JT) (d : O.toC.P.W0) (d₀ : O.P.W0) (_ : O.toC.P.Ea.Str) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.e' + O.Cf.eM < O.Cf.C₀.d → Function.Injective O.py → Sn.OK →
    Sn.Apart → (∀ U V, V ⊆ U → qa U → qa V) → cZ.forget.forget.OkFrom (O.toC.P.chain O.onDec Sn 0) →
    cZ.forget.forget.SidesCT (O.toC.P.q5 Sn qa) → cZ.forget.KB N O.toC.P.key6 kT →
    cZ.OkFromV (O.toC.P.chainV Sn qa N O.onDec 0) → cZ.forget.Coh → (∀ Jn, VT.q Jn fun _ => ∅) →
    LinBListR O.left (O.termT O.onDec Sn qa 0 N cZ d d₀).Q (O.termT O.onDec Sn qa 0 N cZ d d₀).hQ
      N (O.termT O.onDec Sn qa 0 N cZ d d₀).P ∧
    LinBKnowR O.left (O.termT O.onDec Sn qa 0 N cZ d d₀).Q N d0
      (O.termT O.onDec Sn qa 0 N cZ d d₀).P.err

end
end Spec
end Cb
