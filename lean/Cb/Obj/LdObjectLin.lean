-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLin.lean: the test for linear constraints on the encoded index, one instance, over
the configuration of Cb/Obj/LdObjectConf.lean.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation, one of the four sub-protocols of the library's holographic interactive oracle
proof; there it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean). This file puts three
generic definitions together: a configuration made from a linear code (`LdCf`,
Cb/Obj/LdObjectConf.lean), the test for one instance (`LdLinP`, Cb/Ld/LdLin.lean), and what a
preamble leaves (`sigLeft`, Cb/Ld/LdWfClose.lean). It states that the test then has the two items of
the object, under the hypotheses told under "Main names".

Definitions and statements (Cb.Spec.ldOL_*); the proofs are in Cb/Obj/LdObjectLinProofs.lean.
The test is an interactive oracle reduction to the trivial statement for one claim ∑ g(y) eq(ψ, c)
M(y, c) + rest = τ (the tensor row; `LdLinW.Claim`, Cb/Ld/LdLinWords.lean) on the index matrix M
that is read off the encoded index's message.
The object is the holographic IOP (`SubsR.lhr`, Hiop/RecBuild.lean) that is built from four
sub-protocols.

Main names:
  `O : LdOL F E`: the data (among them `Cf`, `S`, `restM`, `more`).
  `O.P`: the test over the configuration: a symbol is a column over F, read over E by the algebra
    map.
  `Spec.ldOL_rel`, `Spec.ldOL_on`, `Spec.ldOL_relR`, `Spec.ldOL_reads`: four bridging facts, (a) to
    (d), at on0 := "no collision of the index at the record's seed" (the first regime of
    Cb/Ld/LdLin.lean).
  `Spec.ldOL_items`, `Spec.ldOL_lin`: if the index code has a position
    (`Nonempty (Fin O.Cf.C₀.n)`), under `HasDist O.Cf.C₀.G O.Cf.C₀.d` and
    `O.Cf.eM < O.Cf.C₀.d`, from a closing `Z : O.P.Closing` that is a tail of a chain (a hypothesis,
    as in Cb/Ld/LdLin.lean) and the hypotheses of `Spec.ldLin_tail` in the first regime, the two
    items of the object: `LinListR` and `LinKnowR` for the test `O.P.lin Z` over `O.Cf.conf` and
    `O.left` (by the generic rule of Cb/Obj/LdObjectTail.lean).
    The budget of the list is "no further read".
    `ldOL_lin`: the first regime's bound on the points that are bad for the fold put in, under the
    hypotheses of `Spec.ldLin_foldErr` (Cb/Ld/LdLin.lean).

Limits:
(1) The tensor row reads no pad, by type: the layout of the index matrix lands in J₀, the entries
that are no pads. (Whether it lands on Cf's layout of the index proper is not asked.)
(2) The item's extractor decodes the statement, as Hiop/RecSubs.lean asks; the chain's own
extractors go backwards and none of them decodes. Nothing is lost: the relaxed relation determines
its witness. Running times are not modelled.
(3) Two hypotheses on lists stand in this library for one thing. `Spec.ldOL_lin` asks a bound L at
the radius e' for every table over E (the convention of the text that we follow: lists and agreement
are those of the code over E). `Cf.OK` (Cb/Obj/LdObjectConf.lean) asks one at the radius eM for
tables over F. A bound at eM for every table over E would give both (e' ≤ eM; a table over F is a
table over E): said here, proved nowhere in this file; `ldCm_list_le`, `ldCm_list_F`
(Cb/Obj/LdObjectConfMore.lean) prove it from the hypothesis `Cf.ListOK L`.
(4) "more" is any predicate and restM any function of the messages: wider by type than rows and a
linear form.
No closing is given; no sender; no bound on a list or on agreement. One instance (the offline
setting); the batch is another file's. This file says nothing on the preamble that leaves S. It
does not say that the conditions can be met together.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinProofs
import Cb.Obj.LdObjectConfProofs
import Cb.Ld.LdWfCloseProofs
import Ior.KnowCollRulesFrameProofs
import Cb.Obj.LdObjectTail
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- The joint on the oracle messages of S alone (no further oracle beside them). Relaxed: by
decoding with a sample, and Pm. Condition: collision-free. -/
def Sig.alone {E : Type} [Field E] (S : Sig E) {Cl : Type} (Pm : Cl → S.Msg → Prop) :
    IOR.Rels Unit (Cl × S.Smp) S.ext S.Wit where
  rel  := fun x y w => S.Enc y w ∧ S.Ans x.2 (S.msgs w) ∧ Pm x.1 (S.msgs w)
  relR := fun a w => (∀ i, S.decs a.1.2 a.2 i = some (w i).1) ∧ Pm a.1.1 (S.msgs w)
  on   := fun a => S.CF a.1.2 a.2
  core := fun _ => ()

/-- The test over the configuration: the data. -/
structure LdOL (F E : Type) [Field F] [Field E] [Algebra F E] where
  Cf : LdCf F E
  /-- the oracle messages that the preamble leaves -/
  S  : Sig E
  /-- the claims proper -/
  Cl : Type
  /-- the layout of the index matrix -/
  Y   : Type
  [finY : Fintype Y]
  klo : ℕ
  l   : ℕ
  /-- where entry (y, j) of a code row's block stands: among the entries that are no pads -/
  lay : Y × (Fin klo → Bool) → Cf.J₀
  py  : Y → Fin l → Bool
  /-- the tensor row; a function and a further predicate on the messages of S -/
  g     : Cl → Y → E
  ψ     : Cl → (Fin Cf.X.v → E) × (Fin klo → E)
  τ     : Cl → E
  restM : Cl → S.Msg → E
  more  : Cl → S.Msg → Prop
  /-- the radius at which the fold is tested; the number of locations -/
  e' : ℕ
  t  : ℕ
  /-- the three families that the test sends -/
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Y → (NO.om iO).C.J

attribute [instance] LdOL.finY

namespace LdOL
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E)

/-- the index, its record, the layout -/
@[reducible] def D : LdLinW E (Fin O.Cf.C₀.n) (Fin O.Cf.C₀.k) O.Cf.J O.Y :=
  ⟨O.Cf.X, O.klo, O.l, fun a => Sum.inl (O.lay a), O.py⟩

/-- The test over the configuration. -/
@[reducible] def P : LdLinP E (Fin O.Cf.C₀.n) (Fin O.Cf.C₀.k) O.Cf.J O.Y where
  D := O.D
  Sy := O.Cf.Sg
  up := fun s r => algebraMap F E (s r)
  e' := O.e'
  t := O.t
  Ea := O.S.ext
  Xa := O.Cl × O.S.Smp
  Wa := O.S.Wit
  Aa := O.S.alone O.more
  g := fun x => O.g x.1
  ψ := fun x => O.ψ x.1
  τ := fun x => O.τ x.1
  rest := fun x w => O.restM x.1 (O.S.msgs w)
  NW := O.NW
  SdW := O.SdW
  iW := O.iW
  lW := O.lW
  NU := O.NU
  SdU := O.SdU
  iU := O.iU
  lU := O.lU
  NO := O.NO
  SdO := O.SdO
  iO := O.iO
  lO := O.lO

variable [Fintype F]

/-- When a claim holds of the message U of the encoded index and the messages m of S. -/
def holds : O.Cl → O.Cf.conf.Rec → O.Cf.conf.Msg → O.S.Msg → Prop := fun cl _ U m =>
  O.D.Claim (O.Cf.upM U) (O.g cl) (O.ψ cl) (O.restM cl m) (O.τ cl) ∧ O.more cl m

/-- What the preamble leaves. -/
@[reducible] def left : O.Cf.conf.Left := sigLeft O.Cf.conf O.S O.Cl O.holds

/-- the honest witness of the list, as a witness of the test -/
def fi (w : O.Cf.conf.PIdx × O.left.WAux) : O.P.W0 :=
  (fun r => Code.liftWord E (O.Cf.full w.1.1.1 w.1.1.2 r), O.S.pair w.2.1 w.2.2)

/-- the first regime: no collision of the index at the record's seed -/
def on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop := fun f rec =>
  ¬ O.Cf.X.Coll f rec.1

variable [Fintype E] [Nonempty (Fin O.Cf.C₀.n)]

/-- The test, its honest side and its numbers, in the list's types. -/
def lin (Z : O.P.Closing) : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone :=
  O.P.lin Z
def hLin (Sn : O.P.Snd) (Z : O.P.Closing) :
    (O.lin Z).Honest (O.Cf.conf.PIdx × O.left.WAux) Unit :=
  IOR.Honest.mapW (O.P.hLin Sn Z) O.fi fun _ o => o
def nums (Sn : O.P.Snd) (Z : O.P.Closing) (εf : ℕ) : LinNumsR (O.lin Z).shape :=
  ⟨(O.P.numsLin Sn Z εf).err, (O.P.numsLin Sn Z εf).pBad, O.t, fun _ T => T = ∅⟩

end LdOL

namespace Spec
open IOR
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: the types meet, by definition. -/
def ldOL_types : Prop :=
  ∀ (O : LdOL F E),
    O.P.X0 = (O.left.Xl × O.Cf.conf.Rec) ∧
    O.P.E0 = O.left.El ∧
    ∀ y : Fin O.Cf.C₀.n → O.Cf.Sg, O.P.tab y = O.Cf.tab y

/-- (a) States: the list's constraint relation gives the test's exact relation at `O.fi`. -/
def ldOL_rel : Prop :=
  ∀ (O : LdOL F E) (x : O.left.Xl × O.Cf.conf.Rec)
      (y : O.left.El.Str) (w : O.Cf.conf.PIdx × O.left.WAux),
    O.left.Rlin x y w → (O.P.j0 O.on0).rel x y (O.fi w)

/-- (b) States: a collision-free statement of the list is a statement of the test's condition, and
conversely. -/
def ldOL_on : Prop := ∀ (O : LdOL F E) (a : O.left.St), O.left.cond a ↔ (O.P.j0 O.on0).on a

/-- (c) States: if `HasDist O.Cf.C₀.G O.Cf.C₀.d` and `O.Cf.eM < O.Cf.C₀.d`, the test's relaxed
relation gives the list's, at the messages of the witness. -/
def ldOL_relR : Prop :=
  ∀ (O : LdOL F E), HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d →
    ∀ (a : O.left.St) (w : O.P.W0), (O.P.j0 O.on0).relR a w → O.left.RlinR a (O.S.msgs w.2)

open Classical in
/-- (d) States: a set of positions within the test's demand holds at most t positions of the encoded
index. -/
def ldOL_reads : Prop :=
  ∀ (O : LdOL F E) (qa : Finset O.P.Ea.Pos → Prop) (U : Finset O.P.E0.Pos),
    O.P.q0 qa U → (U.filter fun p => p.isLeft).card ≤ O.t

/-- The two items of the object: the list (all items but knowledge soundness), and round-by-round
knowledge soundness on all collision-free statements, the extractor decoding the statement. εf: any
bound on the points that are bad for the fold. (not all hypotheses are named here: see the statement
below) -/
def ldOL_items : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.P.Snd)
      (qa : Finset O.P.Ea.Pos → Prop) (Z : O.P.Closing) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.P.FoldErr O.on0 εf →
    Function.Injective O.py → Sn.OK → TailTr Z.T Z.H O.P.j6.cf trivRels Z.ext Z.N (O.P.q5 Sn qa) →
    LinListR O.left (O.lin Z) (O.hLin Sn Z) (O.nums Sn Z εf) ∧
    LinKnowR O.left (O.lin Z) d0 (O.nums Sn Z εf).err

/-- The two items, with the fold's error of the first regime put in. -/
def ldOL_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (bad L : ℕ) (Sn : O.P.Snd)
      (qa : Finset O.P.Ea.Pos → Prop) (Z : O.P.Closing) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → HasDist O.Cf.X.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d →
    O.e' ≤ O.Cf.eM → O.Cf.X.MCAeq O.e' bad →
    (∀ f : O.Cf.X.Row → Fin O.Cf.C₀.n → E, ListLE (DecodesTo O.Cf.X.G O.e' f) L) →
    Function.Injective O.py → Sn.OK → TailTr Z.T Z.H O.P.j6.cf trivRels Z.ext Z.N (O.P.q5 Sn qa) →
    LinListR O.left (O.lin Z) (O.hLin Sn Z)
      (O.nums Sn Z (bad + L * (O.Cf.X.v * Fintype.card E ^ (O.Cf.X.v - 1)))) ∧
    LinKnowR O.left (O.lin Z) d0
      (O.nums Sn Z (bad + L * (O.Cf.X.v * Fintype.card E ^ (O.Cf.X.v - 1)))).err

end
end Spec
end Cb
