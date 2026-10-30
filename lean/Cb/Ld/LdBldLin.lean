-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldLin.lean: this file gives data for two sub-protocols, the test for linear constraints on
the encoded index (Cb/Ld/LdLin.lean) and the link between two encoded indices (Cb/Ld/LdLink.lean),
namely which oracle messages the prover sends in them, and at which coordinates of these messages
the sub-protocols' vectors are, for variable data.

Definitions and statements; the proofs are in Cb/Ld/LdBldLinProofs.lean. Generic: any finite field F
and any finite field E that is an algebra over F; codes and numbers are parameters. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.
`Places` (Cb/Ld/LdLinStd.lean) says that the places lW, lU, lO of the test are the data entries of
the named members that qW, qU, qO name, and that pW, pU, pO send that data entry back to the
vector's entry. `Y.Reads ix rdv` (Cb/Ld/LdSendStdVec.lean) says that every entry c of the vector is
read by rdv at some data place (a, i) with ix a i = some c. `Sd.Fair` (`Sig.Seeds.Fair`) asks of the
joint seeds of a family: for each member a and each seed ρ of that member's sample map `(N.om a).Z`,
at most `Sd.mult a` joint seeds s have `Sd.sd a s = ρ`. In `Spec.bldLn_fair` and `Spec.bldLk_fair`
it is the conclusion.

Why: whoever builds the object with these terms has, from injectivity and one inequality, these
clauses of the records `Cb.Gl.Final` (Cb/Gl/GlFinal.lean) and `Cb.Gl.FinalPp`
(Cb/Gl/GlFinalPp.lean): plS, plB (`Places`); fW, fU, fO, fWB, fUB, fOB, fK (fair seeds); rdK
(`Reads`); and plInj of `LdObjD.Own3₀` (Cb/Obj/LdObjectDataRefJ.lean).

Main names:
  `BldLn E Col κ Y`, the linear test: three families FW, FU, FO; the named members iW, iU, iO; aW,
    aU, aO: at which data entry of its named member each entry of the vector is (w on the
    columns Col; the folded full message u on κ; ω on the rows Y); the fold's radius e' and the
    number t of locations. Every other data entry of every member holds 0; free entries and pads are
    the sender's coins. Further members are allowed (mask-only messages: all entries free).
  `P₀.bldStd L w0 w1 w3`: the data of the three standard senders (`P.Std E`, Cb/Ld/LdLinStd.lean:
    pads in E).
  `Spec.bldLn_places`: `L.Inj` ⇒ `(P₀.bldStd L w0 w1 w3).Places`. `Spec.bldLn_fair`: the three
    families' seeds are fair (`Seeds.Fair`, Cb/Ld/LdSendFam.lean).
  `Spec.bld_invS`: `invS f` undoes an injective f.
  `BldLk E κ`, the link: one family; the two named members i₀, i₁ and where u₀, u₁ are; l: the
    number of coordinates of its last point; radii and numbers of locations.
  `BldLk.Inj`: (u₀, u₁) ↦ data entries is injective as one map (the two members may be one message).
  `Cf.bldK L`: the link's parameters (`Cf.LinkPar`, Cb/Obj/LdObjectLink.lean); the layout's places
    are on the cube of l variables by binary numbering (`binC`).
  `Spec.bldLk_reads`: `L.Inj` ⇒ the layout reads (u₀, u₁) (`Y.Reads`, Cb/Ld/LdSendStdVec.lean).
    `Spec.bldLk_fair`: the family's seeds are fair. `Spec.bldLk_pl`: |Lay| ≤ 2^l ⇒ the places are
    different corners.

Notation: `w0`, `w1`, `w3`: fixed witnesses (fields of `P.Std E`, Cb/Ld/LdLinStd.lean), of the types
`W0`, `W1`, `W3` (Cb/Ld/LdLin.lean).

Limits: on samples the file has one thing: `Spec.bldLn_fair` and `Spec.bldLk_fair` conclude
`Seeds.Fair` (Cb/Ld/LdSendFam.lean), on the seeds of the members' sample maps; beyond it this file
says nothing on codes, lists, samples (Cb/Ld/LdBldMsg.lean). It says nothing
on the plan of whole tests behind the test, its groups, the entry at which a splitting's mask
stands. It does not say which members the technical report's prover messages have.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdBldMsg
import Cb.Ld.LdLinStd
import Cb.Ld.LdSendStdVec
import Cb.Obj.LdObjectWf
import Cb.Obj.LdObject
import Cb.Obj.LdObjectLink
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

open Classical in
/-- Which v a data entry holds, or none. -/
def invS {O V : Type} {D : O → Type} (f : V → Σ a, D a) : ∀ a, D a → Option V :=
  fun a i => if h : ∃ v, f v = ⟨a, i⟩ then some h.choose else none

/-- What the linear test needs beside the configuration and the claims: the data. -/
structure BldLn (E Col κ Y : Type) where
  FW : BldF E
  iW : FW.O
  aW : Col → {i : (FW.m iW).Ent // ¬ (FW.m iW).fr i.1}
  FU : BldF E
  iU : FU.O
  aU : κ → {i : (FU.m iU).Ent // ¬ (FU.m iU).fr i.1}
  FO : BldF E
  iO : FO.O
  aO : Y → {i : (FO.m iO).Ent // ¬ (FO.m iO).fr i.1}
  e' : ℕ
  t  : ℕ

/-- the three maps are injective -/
structure BldLn.Inj {E Col κ Y : Type} (L : BldLn E Col κ Y) : Prop where
  w : Function.Injective L.aW
  u : Function.Injective L.aU
  o : Function.Injective L.aO

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [DecidableEq E]

/-- The test's data with the families laid in. -/
@[reducible] def LdLinP.withBld (P₀ : LdLinP E ι κ J Y) (L : BldLn E P₀.D.Col κ Y) :
    LdLinP E ι κ J Y :=
  { P₀ with
    e' := L.e', t := L.t
    NW := L.FW.sig, SdW := L.FW.Sd, iW := L.iW, lW := fun c => L.FW.lay.atD L.iW (L.aW c)
    NU := L.FU.sig, SdU := L.FU.Sd, iU := L.iU, lU := fun k => L.FU.lay.atD L.iU (L.aU k)
    NO := L.FO.sig, SdO := L.FO.Sd, iO := L.iO, lO := fun y => L.FO.lay.atD L.iO (L.aO y) }

/-- The data of the three standard senders. -/
@[reducible] def LdLinP.bldStd (P₀ : LdLinP E ι κ J Y) (L : BldLn E P₀.D.Col κ Y)
    (w0 : (P₀.withBld L).W0) (w1 : (P₀.withBld L).W1) (w3 : (P₀.withBld L).W3) :
    (P₀.withBld L).Std E where
  YW := L.FW.lay
  YU := L.FU.lay
  YO := L.FO.lay
  pW := invS fun c => ⟨L.iW, L.aW c⟩
  pU := invS fun k => ⟨L.iU, L.aU k⟩
  pO := invS fun y => ⟨L.iO, L.aO y⟩
  qW := L.aW
  qU := L.aU
  qO := L.aO
  w0 := w0
  w1 := w1
  w3 := w3

end

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- the same overwriting, where the preamble of weights-formedness stores these fields (`LdOWf`) -/
@[reducible] def LdOWf.withBld [Fintype F] (W : LdOWf F E)
    (L : BldLn E ((Fin W.Cf.X.v ⊕ Fin W.klo) → Bool) (Fin W.Cf.C₀.k) W.P.Rw) : LdOWf F E :=
  { W with
    e' := L.e', t := L.t
    NW := L.FW.sig, SdW := L.FW.Sd, iW := L.iW, lW := fun c => L.FW.lay.atD L.iW (L.aW c)
    NU := L.FU.sig, SdU := L.FU.Sd, iU := L.iU, lU := fun k => L.FU.lay.atD L.iU (L.aU k)
    NO := L.FO.sig, SdO := L.FO.Sd, iO := L.iO, lO := fun y => L.FO.lay.atD L.iO (L.aO y) }

/-- the same, where a request stores them (`LdOLd`) -/
@[reducible] def LdOLd.withBld {Cf : LdCf F E} (D : LdOLd Cf)
    (L : BldLn E ((Fin Cf.X.v ⊕ Fin D.klo) → Bool) (Fin Cf.C₀.k) D.Y) : LdOLd Cf :=
  { D with
    e' := L.e', t := L.t
    NW := L.FW.sig, SdW := L.FW.Sd, iW := L.iW, lW := fun c => L.FW.lay.atD L.iW (L.aW c)
    NU := L.FU.sig, SdU := L.FU.Sd, iU := L.iU, lU := fun k => L.FU.lay.atD L.iU (L.aU k)
    NO := L.FO.sig, SdO := L.FO.Sd, iO := L.iO, lO := fun y => L.FO.lay.atD L.iO (L.aO y) }

end

/-- What the link needs beside the configuration and the claims: the data. -/
structure BldLk (E κ : Type) where
  F  : BldF E
  i₀ : F.O
  a₀ : κ → {i : (F.m i₀).Ent // ¬ (F.m i₀).fr i.1}
  i₁ : F.O
  a₁ : κ → {i : (F.m i₁).Ent // ¬ (F.m i₁).fr i.1}
  l  : ℕ
  e₀ : ℕ
  e₁ : ℕ
  t₀ : ℕ
  t₁ : ℕ

namespace BldLk
variable {E κ : Type} (L : BldLk E κ)

/-- where (u₀, u₁) is -/
def uvAt : κ ⊕ κ → Σ a, {i : (L.F.m a).Ent // ¬ (L.F.m a).fr i.1} :=
  Sum.elim (fun k => ⟨L.i₀, L.a₀ k⟩) fun k => ⟨L.i₁, L.a₁ k⟩

def Inj : Prop := Function.Injective L.uvAt

/-- Which entry of (u₀, u₁) a data entry holds. -/
def ixK : ∀ a, {i : (L.F.m a).Ent // ¬ (L.F.m a).fr i.1} → Option (κ ⊕ κ) :=
  invS L.uvAt

end BldLk

/-- The link's parameters. -/
@[reducible] def LdCf.bldK {F E : Type} [Field F] [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] (Cf : LdCf F E) (L : BldLk E (Fin Cf.C₀.k)) : Cf.LinkPar where
  l := L.l
  pl := binC Cf.Lay L.l
  e₀ := L.e₀
  e₁ := L.e₁
  t₀ := L.t₀
  t₁ := L.t₁
  N := L.F.sig
  i₀ := L.i₀
  l₀ := fun k => L.F.lay.atD L.i₀ (L.a₀ k)
  i₁ := L.i₁
  l₁ := fun k => L.F.lay.atD L.i₁ (L.a₁ k)

namespace Spec

def bld_invS : Prop :=
  ∀ (O V : Type) (D : O → Type) (f : V → Σ a, D a),
    Function.Injective f → ∀ v, invS f (f v).1 (f v).2 = some v

/-- States: under `L.Inj`, the places of the test are data entries of the named members. -/
def bldLn_places : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [DecidableEq E]
      (P₀ : LdLinP E ι κ J Y) (L : BldLn E P₀.D.Col κ Y) (w0 : (P₀.withBld L).W0)
      (w1 : (P₀.withBld L).W1) (w3 : (P₀.withBld L).W3),
    L.Inj → (P₀.bldStd L w0 w1 w3).Places

def bldLn_fair : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [DecidableEq E]
      (P₀ : LdLinP E ι κ J Y) (L : BldLn E P₀.D.Col κ Y),
    (P₀.withBld L).SdW.Fair ∧ (P₀.withBld L).SdU.Fair ∧ (P₀.withBld L).SdO.Fair

/-- States: under `L.Inj`, the link's layout reads (u₀, u₁). -/
def bldLk_reads : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
      (Cf : LdCf F E) (L : BldLk E (Fin Cf.C₀.k)),
    L.Inj → L.F.lay.Reads L.ixK fun m => Sum.elim ((Cf.bldK L).P.uv₀ m) ((Cf.bldK L).P.uv₁ m)

def bldLk_fair : Prop :=
  ∀ (E κ : Type) [Field E] [Fintype E] [DecidableEq E] (L : BldLk E κ), L.F.Sd.Fair

def bldLk_pl : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
      (Cf : LdCf F E) (L : BldLk E (Fin Cf.C₀.k)),
    Fintype.card Cf.Lay ≤ 2 ^ L.l → Function.Injective (Cf.bldK L).pl

end Spec
end Cb
