-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupStd.lean: the standard group: oracle messages that are declared as "main rows under one
base code beside mask rows under one mask code", all read at the same long positions.

In standard terms: a family of oracle messages, each under an interleaving of rows of one code
beside rows of a second code, all over the same positions and with one proximity radius.

Definitions, statements (in `Cb.Spec`) and proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: for such messages all that Cb/Ld/LdGroupFold.lean (the shape of a group) and
Cb/Ld/LdGroupSeg.lean (kept messages) ask beside the codes' own properties and the arrangement of
the rows holds by definition. So their laws can be met; a toy with numbers is Cb/Ld/LdGroupToy.lean.

Main names:
  `StdG E P`: the data: Cb, Zb; the names A of the messages; their rows Rm a, Rz a; a sample map for
    each; one radius e for all messages and for the group.
  `StdArr D`: the arrangement of the rows; `T.sh : GShape D.G`.
  `StdHeld T kp`: a choice of kept messages: cl; such a message has no mask rows (noZ); slot.
  `Spec.ldStd_fits`: the joint radius implies each member's own (`Grp.Fits`, Cb/Ld/LdBatSig.lean;
    they are one number, under one reading).
  `Spec.ldStd_ok`: the laws of the shape (`GShape.OK`, Cb/Ld/LdGroupFold.lean; and `T.sh.view.Fix e`
    for every e: `Reshape.Fix`, Cb/Ld/LdBatShape.lean), from: the laws of Cb and Zb; every row is
    where the arrangement says; at least one variable.
  `Spec.ldStd_held`: the laws of the choice of kept messages (`GHeld.Laws`, Cb/Ld/LdGroupSeg.lean),
    from: slot k r keeps the row r.

Notation, the fields of `StdArr`, which `T.sh` gives to `GShape` under the same names (in the words
of their doc comments in `GShape`, Cb/Ld/LdGroupFold.lean, and `SumPar`, Cb/Ld/LdSum.lean): `Kp`:
the kept slots; `h`, `g`: mask rows on the cube of h variables, main rows on the cube of h + g;
`dst`, `ord`, `kept`: where a main row goes; what is in the slot none of a super-row; which row is
kept in a slot; `dstZ`, `ordZ`: the same for mask rows; `n`: the largest degree of a round
polynomial; `Ch`: the challenge set; `val : Ch → E`; `AaW`, `TW`, `srcW`, `pk`, `Qw`: the fields of
these names of `SumPar`.

Limits: this file says nothing on messages with readings of their own (a shorter mask-only message
under a repetition), or on formats over a subfield: other views (`GShape.view`,
Cb/Ld/LdGroupFold.lean). It says nothing on numbers.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupSegProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- A standard group: the data. -/
structure StdG (E P : Type) [Field E] [Fintype P] where
  Cb : LdCode E P
  Zb : LdCode E P
  A  : Type
  [finA : Fintype A]
  [decA : DecidableEq A]
  Rm : A → Type
  [finRm : ∀ a, Fintype (Rm a)]
  [decRm : ∀ a, DecidableEq (Rm a)]
  Rz : A → Type
  [finRz : ∀ a, Fintype (Rz a)]
  [decRz : ∀ a, DecidableEq (Rz a)]
  Zs : ∀ a, Sample E ((Cb.il (Rm a)).pair (Zb.il (Rz a))).J
  e  : ℕ

attribute [instance] StdG.finA StdG.decA StdG.finRm StdG.decRm StdG.finRz StdG.decRz

namespace StdG
variable {E P : Type} [Field E] [Fintype P] (D : StdG E P)

@[reducible] def code (a : D.A) : LdCode E P := (D.Cb.il (D.Rm a)).pair (D.Zb.il (D.Rz a))
@[reducible] def S : Sig E :=
  { O := D.A, om := fun a => OMsg.plain (D.code a) (D.Zs a) D.e fun _ => 0 }
@[reducible] def G : Grp D.S := { P := P, mem := fun _ => True, pos := fun _ x => x, e := D.e }

/-- the view: the identity -/
def view :
    Reshape D.G.C (LdCode.fam fun a : D.G.A => (D.Cb.il (D.Rm a.1)).pair (D.Zb.il (D.Rz a.1))) :=
  Reshape.refl _

end StdG

/-- The arrangement of the rows of a standard group, and what the fold needs. -/
structure StdArr {E P : Type} [Field E] [Fintype P] (D : StdG E P) where
  Kp : Type
  [finKp : Fintype Kp]
  [decKp : DecidableEq Kp]
  h : ℕ
  g : ℕ
  dst : (Σ a : D.G.A, D.Rm a.1) → (Fin (h + g) → Bool) ⊕ Kp
  ord : (Fin (h + g) → Bool) → Option (Σ a : D.G.A, D.Rm a.1)
  kept : Kp → Σ a : D.G.A, D.Rm a.1
  dstZ : (Σ a : D.G.A, D.Rz a.1) → Fin h → Bool
  ordZ : (Fin h → Bool) → Option (Σ a : D.G.A, D.Rz a.1)
  n : ℕ
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  val : Ch → E
  AaW : Type
  TW : D.Zb.Word → P → AaW → E
  srcW : P → Finset D.Zb.NP
  pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × D.Zb.J → E
  Qw : Slf E (Fin (h + g) → E) D.Zb.J

attribute [instance] StdArr.finKp StdArr.decKp StdArr.finCh StdArr.neCh

/-- The shape. -/
@[reducible] def StdArr.sh {E P : Type} [Field E] [Fintype P] {D : StdG E P} (T : StdArr D) :
    GShape D.G where
  Cb := D.Cb
  Zb := D.Zb
  Kp := T.Kp
  h := T.h
  g := T.g
  Rm := fun a => D.Rm a.1
  Rz := fun a => D.Rz a.1
  view := D.view
  dst := T.dst
  ord := T.ord
  kept := T.kept
  dstZ := T.dstZ
  ordZ := T.ordZ
  n := T.n
  Ch := T.Ch
  val := T.val
  AaW := T.AaW
  TW := T.TW
  srcW := T.srcW
  pk := T.pk
  Qw := T.Qw

/-- A choice of kept messages in a standard group. -/
structure StdHeld {E P : Type} [Field E] [Fintype P] {D : StdG E P}
    (T : StdArr D) (kp : D.A → Prop) where
  cl : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  /-- a kept message has no mask rows -/
  noZ : ∀ k : {a // cl a}, IsEmpty (D.Rz k.1.1)
  slot : ∀ k : {a // cl a}, D.Rm k.1.1 → T.Kp

attribute [instance] StdHeld.decCl

@[reducible] def StdHeld.hd {E P : Type} [Field E] [Fintype P] {D : StdG E P} {T : StdArr D}
    {kp : D.A → Prop} (Hh : StdHeld T kp) : GHeld T.sh kp where
  cl := Hh.cl
  mem := fun _ => trivial
  slot := Hh.slot
  unW := fun k f =>
    LdCode.mkW (C₁ := D.Cb.il (D.Rm k.1.1)) (C₂ := D.Zb.il (D.Rz k.1.1)) f fun _ s =>
      (Hh.noZ k).elim s.1
  cJ := fun k j => match j with
    | .inl n => n
    | .inr n => (Hh.noZ k).elim n.1
  cQ := fun k q => match q with
    | .inl n => n
    | .inr n => (Hh.noZ k).elim n.1

namespace Spec

def ldStd_fits : Prop := ∀ (E P : Type) [Field E] [Fintype P] (D : StdG E P), D.G.Fits

def ldStd_ok : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (D : StdG E P) (T : StdArr D), D.Cb.Laws →
    D.Zb.Laws → (∀ r b, T.dst r = .inl b → T.ord b = some r) →
    (∀ r j, T.dst r = .inr j → T.kept j = r) → (∀ r, T.ordZ (T.dstZ r) = some r) →
    1 ≤ T.h + T.g → T.sh.OK ∧ ∀ e, T.sh.view.Fix e

def ldStd_held : Prop :=
  ∀ (E P : Type) [Field E] [Fintype P] (D : StdG E P) (T : StdArr D)
      (kp : D.A → Prop) (Hh : StdHeld T kp),
    (∀ k r, T.kept (Hh.slot k r) = ⟨⟨k.1.1, trivial⟩, r⟩) → Hh.hd.Laws

end Spec

theorem ldStd_fits : Spec.ldStd_fits := fun _ _ _ _ _ _ _ _ h => h

theorem ldStd_ok : Spec.ldStd_ok := by
  intro E P _ _ _ D T hC hZ hm hk hz h1
  have hr := ldShape_refl E P D.G.C
  refine ⟨⟨hr.1, hC, hZ, fun r => ?_, hz, h1⟩, hr.2⟩
  split
  · next b hb => exact hm r b hb
  · next j hj => exact hk r j hj

theorem ldStd_held : Spec.ldStd_held := by
  intro E P _ _ D T kp Hh hk
  refine ⟨hk, fun k f => ?_, fun k w j => ?_, fun k w q => ?_, fun k m r => ?_, fun k f g x h => ?_⟩
  · funext p
    rcases p with p | p
    · rfl
    · funext s
      exact (Hh.noZ k).elim s.1
  · rcases j with n | n
    · rfl
    · exact (Hh.noZ k).elim n.1
  · rcases q with n | n
    · rfl
    · exact (Hh.noZ k).elim n.1
  · funext p
    rcases p with p | p
    · rfl
    · funext s
      exact (Hh.noZ k).elim s.1
  · funext α
    rcases α with α | α
    · exact congrFun h α
    · exact (Hh.noZ k).elim α.1

end Cb
