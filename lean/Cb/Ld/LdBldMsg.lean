-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldMsg.lean: this file makes the data of one step of the protocol from variable codes and
numbers, and states its error as a number. The step (a sending, `Sig.sh`, Cb/Ld/LdSendFam.lean) has
two rounds: the prover sends the words of several oracle messages as one oracle, the verifier sends
one joint seed, and the prover sends the answers of all of them.

Definitions, statements and one small lemma (`BldF.c_le`); the statements' proofs are in
Cb/Ld/LdBldMsgProofs.lean. Generic: any finite field E; codes are parameters. Nothing assumed beyond
the hypotheses of the statements and whatever the arguments hold as proofs.
A sample map (`Sample E J`, Cb/Gen/OodDec.lean) gives a matrix for each seed; the answers of a
vector are its products with the matrix's rows; its field err is the stated number of seeds at which
a vector other than 0 may have all answers 0. Seeds are fair (`Seeds.Fair`, Cb/Ld/LdSendFam.lean) if
each seed of a member a comes from at most mult a joint seeds.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: the records on the object ask, for each of its sendings, a family of oracle messages (`Sig E`,
Cb/Ld/LdSig.lean) with a layout (`N.StdL`, Cb/Ld/LdSendStdL.lean). The like definitions in other
files (`StdM`, Cb/Obj/LdObjectToyKit.lean; families: Cb/Obj/LdObjectSendersStdM.lean,
Cb/Ld/LdSendStdMFree.lean; `StdGM`, Cb/Ld/LdGroupStdMsg.lean) serve toys: all members of a family
share one type of long positions, in `StdGM` each entry has a coordinate of the sample of its own,
and the pad's factor is a parameter which some toys set to the one value 1 (`toyStd8`,
Cb/GlVal/GlToyMsg.lean), so that their sample's stated error is the whole set of seeds.

Main names:
  `BldM E`: one oracle message: long positions P; base code Cb, mask code Zb, both read at P; names
    Rm of its main rows, Rz of its mask rows (either may be empty); pj: the pad place (one entry,
    anywhere); fr: which entries are free (uniform, of the sender's coins: masks); every other entry
    is a data entry; c: the number of coordinates of the sample's point; e: the radius of its own
    list.
  `B.Cm`: its code, `(Cb.il Rm).pair (Zb.il Rz)`: the form that the shape of a group needs of a
    member (`view`, Cb/Ld/LdGroupFold.lean).
  `B.M : StdM E B.P`: the message as a standard oracle message: plain format; the sample: the
    multilinear extension of all entries but the pad, laid on the cube of c variables by `binC`, at
    a uniform point, plus β times the pad entry, β uniform among all elements of E other than 0.
  `BldF E`: a family: names O, a message for each: each with its own P.
  `F.cTop`, `F.Sd`: one joint seed for the family: one point with as many coordinates as the largest
    member needs (`F.cTop`) and one factor. The pads, not the factor, carry the hiding: each member
    has a pad entry of its own, so that one factor for all members costs nothing; the zero-evader's
    count is member by member.
  `Spec.bld_lay`: for every member: a word as sent is the code's encoding; the layout lays data,
    free entries and pad at their places; the member is sent in the plain format (one equation); its
    sample, read along the layout, is `Sample.pad` on Fin c with the weight 1 on the one pad entry
    and the factor over the units; under `B.Small` the corners are different.

  `Spec.bld_seed`: what a member reads of the joint seed: coordinate i of its point is coordinate i
    of the joint point; its factor is the joint factor. `Spec.bld_fair`: the seeds are fair, and (a
    member's multiplicity) · (the number of its seeds) = the number of joint seeds.
  `Spec.bld_smpNum`: the sample's numbers, with q = |E|: q^c (q - 1) seeds; stated error max (c
    q^(c-1) (q - 1)) (q^c); so err · X ≤ (number of seeds) as soon as c · X ≤ q and X ≤ q - 1: the
    fraction is max (c / q) (1 / (q - 1)).
  `Spec.bld_sendNum`: the sending's error (`ldSendFamErr`, Cb/Ld/LdSendFam.lean: the sum over the
    members a of mult a · C(L a, 2) · err): if for every member C(L a, 2) · c · (|O| · X) ≤ q and
    C(L a, 2) · (|O| · X) ≤ q - 1, then ldSendFamErr · X ≤ the number of joint seeds.

Limits: this file says nothing on codes: laws, distances, lists, hiding are the caller's. It does
not say that any fraction is small. No sender occurs: the standard sender of a layout is
Cb/Ld/LdSendStdL.lean's. This file does not say which members a sending of this protocol's technical
report has.
Declared differences to this protocol's technical report (lean/CREDITS.md), a list that may not be
whole (by a reading of a print of the technical report; not held against the report's latest
edition): One answer a sample. Every message is over E with one pad entry of E. The numbering of the
entries is a chosen one (no program).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupStdMsg
import Cb.Ld.LdSendStdL
import Cb.Ld.LdSendFamProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- Corners by binary digits. -/
def binC (X : Type) [Fintype X] (c : ℕ) : X → Fin c → Bool := fun x i =>
  ((Fintype.equivFin X x : Fin (Fintype.card X)) : ℕ).testBit i

/-- a point of C coordinates: the first c, the others -/
def ptCut (E : Type) {c C : ℕ} (h : c ≤ C) : (Fin C → E) ≃ (Fin c → E) × (Fin (C - c) → E) :=
  ((Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl E)).trans
      (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl E))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- One oracle message: the data. -/
structure BldM (E : Type) where
  P  : Type
  [finP : Fintype P]
  Cb : LdCode E P
  Zb : LdCode E P
  Rm : Type
  [finRm : Fintype Rm]
  [decRm : DecidableEq Rm]
  Rz : Type
  [finRz : Fintype Rz]
  [decRz : DecidableEq Rz]
  /-- the pad place -/
  pj : (Rm × Cb.J) ⊕ (Rz × Zb.J)
  /-- which entries are free -/
  fr : (Rm × Cb.J) ⊕ (Rz × Zb.J) → Prop
  [decFr : DecidablePred fr]
  /-- the coordinates of the sample's point; the radius -/
  c  : ℕ
  e  : ℕ

attribute [instance] BldM.finP BldM.finRm BldM.decRm BldM.finRz BldM.decRz BldM.decFr

namespace BldM
variable {E : Type} (B : BldM E)

/-- Its code. -/
@[reducible] def Cm : LdCode E B.P := (B.Cb.il B.Rm).pair (B.Zb.il B.Rz)

/-- all entries but the pad -/
abbrev Ent : Type := {j : (B.Rm × B.Cb.J) ⊕ (B.Rz × B.Zb.J) // j ≠ B.pj}

/-- all entries but the pad have room on the cube -/
def Small : Prop := Fintype.card B.Ent ≤ 2 ^ B.c

variable [Field E] [Fintype E] [DecidableEq E]

/-- The message as a standard oracle message. -/
@[reducible] def M : StdM E B.P where
  Cm := B.Cm
  Dt := B.Ent
  place := (splitAt B.pj).symm
  μ := Fin B.c
  plc := binC B.Ent B.c
  B := Eˣ
  b := Units.val
  e := B.e

/-- the entries but the pad: (data, free entries) -/
def sp : B.Ent ≃ {i : B.Ent // ¬ B.fr i.1} ⊕ {i : B.Ent // B.fr i.1} :=
  ((Equiv.sumComm _ _).trans (Equiv.sumCompl fun i : B.Ent => B.fr i.1)).symm

/-- the entries of the message: (data, free entries), the pad -/
def nu : B.Cm.J ≃ ({i : B.Ent // ¬ B.fr i.1} ⊕ {i : B.Ent // B.fr i.1}) ⊕ Unit :=
  (splitAt B.pj).trans (Equiv.sumCongr B.sp (Equiv.refl Unit))

end BldM

/-- A family: the data. -/
structure BldF (E : Type) where
  O : Type
  [finO : Fintype O]
  [decO : DecidableEq O]
  m : O → BldM E

attribute [instance] BldF.finO BldF.decO

namespace BldF
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] (F : BldF E)

/-- The signature. -/
@[reducible] def sig : Sig E := { O := F.O, om := fun a => (F.m a).M.om }

/-- The layout: pads in E. -/
@[reducible] def lay : F.sig.StdL E where
  Dt := fun a => {i : (F.m a).Ent // ¬ (F.m a).fr i.1}
  Fr := fun a => {i : (F.m a).Ent // (F.m a).fr i.1}
  Pd := fun _ => Unit
  ν := fun a => (F.m a).nu
  En := fun a => (F.m a).Cm.Nn
  upM := fun _ m => m
  upR := fun _ r => r
  msgOf := fun a x η j => withPad (F := E) x η ((F.m a).nu j)

/-- the coordinates of the joint point: as many as the largest member needs -/
def cTop : ℕ := Finset.univ.sup fun a => (F.m a).c

omit [Field E] [Fintype E] [DecidableEq E] in
theorem c_le (a : F.O) : (F.m a).c ≤ F.cTop :=
  Finset.le_sup (f := fun a => (F.m a).c) (Finset.mem_univ a)

/-- the joint seeds are, for each member, the pairs (its own seed, the coordinates that it does not
read) -/
def seedEq (a : F.O) :
    (Fin F.cTop → E) × Eˣ ≃ ((Fin (F.m a).c → E) × Eˣ) × (Fin (F.cTop - (F.m a).c) → E) where
  toFun s := (((ptCut E (F.c_le a) s.1).1, s.2), (ptCut E (F.c_le a) s.1).2)
  invFun x := ((ptCut E (F.c_le a)).symm (x.1.1, x.2), x.1.2)
  left_inv s := by simp
  right_inv x := by simp

/-- The seeds: one joint point, one joint factor. -/
@[reducible] def Sd : F.sig.Seeds :=
  Sig.Seeds.parts F.sig ((Fin F.cTop → E) × Eˣ) (fun a => Fin (F.cTop - (F.m a).c) → E) F.seedEq

/-- the corner of an entry, on the layout's names -/
def pl (a : F.O) : F.lay.Dt a ⊕ F.lay.Fr a → Fin (F.m a).c → Bool := fun x =>
  binC (F.m a).Ent (F.m a).c ((F.m a).sp.symm x)

end BldF

namespace Spec

def bld_binC : Prop :=
  ∀ (X : Type) [Fintype X] (c : ℕ), Fintype.card X ≤ 2 ^ c → Function.Injective (binC X c)

/-- Format and sample of every member. -/
def bld_lay : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (F : BldF E) (a : F.O),
    (∀ m r, (F.sig.om a).upW ((F.lay.En a).enc m r) =
      (F.sig.om a).C.enc (F.lay.upM a m) (F.lay.upR a r)) ∧
    (∀ x η n, F.lay.upM a (F.lay.msgOf a x η) ((F.lay.ν a).symm n) = withPad (F := E) x η n) ∧
    ((⟨F.sig.om a, F.lay.En a⟩ : Σ o : OMsg E, Hiop.Enc o.nat) =
      ⟨OMsg.plain (F.sig.om a).C (F.sig.om a).Z (F.sig.om a).e (F.sig.om a).rank,
        (F.sig.om a).C.Nn⟩) ∧
    (F.sig.om a).Z.comap (F.lay.ν a).symm =
      Sample.pad E (Fin (F.m a).c) (F.lay.Dt a ⊕ F.lay.Fr a) (F.lay.Pd a) Eˣ (F.pl a)
        (fun _ => 1) Units.val ∧
    ((F.m a).Small → Function.Injective (F.pl a))

/-- What a member reads of the joint seed. -/
def bld_seed : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (F : BldF E)
      (a : F.O) (s : (Fin F.cTop → E) × Eˣ),
    F.Sd.sd a s =
      ((fun i : Fin (F.m a).c => s.1 (Fin.castLE (F.c_le a) i), s.2) : (Fin (F.m a).c → E) × Eˣ)

def bld_fair : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (F : BldF E),
    F.Sd.Fair ∧ ∀ a, F.Sd.mult a * Fintype.card (F.sig.om a).Z.D = Fintype.card F.Sd.D

/-- The sample's numbers. -/
def bld_smpNum : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (F : BldF E) (a : F.O),
    Fintype.card (F.sig.om a).Z.D = Fintype.card E ^ (F.m a).c * (Fintype.card E - 1) ∧
    (F.sig.om a).Z.err =
      max ((F.m a).c * Fintype.card E ^ ((F.m a).c - 1) * (Fintype.card E - 1))
        (Fintype.card E ^ (F.m a).c) ∧
    ∀ X : ℕ, (F.m a).c * X ≤ Fintype.card E → X ≤ Fintype.card E - 1 →
      (F.sig.om a).Z.err * X ≤ Fintype.card (F.sig.om a).Z.D

/-- The sending's error. -/
def bld_sendNum : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E] (F : BldF E) (L : F.O → ℕ) (X : ℕ),
    (∀ a, (F.m a).c * ((L a).choose 2 * (Fintype.card F.O * X)) ≤ Fintype.card E) →
    (∀ a, (L a).choose 2 * (Fintype.card F.O * X) ≤ Fintype.card E - 1) →
    ldSendFamErr F.sig F.Sd L * X ≤ Fintype.card F.Sd.D

end Spec
end Cb
