-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountRowE.lean: THE ROW `shared_joint_count`, STATED, FIFTH FORM: AT
THE CAP. One definition, ONE STATEMENT, one example. NOTHING IS PROVED IN THIS FILE.


A piece of the written description carries NO KIND's COUNT AND NO PRICE OF THE
PLAN, BUT THE CAP: at each written round the whole number (the number of the round's challenges) / 2
^ 128 (`Err.cap`, Iop/ErrCap.lean: the frame's files'), by the pieces' make. So no
clause on the plan's prices (N at most the plan's number of requests; the blocks' declared
rounds are the plan's; each piece's errors are the plan's whole errors as counts) STANDS, nor any
of the letters cnt, Pn, L. INSTEAD: `EachCapped`: each piece's errors are the cap.

WHERE THAT ARITHMETIC STANDS: in each kind's files. Owed there: a block's
law at ERRORS OF THE KIND's OWN, and that these are shares of at most 1 / 2 ^ 128 of the written
rounds' challenges: the law then stands at the cap: every list below that bound is at most the cap
(`Err.le_cap_of_below`), and the law in two parts is monotone in the errors (its definition has them
on the right of one "at most"). AT "LIN point": the key's part and N TIMES a slot's own part, as
counts of the written round's challenges, are together at most the cap: there N still bites: a rule
that multiplies every shared round by N = 64 fails at 38 of the full plan's 68 shared rounds (by
an exact test and a run in floating point, not shown here).

WHAT THE ROW DOES NOT SAY: that the protocol's own plan prices these rounds. A kind may spend the
whole cap. The sentence "each p.err the plan's price" does not stand
in this form: whether that is wanted is open.

The clauses, in order. (1) the table's number of the shared chain's first own tree is the data's;
(2) each piece's errors are the cap at 128; (3) the named extractor lays what the table says and
nothing else; (4) each block has the plain law for a batch in two parts, for N slots, at its own
errors, at the key "the acting part", towards: the condition behind holds, and for every world w the
relation behind at w gives the relation in front at `ext k a w`; with the hand-over of the
condition. The laws of keys are not asked: they come by make.

STILL A FORM WITH LETTERS: NOT A CLOSED ROW: F, T, D, all, C · Ns, Mg, Pm, Oc, Wt · ext, same · N,
split. Under "for all" over the letters the row is false; under "there is" empty.

Every "there is", walked. In `LeadsBN`: the split of a block's errors; the two games.
None of its own. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountRowB
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Shared

/-- **Each piece's errors are the cap**: at each written round of its stretch the whole number (the
number of the round's challenges) / 2 ^ k. -/
def EachCapped {S Cl W : Type} {C : CK} {F : Frame} (k : ℕ) (l : List (Piece C F S Cl W)) : Prop :=
  ∀ p ∈ l, p.err = Err.cap k (uLT C p.ds)

/-- **THE ROW `shared_joint_count`, AS A FORM: FIFTH FORM.** -/
def SharedJointCountRowE (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type)
    (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt) (Pm : PromMeaning F.S₂)
    (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop) : Prop :=
  Ns.lo = D.t₁ ∧
  EachCapped 128 ((atDesc F T).p₂ :: (atDesc F T).l₂) ∧
  ExtNamed split ext same ∧
  EachLawsBN (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
    (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂)
    (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext) N 0
    ((atDesc F T).p₂ :: (atDesc F T).l₂)

#check @SharedJointCountRowE

-- its last clause is the second form's last clause: so it joins upward as that does
example (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (h : SharedJointCountRowE C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N ext same) :
    EachLawsBN (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
      (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂)
      (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext) N 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂) :=
  h.2.2.2

end VerifiableInference.Desc.Sound
