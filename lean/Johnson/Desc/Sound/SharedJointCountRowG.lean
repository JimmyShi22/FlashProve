-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountRowG.lean: THE ROW `shared_joint_count`, STATED, IN THE
SENTENCE: "each p.err the cap; each [kind]'s own errors, at LIN point the key's part and N
times a slot's own, within it". One STATEMENT with letters, and one theorem: it gives the fifth form
(Johnson/Desc/Sound/SharedJointCountRowE.lean) with 1 ≤ N: so, applied at the table's files' named
terms, the sixth (SharedJointCountRowF.lean: not in this library).

The fifth and sixth forms ask each block's law AT THE CAP. How a kind
comes there (a law at errors of its own that are shares of at most 1 / 2 ^ 128) stands in the row's
ledger (SharedJointCountLedger.lean) alone. HERE:
  own: A LETTER OF THE ROW: each kind's own errors, by the block's number and its piece;
  (5) `EachOwnBelow 128 own`: they are within the cap: one clause a block;
  (6) `EachLawsBNOwn … own`: each block's law for a batch in two parts AT ITS OWN ERRORS, with the
    hand-over of the condition;
  (7) AT BLOCK NUMBER 1 ("LIN point") THE SPLIT IS NAMED: own 1 pt = δK pt + N · δO pt, and the block has
    the law in two parts at just these (`LeadsB`): the key's part once, a slot's own N times.
(1) 1 ≤ N · (2) the table's number is the data's · (3) each piece's errors are the cap · (4) the
named extractor lays what the table says and nothing else: as before.

  `rowG_gives_E`: by `eachLawsBN_atCap`.

STILL A FORM WITH LETTERS: NOT A CLOSED ROW: the fifth form's, and own, δK, δO. It is laid at the
table's named terms in a seventh form (SharedJointCountRowH.lean).
What one may try against it. own := the cap itself (allowed: then (6) is the fifth form's clause) ·
δO := 0 at the point (then (7) says that the point is paid once: false of the real block, so unpaid)
· a chain without a block number 1 ((7) holds for nothing: the ledger asks l₂ = pt :: q :: r).
Every "there is", walked: none of its own; in `LeadsBN`, `LeadsB`: the split; the two games.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Shared

/-- **THE ROW `shared_joint_count`, AS A FORM, IN THE SENTENCE OF THIS FILE's HEAD.** -/
def SharedJointCountRowG (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type)
    (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt) (Pm : PromMeaning F.S₂)
    (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (δK δO : (p : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      Wt) → Err (uLT C p.ds)) : Prop :=
  1 ≤ N ∧
  Ns.lo = D.t₁ ∧
  EachCapped 128 ((atDesc F T).p₂ :: (atDesc F T).l₂) ∧
  ExtNamed split ext same ∧
  EachOwnBelow 128 own 0 ((atDesc F T).p₂ :: (atDesc F T).l₂) ∧
  EachLawsBNOwn (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
    (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂)
    (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext) N own 0
    ((atDesc F T).p₂ :: (atDesc F T).l₂) ∧
  ∀ pt, ((atDesc F T).p₂ :: (atDesc F T).l₂)[1]? = some pt →
    own 1 pt = Err.add (δK pt) (Err.times N (δO pt)) ∧
      pt.ior.red.LeadsB (keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂ 1)
        (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ 1)
        (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (atDesc F T).l₂ ext 1) (δK pt) (δO pt)

/-- **It gives the fifth form, for at least one slot.** -/
theorem rowG_gives_E (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type)
    (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt) (Pm : PromMeaning F.S₂)
    (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (ext : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D all).Str → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (δK δO : (p : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      Wt) → Err (uLT C p.ds))
    (h : SharedJointCountRowG C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N ext same own δK δO) :
    1 ≤ N ∧ SharedJointCountRowE C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N ext same :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    eachLawsBN_atCap 128 _ _ _ N own _ 0 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowG_gives_E
