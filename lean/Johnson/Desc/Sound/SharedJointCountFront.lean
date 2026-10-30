-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountFront.lean: THE FRONT BLOCK's DEBTS OF THE ROW
`shared_joint_count` (Johnson/Desc/Sound/SharedJointCountLedger.lean), PAID BY MAKE AT A DESCRIPTION, as
far as they are facts on the description's own text. Statements written as `def … : Prop`, and their
proofs. The proofs rest on the lemmas of Johnson/Desc/Sound/ that are named below.

The ledger has four debts of the front block: it keeps the record (b.1 = a.1) · it sends no tree
(pt.base = p₂.base) · the book-keeping's Bool at 0 gives that at 1 · `FrontRides`.
  `FrontByMake`: THE FIRST TWO, for every description F whose shared chain's flat list begins with a
    block fb that (i) says "ok" with the record as it is, whatever it is shown, and (ii) declares
    no round: two facts on F's text, to be had by rfl at a block made by `roundlessBlock … .ok`. From
    `OfDesc` (the pieces hold F's own blocks, below, lifted) and `Fits` (tiled). By `Block.Leaves`,
    `leavesLift`, `leavesLiftIn` (Johnson/Desc/Sound/FoldHeard.lean, FoldHeardProofs.lean), `leavesBelow`,
    `leavesOutOfBlock` (ExtHeard.lean, ExtHeardProofs.lean).



  AT WHICH BYTES (i) AND (ii) ARE MEANT: K14's `frontBlock c` :=
    { roundlessBlock "the shared chain's front" 2 none 0 .ok with planOk := … } and `chainOf`'s front := [frontBlock c]
    (Johnson/Desc/K14/Blocks.lean, in a version of it): HELD BY
    READING THAT TEXT; not by Lean (it is not in this file's ground). A front block that tests anything has
    not (i): then `frontByMake` and `frontRidesAtDesc` say nothing of it.
  `FrontRidesAtDesc`: THE FOURTH, from the same two facts, Ns.lo = t₁, and: the slot's own condition
    and the own items that are open at the chain's start read the oracles through the stored table
    and the trees below lo alone (`SameBelow`): by `frontRides_of_below`.
  `quiet_ok`: a block made by `roundlessBlock … .ok`, with whatever test on the plan, has (i) and (ii).
LEFT OF THE FRONT BLOCK's FOUR: the book-keeping's Bool (a letter of the promise's meaning), and that
the letters Oc and the four own meanings read so: not shown here.

Nearest kin: `leavesQuiet` (FoldHeardProofs.lean: at a block that IS `roundlessBlock …`; the flat
list's head is that with another test on the plan: so `leaves_id_of_ok` reads the decision alone: three
lines) · `Keeps.Decides R b`, `quiet_decides` (Johnson/Desc/BlockKeeps.lean; not in this
ground).
Every "there is", walked: none.
Limits. RULES: they close no row. No real description is named here: the term does not lie in this
file's ground. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountLedger
import Johnson.Desc.Sound.ExtHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- A block that says "ok" with the record as it is leaves the record. -/
theorem leaves_id_of_ok {S Cl : Type} (b : Block S Cl) (h : ∀ s rs gs, b.decide s rs gs = .ok s) :
    b.Leaves id := fun s rs gs s' hd => by
  rw [h] at hd
  exact (Except.ok.inj hd).symm

/-- A quiet block that says "ok", with whatever test on the plan: the two facts. -/
theorem quiet_ok {S Cl : Type} (name : String) (chain : ℕ) (link : Option ℕ) (piece : ℕ)
    (ok : Bool) :
    (∀ s rs gs, ({ roundlessBlock name chain link piece .ok with planOk := ok } :
      Block S Cl).decide s rs gs = .ok s) ∧
    ({ roundlessBlock name chain link piece .ok with planOk := ok } : Block S Cl).rounds = [] :=
  ⟨fun _ _ _ => rfl, rfl⟩

/-- **The front block keeps the record and sends no tree, by make.** -/
def FrontByMake : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ Wt : Type) (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ Wt) (fb : Block F.S₂ F.Cl) (rest : List (Block F.S₂ F.Cl))
    (pt : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (m : List (Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)),
    OfDesc F T → (atDesc F T).Fits → F.shared.blocksInOrder = fb :: rest →
    (∀ s rs gs, fb.decide s rs gs = .ok s) → fb.rounds = [] → (atDesc F T).l₂ = pt :: m →
    (∀ a τ b, (atDesc F T).p₂.ior.red.out a τ = some b → b.1 = a.1) ∧
      pt.base = (atDesc F T).p₂.base

theorem frontByMake : FrontByMake := by
  intro C D all Xi X₁ X₂ Wt F T fb rest pt m hO hf hfl hok hr hl
  have h2 := hO.b₂
  rw [hfl] at h2
  have hbk : (atDesc F T).p₂.b =
      (below fb).lift Prod.snd (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) :=
    Option.some.inj (congrArg List.head? h2)
  refine ⟨fun a τ b hb => ?_, ?_⟩
  · have k1 : (atDesc F T).p₂.b.Leaves fun t => id (Prod.snd t) := by
      rw [hbk]
      exact leavesLiftIn _ _ _ _ id Prod.snd _ (below fb) (fun _ _ => rfl)
        (leavesBelow _ _ _ id fb (leaves_id_of_ok fb hok))
    have k2 : (atDesc F T).p₂.b.Leaves Prod.fst := by
      rw [hbk]
      exact leavesLift _ _ _ _ Prod.fst Prod.snd _ (below fb) fun _ _ => rfl
    exact Prod.ext (leavesOutOfBlock _ _ _ _ C _ Prod.fst _ k2 a τ b hb)
      (leavesOutOfBlock _ _ _ _ C _ _ _ k1 a τ b hb)
  · have ht := hf.tiled₂
    rw [hl] at ht
    have ho : (atDesc F T).p₂.ds.length + (atDesc F T).p₂.back.length =
        (atDesc F T).p₂.b.rounds.length := ht.1.1
    have hr' : (atDesc F T).p₂.b.rounds = [] := by
      rw [hbk]
      exact hr
    rw [hr'] at ho
    have hds : (atDesc F T).p₂.ds = [] :=
      List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right ho)
    have h0 : (atDesc F T).p₂.trees = 0 := by
      unfold Piece.trees
      rw [hds]
      rfl
    rw [ht.2.2.2.1, h0, Nat.add_zero]

/-- **What a slot has of its own rides past the front block, at a description.** -/
def FrontRidesAtDesc : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ Wt : Type) (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool)
    (fb : Block F.S₂ F.Cl) (rest : List (Block F.S₂ F.Cl))
    (pt : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (m : List (Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)),
    OfDesc F T → (atDesc F T).Fits → F.shared.blocksInOrder = fb :: rest →
    (∀ s rs gs, fb.decide s rs gs = .ok s) → fb.rounds = [] → (atDesc F T).l₂ = pt :: m →
    Ns.lo = D.t₁ →
    (∀ x y y', SameBelow Ns.lo y y' → Oc x y → Oc x y') →
    (∀ i ∈ ownAt 0, ∀ x s y y' w, SameBelow Ns.lo y y' →
      ItemS.holdsOwn Ns Mg i x s y w → ItemS.holdsOwn Ns Mg i x s y' w) →
    FrontRides Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: m)

theorem frontRidesAtDesc : FrontRidesAtDesc := by
  intro C D all Xi X₁ X₂ Wt F T Ns Mg Pm Oc split fb rest pt m hO hf hfl hok hr hl hlo hOc hOwn
  exact frontRides_of_below Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: m)
    (by rw [hlo, hf.base₂])
    (frontByMake C D all Xi X₁ X₂ Wt F T fb rest pt m hO hf hfl hok hr hl).1 hOc hOwn

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.quiet_ok
#print axioms VerifiableInference.Desc.Sound.frontByMake
#print axioms VerifiableInference.Desc.Sound.frontRidesAtDesc
