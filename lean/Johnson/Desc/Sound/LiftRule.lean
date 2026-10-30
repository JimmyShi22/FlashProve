-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LiftRule.lean: A BLOCK THAT IS TYPED AT A PART OF THE CARRIED RECORD AND LIFTED
(`Block.lift`, Johnson/Desc/Block.lean): what is shown of it at its own part holds of the lifted
block at the whole record. Six statements, written as `def … : Prop`, and their proofs.

Why. In the filling that is meant (`Three.ofStarts`, Johnson/Desc/Sound/FileRule.lean) a chain's
record holds, beside the chain's own record, what was handed to the chain, and the blocks are
lifted; and a block is typed at the part of a chain's record that its kind needs. The rule of
composition asks goodness of the lifted blocks. So that whoever proves a block owes ONE law, at the
block's own part, this file carries that law up.

Main names.
  `Piece.lift get set p`: the block lifted, with the same stretch and errors; its extractor reads
    the statement's part. `atPart get a`: a statement with the record's part in place of the record.
  THE STATEMENTS: `LiftOut` (what the lifted block's reduction puts out is what the block's puts out
    at the part, laid back) · `LiftGoodIn` (`Piece.GoodIn` at the part gives `Piece.GoodIn` of the
    lifted block, at the conditions and relations read through the part) · `LiftTiled` (the
    stretches of the lifted blocks tile what the blocks' stretches tile) · `EachGoodOfLift`,
    `EachGoodInOfLift` (a row of blocks with `GoodIn` at the part: the lifted row meets `EachGood`,
    and has `GoodIn` block by block) · `LiftKeepsFirst` (a block that is lifted to a pair leaves the
    first part as it is).

Limits. (1) `get` and `set` obey two laws of a part of a record (what was laid is got; what is laid
last stays): premises. (2) The conditions and relations that come out read the statement THROUGH THE
PART: a claim on the rest of the record is laid beside by `GoodInBeside`
(Johnson/Desc/Sound/GoodIn.lean), whose premise on the extractor is owed then. (3) Those of
ChainRule.lean and GoodIn.lean: rules, whose premises are met by no block here; nothing on
acceptance.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileKnowsProof
import Johnson.Desc.Sound.FoldLiftProof
import Johnson.Desc.Sound.GoodInProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S S₀ Cl W : Type} {C : CK} {F : Frame}

/-- A statement with the record's part in place of the record. -/
def atPart (get : S → S₀) (a : S × F.E.Str) : S₀ × F.E.Str := (get a.1, a.2)

/-- **A block with its stretch, lifted**: the block by `Block.lift`; the same stretch, rounds put
back and errors; the extractor reads the statement's part. -/
def Piece.lift (get : S → S₀) (set : S → S₀ → S) (p : Piece C F S₀ Cl W) : Piece C F S Cl W :=
  ⟨p.b.lift get set, p.base, p.ds, p.back, fun a τ w => p.ext (atPart get a) τ w, p.err⟩

/-- What the lifted block's reduction puts out is what the block's puts out at the part, laid back.
An equation at every statement and transcript. -/
def LiftOut : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (p : Piece C F S₀ Cl W),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    ∀ (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)),
      (p.lift get set).ior.red.out a τ =
        (p.ior.red.out (atPart get a) τ).map fun b => (set a.1 b.1, b.2)

/-- **One law, at the block's own part.** -/
def LiftGoodIn : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (p : Piece C F S₀ Cl W) (on on' : S₀ × F.E.Str → Prop) (R R' : S₀ × F.E.Str → W → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    p.GoodIn on on' R R' →
    (p.lift get set).GoodIn (fun a => on (atPart get a)) (fun a => on' (atPart get a))
      (fun a w => R (atPart get a) w) (fun a w => R' (atPart get a) w)

/-- The stretches of the lifted blocks tile what the blocks' stretches tile. -/
def LiftTiled : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (p : Piece C F S₀ Cl W) (l : List (Piece C F S₀ Cl W)),
    Tiled p l → Tiled (p.lift get set) (l.map (Piece.lift get set))

/-- A row of blocks with `GoodIn` at the part: the lifted row meets the premise of the rule of
composition. -/
def EachGoodOfLift : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (on : ℕ → S₀ × F.E.Str → Prop) (R : ℕ → S₀ × F.E.Str → W → Prop) (i : ℕ)
    (l : List (Piece C F S₀ Cl W)),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    EachGoodIn on R i l →
    EachGood (fun k a => on k (atPart get a)) (fun k a w => R k (atPart get a) w) i
      (l.map (Piece.lift get set))

/-- The same row form, ending in `GoodIn` itself: what the rules for the shared chain ask of the
lifted row. -/
def EachGoodInOfLift : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S)
    (on : ℕ → S₀ × F.E.Str → Prop) (R : ℕ → S₀ × F.E.Str → W → Prop) (i : ℕ)
    (l : List (Piece C F S₀ Cl W)),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    EachGoodIn on R i l →
    EachGoodIn (fun k a => on k (atPart get a)) (fun k a w => R k (atPart get a) w) i
      (l.map (Piece.lift get set))

/-- **A block that is lifted to a pair leaves the first part as it is**: the record's half of "the
carried claim is kept". Z: what was handed to the chain. So of the premise of `GoodInBeside`, for a
claim that reads the first part and the witness, only the witness's half is left: that the block's
extractor leaves alone what the claim reads of the witness. -/
def LiftKeepsFirst : Prop :=
  ∀ (Z S₀ Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S₀ Cl W) (a b : (Z × S₀) × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)),
    (p.lift Prod.snd fun t s => (t.1, s)).ior.red.out a τ = some b → b.1.1 = a.1.1

/-! ## The proofs -/

theorem lift_run (get : S → S₀) (set : S → S₀ → S) (p : Piece C F S₀ Cl W)
    (h1 : ∀ t s, get (set t s) = s) (h2 : ∀ t s s', set (set t s) s' = set t s') :
    (p.lift get set).run = fun t v => (p.run (get t) v).map (set t) := by
  funext t v
  exact foldLift S S₀ Cl F p.b.name [p.b] p.back get set h1 h2 t v

theorem liftOut : LiftOut := by
  intro S S₀ Cl W C F get set p h1 h2 a τ
  show (stageIOR C p.stage (p.lift get set).run).red.out (a.1, a.2) τ = _
  rw [lift_run get set p h1 h2]
  exact stage_map p.stage p.run get set a.1 a.2 τ

theorem liftGoodIn : LiftGoodIn := by
  intro S S₀ Cl W C F get set p on on' R R' h1 h2 h a ha
  refine Doomed.mono _ _ ?_ (h (atPart get a) ha)
  intro τ hτ b hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  obtain ⟨ho, hk⟩ := hτ b₀ hb₀
  refine ⟨?_, fun w hw => ?_⟩
  · show on' (atPart get (set a.1 b₀.1, b₀.2))
    rw [e]
    exact ho
  · have hw' : R' (atPart get (set a.1 b₀.1, b₀.2)) w := hw
    rw [e] at hw'
    exact hk w hw'

theorem liftTiled : LiftTiled := by
  intro S S₀ Cl W C F get set p l
  induction l generalizing p with
  | nil => exact fun h => h
  | cons q l ih => exact fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ih q h.2.2.2.2⟩

theorem eachGoodOfLift : EachGoodOfLift := by
  intro S S₀ Cl W C F get set on R i l h1 h2
  induction l generalizing i with
  | nil => exact fun _ => trivial
  | cons p l ih =>
    exact fun h => ⟨goodOfGoodIn S Cl W C F (p.lift get set) _ _ _ _
      (liftGoodIn S S₀ Cl W C F get set p _ _ _ _ h1 h2 h.1), ih (i + 1) h.2⟩

theorem eachGoodInOfLift : EachGoodInOfLift := by
  intro S S₀ Cl W C F get set on R i l h1 h2
  induction l generalizing i with
  | nil => exact fun _ => trivial
  | cons p l ih =>
    exact fun h => ⟨liftGoodIn S S₀ Cl W C F get set p _ _ _ _ h1 h2 h.1, ih (i + 1) h.2⟩

theorem liftKeepsFirst : LiftKeepsFirst := by
  intro Z S₀ Cl W C F p a b τ hb
  rw [liftOut (Z × S₀) S₀ Cl W C F Prod.snd (fun t s => (t.1, s)) p (fun _ _ => rfl)
    (fun _ _ _ => rfl) a τ] at hb
  obtain ⟨b₀, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  rfl

end VerifiableInference.Desc.Sound
