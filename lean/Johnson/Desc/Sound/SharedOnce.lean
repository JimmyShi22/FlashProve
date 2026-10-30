-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedOnce.lean: WHEN A BLOCK OF THE SHARED CHAIN IS PAID ONCE FOR ALL N SLOTS, in
the form in which a kind's files can meet it: from the block's law for ONE statement, with
conditions, relations and extractor GIVEN AS FUNCTIONS OF THE ACTING PART. A SHEET OF STATEMENTS:
definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

Why. A proof file's second chain is run once for the N slots of a batch; a shared round's error must
bound the challenges that are bad for SOME slot (Johnson/Desc/Sound/SharedRule.lean, whose words are
kept). In a stretch of that chain in which nothing of a slot's own is tested (what is meant: the two
proximity tests) each round should cost what it costs for one statement. SharedRule.lean says so
under `RelsBy` (`LostOfGoodIn`, `LostBeside`, `PaidOnce`): four implications a block, on conditions
and relations that are letters.

What is said. NO NEW RULE: the named rules of SharedRule.lean, composed, in a form whose premise on
the relations is met BY THE WAY THEY ARE WRITTEN.
  `Piece.ExtBy p act`: the block's extractor reads the statement through the acting part alone.
  `RelsOfActs`: a condition behind the block and two relations that are written as functions of the
    VALUE of the acting part have `RelsBy`, if the extractor has `ExtBy`.
  `Piece.PaysN`: the block's own reduction, run once by the shared part, is knowledge sound into its
    promise, at its own errors and with its own extractor, for the vectors of at most N statements
    with one acting part. (It is, letter for letter, `Piece.Pays` of Johnson/Desc/Sound/
    FoldSlotsLinks.lean, which was not in the build on which this file was written and which this file's imports do not reach: PaysN was to
    be struck for that when the files were joined, and has not been.)
  `OnceOfGoodIn`: THE FORM TO USE, FOR ONE BLOCK. The block is typed at the chain's own part of the
    record and lifted; its rounds open no tree below lo; it has `GoodIn` for ONE statement between a
    condition in front that is free, a promise o' and relations ρ, ρ' that are functions of the value
    of (the chain's own record · the stored table · the chain's own trees); its extractor reads so
    too and keeps a carried claim Rc. THEN IT PAYS FOR EVERY N, AT ITS OWN ERRORS, between
    "ρ and Rc" and "ρ' and Rc". N occurs in no premise and in no error.
  `PaysCarry`: a condition oc that each slot has of its own and that the block carries for certain may
    be laid beside the condition in front and the promise behind.
  `EachPaysN`, `EachExtBy`, `RowOnce`: the same along a stretch of blocks that stands at place i of a
    chain: so a chain in which one block is of another kind (Limits (3)) is spliced: that block by
    its own law, the stretch behind it by `RowOnce`.

Who reads each letter. p: the block is the verifier's; stretch, extractor and errors are the law's
prover's. get, set, lo: how the chain's own part lies in the record, and the number of its first own
tree. o', ρ, ρ', Rc, on: read by no verifier.

Limits. (1) RULES. No block of the protocol is shown to meet a premise. `GoodIn` for one statement
is the whole of a block's soundness: it is a premise. (2) Met for nothing, and then saying nothing:
by a block that refuses all; at errors as large as a round's number of challenges; at a condition
`on` that holds of no statement; at N = 0; at a carried claim Rc that holds of nothing (both
relations are then empty); at a ρ' that holds of nothing (`GoodIn` is then the promise alone). (3) WHAT IS NOT COVERED: a block that tests a slot's own
statement at a shared challenge (the shared point): its relation in front cannot be written as a
function of this acting part; for it: a law in two parts, or the carriage of a typed clause for a
batch (`Piece.LostBoth`, FoldSlots.lean; `PiecePaysOfProved`, FoldSlotsLinks.lean). (4) A relation that reads the record
outside the chain's own part, or a tree below lo, is not of the form asked; there is such a relation
at which the block has `GoodIn` for one statement at the error 1 and does NOT pay for two slots at
that error (said here without a theorem). (5) That the slots of a batch have one acting part at the
head of the chain is not said here (DescThree.lean). (6) The witness w may be read whole by ρ, ρ'
and Rc.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 1 Written through the acting part -/

/-- The block's extractor reads the statement through the acting part alone. -/
def Piece.ExtBy (p : Piece C F S Cl W) (act : BKey F S) : Prop :=
  ∀ a a' τ w, act.2 a = act.2 a' → p.ext a τ w = p.ext a' τ w

/-- **A condition and relations that are written as functions of the acting part's value read the
statement through the acting part alone.** -/
def RelsOfActs : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (act act' : BKey F S)
    (o' : act'.1 → Prop) (ρ : act.1 → W → Prop) (ρ' : act'.1 → W → Prop),
    p.ExtBy act →
    p.RelsBy (fun b => o' (act'.2 b)) (fun a w => ρ (act.2 a) w) (fun b w => ρ' (act'.2 b) w) act
      act'

/-! ## 2 One block -/

/-- **A shared block pays for N slots**: knowledge sound into its promise, at its own errors, for
the vectors of at most N statements with one acting part. -/
def Piece.PaysN (p : Piece C F S Cl W) (N : ℕ) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) : Prop :=
  p.ior.KnowBInto (shAn p.ior.shape) N (IOR.SameKey act.2) on on' R R' p.ext p.err

/-- **From the law for one statement to every N, at the block's own errors.** The acting part behind
the block is taken at the number behind its own trees (p.base + p.trees). In a row the next block's
acting part is taken at that block's base: one number by two roads, tied by `Tiled` alone: whoever
splices blocks by hand needs that equation. -/
def OnceOfGoodIn : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl)
    (p : Piece C F S Cl W) (lo N : ℕ) (on : S × F.E.Str → Prop)
    (o' : (actAt F get lo (p.base + p.trees)).1 → Prop)
    (ρ : (actAt F get lo p.base).1 → W → Prop)
    (ρ' : (actAt F get lo (p.base + p.trees)).1 → W → Prop) (Rc : S × F.E.Str → W → Prop),
    p.b = b₀.lift get set → (∀ t s, get (set t s) = s) →
    (∀ t s s', set (set t s) s' = set t s') → (∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) →
    p.GoodIn on (fun b => o' ((actAt F get lo (p.base + p.trees)).2 b))
      (fun a w => ρ ((actAt F get lo p.base).2 a) w)
      (fun b w => ρ' ((actAt F get lo (p.base + p.trees)).2 b) w) →
    p.ExtBy (actAt F get lo p.base) →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b →
      o' ((actAt F get lo (p.base + p.trees)).2 b) → Rc b w → Rc a (p.ext a τ w)) →
    p.PaysN N on (fun b => o' ((actAt F get lo (p.base + p.trees)).2 b))
      (fun a w => ρ ((actAt F get lo p.base).2 a) w ∧ Rc a w)
      (fun b w => ρ' ((actAt F get lo (p.base + p.trees)).2 b) w ∧ Rc b w)
      (actAt F get lo p.base)

/-- **A slot's own condition, carried for certain, may stand beside both conditions.** (The promise of
a stretch that is paid once is a function of the acting part; what a later chain needs of a slot's own
promise rides so.) -/
def PaysCarry : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (N : ℕ)
    (on on' oc : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (act : BKey F S),
    p.PaysN N on on' R R' act → (∀ a τ b, oc a → p.ior.red.out a τ = some b → oc b) →
    p.PaysN N (fun a => on a ∧ oc a) (fun b => on' b ∧ oc b) R R' act

/-! ## 3 A row of blocks -/

/-- Every block of a row pays, at the acting part of the place in front of it. -/
def EachPaysN (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.PaysN N (on i) (on (i + 1)) (R i) (R (i + 1)) (act i) ∧ EachPaysN N on R act (i + 1) l

/-- Every block's extractor reads the statement through the acting part in front of it. -/
def EachExtBy (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => p.ExtBy (act i) ∧ EachExtBy act (i + 1) l

/-- **The same along a stretch of blocks that stands at place i.** act: the acting parts at the
places of the whole chain; from place i on they are those that are meant for the stretch p :: l
(at `actsOf` of a whole row and a tail of it this premise holds by unfolding `hiAt`). The stretches
tile; every block is lifted and opens no tree below lo; behind place i the conditions, and from place
i on the relations, are written as functions of the acting part's value; every block has `GoodIn` for
one statement; every extractor reads through the acting part and keeps the carried claim. Then every
block of the stretch pays for every N at its own errors, between "ρ and Rc". The condition at place i
itself is free. -/
def RowOnce : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (lo N i : ℕ)
    (act : ℕ → BKey F S) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (on : ℕ → S × F.E.Str → Prop) (o : ∀ k, (act k).1 → Prop) (ρ : ∀ k, (act k).1 → W → Prop)
    (Rc : S × F.E.Str → W → Prop),
    (∀ k, act (i + k) = actAt F get lo (hiAt k p l)) → Tiled p l →
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
    (∀ k, i < k → on k = fun a => o k ((act k).2 a)) →
    EachGoodIn on (fun k a w => ρ k ((act k).2 a) w) i (p :: l) →
    EachExtBy act i (p :: l) → EachKeeps on Rc i (p :: l) →
    EachPaysN N on (fun k a w => ρ k ((act k).2 a) w ∧ Rc a w) act i (p :: l)

/-- A tail's acting parts are the whole row's, one place on: the first premise of `RowOnce` at a row
without its first block. -/
def TailActs : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (lo : ℕ) (p q : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (k : ℕ),
    actsOf get lo p (q :: l) (1 + k) = actAt F get lo (hiAt k q l)

#check @RelsOfActs
#check @OnceOfGoodIn
#check @PaysCarry
#check @RowOnce
#check @TailActs

end VerifiableInference.Desc.Sound
