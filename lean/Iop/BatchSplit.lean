-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchSplit.lean: splitting rounds of a protocol with slots. Definitions and statements; proofs:
Iop/BatchSplitProofs.lean. (Words of this library: lean/GLOSSARY.md.)

As Iop/Split.lean for ordinary IOPs, whose header says what the construction is for. A prover
message is sent in parts, each in a separate round, and after every part but the last the challenge
is empty. A protocol with slots is an ordinary IOP (a slot's verifier) with an annotation of its
rounds (Iop/Batch.lean): each round has a kind, shared (one challenge for all slots) or local (one
for each slot), and each prover message has a shared component and the slot's component. So the plan
of splits (`SPlan`) is applied to the slot's verifier, and what is new here is the annotation of the
parts: a first part and a remainder for each split. "Old" refers to the rounds before the plan is
applied, "new" to those after it.
  `ACut c a`         for a split c of a round with the annotation a: the kind of the round of the
                     first part (free: its challenge is empty, so "one for all slots" and "one for
                     each slot" say the same), the components of the two parts, and how the shared
                     component and the slot's component of the old message are split. The remainder
                     keeps the kind of the old round, by definition.
  `APlan P A`        one `ACut` for each split of the plan P. `RoundSplits.split` is the annotation of the
                     new rounds.
  `APlan.Fit`        which plans preserve the pattern of rounds `RoundSplits.Fmt` (Iop/BatchFmt.lean), the
                     condition on kinds and components that the compiler's theorems assume
                     (Compile/Batch/Spec.lean).
  `BatchProtocol.split`        also moves the field `late` (the round in whose query the compiler puts the
                     whole request) to the first part of that round (`SPlan.idx`).
  `sndB_split`, `sndBL_split` (Iop/BatchSplitProofs.lean)
                     the soundness property `SndB` (Snd-B) and its late form are preserved for an
                     explicit list of errors, under `APlan.OK` and, at `late`, `APlan.LoTo`; the
                     round of a first part has the error 0, as a local round and as a shared one.
                     The error 0 does not lower the compiler's bound `epsB`
                     (Compile/Batch/SpecBinding.lean), which counts εs for every query (under
                     `BatchProtocol.Sound` (Iop/Batch.lean) εs bounds every round-by-round error, as a
                     probability; the usual convention: the bound on binding is the number of
                     queries times εs, plus a hash term): the bound on binding grows by εs for each
                     split, and by its share of the hash term.
  `Spec.splitPropsB`
                     `BatchProtocol.Props` is preserved, with the same numbers, under `SPlan.OK`, `APlan.OK`
                     and, at `late`, `APlan.LoTo`.
  `Spec.splitFmtB`   `RoundSplits.Fmt` is preserved by a plan that fits and satisfies `APlan.OK`;
                     `ExtShared` by every plan.

What a plan may do with the kinds. For `BatchProtocol.Props`: every first part split off a round up to `late`
is local (`APlan.LoTo`); beyond that, and if `late = none`, anything. For `RoundSplits.Fmt`: the table
below (`APlan.Fit`, `FPhase.fit`), with ph the phase of the round. In Iop/BatchFmt.lean a round has
a format if the compiled verifier has a Fiat-Shamir query for its kind in its phase (`FPhase`:
before the first round; in the local rounds before the shared ones; in the shared rounds; in the
local rounds after them); the joining round is the first shared round; `RoundSplits.Fmt` says that every
round has a format and that a component that is not sent is empty.
  a local part of a local round                                    allowed
  a shared part of a shared round after the joining round          allowed
  a shared part of the joining round
      allowed if the remainder has no slot's component: the first shared round is the only one in
      which the slot's component is hashed
  a local part before the joining round
      allowed if the part has no shared component: so the slot's component of the joining round may
      be sent in local rounds before it
  a local part of a later shared round; a shared part of a local round; any split of a shared round
  that has no format
      rejected here; some of these would have a format, none is needed

Notation: `RComp r : Type 1` (this file): the components of the prover messages of a round: the
fields of `RAnn` (Iop/Batch.lean) except the kind; `M0`, `Mj : Type` (fields of `RAnn`,
Iop/Batch.lean): the shared part m_0 of a prover message; the part m_j of one slot; `P0`,
`Pj : Type` (there): the plain strings of the parts; `own : r.Pos → Bool` (a field of `RAnn`,
Iop/Batch.lean): does this oracle position lie in m_j (true) or in m_0 (false); `Bad`, `Hid`,
`stop0`: fields of `BatchHonestProver` (Iop/Batch.lean): see their docstrings; `early : X → X` (a field of
`BatchProtocol`, Iop/Batch.lean): what of an instance layer 1 (the compiler) writes into the first query of
the chain of a slot of Batch; `wordLength : ℕ`, `Symbol : Type` (fields of `BatchProtocol`, Iop/Batch.lean): in `oneExternalString wordLength Symbol`
(Iop/InteractiveOracleProof.lean), one string of wordLength symbols as external oracle; `EncodingRandomness : Type`: in
`honestOnlineBatchProver : BatchHonestProver onlineBatch (I × EncodingRandomness)`, by the docstring of `BatchHonestProver`: (index, encoding randomness).

Limits: nothing is said on the pattern (Sh) in the form `RoundSplits.OneBlock`, which no file of Compile/
mentions, nor on which plan an instance should take.
-/
import Iop.Split
import Iop.Batch
import Iop.BatchFmt

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Components, and the annotation of a split -/

/-- The components of the prover messages of a round: the fields of `RAnn` (Iop/Batch.lean) except
the kind. -/
structure RComp (r : Round) where
  M0    : Type
  Mj    : Type
  split : r.Msg ≃ M0 × Mj
  P0    : Type
  Pj    : Type
  pl0   : M0 → P0
  plj   : Mj → Pj
  plain : r.Plain ≃ P0 × Pj
  own   : r.Pos → Bool

/-- Components and a kind are an annotation. -/
@[reducible] def RComp.ann {r : Round} (C : RComp r) (k : Kind) : RAnn r where
  kind := k
  M0 := C.M0
  Mj := C.Mj
  split := C.split
  P0 := C.P0
  Pj := C.Pj
  pl0 := C.pl0
  plj := C.plj
  plain := C.plain
  own := C.own

/-- the components of an annotation -/
def RAnn.comp {r : Round} (a : RAnn r) : RComp r :=
  ⟨a.M0, a.Mj, a.split, a.P0, a.Pj, a.pl0, a.plj, a.plain, a.own⟩

/-- only the slots send -/
def RComp.ofSlot (r : Round) : RComp r := (RAnn.ofSlot .lo r).comp
/-- only the shared component is sent -/
def RComp.ofShared (r : Round) : RComp r := (RAnn.ofShared .lo r).comp

/-- The annotation of a split c of a round with the annotation a. -/
structure ACut {r : Round} (c : RCut r) (a : RAnn r) where
  /-- the kind of the round of the first part -/
  kind : Kind
  /-- the components of the first part, and of the remainder -/
  A : RComp c.fst
  B : RComp c.snd
  /-- how the shared component of the old message is split -/
  m0 : a.M0 ≃ A.M0 × B.M0
  /-- how the slot's component of the old message is split -/
  mj : a.Mj ≃ A.Mj × B.Mj

variable {r : Round} {c : RCut r} {a : RAnn r}

/-- the annotation of the round of the first part -/
@[reducible] def ACut.ann1 (b : ACut c a) : RAnn c.fst := b.A.ann b.kind
/-- the annotation of the round of the remainder: the kind is that of the old round -/
@[reducible] def ACut.ann2 (b : ACut c a) : RAnn c.snd := b.B.ann a.kind

/-- The conditions: putting components together commutes with the split; a position belongs to the
same component as before; the plain parts of the two parts fit. -/
structure ACut.OK (b : ACut c a) : Prop where
  /-- the message with the components m0 and mj is split into the messages whose components are the
  parts of m0 and mj -/
  join : ∀ m0 mj, a.join m0 mj =
    c.join (b.ann1.join (b.m0 m0).1 (b.mj mj).1) (b.ann2.join (b.m0 m0).2 (b.mj mj).2)
  ownA : ∀ p, b.A.own p = a.own (c.pos (.inl p))
  ownB : ∀ p, b.B.own p = a.own (c.pos (.inr p))
  plainA : ∀ m0 mj, b.A.plain (b.ann1.join m0 mj).2 = (b.A.pl0 m0, b.A.plj mj)
  plainB : ∀ m0 mj, b.B.plain (b.ann2.join m0 mj).2 = (b.B.pl0 m0, b.B.plj mj)

/-! ## 2. Plans with annotations -/

/-- For each split of the plan, its annotation. -/
def APlan : {s : Shape} → SPlan s → RoundSplits s → Type 1
  | _, .nil => fun _ => PUnit
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) => APlan P A.2
  | _, .cut (r := r) (s := s) c P =>
    fun (A : RAnn r × RoundSplits s) =>
      (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))

/-- The annotation of the new rounds. -/
def RoundSplits.split : {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → APlan P A → RoundSplits P.shape
  | _, .nil => fun _ _ => PUnit.unit
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => (A.1, RoundSplits.split P A.2 Z)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      (Z.1.ann1, RoundSplits.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)

/-- The annotation of every split satisfies `ACut.OK`. -/
def APlan.OK : {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → APlan P A → Prop
  | _, .nil => fun _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => APlan.OK P A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      Z.1.OK ∧ APlan.OK P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2

/-! ## 3. Challenges -/

/-- the one value of an empty challenge of the whole batch -/
def Kind.unitAll (N : ℕ) : (k : Kind) → k.All N Unit
  | .sh => ()
  | .lo => fun _ => ()

/-- The verifier randomness of the whole batch: the empty challenges are dropped. -/
def BRho.merge {N : ℕ} :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    BRho N P.shape (A.split P Z) → BRho N s A
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (ρ : A.1.kind.All N r.Chal × BRho N P.shape (RoundSplits.split P A.2 Z)) =>
      (ρ.1, BRho.merge P A.2 Z ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (ρ : Z.1.kind.All N Unit ×
            BRho N P.shape (RoundSplits.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      BRho.merge P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ρ.2

/-- The inverse of `BRho.merge`. -/
def BRho.split {N : ℕ} :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    BRho N s A → BRho N P.shape (A.split P Z)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (ρ : A.1.kind.All N r.Chal × BRho N _ A.2) =>
      (ρ.1, BRho.split P A.2 Z ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) ρ =>
      (Kind.unitAll N Z.1.kind, BRho.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ρ)

/-- `BRho.merge` for the local challenges of a slot. -/
def RhoLo.merge :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    RhoLo P.shape (A.split P Z) → RhoLo s A
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (ρ : A.1.kind.Lo r.Chal × RhoLo P.shape (RoundSplits.split P A.2 Z)) =>
      (ρ.1, RhoLo.merge P A.2 Z ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (ρ : Z.1.kind.Lo Unit ×
            RhoLo P.shape (RoundSplits.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      RhoLo.merge P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ρ.2

/-- `BRho.merge` for the shared challenges. -/
def RhoSh.merge :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    RhoSh P.shape (A.split P Z) → RhoSh s A
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (ρ : A.1.kind.Sh r.Chal × RhoSh P.shape (RoundSplits.split P A.2 Z)) =>
      (ρ.1, RhoSh.merge P A.2 Z ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (ρ : Z.1.kind.Sh Unit ×
            RhoSh P.shape (RoundSplits.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      RhoSh.merge P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ρ.2

/-! ## 4. Protocols and honest provers -/

/-- The honest strategy for the shared component sends each of its messages part by part. It still
sees the shared challenges only. -/
def SStrat.split :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    SStrat s A → SStrat P.shape (A.split P Z)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (σ : A.1.M0 × (A.1.kind.Sh r.Chal → SStrat _ A.2)) =>
      (σ.1, fun v => SStrat.split P A.2 Z (σ.2 v))
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (σ : A.1.M0 × (A.1.kind.Sh r.Chal → SStrat s A.2)) =>
      ((Z.1.m0 σ.1).1,
        fun _ =>
          SStrat.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ((Z.1.m0 σ.1).2, σ.2))

/-- The honest strategy for a slot's component sends each of its messages part by part. -/
def LStrat.split :
    {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → (Z : APlan P A) →
    LStrat s A → LStrat P.shape (A.split P Z)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (σ : A.1.Mj × (r.Chal → LStrat _ A.2)) =>
      (σ.1, fun v => LStrat.split P A.2 Z (σ.2 v))
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (σ : A.1.Mj × (r.Chal → LStrat s A.2)) =>
      ((Z.1.mj σ.1).1,
        fun _ =>
          LStrat.split P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ((Z.1.mj σ.1).2, σ.2))

variable {X : Type} {E : ExtSpec}

/-- The protocol with slots, with its prover messages sent in parts. -/
def BatchInteractiveOracleProof.split (Q : BatchInteractiveOracleProof X E) (P : SPlan Q.loc.shape) (Z : APlan P Q.ann) :
    BatchInteractiveOracleProof X E :=
  ⟨Q.loc.split P, Q.ann.split P Z⟩

/-- The honest prover: the same coins and the same external string; the shared component and the
slots' components are sent in parts; a value of a slot's local challenges is in the abort set if the
old one is. -/
def BatchHonestProver.split {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt)
    (P : SPlan Q.loc.shape) (Z : APlan P Q.ann) : BatchHonestProver (Q.split P Z) Wt where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := H.ext
  strat0 := fun w c0 => SStrat.split P Q.ann Z (H.strat0 w c0)
  strat := fun w c0 x c => LStrat.split P Q.ann Z (H.strat w c0 x c)
  Bad := {ρ | RhoLo.merge P Q.ann Z ρ ∈ H.Bad}
  Hid := fun w x => {ρ | RhoLo.merge P Q.ann Z ρ ∈ H.Hid w x}
  stop0 := fun ρ => H.stop0 (RhoSh.merge P Q.ann Z ρ)

/-- The record of protocols: encoder, decoder and the number of slots do not change. -/
def BatchProtocol.split {I X : Type} (L : BatchProtocol I X) (PT : SPlan L.offline.shape) (PL : SPlan L.link.shape)
    (PB : SPlan L.onlineBatch.loc.shape) (ZB : APlan PB L.onlineBatch.ann) : BatchProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := L.decodeIndex
  offline := L.offline.split PT
  link := L.link.split PL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.split PB ZB
  honestOfflineProver := L.honestOfflineProver.split PT
  honestLinkProver := L.honestLinkProver.split PL
  honestOnlineBatchProver := L.honestOnlineBatchProver.split PB ZB
  early := L.early
  late := L.late.map PB.idx

/-- Every first part that is split off one of the rounds 0, .., n is a local round. (Asked of the
plan for Batch for n = the round `L.late`, which with all rounds before it must be local: `SndBL`,
Iop/Batch.lean.) -/
def APlan.LoTo : {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → APlan P A → ℕ → Prop
  | _, .nil => fun _ _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z n => match n with
      | 0 => True
      | n + 1 => APlan.LoTo P A.2 Z n
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) n =>
      Z.1.kind = .lo ∧ APlan.LoTo P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 n

/-! ## 5. The pattern `RoundSplits.Fmt` -/

/-- the phase after a round of the kind k that has a format in the phase ph -/
def FPhase.after : Kind → FPhase → FPhase
  | .lo, ph => ph.afterLo
  | .sh, _ => .shr

/-- The table in the header: may a first part of the kind k1 be split off a round of the kind k that
is in the phase ph? -/
def FPhase.fit (k1 k : Kind) (ph : FPhase) (restNoSlot pieceNoShared : Prop) : Prop :=
  match k1, k, ph with
  | .lo, .lo, _ => True
  | .sh, .sh, .shr => True
  | .sh, .sh, .loc => restNoSlot
  | .lo, .sh, .loc => pieceNoShared
  | _, _, _ => False

/-- The plan fits `RoundSplits.Fmt`, from the phase ph on. -/
def APlan.Fit : {s : Shape} → (P : SPlan s) → (A : RoundSplits s) → APlan P A → FPhase → Prop
  | _, .nil => fun _ _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z ph => APlan.Fit P A.2 Z (FPhase.after A.1.kind ph)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) ph =>
      FPhase.fit Z.1.kind A.1.kind ph Z.1.ann2.NoSlot Z.1.ann1.NoShared ∧
      APlan.Fit P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 (FPhase.after Z.1.kind ph)

/-! ## 6. The statements -/

namespace Spec


/-- `BatchProtocol.Props` is preserved, with the same numbers, under `SPlan.OK`, `APlan.OK` and the hypothesis
on `L.late` (empty if `late = none`; it follows from `RoundSplits.LocalTo` and `APlan.Fit`: `splitLoTo`).
-/
def splitPropsB : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) (PT : SPlan L.offline.shape)
      (PL : SPlan L.link.shape) (PB : SPlan L.onlineBatch.loc.shape) (ZB : APlan PB L.onlineBatch.ann),
    PT.OK → PL.OK → PB.OK → APlan.OK PB L.onlineBatch.ann ZB →
    (∀ n, L.late = some n → APlan.LoTo PB L.onlineBatch.ann ZB n) →
    L.Props Ryes Rno M → (L.split PT PL PB ZB).Props Ryes Rno M

/-- If the rounds 0, .., n are local, a plan that fits splits only local first parts off them. -/
def splitLoTo : Prop :=
  ∀ (s : Shape) (P : SPlan s) (A : RoundSplits s) (Z : APlan P A) (n : ℕ) (ph : FPhase),
    RoundSplits.LocalTo n s A → APlan.Fit P A Z ph → APlan.LoTo P A Z n

/-- `RoundSplits.Fmt` is preserved by a plan that fits and satisfies `APlan.OK`, and `ExtShared` by every
plan. -/
def splitFmtB : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (P : SPlan Q.loc.shape) (Z : APlan P Q.ann),
    (APlan.OK P Q.ann Z → Q.ann.Fmt → APlan.Fit P Q.ann Z .first → (Q.split P Z).ann.Fmt) ∧
    (Q.ExtShared → (Q.split P Z).ExtShared)

end Spec

end Iop
