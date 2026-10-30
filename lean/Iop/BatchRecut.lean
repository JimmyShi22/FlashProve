-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchRecut.lean: the rounds of a protocol with slots are split and merged in one pass.
Definitions and statements; proofs: Iop/BatchRecutProofs.lean. (Words of this library:
lean/GLOSSARY.md.)

As Iop/Recut.lean for ordinary IOPs. What the construction is for is told in the headers of
Iop/Split.lean and Iop/Join.lean. A protocol with slots is an ordinary IOP (a slot's verifier) with
an annotation of its rounds (Iop/Batch.lean): each round has a kind, shared (one challenge for all
slots) or local (one for each slot), and each prover message has a shared component and the slot's
component. So the plan (`XPlan`) is applied to the slot's verifier, and what this file adds is the
annotation of the new rounds. At a split it is a datum (`ACut`, Iop/BatchSplit.lean); at a merge,
(J1) of prover messages or (J2) of challenges, it is built from the old annotations: at (J1) from
both, at (J2) it is the first round's (`RAnn.joinMsg`, `RAnn.joinChal`, Iop/BatchJoin.lean). "Old"
refers to the rounds before the plan is applied, "new" to those after it; a run is a sequence of old
rounds that are merged.
  `AXPlan P A`         one `ACut` for each split of the plan P; `RoundSplits.recut P A Z`: the annotation
                       of the new rounds
  `AXPlan.Kinds`       two rounds merged by (J2) have the same kind ("one verifier message for all
                       slots" and "one for each slot" cannot be one message). A proof of it is an
                       argument of `BRho.old`, `BRho.new`, `RhoLo.old`, `RhoSh.old`, `SStrat.recut`,
                       `BatchHonestProver.recut`, `BatchProtocol.recut`: without it the types do not fit; no value
                       depends on it
  `BatchProtocol.recut`          moves the field `late` (the round in whose query the compiler puts the whole
                       request) to `XPlan.idx`
  `AXPlan.Late .. n`   what `sndBL_recut` and `BatchProtocol.SoundAt.recut` (Iop/BatchRecutProofs.lean) ask of
                       the plan for Batch (`L.onlineBatch`) at the round n = `L.late`; the docstring of
                       `AXPlan.Late` has the four clauses. Under it exactly the challenges of the
                       old rounds before n come before the new round `P.idx n`: the prover fixes the
                       rest of the request after the same challenges as before, neither later nor
                       earlier. What can move is which prover message is in that new round: after
                       (J1) and a split of the merged round it may contain nothing of the old round
                       n. The condition is sufficient and stricter than needed: a local round before
                       n whose challenge has one value cannot be put into n's new round by (J1),
                       though the request would then be fixed after the same challenges
  `AXPlan.Fit`         which plans preserve the pattern of rounds `RoundSplits.Fmt` (Iop/BatchFmt.lean): at
                       a split the table of Iop/BatchSplit.lean (`FPhase.fit`), at (J1) that of
                       Iop/BatchJoin.lean (`FPhase.fitMsg`); at (J2) the two kinds are equal by
                       `Kinds`, and nothing else is asked
  `Spec.recutPropsB`   `BatchProtocol.Props` except soundness is preserved, with the same numbers, if the
                       plans and the annotated splits satisfy their conditions (`XPlan.OK`,
                       `AXPlan.OK`, `AXPlan.Kinds`); soundness at the bound εs' is a hypothesis
  `BatchProtocol.SoundAt.recut`, `simRecutB` (Iop/BatchRecutProofs.lean)
                       soundness for three explicit lists of errors (Iop/SoundAt.lean); the
                       simulator for sets of slots as a term
  `Spec.recutFmtB`     `RoundSplits.Fmt` is preserved by a plan that fits and satisfies `AXPlan.OK` and
                       `Kinds`; `ExtShared` by every plan with `Kinds`
The theorems on the soundness property `SndB` (Snd-B) ask for 0 < N and for the error 0 where the
challenge has one value (`Err.UnitZero`) (the reason: headers of Iop/BatchJoin.lean and
Iop/BatchJoinProofs.lean).

Notation: `Z : AXPlan P A` (this file): for each split of the plan, its annotation; `u : r1.Chal` in
`XPlan.msg r1 r2 u X` (Iop/Recut.lean): (J1): u is a value of the challenge of r1; `XPlan.OK` asks
that it is the only one; `noPos : r2.Pos → Empty` in `XPlan.chal r1 r2 noPos X` (there): (J2): r2
has no position; `c : RCut r` (Iop/Split.lean): a split of the prover message of the round r into a
first part A and the remainder B; `c.fst`, `c.snd`: their rounds; `b.ann1`, `b.ann2`
(Iop/BatchSplit.lean): the annotations of the round of the first part and of the round of the
remainder; `M0`, `Mj : Type` (fields of `RAnn`, Iop/Batch.lean): the shared part m_0 of a prover
message; the part m_j of one slot; `early : X → X` (a field of `BatchProtocol`, Iop/Batch.lean): what of an
instance layer 1 (the compiler) writes into the first query of the chain of a slot of Batch; `Bad`,
`Hid`, `stop0`: fields of `BatchHonestProver` (Iop/Batch.lean): see their docstrings.
-/
import Iop.Recut
import Iop.BatchSplit
import Iop.BatchJoin

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Plans with annotations -/

/-- For each split of the plan, its annotation. -/
def AXPlan : {s : Shape} → XPlan s → RoundSplits s → Type 1
  | _, .nil => fun _ => PUnit
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) => AXPlan P A.2
  | _, .cut (r := r) (s := s) c P =>
    fun (A : RAnn r × RoundSplits s) =>
      (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))
  | _, .msg r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
  | _, .chal r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))

/-- The annotation of the new rounds. -/
def RoundSplits.recut : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → RoundSplits P.shape
  | _, .nil => fun _ _ => PUnit.unit
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => (A.1, RoundSplits.recut P A.2 Z)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      (Z.1.ann1, RoundSplits.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)
  | _, .msg r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      RoundSplits.recut P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      RoundSplits.recut P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-- The annotation of every split satisfies `ACut.OK`. -/
def AXPlan.OK : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → Prop
  | _, .nil => fun _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => AXPlan.OK P A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      Z.1.OK ∧ AXPlan.OK P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.OK P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.OK P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-- Two rounds merged by (J2) have the same kind. -/
def AXPlan.Kinds : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → Prop
  | _, .nil => fun _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => AXPlan.Kinds P A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      AXPlan.Kinds P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.Kinds P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      A.2.1.kind = A.1.kind ∧
      AXPlan.Kinds P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-- Nothing is split, so nothing is to be annotated. -/
def AXPlan.keepAll : (s : Shape) → (A : RoundSplits s) → AXPlan (XPlan.keepAll s) A
  | [], _ => PUnit.unit
  | _ :: s, A => AXPlan.keepAll s A.2

/-! ## 2. Verifier randomness -/

/-- The verifier randomness of the whole batch: from the new rounds to the old ones. -/
def BRho.old {N : ℕ} :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kinds P A Z → BRho N P.shape (A.recut P Z) → BRho N s A
  | _, .nil => fun _ _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z h
      (ρ : A.1.kind.All N r.Chal × BRho N P.shape (RoundSplits.recut P A.2 Z)) =>
        (ρ.1, BRho.old P A.2 Z h ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) h
          (ρ : Z.1.kind.All N Unit ×
            BRho N P.shape (RoundSplits.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      BRho.old P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 h ρ.2
  | _, .msg r1 r2 (s := s) u P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      (Kind.constAll N A.1.kind u,
        (BRho.old P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z h ρ :
          BRho N (r1.joinMsg r2 :: s) (A.1.joinMsg A.2.1, A.2.2)))
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      let z : BRho N (r1.joinChal r2 :: s) (A.1.joinChal r2, A.2.2) :=
        BRho.old P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z h.2 ρ
      (A.1.kind.mapAll Prod.fst z.1, Kind.sndAll A.1.kind A.2.1.kind h.1 z.1, z.2)

/-- The map in the other direction, from the old rounds to the new ones. -/
def BRho.new {N : ℕ} :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kinds P A Z → BRho N s A → BRho N P.shape (A.recut P Z)
  | _, .nil => fun _ _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z h (ρ : A.1.kind.All N r.Chal × BRho N _ A.2) =>
      (ρ.1, BRho.new P A.2 Z h ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) h ρ =>
      (Kind.unitAll N Z.1.kind, BRho.new P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 h ρ)
  | _, .msg r1 r2 (s := s) _ P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h
          (ρ : A.1.kind.All N r1.Chal × A.2.1.kind.All N r2.Chal × BRho N s A.2.2) =>
      BRho.new P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z h ρ.2
  | _, .chal r1 r2 (s := s) _ P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h
          (ρ : A.1.kind.All N r1.Chal × A.2.1.kind.All N r2.Chal × BRho N s A.2.2) =>
      BRho.new P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z h.2
        (Kind.pairAll A.1.kind A.2.1.kind h.1 ρ.1 ρ.2.1, ρ.2.2)

/-- `BRho.old` for the local challenges of a slot. -/
def RhoLo.old :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kinds P A Z → RhoLo P.shape (A.recut P Z) → RhoLo s A
  | _, .nil => fun _ _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z h (ρ : A.1.kind.Lo r.Chal × RhoLo P.shape (RoundSplits.recut P A.2 Z)) =>
      (ρ.1, RhoLo.old P A.2 Z h ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) h
          (ρ : Z.1.kind.Lo Unit ×
            RhoLo P.shape (RoundSplits.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      RhoLo.old P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 h ρ.2
  | _, .msg r1 r2 (s := s) u P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      (A.1.kind.loOf u,
        (RhoLo.old P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z h ρ :
          RhoLo (r1.joinMsg r2 :: s) (A.1.joinMsg A.2.1, A.2.2)))
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      let z : RhoLo (r1.joinChal r2 :: s) (A.1.joinChal r2, A.2.2) :=
        RhoLo.old P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z h.2 ρ
      (A.1.kind.mapLo Prod.fst z.1, Kind.sndLo A.1.kind A.2.1.kind h.1 z.1, z.2)

/-- `BRho.old` for the shared challenges. -/
def RhoSh.old :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kinds P A Z → RhoSh P.shape (A.recut P Z) → RhoSh s A
  | _, .nil => fun _ _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z h (ρ : A.1.kind.Sh r.Chal × RhoSh P.shape (RoundSplits.recut P A.2 Z)) =>
      (ρ.1, RhoSh.old P A.2 Z h ρ.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) h
          (ρ : Z.1.kind.Sh Unit ×
            RhoSh P.shape (RoundSplits.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)) =>
      RhoSh.old P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 h ρ.2
  | _, .msg r1 r2 (s := s) u P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      (A.1.kind.shOf u,
        (RhoSh.old P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z h ρ :
          RhoSh (r1.joinMsg r2 :: s) (A.1.joinMsg A.2.1, A.2.2)))
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h ρ =>
      let z : RhoSh (r1.joinChal r2 :: s) (A.1.joinChal r2, A.2.2) :=
        RhoSh.old P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z h.2 ρ
      (A.1.kind.mapSh Prod.fst z.1, Kind.sndSh A.1.kind A.2.1.kind h.1 z.1, z.2)

/-! ## 3. Protocols and honest provers -/

/-- The honest strategy for the shared component. It still sees the shared challenges only. -/
def SStrat.recut :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kinds P A Z → SStrat s A → SStrat P.shape (A.recut P Z)
  | _, .nil => fun _ _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z h (σ : A.1.M0 × (A.1.kind.Sh r.Chal → SStrat _ A.2)) =>
      (σ.1, fun v => SStrat.recut P A.2 Z h (σ.2 v))
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) h
          (σ : A.1.M0 × (A.1.kind.Sh r.Chal → SStrat s A.2)) =>
      ((Z.1.m0 σ.1).1,
        fun _ =>
          SStrat.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 h ((Z.1.m0 σ.1).2, σ.2))
  | _, .msg r1 r2 (s := s) u P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h
      (σ : A.1.M0 × (A.1.kind.Sh r1.Chal → A.2.1.M0 × (A.2.1.kind.Sh r2.Chal → SStrat s A.2.2))) =>
      SStrat.recut P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z h
        ((σ.1, (σ.2 (A.1.kind.shOf u)).1), (σ.2 (A.1.kind.shOf u)).2)
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z h
      (σ : A.1.M0 × (A.1.kind.Sh r1.Chal → A.2.1.M0 × (A.2.1.kind.Sh r2.Chal → SStrat s A.2.2))) =>
      SStrat.recut P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z h.2
        (σ.1, fun c : A.1.kind.Sh (r1.Chal × r2.Chal) =>
            (σ.2 (A.1.kind.mapSh Prod.fst c)).2 (Kind.sndSh A.1.kind A.2.1.kind h.1 c))

/-- The honest strategy for a slot's component. -/
def LStrat.recut :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → (Z : AXPlan P A) →
    LStrat s A → LStrat P.shape (A.recut P Z)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) Z (σ : A.1.Mj × (r.Chal → LStrat _ A.2)) =>
      (σ.1, fun v => LStrat.recut P A.2 Z (σ.2 v))
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (σ : A.1.Mj × (r.Chal → LStrat s A.2)) =>
      ((Z.1.mj σ.1).1,
        fun _ =>
          LStrat.recut P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 ((Z.1.mj σ.1).2, σ.2))
  | _, .msg r1 r2 (s := s) u P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z
          (σ : A.1.Mj × (r1.Chal → A.2.1.Mj × (r2.Chal → LStrat s A.2.2))) =>
      LStrat.recut P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
        Z ((σ.1, (σ.2 u).1), (σ.2 u).2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z
          (σ : A.1.Mj × (r1.Chal → A.2.1.Mj × (r2.Chal → LStrat s A.2.2))) =>
      LStrat.recut P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z
        (σ.1, fun c : r1.Chal × r2.Chal => (σ.2 c.1).2 c.2)

variable {X : Type} {E : ExtSpec}

/-- The protocol with slots, with its rounds split and merged. -/
def BatchInteractiveOracleProof.recut (Q : BatchInteractiveOracleProof X E) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann) :
    BatchInteractiveOracleProof X E :=
  ⟨Q.loc.recut P, Q.ann.recut P Z⟩

/-- The honest prover: the same coins and the same external string; a value of a slot's local
challenges is in the abort set if the old one is. -/
def BatchHonestProver.recut {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt) (P : XPlan Q.loc.shape)
    (Z : AXPlan P Q.ann) (hK : AXPlan.Kinds P Q.ann Z) : BatchHonestProver (Q.recut P Z) Wt where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := H.ext
  strat0 := fun w c0 => SStrat.recut P Q.ann Z hK (H.strat0 w c0)
  strat := fun w c0 x c => LStrat.recut P Q.ann Z (H.strat w c0 x c)
  Bad := {ρ | RhoLo.old P Q.ann Z hK ρ ∈ H.Bad}
  Hid := fun w x => {ρ | RhoLo.old P Q.ann Z hK ρ ∈ H.Hid w x}
  stop0 := fun ρ => H.stop0 (RhoSh.old P Q.ann Z hK ρ)

/-- Where an old round begins: the number (counted from 0) of the first new round made from the run
of old rounds that contains n. If n is not the first old round of its run, first parts split off
before n is merged into it are not counted. If no merged round is split, that is the new round in
which the old round n begins. -/
def XPlan.idx : {s : Shape} → XPlan s → ℕ → ℕ
  | _, .nil, n => n
  | _, .keep _ _, 0 => 0
  | _, .keep _ P, n + 1 => P.idx n + 1
  | _, .cut _ _, 0 => 0
  | _, .cut _ P, n + 1 => P.idx (n + 1) + 1
  | _, .msg _ _ _ P, n => P.idx (n - 1)
  | _, .chal _ _ _ P, n => P.idx (n - 1)

/-- The record of protocols: encoder, decoder and the number of slots do not change. -/
def BatchProtocol.recut {I X : Type} (L : BatchProtocol I X) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape)
    (XB : XPlan L.onlineBatch.loc.shape) (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) :
    BatchProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := L.decodeIndex
  offline := L.offline.recut XT
  link := L.link.recut XL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.recut XB ZB
  honestOfflineProver := L.honestOfflineProver.recut XT
  honestLinkProver := L.honestLinkProver.recut XL
  honestOnlineBatchProver := L.honestOnlineBatchProver.recut XB ZB hK
  early := L.early
  late := L.late.map XB.idx

/-- What is asked at the round `late` (given that the old rounds 0, .., n are local): every first
part split off a round before n is local; so is the first part split off round n or off the run that
begins with it; n is the first old round of its run; all rounds merged with it by (J1) before a
first part is split off are local. -/
def AXPlan.Late : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → ℕ → Prop
  | _, .nil => fun _ _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z n => match n with
      | 0 => True
      | n + 1 => AXPlan.Late P A.2 Z n
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) n =>
            match n with
      | 0 => Z.1.kind = .lo
      | n + 1 =>
        Z.1.kind = .lo ∧ AXPlan.Late P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 (n + 1)
  | _, .msg r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z n => match n with
      | 0 =>
        A.2.1.kind = .lo ∧
        AXPlan.Late P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z 0
      | 1 => False
      | n + 2 =>
        AXPlan.Late P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z (n + 1)
  | _, .chal r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z n => match n with
      | 0 => AXPlan.Late P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z 0
      | 1 => False
      | n + 2 =>
        AXPlan.Late P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z (n + 1)

/-! ## 4. The pattern `RoundSplits.Fmt` -/

/-- The plan fits `RoundSplits.Fmt`, from the phase ph on. -/
def AXPlan.Fit : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → FPhase → Prop
  | _, .nil => fun _ _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z ph => AXPlan.Fit P A.2 Z (FPhase.after A.1.kind ph)
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) ph =>
      FPhase.fit Z.1.kind A.1.kind ph Z.1.ann2.NoSlot Z.1.ann1.NoShared ∧
      AXPlan.Fit P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 (FPhase.after Z.1.kind ph)
  | _, .msg r1 r2 (s := s) _ P => fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z ph =>
      FPhase.fitMsg A.1.kind A.2.1.kind ph ∧
      AXPlan.Fit P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z ph
  | _, .chal r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z ph =>
      AXPlan.Fit P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z ph

/-! ## 5. The statements -/

namespace Spec


/-- `BatchProtocol.Props` except soundness is preserved, with the same numbers, if the plans and the annotated
splits satisfy their conditions (`XPlan.OK`, `AXPlan.OK`, `AXPlan.Kinds`); soundness at the bound
εs' is a hypothesis. -/
def recutPropsB : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) (XT : XPlan L.offline.shape)
      (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape) (ZB : AXPlan XB L.onlineBatch.ann)
      (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (εs' : ℝ≥0∞),
    XT.OK → XL.OK → XB.OK → AXPlan.OK XB L.onlineBatch.ann ZB → L.Props Ryes Rno M →
    (L.recut XT XL XB ZB hK).Sound Rno εs' →
    (L.recut XT XL XB ZB hK).Props Ryes Rno { M with εs := εs' }


/-- `RoundSplits.Fmt` is preserved by a plan that fits and satisfies `AXPlan.OK` and `Kinds`, and
`ExtShared` by every plan with `Kinds`. -/
def recutFmtB : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann),
    (AXPlan.OK P Q.ann Z → AXPlan.Kinds P Q.ann Z → Q.ann.Fmt →
      AXPlan.Fit P Q.ann Z .first → (Q.recut P Z).ann.Fmt) ∧
    (AXPlan.Kinds P Q.ann Z → Q.ExtShared → (Q.recut P Z).ExtShared)

end Spec

end Iop
