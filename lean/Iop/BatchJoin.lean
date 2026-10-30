-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchJoin.lean: merging two rounds of a protocol with slots: the annotation of the merged round.
Lemmas on it: Iop/BatchJoinProofs.lean. (Words of this library: lean/GLOSSARY.md.)

As Iop/Join.lean for ordinary IOPs, whose header says what the construction is for: (J1) merges two
prover messages, (J2) two challenges. A protocol with slots is an ordinary IOP (a slot's verifier)
with an annotation of its rounds (Iop/Batch.lean): each round has a kind, shared (one challenge for
all slots) or local (one for each slot), and each prover message has a shared component and the
slot's component. This file has the annotation of a merged round. It needs no further data. Plans of
splits and merges: Iop/BatchRecut.lean.
  `RAnn.joinMsg a1 a2`    (J1): both components are pairs; a position belongs to the component to
                          which it belonged; the kind is that of the second round (the kind of the
                          first says nothing: its challenge has one value)
  `RAnn.joinChal a1 r2`   (J2): the components of the first round; the kind of the first round
  `Err.UnitZero`          a round whose challenge has one value has the error 0 (it holds for every
                          list with `Err.Below ε c`, c < 1: `unitZero_of_below`,
                          Iop/BatchJoinProofs.lean)
Which rounds may be merged by (J1), for the pattern of rounds `RoundSplits.Fmt` (`FPhase.fitMsg`), with ph
the phase of the first of the two rounds. A round's phase (`FPhase`, Iop/BatchFmt.lean) is: before
the first round (`first`); in the local rounds before the shared ones (`loc`); in the shared rounds
(`shr`); in the local rounds after them (`aft`) (how a round moves the phase: `RoundSplits.FmtFrom`,
`FPhase.afterLo`, Iop/BatchFmt.lean). The joining round is the first shared round.
  two local rounds; two shared rounds, the first of which may be the joining round           allowed
  a local round and the joining round after it, if a local round comes before
      allowed: the merged round is the joining round, with both components
  all else   rejected here
The soundness property `SndB` (Snd-B) and N = 0. A prover message merged by (J1) must not change the
state from 0 to 1; that it does not follows from the condition on challenges (`JointLaw`), which
says nothing if there is no slot. So the statements on (Snd-B) (`sndB_recut`, `sndBL_recut`,
Iop/BatchRecutProofs.lean) ask for 0 < N.
-/
import Iop.Join
import Iop.Batch
import Iop.BatchFmt
import Iop.BatchPull
import Iop.BatchSplit

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Challenges of the whole batch -/

namespace Kind
variable {C C1 C2 : Type} {N : ℕ}

/-- the same value for all slots -/
def constAll (N : ℕ) : (k : Kind) → C → k.All N C
  | sh, c => c
  | lo, c => fun _ => c

/-- the second coordinates of a challenge of pairs, for two rounds of the same kind -/
def sndAll : (k1 k2 : Kind) → k2 = k1 → k1.All N (C1 × C2) → k2.All N C2
  | sh, sh, _, c => c.2
  | lo, lo, _, c => fun j => (c j).2

/-- the challenge of pairs -/
def pairAll : (k1 k2 : Kind) → k2 = k1 → k1.All N C1 → k2.All N C2 → k1.All N (C1 × C2)
  | sh, sh, _, a, b => (a, b)
  | lo, lo, _, a, b => fun j => (a j, b j)

def sndSh : (k1 k2 : Kind) → k2 = k1 → k1.Sh (C1 × C2) → k2.Sh C2
  | sh, sh, _, c => c.2
  | lo, lo, _, _ => ()

def sndLo : (k1 k2 : Kind) → k2 = k1 → k1.Lo (C1 × C2) → k2.Lo C2
  | sh, sh, _, _ => ()
  | lo, lo, _, c => c.2

end Kind

/-! ## 2. Annotations -/

section
variable {r1 r2 : Round}

/-- (J1): the annotation of the merged round. -/
@[reducible] def RAnn.joinMsg (a1 : RAnn r1) (a2 : RAnn r2) : RAnn (r1.joinMsg r2) where
  kind := a2.kind
  M0 := a1.M0 × a2.M0
  Mj := a1.Mj × a2.Mj
  split :=
    { toFun := fun m =>
        (((a1.split (Round.msgFst m)).1, (a2.split (Round.msgSnd m)).1),
          ((a1.split (Round.msgFst m)).2, (a2.split (Round.msgSnd m)).2))
      invFun := fun z => Round.msgPair (a1.join z.1.1 z.2.1) (a2.join z.1.2 z.2.2)
      left_inv := fun m => by
        show Round.msgPair
            (a1.split.symm ((a1.split (Round.msgFst m)).1, (a1.split (Round.msgFst m)).2))
            (a2.split.symm ((a2.split (Round.msgSnd m)).1, (a2.split (Round.msgSnd m)).2)) = m
        rw [Prod.mk.eta, Prod.mk.eta, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl
      right_inv := fun z => by
        show (((a1.split (a1.split.symm (z.1.1, z.2.1))).1,
              (a2.split (a2.split.symm (z.1.2, z.2.2))).1),
            ((a1.split (a1.split.symm (z.1.1, z.2.1))).2,
              (a2.split (a2.split.symm (z.1.2, z.2.2))).2)) = z
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] }
  P0 := a1.P0 × a2.P0
  Pj := a1.Pj × a2.Pj
  pl0 := fun m => (a1.pl0 m.1, a2.pl0 m.2)
  plj := fun m => (a1.plj m.1, a2.plj m.2)
  plain :=
    (Equiv.prodCongr a1.plain a2.plain).trans (Equiv.prodProdProdComm a1.P0 a1.Pj a2.P0 a2.Pj)
  own := fun p => match p with
    | .inl p => a1.own p
    | .inr p => a2.own p

/-- (J2): the annotation of the merged round is that of the first round. -/
@[reducible] def RAnn.joinChal (a1 : RAnn r1) (r2 : Round) : RAnn (r1.joinChal r2) where
  kind := a1.kind
  M0 := a1.M0
  Mj := a1.Mj
  split := a1.split
  P0 := a1.P0
  Pj := a1.Pj
  pl0 := a1.pl0
  plj := a1.plj
  plain := a1.plain
  own := a1.own

end





/-! ## 3. Error counts -/


variable {X : Type} {E : ExtSpec}



/-- A round whose challenge has one value has the error 0. -/
def Err.UnitZero : {s : Shape} → Err s → Prop
  | [], _ => True
  | r :: _, (e, ε) => (Fintype.card r.Chal = 1 → e = 0) ∧ Err.UnitZero ε

/-! ## 4. The pattern `RoundSplits.Fmt` -/

/-- The table in the header, for (J1): may a round of the kind k1 in the phase ph be merged with the
next, of the kind k2? -/
def FPhase.fitMsg (k1 k2 : Kind) (ph : FPhase) : Prop :=
  match k1, k2, ph with
  | .lo, .lo, _ => True
  | .sh, .sh, .loc => True
  | .sh, .sh, .shr => True
  | .lo, .sh, .loc => True
  | _, _, _ => False

end Iop
