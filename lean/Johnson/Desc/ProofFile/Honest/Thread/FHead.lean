-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHead.lean: the condition `keeps` of the first chain's
invariant at the full size, written kind by kind. `lettersHead` (FirstHead.lean) takes `keeps`
through an argument `Kp`, and `kpBy f` (KeepsBy.lean) gives `Kp` from a family `f` with one clause
for each kind of sub-protocol. Until now `f` was an argument everywhere. Here it is one definition,
`fHead`. Each arm is the clause that the authors of that kind's lemmas have written, at the name
under which their lemmas prove it from the sub-protocol's accepting step.

  1  `fHead`   the definition
  2  `fHead_frame`, `fHead_K3`, `fHead_K5`, `fHead_K6`   it satisfies the equations that lemmas of
     other files ask of `f` as hypotheses
  3  `fHead_K1_first`, `fHead_K1_send`, `fHead_K1_later`, `fHead_K2_link`, `fHead_K2_head`,
     `fHead_K2_finish`   what the arms with cases are at each case

The arguments. Each stands for public numbers of one kind, and whoever instantiates the invariant
supplies them.
  * `Zp`, `cF`: the public part and the first chain, as in `AtMgA`.
  * `G`: the ground from which the clause of K7 takes its numbers.
  * `take l`: segment `l` leaves a pending row (KeepsFrame.lean).
  * `P11`, `p12`, `P13`: the numbers of K11, K12, K13.

Four arms are not one author's clause as it stands.
  * Number 2 (kind K1, segment 0, piece 1). The sub-protocol is K1's opening with the frame's step
    "opened" joined after it. `K1KeepsAt` is `False` there by its own text. The arm has the form in
    which `keeps_joined_openedR` (OpenedKeepsR.lean) ends: there is a state between; `K1FirstKeeps`
    and `K1Out` (Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean) hold up to it and
    `keepsOpenedR 0` from it.
  * Number 356 (kind K1, no segment, piece 4). The sub-protocol is K1's sending of W with a step of
    K13 after it. `K1KeepsAt` is `False` there too. There is a state between; `K1SendKeeps` holds up
    to it and `K13RowsKeeps P13` (Johnson/Desc/K13/Honest/RowsKeeps.lean) from it. "No mark of
    failure after the step" is added here.
  * The 50 other sub-protocols of K1. The arm is `K1KeepsAt` and `K1LaterRels` (K1LaterRels.lean):
    six relations that the items `row` and `pile` need in order to pass over a sending
    (RowForward.lean, PileForward.lean).
  * The code switch (K2). `K2Keeps` (Johnson/Desc/K2/Honest/KeepsAt.lean) reads of its parameter
    only the field `stands`. So the arm says: `K2Keeps` holds at some parameter with the `stands` of
    the place. At the first places of segments 1 to 23 the code switch is joined with "opened" as
    at number 2, and the arm has the same form, with `K2Keeps` up to the state between. The number
    24 in the text is the output head's segment at the full size.

Limits.
  * A definition and unfoldings. Nothing shows that any clause holds at any step.
  * At K11 the clause is the stronger `K11KeepsYesAt`, which contains the acceptance of the merge's
    own decision.
  * Full size only.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.K1LaterRels
import Johnson.Desc.ProofFile.Honest.Thread.OpenedKeepsR
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.OpenedKeeps
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsMember
import Johnson.Desc.K2.Honest.KeepsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.K5.Honest.Law.KeepsM
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.ProofFile.Honest.K7.KeepsAt
import Johnson.Desc.K8.Honest.KeepsMark
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtPlace
import Johnson.Desc.K10.Honest.Keeps
import Johnson.Desc.K11.Returns.KeepsYesStatement
import Johnson.Desc.K12.Honest.Shape.TestKeepsFirst
import Johnson.Desc.K13.Honest.KeepsAllM3
import Johnson.Desc.K13.Honest.RowsKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open P5J (TS)

/-- **The clause of `keeps` of the first chain's sub-protocols at the full size, kind by kind.** The
file's head says what each argument is and why some arms have cases. The number 24 is the output
head's segment at the full size. At K2, "some `q`" loses nothing against a named parameter:
`K2Keeps` reads of `q` only the field `stands` (Johnson/Desc/K2/Honest/KeepsAt.lean). It is a
definition: it fills an argument of the invariant. -/
def fHead (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) : KindName → Place → TS → TS → Prop
  | .frame => keepsFrame P5J.At.links take
  | .K1 => fun p s s' =>
    if p.link = some 0 ∧ p.piece = 1 then
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s'
    else if p.link = none ∧ p.piece = 4 then
      (∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P13 m s') ∧ s'.failed = none
    else ProofFile.Honest.K1.K1KeepsAt p s s' ∧ K1LaterRels s s'
  | .K2 => fun p s s' =>
    match p.link with
    | some l =>
      if l = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
      else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s'
    | none => ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .finish ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
  | .K3 => ProofFile.Honest.K3.Law.AtThr.k3KeepsAt Zp
  | .K4 => fun _ => ProofFile.Honest.K4.K4KeepsM
  | .K5 => H2K5.Honest.K5KeepsAt (P5J.At.X Zp)
  | .K6 => fun _ => VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps
  | .K7 => K7KeepsAt G
  | .K8 => fun _ => VerifiableInference.Desc.First.K8.Honest.K8KeepsM
  | .K9 => ProofFile.Honest.K9.k9KeepsAt cF Zp
  | .K10 => fun _ => ProofFile.Honest.K10.YesFree.K10Keeps
  | .K11 => Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt P11
  | .K12 => fun _ => ProofFile.Honest.Sh.K12KeepsFirst p12
  | .K13 => fun _ => VerifiableInference.Desc.K13.Honest.K13KeepsAll P13
  | .K14 => fun _ _ _ => True
  | .K15 => fun _ _ _ => True

variable (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-! ## 2 The equations that other files ask of `f` -/

theorem fHead_frame :
    fHead Zp cF G take P11 p12 P13 KindName.frame = keepsFrame P5J.At.links take := rfl

theorem fHead_K3 :
    fHead Zp cF G take P11 p12 P13 .K3 = ProofFile.Honest.K3.Law.AtThr.k3KeepsAt Zp := rfl

theorem fHead_K5 (p : Place) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K5 p s s' ↔
      H2K5.Honest.K5KeepsAt (P5J.At.X Zp) p s s' := Iff.rfl

theorem fHead_K6 (p : Place) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K6 p s s' ↔
      VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps s s' := Iff.rfl

/-! ## 3 The arms with cases -/

/-- At number 2. -/
theorem fHead_K1_first {p : Place} (h1 : p.link = some 0) (h2 : p.piece = 1) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K1 p s s' ↔
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s' := by
  show (if p.link = some 0 ∧ p.piece = 1 then
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s'
    else if p.link = none ∧ p.piece = 4 then
      (∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P13 m s') ∧ s'.failed = none
    else ProofFile.Honest.K1.K1KeepsAt p s s' ∧ K1LaterRels s s') ↔ _
  rw [if_pos ⟨h1, h2⟩]

/-- At number 356. -/
theorem fHead_K1_send {p : Place} (h1 : p.link = none) (h2 : p.piece = 4) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K1 p s s' ↔
      (∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P13 m s') ∧ s'.failed = none := by
  have n1 : ¬ (p.link = some 0 ∧ p.piece = 1) := fun h => by
    rw [h1] at h
    cases h.1
  show (if p.link = some 0 ∧ p.piece = 1 then
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s'
    else if p.link = none ∧ p.piece = 4 then
      (∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P13 m s') ∧ s'.failed = none
    else ProofFile.Honest.K1.K1KeepsAt p s s' ∧ K1LaterRels s s') ↔ _
  rw [if_neg n1, if_pos ⟨h1, h2⟩]

/-- At a place inside a segment behind its first piece. -/
theorem fHead_K1_later {p : Place} {l : Nat} (h1 : p.link = some l) (h2 : p.piece ≠ 1)
    (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K1 p s s' ↔
      ProofFile.Honest.K1.K1KeepsAt p s s' ∧ K1LaterRels s s' := by
  have n1 : ¬ (p.link = some 0 ∧ p.piece = 1) := fun h => h2 h.2
  have n2 : ¬ (p.link = none ∧ p.piece = 4) := fun h => by
    rw [h1] at h
    cases h.1
  show (if p.link = some 0 ∧ p.piece = 1 then
      ∃ m, (ProofFile.Honest.K1.K1FirstKeeps s m ∧ ProofFile.Honest.K1.K1Out s m) ∧ keepsOpenedR 0 m s'
    else if p.link = none ∧ p.piece = 4 then
      (∃ m, ProofFile.Honest.K1.K1SendKeeps s m ∧
        VerifiableInference.Desc.K13.Honest.K13RowsKeeps P13 m s') ∧ s'.failed = none
    else ProofFile.Honest.K1.K1KeepsAt p s s' ∧ K1LaterRels s s') ↔ _
  rw [if_neg n1, if_neg n2]

/-- At the first place of a segment other than the output head's. -/
theorem fHead_K2_link {p : Place} {l : Nat} (h1 : p.link = some l) (h2 : l ≠ 24) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K2 p s s' ↔
      ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s' := by
  show (match p.link with
    | some l =>
      if l = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
      else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s'
    | none => ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .finish ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s') ↔ _
  rw [h1]
  show (if l = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
    else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s') ↔ _
  rw [if_neg h2]

/-- In the output head's segment. -/
theorem fHead_K2_head {p : Place} (h1 : p.link = some 24) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K2 p s s' ↔
      ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s' := by
  show (match p.link with
    | some l =>
      if l = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
      else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s'
    | none => ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .finish ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s') ↔ _
  rw [h1]
  show (if 24 = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
    else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR 24 m s') ↔ _
  rw [if_pos rfl]

/-- After the last segment. -/
theorem fHead_K2_finish {p : Place} (h1 : p.link = none) (s s' : TS) :
    fHead Zp cF G take P11 p12 P13 .K2 p s s' ↔
      ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .finish ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s' := by
  show (match p.link with
    | some l =>
      if l = 24 then ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .head ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s s'
      else ∃ m, (∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .link ∧
        VerifiableInference.Desc.K2.Honest.K2Keeps q s m) ∧ keepsOpenedR l m s'
    | none => ∃ q : VerifiableInference.Desc.First.K2.P2, q.stands = .finish ∧
      VerifiableInference.Desc.K2.Honest.K2Keeps q s s') ↔ _
  rw [h1]

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_frame
#print axioms ProofFile.Honest.FirstThread.fHead_K3
#print axioms ProofFile.Honest.FirstThread.fHead_K5
#print axioms ProofFile.Honest.FirstThread.fHead_K6
#print axioms ProofFile.Honest.FirstThread.fHead_K1_first
#print axioms ProofFile.Honest.FirstThread.fHead_K1_send
#print axioms ProofFile.Honest.FirstThread.fHead_K1_later
#print axioms ProofFile.Honest.FirstThread.fHead_K2_link
#print axioms ProofFile.Honest.FirstThread.fHead_K2_head
#print axioms ProofFile.Honest.FirstThread.fHead_K2_finish
