-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKeyOwn/ReadsAtPins.lean: THE TWO READS THAT THE KEY FILE's OWN TEST OWES, AT A SOURCE WHOSE PUBLIC
VALUES ARE THE WRITTEN ONES (ChainPins, Johnson/HB/LLHARD/KB4/Frame.lean). The public premises of ReadsBelow.lean are paid here:
rewritten to the written letters, then evaluated in Lean's kernel.

  wReads_of_readsBelow   from readsBelow to the form "two fronts that agree on the first n challenges give one datum"
  lenIs, lensOk, frontBy, front_by   a list's length in stretches; roundsInFront with the numbers of rounds handed in
  stretchesW, lookW, faceW, baseW, battW, nW   the written letters (nW off the written declared rounds declKeyFull)
  belowW_yes · batt_tight · nW_eq · sharedW_eq   CLOSED FACTS, by evaluation in Lean's kernel. batt_tight IS THE TOOTH: the last
                         challenge that W's data reads is the last one heard in front of W's sending: at n - 1 the bound fails
  keyPointsBelow_pinned · battBelow_pinned   the two public premises, under ChainPins
  keyW_readsBelow_pinned   W's sending reads none but the challenges heard when its tree is sent
  **wReads_pinned**      the clause wReads of the own test's ground, at K.w := batchedRowsSending f Xs N
  **omegaReads_pinned**  the clause omegaReads, at a sender whose atPoint is 0: the tree of "send o_omega" is sent behind round 0

Cost. No line of the kernel's climbs more than 2,400 rounds: the sub-protocols' numbers of rounds are held in stretches
(stretchesW_yes, front_by), the walk over the declared rounds likewise (quiet1 to quiet8, skip_quiet).

Limits. ChainPins is a hypothesis. That a value's field w is batchedRowsSending f Xs N, and that its sender's atPoint is 0, is the caller's
to say. At the full size alone. This file proves nothing about completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKeyOwn.ReadsBelow
import E2E.KeyThreadBase
import Johnson.HB.LLHARD.KB4.Frame
import Johnson.Desc.ProofFile.Honest.Small.SentFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKeyOwn
open OnBytes OnBytes.Params
open ProofFile.Honest.K1 (SendJob)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource pieces)
open AtPublicFiles.KeyThread (sentIn decl₁ decl₂ fixedLast)
open AtPublicFiles.KeyValues (batchedRowsSending keyPoints battAt baseAt faceAt lookAt blocksOf placeAt oneOf)
open Lk6.AtPlan (keyFull)
open Johnson.KB4 (WK ChainPins first_of decl_of)
open Johnson.KB8 (declKeyFull)

variable {W X : Type}

/-- **Two fronts that agree on the first n challenges give one datum.** -/
theorem wReads_of_readsBelow {J : SendJob W X} {n : Nat} (h : readsBelow J n) :
    ∀ x (fr fr' : Front X), fr.heard.take n = fr'.heard.take n → J.data x fr = J.data x fr' := by
  intro x fr fr' e
  rw [← h x fr fr.own fr.seen, ← h x fr' fr.own fr.seen, e]

/-! ## Lengths in stretches -/

/-- The list has just the lengths cs, one stretch behind the other. -/
def lenIs {α : Type} : List α → List Nat → Bool
  | l, [] => l.isEmpty
  | l, c :: cs => ((l.take c).length == c) && lenIs (l.drop c) cs

theorem lenIs_length {α : Type} : ∀ (cs : List Nat) (l : List α), lenIs l cs = true → l.length = cs.sum
  | [], l, h => by
    have e : l = [] := List.isEmpty_iff.1 h
    rw [e]
    rfl
  | c :: cs, l, h => by
    unfold lenIs at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have e := congrArg List.length (List.take_append_drop c l)
    rw [List.length_append, h.1, lenIs_length cs _ h.2] at e
    rw [← e, List.sum_cons]

/-- Each sub-protocol's rounds have the lengths of its row. -/
def lensOk {S Cl : Type} : List (VerifiableInference.Desc.Block S Cl) → List (List Nat) → Bool
  | [], [] => true
  | b :: bs, cs :: r => lenIs b.rounds cs && lensOk bs r
  | _, _ => false

/-- roundsInFront, with the numbers of rounds handed in. -/
def frontBy {S Cl : Type} : List (VerifiableInference.Desc.Block S Cl) → List Nat → Place → Option Nat
  | b :: bs, n :: ns, a => if b.place == a then some 0 else (frontBy bs ns a).map (· + n)
  | _, _, _ => none

theorem front_by {S Cl : Type} : ∀ (bs : List (VerifiableInference.Desc.Block S Cl)) (css : List (List Nat)),
    lensOk bs css = true → ∀ a, roundsInFront bs a = frontBy bs (css.map List.sum) a
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | b :: bs, cs :: r, h, a => by
    unfold lensOk at h
    simp only [Bool.and_eq_true] at h
    show (if b.place == a then some 0 else (roundsInFront bs a).map (· + b.rounds.length)) =
      (if b.place == a then some 0 else (frontBy bs (r.map List.sum) a).map (· + cs.sum))
    rw [front_by bs r h.2 a, lenIs_length cs _ h.1]

/-! ## The written letters -/

/-- The first chain's nineteen sub-protocols' numbers of rounds, in stretches of at most 2,400. -/
def stretchesW : List (List Nat) :=
  [[2], [2], [], [], [2400, 2400, 2400, 2381], [], [], [], [], [], [2400, 2400, 2400, 2020], [], [], [],
    [], [23], [20], [2], [1]]

def lookW : List Lkp.Public := Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)
def faceW (i : Nat) : K3.LFace := VerifiableInference.Desc.K3.faceOfLkp (lookW.getD i default)
def baseW (i : Nat) : Nat := (frontBy WK.first.blocksInOrder (stretchesW.map List.sum) (placeAt i)).getD 0
def battW : Nat :=
  (frontBy WK.first.blocksInOrder (stretchesW.map List.sum) (⟨1, none, pieces.batt, .K13⟩ : Place)).getD 0
def nW : Nat := sentIn declKeyFull.1 5

/-- The test: at each part of each written lookup that has a level, the two bounds. -/
def belowW : Bool :=
  (List.range lookW.length).all fun i => (List.range (faceW i).parts.length).all fun p =>
    match (faceW i).parts.getD p 0 with
    | 0 => true
    | m + 1 => decide (K3.roundAt (faceW i) (baseW i) (.key p m) + 1 + m ≤ 18848) &&
        decide (K3.roundAt (faceW i) (baseW i) (.keyLine p m) < 18848)

/-! ## Closed facts -/

theorem stretchesW_yes : lensOk WK.first.blocksInOrder stretchesW = true := by decide +kernel

theorem belowW_yes : belowW = true := by decide +kernel

/-- A stretch of c rounds from round a on that sends no tree. -/
def quietB (l : List Fmt.DeclaredRound) (a c : Nat) : Bool :=
  ProofFile.Honest.Small.rootsSum ((l.drop a).take c) == 0 && ((l.drop a).take c).length == c

/-- Behind such a stretch the sending round is c later. -/
theorem skip_quiet (l : List Fmt.DeclaredRound) (a c j : Nat) (h : quietB l a c = true) :
    VerifiableInference.Desc.sendRound (l.drop a) j =
      (VerifiableInference.Desc.sendRound (l.drop (a + c)) j).map (· + c) := by
  unfold quietB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have e := ProofFile.Honest.Small.sender_behind ((l.drop a).take c) ((l.drop a).drop c) j
  rw [List.take_append_drop, h.1, h.2, List.drop_drop, Nat.zero_add] at e
  exact e

/-! In stretches of at most 2,400 rounds: over all 18,848 at once the kernel answers "deep recursion". -/

theorem frontRoots : ProofFile.Honest.Small.rootsSum (declKeyFull.1.take 4) = 2 := by decide +kernel
theorem frontLength : (declKeyFull.1.take 4).length = 4 := by decide +kernel
theorem quiet1 : quietB declKeyFull.1 4 2400 = true := by decide +kernel
theorem quiet2 : quietB declKeyFull.1 2404 2400 = true := by decide +kernel
theorem quiet3 : quietB declKeyFull.1 4804 2400 = true := by decide +kernel
theorem quiet4 : quietB declKeyFull.1 7204 2400 = true := by decide +kernel
theorem quiet5 : quietB declKeyFull.1 9604 2400 = true := by decide +kernel
theorem quiet6 : quietB declKeyFull.1 12004 2400 = true := by decide +kernel
theorem quiet7 : quietB declKeyFull.1 14404 2400 = true := by decide +kernel
theorem quiet8 : quietB declKeyFull.1 16804 2001 = true := by decide +kernel
theorem backSends : VerifiableInference.Desc.sendRound (declKeyFull.1.drop 18805) 3 = some 43 := by
  decide +kernel

/-- W's tree is sent in round 18848 of the first chain. -/
theorem nW_eq : nW = 18848 := by
  have e := ProofFile.Honest.Small.sender_behind (declKeyFull.1.take 4) (declKeyFull.1.drop 4) 3
  rw [List.take_append_drop, frontRoots, frontLength, skip_quiet _ 4 2400 3 quiet1,
    skip_quiet _ 2404 2400 3 quiet2, skip_quiet _ 4804 2400 3 quiet3,
    skip_quiet _ 7204 2400 3 quiet4, skip_quiet _ 9604 2400 3 quiet5,
    skip_quiet _ 12004 2400 3 quiet6, skip_quiet _ 14404 2400 3 quiet7,
    skip_quiet _ 16804 2001 3 quiet8, backSends] at e
  unfold nW sentIn
  rw [show (5 : Nat) = 2 + 3 from rfl, e]
  rfl

/-- **THE TOOTH**: the batching's last column variable's challenge is the last one in front of W's sending. -/
theorem batt_tight : battW + 2 + (Wf.matrixOf keyFull.once.shape).kCol = 18848 := by decide +kernel

/-- There are lookups, and each has a part with a level: the test is not idle. -/
theorem belowW_bites : lookW.length = 2 ∧ (faceW 0).parts.getD 0 0 = 36 ∧ (faceW 1).parts.getD 0 0 = 35 := by
  decide +kernel

theorem face_default : (VerifiableInference.Desc.K3.faceOfLkp default).parts = [] := by decide +kernel

/-- The tree of "send o_omega" is sent in round 4 of the shared chain. -/
theorem sharedW_eq : sentIn declKeyFull.2.1 1 = 4 := by decide +kernel

/-! ## Under the pins -/

variable {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

theorem faceAt_pinned (h : ChainPins Xs N Pl) (i : Nat) : faceAt Xs i = faceW i := by
  unfold faceAt lookAt VerifiableInference.Desc.Key.lookupsOf
  rw [h.ranges, h.lin]
  rfl

theorem blocks_pinned (h : ChainPins Xs N Pl) : blocksOf Xs N = WK.first.blocksInOrder :=
  congrArg (·.blocksInOrder) (first_of h)

theorem baseAt_pinned (h : ChainPins Xs N Pl) (i : Nat) : baseAt Xs N i = baseW i := by
  unfold baseAt
  rw [blocks_pinned h]
  exact congrArg (·.getD 0) (front_by _ _ stretchesW_yes (placeAt i))

theorem sent5_pinned (h : ChainPins Xs N Pl) : sentIn (decl₁ (descriptionFromSource Xs N Pl)) 5 = 18848 := by
  have e : decl₁ (descriptionFromSource Xs N Pl) = declKeyFull.1 := congrArg Prod.fst (decl_of h)
  rw [e]
  exact nW_eq

/-- **The key claims' points lie below W's sending.** -/
theorem keyPointsBelow_pinned (h : ChainPins Xs N Pl) :
    KeyPointsBelow Xs N (sentIn (decl₁ (descriptionFromSource Xs N Pl)) 5) := by
  intro i p m hm
  rw [sent5_pinned h, faceAt_pinned h, baseAt_pinned h]
  rw [faceAt_pinned h] at hm
  by_cases hi : i < lookW.length
  · by_cases hp : p < (faceW i).parts.length
    · have t := List.all_eq_true.1 (List.all_eq_true.1 belowW_yes i (List.mem_range.2 hi)) p
        (List.mem_range.2 hp)
      rw [hm] at t
      simp only [Bool.and_eq_true, decide_eq_true_eq] at t
      exact t
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hp)] at hm
      cases hm
  · have e : (faceW i).parts = [] := by
      unfold faceW
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact face_default
    rw [e] at hm
    cases hm

/-- **The batching's challenges lie below W's sending**: with equality (batt_tight). -/
theorem battBelow_pinned (h : ChainPins Xs N Pl) :
    (battAt Xs N).first + (Wf.matrixOf (oneOf Xs).lin).kCol ≤ sentIn (decl₁ (descriptionFromSource Xs N Pl)) 5 := by
  rw [sent5_pinned h, h.lin]
  show (roundsInFront (blocksOf Xs N) (⟨1, none, pieces.batt, .K13⟩ : Place)).getD 0 + 2 + _ ≤ _
  rw [blocks_pinned h]
  exact Nat.le_of_eq ((congrArg (fun o : Option Nat => o.getD 0 + 2 + (Wf.matrixOf keyFull.once.shape).kCol)
    (front_by _ _ stretchesW_yes (⟨1, none, pieces.batt, .K13⟩ : Place))).trans batt_tight)

/-- **W's SENDING READS NONE BUT THE CHALLENGES HEARD WHEN ITS TREE IS SENT.** -/
theorem keyW_readsBelow_pinned {W₀ Rc : Type} (h : ChainPins Xs N Pl) (f : W₀ → Weights) :
    readsBelow (batchedRowsSending (Rc := Rc) (X := X) f Xs N) (fixedLast (descriptionFromSource Xs N Pl) (.taken 0 5)) :=
  keyW_readsBelow f Xs N _ (keyPointsBelow_pinned h) (battBelow_pinned h)

/-- **THE CLAUSE wReads OF THE OWN TEST's GROUND**, at K.w := batchedRowsSending f Xs N. -/
theorem wReads_pinned {W₀ Rc : Type} (h : ChainPins Xs N Pl) (f : W₀ → Weights) :
    ∀ x (fr fr' : Front X),
      fr.heard.take (fixedLast (descriptionFromSource Xs N Pl) (.taken 0 5)) =
        fr'.heard.take (fixedLast (descriptionFromSource Xs N Pl) (.taken 0 5)) →
      (batchedRowsSending (Rc := Rc) (X := X) f Xs N).data x fr = (batchedRowsSending (Rc := Rc) (X := X) f Xs N).data x fr' :=
  wReads_of_readsBelow (keyW_readsBelow_pinned h f)

/-- **THE CLAUSE omegaReads**, at a sender whose atPoint is 0. -/
theorem omegaReads_pinned (h : ChainPins Xs N Pl) : 0 < sentIn (decl₂ (descriptionFromSource Xs N Pl)) 1 := by
  have e : decl₂ (descriptionFromSource Xs N Pl) = declKeyFull.2.1 :=
    congrArg (fun t : _ × _ × _ => t.2.1) (decl_of h)
  rw [e, sharedW_eq]
  exact Nat.succ_pos 3

end ProofFile.Honest.K12.AtKeyOwn

#print axioms ProofFile.Honest.K12.AtKeyOwn.belowW_yes
#print axioms ProofFile.Honest.K12.AtKeyOwn.batt_tight
#print axioms ProofFile.Honest.K12.AtKeyOwn.keyPointsBelow_pinned
#print axioms ProofFile.Honest.K12.AtKeyOwn.battBelow_pinned
#print axioms ProofFile.Honest.K12.AtKeyOwn.wReads_pinned
#print axioms ProofFile.Honest.K12.AtKeyOwn.omegaReads_pinned
