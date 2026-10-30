-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Front.lean

What it proves. The front of the proximity test's parts (guardedProximityTestParts.front,
Johnson/Desc/K12/JoinGuarded.lean) reads no row's target: at two records inside a test that agree but for
targets (Agree, Wipe.lean in this folder), at one list of rounds and one list of groups: both refuse
with one word, or both return, and what they return agrees but for targets. No premise but Agree. It
is one of the five steps by which the test's text advances the verifier's state.

Names.
  on_map             a clause on a value that may be missing, at a mapped value.
  frontL_wipe        the front's nineteen named clauses are one list at a statement and at that
      statement with every target set to zero.
  openClaimsE_wipe   so is the outcome of the test on the claims that lie open on the group.
  frontE_wipe, frontE_rel   the front's whole test: at a statement and that statement wiped; at two
      statements that agree but for targets.
  frontJ_alike       the front as Johnson/Desc/K12/Join.lean has it.
  front_agree        the step, with guardedProximityTestParts's two own guards: (f), on the count of roots; (p), on
      the record's codes.

By what. The texts of frontL, frontE (Johnson/Desc/K12/Front.lean), openClaimsE, refuse
(Johnson/Desc/Ground/Ask.lean), frontJ, guardedProximityTestParts. pass_cases (Wipe.lean). Of the kind K10's authors:
AlikeE and its laws (Honest/K10/Wipe/Alike.lean); wipeSt_group_at, wipeSt_oracle_at, wipeSt_size
(Honest/K10/BatWipe.lean); rowL_wipe (Honest/K10/Wipe/WipeGround.lean).

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: BatWipe, StAtZero, Wipe/Alike, Wipe/KeepK10, Wipe/WipeGround,
Wipe/WipeLaws, WipeFold, WipeS), and Wipe.lean and Fold.lean in this folder.

Limits.
- At one list of groups: this is no law on a fold at made-up columns through the test's block. The
  front hands its rounds and its groups to nobody: at it the list is idle.
- The front alone of the five steps. The base case tests a target's value: no such law holds there.
  The verifier runs the base case; the prover's text of the test (Test.lean in the folder above)
  never does.
- Values of coefficients are tested here (the eighth clause on a claim: no coefficient on a pad): so
  "agree in shape" would not serve in the place of Agree.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open OnBytes (Statement TreeBook Row)
open VerifiableInference.Desc.Ground (on refuse openClaimsE rowL)
open VerifiableInference.Desc.K12 (T12 Passing P12 guardedProximityTestParts frontJ frontL frontE)
open ProofFile.Honest.K10 (wipeSt wipeRow wipeOr wipeGr AlikeE wipeSt_group_at wipeSt_oracle_at
  wipeSt_size rowL_wipe)

/-- A clause on a value that may be missing, at a mapped value. -/
theorem on_map {α β : Type} (x : Option α) (h : α → β) (f : β → Bool) :
    on (x.map h) f = on x fun a => f (h a) := by
  cases x <;> rfl

/-- The list of clauses at the front of a proximity test is one at a statement and at that statement
with every target set to zero: name by name, Bool by Bool. -/
theorem frontL_wipe (S : Statement) (B : TreeBook) (g : Nat) (mask : Option Nat) :
    frontL (wipeSt S) B g mask = frontL S B g mask := by
  have hM : (mask.bind fun m => (S.oracles[m]?).map wipeOr) =
      (mask.bind fun m => S.oracles[m]?).map wipeOr := by
    cases mask <;> rfl
  unfold frontL
  simp only [wipeSt_group_at, wipeSt_oracle_at, wipeSt_size, hM, on_map, Option.isSome_map]
  have hS : ∀ y : OnBytes.Oracle, (wipeOr y).sampleRows.size = y.sampleRows.size := fun y => by
    show (y.sampleRows.map wipeRow).size = _
    rw [Array.size_map]
  have hR : ∀ G : OnBytes.Group, ((wipeGr G).rows.all fun r => r.kind != .sample) =
      G.rows.all fun r => r.kind != .sample := fun G => by
    show ((G.rows.map wipeRow).all fun r => r.kind != .sample) = _
    rw [Array.all_map]
    rfl
  simp only [hS, hR]
  rfl

/-- "Every claim that lies open on the group could be laid on it now" has one outcome at both: one
word, or yes. -/
theorem openClaimsE_wipe (S : Statement) (g : Nat) :
    openClaimsE (wipeSt S) g = openClaimsE S g := by
  unfold openClaimsE
  rw [wipeSt_group_at]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    show ((G.rows.map wipeRow).toList.forM fun row => refuse (rowL (wipeSt S) g row)) =
      G.rows.toList.forM fun row => refuse (rowL S g row)
    rw [Array.toList_map]
    induction G.rows.toList with
    | nil => rfl
    | cons r l ih =>
      show (refuse (rowL (wipeSt S) g (wipeRow r)) >>= fun _ =>
          (l.map wipeRow).forM fun row => refuse (rowL (wipeSt S) g row)) =
        (refuse (rowL S g r) >>= fun _ => l.forM fun row => refuse (rowL S g row))
      rw [rowL_wipe, ih]

/-- So has the front's whole test. -/
theorem frontE_wipe (S : Statement) (B : TreeBook) (g : Nat) (mask : Option Nat) :
    frontE (wipeSt S) B g mask = frontE S B g mask := by
  unfold frontE
  rw [frontL_wipe, openClaimsE_wipe]

/-- At two statements that agree but for targets. -/
theorem frontE_rel {S S' : Statement} (h : wipeSt S = wipeSt S') (B : TreeBook) (g : Nat)
    (mask : Option Nat) : frontE S B g mask = frontE S' B g mask := by
  rw [← frontE_wipe S, ← frontE_wipe S', h]

/-- The front as Join.lean has it. -/
theorem frontJ_alike (p : P12) {t t' : T12} (ht : Agree t t') (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    AlikeE wipeT ((frontJ p).decide t rs gs) ((frontJ p).decide t' rs gs) := by
  have hst : wipeSt t.st = wipeSt t'.st := congrArg (·.st) ht
  have hb : t.book = t'.book := congrArg (·.book) ht
  have hg : t.g = t'.g := congrArg (·.g) ht
  have hm : t.mask = t'.mask := congrArg (·.mask) ht
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) ht
  unfold frontJ
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, -⟩ | ⟨R, R', n, a, b, -⟩ |
    ⟨out, theta, n, a, b⟩
  · simp only [a, b]
    rw [← hb, ← hg, ← hm, frontE_rel hst t.book t.g t.mask]
    exact AlikeE.head' fun _ => AlikeE.ok ht
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'
  · simp only [a, b]
    exact AlikeE.rfl'

/-- **The front of the proximity test's parts (guardedProximityTestParts.front) reads no row's target**: at two
records that agree but for targets, at one list of rounds and one list of groups: both refuse with
one word, or both return, and what they return agrees but for targets. No premise but Agree. With
its two own guards: (f), on the count of roots; (p), on the record's codes. -/
theorem front_agree (p : P12) {t t' : T12} (ht : Agree t t') (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    AlikeE wipeT ((guardedProximityTestParts.front p).decide t rs gs) ((guardedProximityTestParts.front p).decide t' rs gs) := by
  have hr : t.roots = t'.roots := congrArg (·.roots) ht
  show AlikeE wipeT
    (VerifiableInference.Desc.need
        "(f): the plan's count of roots in front of the test is not the record's"
        (p.nums.free == t.roots) >>= fun _ =>
      (frontJ p).decide t rs gs >>= fun x =>
        VerifiableInference.Desc.need
          "(p): the record's codes or the place's rounds fail a public clause of the chain"
          (H2K.Pub.pubOk p x.st.codes) >>= fun _ => pure x)
    (VerifiableInference.Desc.need
        "(f): the plan's count of roots in front of the test is not the record's"
        (p.nums.free == t'.roots) >>= fun _ =>
      (frontJ p).decide t' rs gs >>= fun x =>
        VerifiableInference.Desc.need
          "(p): the record's codes or the place's rounds fail a public clause of the chain"
          (H2K.Pub.pubOk p x.st.codes) >>= fun _ => pure x)
  rw [← hr]
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.bind' (frontJ_alike p ht rs gs) fun x x' hx => ?_
  have hc : x.st.codes = x'.st.codes := congrArg (·.st.codes) (hx : wipeT x = wipeT x')
  rw [hc]
  exact AlikeE.head' fun _ => AlikeE.ok hx

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.on_map
#print axioms ProofFile.Honest.K12.Blind.frontL_wipe
#print axioms ProofFile.Honest.K12.Blind.openClaimsE_wipe
#print axioms ProofFile.Honest.K12.Blind.frontE_wipe
#print axioms ProofFile.Honest.K12.Blind.frontE_rel
#print axioms ProofFile.Honest.K12.Blind.frontJ_alike
#print axioms ProofFile.Honest.K12.Blind.front_agree
