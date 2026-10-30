--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStartsBare.lean: `Starts₂` (E2E/KeySharedStands.lean) HAS A MEMBER: its seven premises hold
together at A PROVER WITHOUT ANY HALF, the key file's own book and a filling of the letters that
says nothing. So `stands₁` there is applied: the key file's shared thread stands at border 1: in
scope at all files of which the description is made; and, WITH NO PREMISE, at the library's three
written full-size public files. NO PROPERTY OF A PROVER IS CLAIMED.

WHAT IT IS WORTH. IT HOLDS OF A PROVER THAT NEVER SPEAKS, AT LETTERS THAT SAY NOTHING. The prover
has no half at any place, no stored table, and hands the shared chain the instance's own key. The
frame's tests on a run do not ask that any half stand: where none stands at a place they refuse
nothing and lay a step without a move. Of the letters: the cells, the messages and the samples are
of the type with one member; of which inputs something is said, "the carried OOD sample is the
cells' own", and what a kind's step keeps are `True`. At such letters the thread's clause on the
input and its one open item say nothing. WHAT THE MEMBER SHOWS: the seven premises can hold
together, so `stands₁` is not empty; no more. Up to border 1 nothing is played, sent or heard.

  `chainSteps_nil`   GENERAL: at an empty list of halves the frame lays each sub-protocol's steps
      without a move (`bareSteps`, Johnson/Desc/ProofFile/Honest/Law/Thread.lean), where each has
      as many lists of oracle messages as rounds.
  `placesOk_of_plan`, `lengths_of_shaped`   two clauses of the library's tests on the plan
      (Johnson/Desc/Block.lean).
  `bareProver`, ★ `ready_bare`   the prover; GENERAL: the frame's tests on a run go through at it,
      at every description that passes the tests on the plan, every book that passes the frame's
      tests on a book, every instance and all coins.
  `bareFill`   the filling of the letters.
  ★★ `starts₂_bare`   the seven, in scope, at the instance written of any OOD sample r. The book's
      word: `book_passes` (E2E/KeyBookThirdNamed.lean); the key fits: `fits_of_own`
      (E2E/KeyStartsAt.lean); the sample: the library's `recBack_instK`.
  ★★ `stands_bare`   `stands₁` there.
  ★★ `stands_bare_zFull`   at `VerifierAndGoals.storedPublicFiles`, the library's sample of zeros and the default coins:
      no premise. By `key_sourced` (E2E/KeyPublic.lean), the side library's `theLive_zFull` and
      `VerifierAndGoals.inScope_full`.

Limits. All limits of E2E/KeySharedStands.lean but its first stand. Nothing on the key file's own
prover: at that one the frame's tests on a run ask four tests and a lending at each of sixteen
halves: untouched here. Nothing on any later border: the next sub-protocol is of a kind, and a
prover without a half plays no move there. `VerifierAndGoals.storedPublicFiles` is three terms written in the library; no
Lean code ties them to files in a folder; at the earlier hash; by a side library that is built with
a larger stack (E2E/KeyShapeFullAtZFull.lean's limits). Nothing on completeness, on soundness or on
what a view shows.


-/
import E2E.KeyStartsAt
import E2E.KeyBookThirdNamed
import E2E.KeyPublic
import AtFullSide.Top.LiveAtFull
import Johnson.Flat.ThreeAtFiles
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place FileDescription)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces keyInstanceOfOutOfDomainSample)
open Johnson.RunOne.KeyRows23 (St₂)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub book_passes full_made)
open OnBytes.Flat (RecFull)
open VerifiableInference.OnPublicFiles (recZeroFull)
open ProofFile.Honest

/-! ## 1 General -/

section
variable {S Cl V W X : Type}

/-- **At an empty list of halves each sub-protocol's steps are laid without a move.** -/
theorem chainSteps_nil (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) : ∀ bs : List (Block S Cl),
      (∀ b ∈ bs, b.oracles.length = b.rounds.length) →
      chainSteps Bk rows look v bs ([] : List (Placed V W X)) =
        .ok (bs.flatMap fun b => bareSteps (W := W) (Y := X) b)
  | [], _ => rfl
  | b :: bs, h => by
    have hb := h b List.mem_cons_self
    have ih := chainSteps_nil Bk rows look v bs fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [chainSteps, if_neg (by rw [hb]; simp)]
    show (chainSteps Bk rows look v bs ([] : List (Placed V W X))).map _ = _
    rw [ih]
    rfl

end

/-- The tests on the plan hold the test on the places. -/
theorem placesOk_of_plan {Xi' : Type} {F : FileDescription Xi'} (h : F.planOk = true) :
    F.placesOk = true := by
  cases hb : F.placesOk with
  | true => rfl
  | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h

/-- A shaped sub-protocol has a list of oracle messages for each round. -/
theorem lengths_of_shaped {S Cl : Type} {b : Block S Cl} (h : b.shaped = true) :
    b.oracles.length = b.rounds.length := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true] at h
  exact eq_of_beq h.1

/-! ## 2 The prover without a half -/

/-- **A prover that never speaks**: no half at any place, no stored table; every request has a
trace; the key that it hands the shared chain is the instance's. -/
def bareProver : Prover Unit Unit Xi OnBytes.TableKey Unit Unit Unit where
  stored := fun _ _ _ _ => none
  trace := fun _ _ => some ()
  key := fun x => x.key
  inRange := fun _ => true
  dummy := ()
  own₀ := ()
  ownShared₀ := ()
  first := []
  shared := []
  second := []
  meet := fun _ _ => ()

/-- What the frame lays ready at that prover. -/
def bareReady (F : FileDescription Xi) (x : Xi) : Ready Unit Unit Xi OnBytes.TableKey Unit Unit Unit :=
  ⟨⟨(), (), x, ()⟩, ⟨(), (), x.key⟩, F.first.blocksInOrder.flatMap fun b => bareSteps b,
    F.shared.blocksInOrder.flatMap fun b => bareSteps b, F.second.blocksInOrder.flatMap fun b => bareSteps b⟩

/-- ★ **THE FRAME's TESTS ON A RUN GO THROUGH AT THE PROVER WITHOUT A HALF.** -/
theorem ready_bare {F : FileDescription Xi} {B : ProverCoinCounts} (hp : F.planOk = true) (hw : B.word F = none)
    (x : Xi) (k : Coins B) : ready F B bareProver () () x k = .ok (bareReady F x) := by
  obtain ⟨p1, p2, p3⟩ := planOk_all hp
  have t : readyTests F B bareProver () = .ok () := by
    unfold readyTests
    rw [placesOk_of_plan hp, hw]
    rfl
  unfold ready
  rw [t]
  show (unfit (chainSteps B (B.rowsOf 0) (k.look 0) _ F.first.blocksInOrder [])).bind _ = _
  rw [chainSteps_nil _ _ _ _ _ fun b hb => lengths_of_shaped (p1 b hb).2]
  show (sharedSteps F B bareProver _ k.shared).bind _ = _
  unfold sharedSteps
  show (unfit (chainSteps B (B.rowsOf 1) _ _ F.shared.blocksInOrder [])).bind _ = _
  rw [chainSteps_nil _ _ _ _ _ fun b hb => lengths_of_shaped (p2 b hb).2]
  show (unfit (chainSteps B (B.rowsOf 2) (k.look 2) _ F.second.blocksInOrder [])).map _ = _
  rw [chainSteps_nil _ _ _ _ _ fun b hb => lengths_of_shaped (p3 b hb).2]
  rfl

/-! ## 3 The letters -/

/-- **A filling of the letters that says nothing**, but for the library's own letter for the OOD
sample whose key an instance is. -/
noncomputable def bareFill (Bk : ProverCoinCounts) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) :
    KeyFill Bk Unit Unit Unit Unit Unit RecFull where
  R := ⟨fun _ _ _ => 0, fun _ _ _ => OnBytes.zeroE, fun _ _ => (), fun _ _ => True⟩
  base :=
    { arr := fun _ _ => 0, lay := fun _ _ _ _ => (), enc := fun _ _ _ _ _ => True
      rad := fun _ _ _ => 0, meets := fun _ _ _ _ _ => True, decT := fun _ _ => none
      recOf := LPFD.recBack, sm := fun _ _ _ => none, orc₁ := fun _ => none }
  meetsT := fun _ _ => True
  enc := fun f n => f n
  rad := 0
  cells := fun _ _ => ()
  msg := fun _ _ _ _ _ => ()
  fixedMsg := fun _ => 0
  pad := fun _ _ _ _ _ => ()
  ends := fun _ _ _ x _ => ((D Xs N Pl).start₁ x, (D Xs N Pl).start₂ x)
  kind₁ := fun _ _ _ => True
  kind₂ := fun _ _ _ => True
  kind₃ := fun _ _ _ => True
  Rel := fun _ _ _ => True
  stored := fun _ _ _ _ => none
  item := 0
  table₁ := fun _ _ _ _ => (default, ⟨0, 0, fun _ i => i.elim0⟩)
  table₂ := fun _ _ _ _ => (default, ⟨0, 0, fun _ i => i.elim0⟩)
  table₃ := fun _ _ _ _ => (default, ⟨0, 0, fun _ i => i.elim0⟩)

/-! ## 4 The member -/

section
variable {Z : VerifierAndGoals.PublicFiles} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)

/-- ★★ **THE SEVEN PREMISES HOLD TOGETHER.** r: any OOD sample; the instance is written of it. -/
theorem starts₂_bare (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (K : KeyPub) (hK : fullPub = some K) (r : RecFull) (k : Coins (keyBook K)) :
    Starts₂ Xs N Pl (bareFill (keyBook K) Xs N Pl) () () (keyInstanceOfOutOfDomainSample r) bareProver k
      (bareReady (D Xs N Pl) (keyInstanceOfOutOfDomainSample r)) where
  ready := ready_bare hs.named.plan (book_passes scope hs.named K hK) _ k
  key := rfl
  bare := fun _ _ => rfl
  stored := fun _ _ => rfl
  fits := fits_of_own Xs N Pl (bareFill (keyBook K) Xs N Pl) (keyInstanceOfOutOfDomainSample r) hs scope rfl
    (LPFD.recBack_instK r)
  rel := trivial
  own := ⟨r, LPFD.recBack_instK r, trivial⟩

/-- ★★ **THE SHARED THREAD STANDS AT BORDER 1, AT THE PROVER THAT NEVER SPEAKS.** -/
theorem stands_bare (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (K : KeyPub) (hK : fullPub = some K) (r : RecFull) (k : Coins (keyBook K)) :
    ∃ (s' : St₂) (y : List Played × Mid (Common Unit Unit OnBytes.TableKey) Unit),
      Thr (laid₂ Xs N Pl (bareFill (keyBook K) Xs N Pl) () () (keyInstanceOfOutOfDomainSample r) bareProver.shared
          (bareFill (keyBook K) Xs N Pl).table₂) 1 k s' y.2
        ((envOf (bareProver.storedWords () ()) (fun _ _ => none) []).add y.1) :=
  stands₁ Xs N Pl (bareFill (keyBook K) Xs N Pl) () () (keyInstanceOfOutOfDomainSample r) bareProver _ hs scope
    (starts₂_bare Xs N Pl hs scope K hK r k)

end

/-- ★★ **WITH NO PREMISE: at the library's three written full-size public files.** -/
theorem stands_bare_zFull :
    ∃ (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyPub) (s' : St₂)
      (y : List Played × Mid (Common Unit Unit OnBytes.TableKey) Unit),
      AtPublicFiles.AtFiles.KeySourced VerifierAndGoals.storedPublicFiles Xs N Pl ∧ fullPub = some K ∧
      Thr (laid₂ Xs N Pl (bareFill (keyBook K) Xs N Pl) () () (keyInstanceOfOutOfDomainSample recZeroFull)
          bareProver.shared (bareFill (keyBook K) Xs N Pl).table₂) 1 default s' y.2
        ((envOf (bareProver.storedWords () ()) (fun _ _ => none) []).add y.1) := by
  obtain ⟨Xs, N, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K, hK⟩ := full_made
  obtain ⟨s', y, h⟩ := stands_bare Xs N Pl hs VerifierAndGoals.inScope_full K hK recZeroFull default
  exact ⟨Xs, N, Pl, K, s', y, hs, hK, h⟩

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.chainSteps_nil
#print axioms AtPublicFiles.KeyThread.placesOk_of_plan
#print axioms AtPublicFiles.KeyThread.lengths_of_shaped
#print axioms AtPublicFiles.KeyThread.ready_bare
#print axioms AtPublicFiles.KeyThread.starts₂_bare
#print axioms AtPublicFiles.KeyThread.stands_bare
#print axioms AtPublicFiles.KeyThread.stands_bare_zFull
