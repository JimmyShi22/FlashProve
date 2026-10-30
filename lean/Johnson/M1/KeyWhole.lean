-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: no side of the offline prover is missing.
/-
Johnson/M1/KeyWhole.lean: in scope, under KeyNamed, at letters that bear the key file's sixteen places: a half of keyProver K stands at every
sub-protocol that sends a root (rootedAll_key), beside the library's halvedAll_key; and the first chain's last declared round is plain
(sealPlain_key). What the test reads is the rows, the written declared rounds and the halves' places, and the kernel evaluates it.

  rootedRows         the test, on rows, rounds and places.
  rooted_of_rows     its yes gives rooted.

That the letters of any value bear the places is KeyParts.AtAll, a premise.
No property of the protocol is claimed here.
-/
import Johnson.M1.KeyNumbersAt
import E2E.KeyLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1
open ProofFile.Honest OnBytes VerifiableInference.Desc
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open AtPublicFiles.KeyFile (KeyParts keyProver first_places keyProver_shared)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyLink (any_places)
open Johnson.RunOne.Sound (rowsOf)

/-- A half at every row whose rounds send a root, row by row along the rounds. -/
def rootedRows : List (Place × Nat) → List Fmt.DeclaredRound → List Place → Bool
  | [], _, _ => true
  | r :: l, D, ps =>
    (ps.any (· == r.1) || (D.take r.2).all fun d => d.entry.roots == 0) && rootedRows l (D.drop r.2) ps

section
variable {S Cl V W Y : Type}

theorem rooted_of_rows (hs : List (Placed V W Y)) : ∀ bs : List (Block S Cl),
    rootedRows (rowsOf bs) (bs.flatMap (·.rounds)) (hs.map (·.place)) = true → rooted bs hs = true
  | [], _ => rfl
  | b :: bs, h => by
    have e : rowsOf (b :: bs) = (b.place, b.rounds.length) :: rowsOf bs := rfl
    rw [e, List.flatMap_cons] at h
    unfold rootedRows at h
    rw [List.take_left', List.drop_left'] at h
    · have h' := Bool.and_eq_true_iff.1 h
      have ih := rooted_of_rows hs bs h'.2
      unfold rooted at ih ⊢
      rw [List.all_cons, ih, Bool.and_true, any_places]
      exact h'.1
    · rfl
    · rfl

end

section
variable {W₀ Rc X₀ X Wk : Type} {Z : VerifierAndGoals.PublicFiles} {Xs : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

set_option maxRecDepth 1000000 in
theorem first_rootedW : rootedRows fullFirst declKeyFull.1
    [⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, some 0, 2, .K3⟩, ⟨1, some 1, 2, .K3⟩,
      ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩, ⟨1, none, 14, .K1⟩] = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem shared_rootedW : rootedRows fullShared declKeyFull.2.1
    [ProofFile.Honest.K14.place 1, ProofFile.Honest.K14.sendPlace 2, ProofFile.Honest.K14.place 4, ProofFile.Honest.K14.sendPlace 5,
      ProofFile.Honest.K14.place 7, ProofFile.Honest.K14.place 8, foldedTestPlace, omegaTestPlace] = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem second_rootedW : rootedRows fullSecond declKeyFull.2.2 [ownTestPlace] = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test bites: with no half at the folded row's test a root stands alone. -/
theorem shared_rootedW_bites : rootedRows fullShared declKeyFull.2.1
    [ProofFile.Honest.K14.place 1, ProofFile.Honest.K14.sendPlace 2, ProofFile.Honest.K14.place 4, ProofFile.Honest.K14.sendPlace 5,
      ProofFile.Honest.K14.place 7, ProofFile.Honest.K14.place 8, omegaTestPlace] = false := by decide +kernel

/-- **In scope a half of keyProver K stands at every sub-protocol of the key file that sends a root.** -/
theorem rootedAll_key (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N P)
    (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) : rootedAll (keyFileDescription Xs N P) (keyProver K) = true := by
  obtain ⟨r1, r2, r3⟩ := places_named scope h
  have hd := keyDecl_of_named scope h
  have d1 : (keyFileDescription Xs N P).first.blocksInOrder.flatMap (·.rounds) = declKeyFull.1 := congrArg Prod.fst hd
  have d2 : (keyFileDescription Xs N P).shared.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.1 :=
    congrArg (fun D => D.2.1) hd
  have d3 : (keyFileDescription Xs N P).second.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.2 :=
    congrArg (fun D => D.2.2) hd
  have a1 : rooted (keyFileDescription Xs N P).first.blocksInOrder (keyProver K).first = true := by
    refine rooted_of_rows _ _ ?_
    rw [r1, d1, first_places K hK.first]
    exact first_rootedW
  have a2 : rooted (keyFileDescription Xs N P).shared.blocksInOrder (keyProver K).shared = true := by
    refine rooted_of_rows _ _ ?_
    rw [r2, d2, keyProver_shared K hK.splits, hK.onU, hK.onOmega]
    exact shared_rootedW
  have a3 : rooted (keyFileDescription Xs N P).second.blocksInOrder (keyProver K).second = true := by
    refine rooted_of_rows _ _ ?_
    rw [r3, d3]
    show rootedRows fullSecond declKeyFull.2.2 [K.own.place] = true
    rw [hK.own]
    exact second_rootedW
  unfold rootedAll
  rw [a1, a2, a3]
  rfl

set_option maxRecDepth 1000000 in
theorem seal_plainW : (declKeyFull.1.getLast?.map fun d =>
    (d.items.filter (· != .root)).isEmpty && d.entry.roots == 0).getD false = true := by decide +kernel

/-- **In scope the first chain's last declared round is plain.** -/
theorem sealPlain_key (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N P) :
    sealPlain (keyFileDescription Xs N P) = true := by
  unfold sealPlain
  rw [keyDecl_of_named scope h]
  exact seal_plainW

/-- **No offline side is missing.** -/
theorem sidesWhole_key (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N P)
    (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) :
    halvedAll (keyFileDescription Xs N P) (keyProver K) = true ∧ rootedAll (keyFileDescription Xs N P) (keyProver K) = true ∧
      sealPlain (keyFileDescription Xs N P) = true :=
  ⟨AtPublicFiles.KeyFile.halvedAll_key scope h K hK, rootedAll_key scope h K hK, sealPlain_key scope h⟩

end

end OnBytes.M1

#print axioms OnBytes.M1.rooted_of_rows
#print axioms OnBytes.M1.rootedAll_key
#print axioms OnBytes.M1.sealPlain_key
#print axioms OnBytes.M1.sidesWhole_key
#print axioms OnBytes.M1.shared_rootedW_bites
