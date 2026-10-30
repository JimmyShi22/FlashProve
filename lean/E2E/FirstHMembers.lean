-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHMembers.lean: which sub-protocols stand at the numbers 0, 1, 16 and 17 of the key file's
first chain, in scope, and which half of `keyProver K` stands at each.

  `member0`, `member1`, `member16`, `member17`: the sub-protocols, as the description lays them.
  `find_idx`, `find_msg`, `find_batt`, `find_w`: the search for a half at the four places.

Limits. Conditional on `K.AtPlaces`, which says where K's senders stand. Nothing on a run.
-/
import E2E.KeyProver
import E2E.KeyShapeFullSourced
import E2E.KeyShapeFirstWhole

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH
open ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (FirstState Claim Source LaterPlaces sendIndexMasks sendOwnMessage
  batchTableRows pieces groupsTold rootsAt rootsBefore)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription pubOf flat₁ flat₁_whole flat₁_cut sentAt keysAt sendWAt
  PublicFirst)
open AtPublicFiles.AtFiles.Full (public_first_sourced)
open AtPublicFiles.KeyThread (lengths)
open AtPublicFiles.KeyFile (KeyParts keyProver In1)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- In scope W's sub-protocol is there. -/
theorem w_there (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    ∃ bw, sendWAt (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw := by
  obtain ⟨bw, h, -⟩ := public_first_sourced hs scope
  exact ⟨bw, h⟩

/-- **Number 0.** -/
theorem member0 {bw : Block FirstState Claim}
    (hw : sendWAt (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw) :
    (keyFileDescription Xs N Pl).first.blocksInOrder[0]? =
      some (sendIndexMasks Xs.Y.k.oneTime pieces
        (groupsTold Xs.Y.told.1 0 (rootsAt Xs.Y.D.1 0))).asBare := by
  have e : (keyFileDescription Xs N Pl).first.blocksInOrder = _ := flat₁_whole (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 N bw hw
  rw [e]
  rfl

/-- **Number 1.** -/
theorem member1 {bw : Block FirstState Claim}
    (hw : sendWAt (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw) :
    (keyFileDescription Xs N Pl).first.blocksInOrder[1]? =
      some (sendOwnMessage Xs.Y.k.oneTime pieces
        (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 2) (rootsAt Xs.Y.D.1 2))).asBare := by
  have e : (keyFileDescription Xs N Pl).first.blocksInOrder = _ := flat₁_whole (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 N bw hw
  rw [e]
  rfl

/-- A list of nineteen, cut in front of its last four. -/
theorem tail_at {α : Type} (pre : List α) (a b c d : α) (h : (pre ++ [a, b, c, d]).length = 19) :
    (pre ++ [a, b, c, d])[16]? = some b ∧ (pre ++ [a, b, c, d])[17]? = some c := by
  have hl : pre.length = 15 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  constructor
  · rw [List.getElem?_append_right (by omega), hl]
    rfl
  · rw [List.getElem?_append_right (by omega), hl]
    rfl

/-- **Numbers 16 and 17.** -/
theorem member_back (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {bw : Block FirstState Claim} (hw : sendWAt (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw) :
    (keyFileDescription Xs N Pl).first.blocksInOrder[16]? =
        some (batchTableRows keysAt Xs.Y.k.oneTime pieces (sentAt Xs.Y.D.1)).asBare ∧
      (keyFileDescription Xs N Pl).first.blocksInOrder[17]? = some bw.asBare := by
  have e : (keyFileDescription Xs N Pl).first.blocksInOrder = _ := flat₁_cut (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 N bw hw
  have hl := (lengths scope hs.named).1
  rw [e] at hl ⊢
  exact tail_at _ _ _ _ _ hl

section Halves
variable {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)

/-- The search at the first sending's place. -/
theorem find_idx (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 1, .K1⟩ : Place)) =
      some (K1.proverSideOfSending K.idx) := by
  have e1 : ((K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place ==
      (⟨1, none, 1, .K1⟩ : Place)) = true := by
    show (K.idx.P.place == _) = true
    rw [h.idx]
    decide
  show List.find? _ (K1.proverSideOfSending K.idx :: _) = _
  simp only [List.find?, e1]

/-- The search at the second sending's place. -/
theorem find_msg (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 2, .K1⟩ : Place)) =
      some (K1.proverSideOfSending K.msg) := by
  have e1 : ((K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place ==
      (⟨1, none, 2, .K1⟩ : Place)) = false := by
    show (K.idx.P.place == _) = false
    rw [h.idx]
    decide
  have e2 : ((K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place ==
      (⟨1, none, 2, .K1⟩ : Place)) = true := by
    show (K.msg.P.place == _) = true
    rw [h.msg]
    decide
  show List.find? _ (K1.proverSideOfSending K.idx :: K1.proverSideOfSending K.msg :: _) = _
  simp only [List.find?, e1, e2]

/-- The halves in front of the batching's do not stand at a place of another number. -/
theorem find_back (h : K.AtPlaces) {p : Place}
    (h1 : (⟨1, none, 1, .K1⟩ : Place) ≠ p) (h2 : (⟨1, none, 2, .K1⟩ : Place) ≠ p)
    (h3 : (⟨1, some 0, 2, .K3⟩ : Place) ≠ p) (h4 : (⟨1, some 1, 2, .K3⟩ : Place) ≠ p)
    (h5 : (⟨1, none, 5, .K12⟩ : Place) ≠ p) :
    ((keyProver K).first.find? fun g => g.place == p) =
      ([K13.proverSideOfClaimCombination K.weights K.pile K.batt, K1.proverSideOfSending K.w] :
        List (Placed (In1 W₀ Rc) (In1 W₀ Rc) X)).find? fun g => g.place == p := by
  have no : ∀ {a : Place}, a ≠ p → (a == p) = false := fun ha => beq_eq_false_iff_ne.2 ha
  have e1 : ((K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == p) = false := by
    show (K.idx.P.place == p) = false
    rw [h.idx]
    exact no h1
  have e2 : ((K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == p) = false := by
    show (K.msg.P.place == p) = false
    rw [h.msg]
    exact no h2
  have e3 : ((K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X) (K3.keyOwners K.look0.face) K.reads
      K.jobs0 K.wit K.look0).place == p) = false := by
    show (K.look0.place == p) = false
    rw [h.look0]
    exact no h3
  have e4 : ((K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X) (K3.keyOwners K.look1.face) K.reads
      K.jobs1 K.wit K.look1).place == p) = false := by
    show (K.look1.place == p) = false
    rw [h.look1]
    exact no h4
  have e5 : (K.rng.place == p) = false := by
    rw [h.rng]
    exact no h5
  show List.find? _ (K1.proverSideOfSending K.idx :: K1.proverSideOfSending K.msg ::
    K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0 ::
    K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1 :: K.rng ::
    _) = _
  simp only [List.find?, e1, e2, e3, e4, e5]

/-- The search at the batching's place. -/
theorem find_batt (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 13, .K13⟩ : Place)) =
      some (K13.proverSideOfClaimCombination K.weights K.pile K.batt) := by
  rw [find_back K h (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e : ((K13.proverSideOfClaimCombination K.weights K.pile K.batt :
      Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == (⟨1, none, 13, .K13⟩ : Place)) = true := by
    show (K13.k13Place K.batt == _) = true
    rw [h.batt]
    decide
  simp only [List.find?, e]

/-- The search at W's place. -/
theorem find_w (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 14, .K1⟩ : Place)) =
      some (K1.proverSideOfSending K.w) := by
  rw [find_back K h (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e1 : ((K13.proverSideOfClaimCombination K.weights K.pile K.batt :
      Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == (⟨1, none, 14, .K1⟩ : Place)) = false := by
    show (K13.k13Place K.batt == _) = false
    rw [h.batt]
    decide
  have e2 : ((K1.proverSideOfSending K.w : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place ==
      (⟨1, none, 14, .K1⟩ : Place)) = true := by
    show (K.w.P.place == _) = true
    rw [h.w]
    decide
  simp only [List.find?, e1, e2]

end Halves

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.w_there
#print axioms AtPublicFiles.FirstH.member0
#print axioms AtPublicFiles.FirstH.member1
#print axioms AtPublicFiles.FirstH.member_back
#print axioms AtPublicFiles.FirstH.find_idx
#print axioms AtPublicFiles.FirstH.find_msg
#print axioms AtPublicFiles.FirstH.find_batt
#print axioms AtPublicFiles.FirstH.find_w
