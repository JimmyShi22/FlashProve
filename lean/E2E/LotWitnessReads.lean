-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotWitnessReads.lean: AT THE LAID FILLING THE THREAD's WITNESS READS THE ROWS THAT THE TWO OWNERS' SENDERS LAY: the one premise that
E2E/LotJoinFirstLookups.lean leaves at the two lookups (`LookupsLeft`: the lookups' `WitnessReadsTheSendersRows`, their row 20), paid: because
`fillH` (E2E/FirstHFill.lean) lays the witness's messages 0 and 1 as the words of the rows that these two senders' parts lay of their own cut of
the run's coins (`msgRun`).

  `ties_front`: at a border behind 0 the book-keeping's Bool says that the lookups' own message has the number 1 and the index masks' 0.
  `msgRun_word`: `msgRun` at coins that are the book's at the sender's address is the word of the sender's rows.
  `mk_own`, `mk_key`: a mask entry of message 1 | 0, read off a witness.
  **`lookupsLeft_laid`**: `LookupsLeft`, in scope.
  **`lookupsFive_laid`**: `FiveAtBorder` at 4 and 10 at the laid thread, at every Said and fall: NO PREMISE BUT THE PUBLIC THREE.
  **`leftJoin_of_six_laid`**: `LeftJoin` at the laid Q from `LeftSix` alone.

Limits. It says that two terms are one term read twice: the witness was LAID as the senders' rows, so this is no fact on a run. `ThrS` in front, the
premise inside every debt, is met by nothing here. All content at 4 and 10 is the lookups' and part 5's. In scope, at the written sizes and book.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinFirstLookups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open OnBytes (E Part)
open OnBytes.Slice (readE ofE)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Key (Xi FirstState Source mkOf shape₁_iff)
open Johnson.RunOne.KeyRows1 (plan₁ ties₁ tiesA)
open Johnson.Prover.Send (shapeAt)
open AtPublicFiles.KeyThread (one₀ D)
open AtPublicFiles.KeyFile (In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub msgPlace idxPlace rideMsg)
open AtPublicFiles.KeyValues (multiplicitiesSending indexMaskSending)
open AtPublicFiles.Lookup.Key
open ProofFile.Honest.K1 (SendJob dueR lentCut rowsLaid)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- At a border behind 0: the two messages' numbers. -/
theorem ties_front {Xs : Source} {b : Nat} (hb : b ≠ 0) {s : FirstState}
    (h : ShapeAt Xs b s = true) : (one₀ Xs).ranges.messageId = 1 ∧ s.idx = 0 := by
  have ht : ties₁ (one₀ Xs) b s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  refine ⟨ht.1.1.1.1.1.2, ?_⟩
  rcases ht.1.1.1.2 with h | h
  · exact absurd h hb
  · exact h

/-- **`msgRun` is the word of the sender's rows**, at coins that are the book's at the sender's address. -/
theorem msgRun_word {Bk : ProverCoinCounts} {W X : Type} (J : SendJob W X) (own₀ : X)
    (own : Coins Bk → Cs (dueR J.P J.ride)) (hO : OwnIs Bk 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) own)
    (hs : 0 < J.P.sent.size) (k : Coins Bk) (w : W) (h : List Fmt.Drawn) (part : Part) (i : Nat) :
    msgRun J own₀ k w h part i = (rowsLaid J own₀ (own k) w h 0).word (shapeAt J.P 0) part i := by
  have e : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some (own k) := hO k
  unfold msgRun
  rw [e]
  show Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P (rowsLaid J own₀ (own k) w h) J.first
    part i = _
  unfold Johnson.Prover.Send.held
  rw [if_pos ⟨Nat.le_refl _, Nat.lt_add_of_pos_right hs⟩, Nat.sub_self]

theorem mk_own (one : OnBytes.Params.OneTime) (u : Wit HCells Unit HTab) (ν : Nat) :
    mkOf (plan₁ one) readH u ⟨1, ν⟩ = readH.val (u.msg 1) .mask ν := rfl

theorem mk_key (one : OnBytes.Params.OneTime) (u : Wit HCells Unit HTab) (ν : Nat) :
    mkOf (plan₁ one) readH u ⟨0, ν⟩ = readH.val (u.msg 0) .mask ν := rfl

section
variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed} {x : Xi}

theorem own_size : 0 < (multiplicitiesSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixWeights d.source).P.sent.size := by
  show 0 < (VerifiableInference.Desc.Key.sendingPar _ _ _ _ _).sent.size
  rw [AtPublicFiles.KeyBook.sendingPar_sent]
  exact (AtPublicFiles.KeyLookup.messageOf_head _).1

theorem key_size : 0 < (indexMaskSending (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) d.source).P.sent.size := by
  show 0 < (VerifiableInference.Desc.Key.sendingPar _ _ _ _ _).sent.size
  rw [AtPublicFiles.KeyBook.sendingPar_sent]
  exact Nat.zero_lt_one

/-- **The witness reads the senders' rows**, at the laid filling. -/
theorem lookupsLeft_laid : LookupsLeft Z d K₀ w x := by
  intro number _ ownCoins keyCoins hOwn hKey
  refine ⟨?_, ?_⟩
  · intro k s m E hT more n
    have hb : (if number = 0 then 4 else 10) ≠ 0 := by split <;> decide
    obtain ⟨hid, hidx⟩ := ties_front (Xs := d.source) (s := s) hb hT.2.2.1.1
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hid]
      exact congrArg (fun t => Johnson.RunOne.KeyRows23.readE (OnBytes.E.ofTriple (ofE t)))
        (msgRun_word (multiplicitiesSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixWeights d.source) () ownCoins hOwn
          own_size k ⟨m.st.input.w₀, m.st.input.rc, x, ()⟩ _ .mask _)
    · rw [hidx]
      exact congrArg (fun t => Johnson.RunOne.KeyRows23.readE (OnBytes.E.ofTriple (ofE t)))
        (msgRun_word (indexMaskSending (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) d.source) () keyCoins hKey
          key_size k ⟨m.st.input.w₀, m.st.input.rc, x, ()⟩ _ .mask _)
  · intro k input heard _ place _
    exact congrArg (fun t => readE (OnBytes.E.ofTriple (ofE t)))
      (msgRun_word (multiplicitiesSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixWeights d.source) () ownCoins hOwn
        own_size k ⟨input.w₀, input.rc, x, ()⟩ _ .main place)

/-- **`FiveAtBorder` at 4 and 10 at the laid thread**, under the public three alone. -/
theorem lookupsFive_laid (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK : fullPub = some K₀)
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) Unit → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [4, 10], FiveAtBorder (joinThread d (laterValue Z d K₀) w x) Said fall b :=
  lookupsFive hs scope hK lookupsLeft_laid Said fall

/-- **`LeftJoin` at the laid Q from the six cells alone.** -/
theorem leftJoin_of_six_laid (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) (hK : fullPub = some K₀) (six : LeftSix Z d K₀ w x) :
    LeftJoin d (laterValue Z d K₀) w x :=
  leftJoin_of_six hs scope hK lookupsLeft_laid six

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.ties_front
#print axioms AtPublicFiles.FirstH.Lots.msgRun_word
#print axioms AtPublicFiles.FirstH.Lots.lookupsLeft_laid
#print axioms AtPublicFiles.FirstH.Lots.lookupsFive_laid
#print axioms AtPublicFiles.FirstH.Lots.leftJoin_of_six_laid
