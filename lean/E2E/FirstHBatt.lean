-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHBatt.lean: number 16 of the key file's first chain, the batching, at the thread `T₁`: all
debts but the item "pile".

  `batt_member`: the sub-protocol, its rounds, its oracle messages, its place and its half.
  `batt_stays`: a yes of the batching keeps the older messages.
  `plays_batt`, `accepted_batt`, `behind_batt`, `rides_batt`.
  `pinT_item`, `pin_again`: two of the three items that the row owes: pinT is idle here, and pin 0
    was open in front.

Limits. The item "pile" is not here. Conditional on `FirstPublic` and on the thread in front.
-/
import E2E.FirstHRows
import E2E.FirstHPile
import Johnson.Desc.Key.KeyPileSays
import Johnson.Desc.K13.Law.PinDec

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Means
open VerifiableInference.Desc (Block OpenedColumn Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem Source LaterPlaces start₁ batchTableRows
  pieces seat_says seat_rounds batchWhere rootsBefore batchRound quietAt)
open VerifiableInference.Desc.K13 (battRounds)
open VerifiableInference.Desc.K13.Law (SameAll batt_same)
open AtPublicFiles.KeyThread (D rowsFirst form_behind₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keysAt sentAt)
open AtPublicFiles.AtFiles.Full (accepted_first)
open AtPublicFiles.KeyValues (keyBatt oneOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K13 (proverSideOfClaimCombination k13Half_rounds battRounds_length)
open ProofFile.Honest.Small (Listed lists_of_shaped)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- From the same messages, as a row or a sample reads them, to the older messages' staying. -/
theorem stay_of_same {T T' : Statement} (h : SameAll T T') : OlderStay T T' := by
  refine ⟨h.1, fun o y hy => ?_⟩
  have e := h.2 o
  unfold VerifiableInference.Desc.K13.Law.sampleOf at e
  rw [hy, Option.map_some] at e
  obtain ⟨y', hy', e'⟩ := Option.map_eq_some_iff.1 e
  have e1 := Prod.mk.inj e'
  have e2 := Prod.mk.inj e1.2
  have e3 := Prod.mk.inj e2.2
  exact ⟨y', hy', e1.1, e2.1, e3.1⟩

/-- **The sub-protocol.** -/
theorem batt_member (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) :
    ∃ blk, (Th Xs N Pl K f Q w₀ rc x).bs[16]? = some blk ∧ blk.rounds = battRounds K.batt ∧
      blk.oracles = List.replicate (2 + K.batt.lin.kCol) [] ∧
      ((Th Xs N Pl K f Q w₀ rc x).hs.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination K.weights K.pile K.batt) ∧
      (∀ {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))},
        blk.decide s rs gs = .ok s' → StaysK s s') ∧
      ∀ (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        blk.decide s rs gs =
          (batchTableRows (Cl := Claim) keysAt (oneOf Xs) pieces (sentAt Xs.Y.D.1)).decide s rs gs := by
  obtain ⟨bw, hw⟩ := w_there hs scope
  refine ⟨_, (member_back hs scope hw).1, ?_, ?_, ?_, fun {s s' rs gs} h => ?_, fun _ _ _ => rfl⟩
  · rw [hp.batt]
    exact seat_rounds (Cl := Claim) keysAt (oneOf Xs) pieces (sentAt Xs.Y.D.1)
  · rw [hp.batt]
    show (batchTableRows (Cl := Claim) keysAt (oneOf Xs) pieces (sentAt Xs.Y.D.1)).oracles = _
    simp [batchTableRows, VerifiableInference.Desc.Block.andThen, quietAt,
      VerifiableInference.Desc.K13.frontB, VerifiableInference.Desc.K13.still,
      VerifiableInference.Desc.K13.claimCombinationBlock, VerifiableInference.Desc.K13.quietB, keyBatt]
  · exact find_batt K hp.places
  · obtain ⟨rows, out, msg, rs', -, -, hb, rfl⟩ := seat_says keysAt (oneOf Xs) pieces
      (sentAt Xs.Y.D.1) s s' rs gs h
    exact stay_of_same (batt_same hb)

/-- **It plays.** -/
theorem plays_batt (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) : Plays (Th Xs N Pl K f Q w₀ rc x) 16 := by
  obtain ⟨blk, hb, hr, ho, hf, -, -⟩ := batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  exact plays_k13 _ K.weights K.pile K.batt hb hr ho hf

/-- **It accepts**, from the thread alone. -/
theorem accepted_batt (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Accepted (Th Xs N Pl K f Q w₀ rc x) fall 16 := by
  obtain ⟨blk, hb, hr, ho, hf, -, -⟩ := batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  have hl : Listed blk := lists_of_shaped
    ((planOk_all hs.named.plan).1 blk (List.mem_of_getElem? hb)).2
  refine accepted_first hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
    (fun _ _ _ _ _ hbeg => ⟨_, hbeg⟩) fall (by decide) (by decide)
    (fitsAt_half (Th Xs N Pl K f Q w₀ rc x) hb hf ?_ hl.1.symm)
  rw [hr, battRounds_length]
  exact k13Half_rounds K.weights K.pile K.batt

/-- **Behind it.** -/
theorem behind_batt (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) : Behind (Th Xs N Pl K f Q w₀ rc x) 16 := by
  obtain ⟨blk, hb, -, -, -, hst, -⟩ := batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  intro blk' hb' k s m E ds y cols s' hT hd hS
  rw [hb] at hb'
  obtain rfl : blk = blk' := Option.some.inj hb'
  refine ⟨form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope (by decide) hb hT hS, trivial,
    ?_⟩
  obtain ⟨-, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hS.2
  exact hst hdec

/-- **What rides past it.** -/
theorem rides_batt : RidesPast (Th Xs N Pl K f Q w₀ rc x) 16 :=
  rides_send (fun _ _ e => e) (by decide)

/-- The stored table's pin: idle at this thread. -/
theorem pinT_item {k : Coins Bk} {s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} :
    (Th Xs N Pl K f Q w₀ rc x).Items [.pinT] k s' m E := by
  intro ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  exact ⟨(), rfl, trivial⟩

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.stay_of_same
#print axioms AtPublicFiles.FirstH.batt_member
#print axioms AtPublicFiles.FirstH.plays_batt
#print axioms AtPublicFiles.FirstH.accepted_batt
#print axioms AtPublicFiles.FirstH.behind_batt
#print axioms AtPublicFiles.FirstH.rides_batt
#print axioms AtPublicFiles.FirstH.pinT_item
