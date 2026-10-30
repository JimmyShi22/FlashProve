-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyK1/KeyK1AtTerm.lean: KeyK1Rows.lean AT THE VALUE THAT COUNTS: the offline prover's arguments
(thePartsAt files, E2E/KeyArgumentsAt.lean), the offline description that the public files make (offlineDescription,
E2E/TheHonestProver.lean), that value's own book, the frame's order.

  description_of_live        in scope's gate: offlineDescription returns, and what it returns passes its tests on the plan.
  chainPins_at_description   in scope, at what offlineDescription returns: ChainPins.
  book_at_value              the value's book IS offlineProverCoinCounts (by definition); offlineBook_is: it is keyBook at what fullPub returns.
  prover_k1_halves           at the value, under the description's return: the offline prover's first chain has at its
                             numbers 0, 1, 6 the sendings of the three jobs.
  **prover_k1_filter**       and its halves at places of the kind K1, in order, ARE these three.
  **key_k1_good_at_term**    Good at the three rows, at the value's own book, at the frame's order: the premises left: in scope;
                             the description's return.
  key_k1_fit_at_term, key_k1_shows_at_term   the jobs fit; at every coin the sender shows and the simulator tells something.

Limits. At the three places of the kind K1 in the key file's FIRST chain (the kind has five in the key file). The index-mask row
holds no datum: exact has content at two of the three. IT STANDS OVER A TURNED E2E/KeyProver.lean, which shadows
laws.14's: a ride over laws.14 with that turn is a trial and no print of record. What AtKey.lean's Limits say of the coins stands.
f, W₀, Rc, V, X, Pb stay letters in the laws on Good: the prover's own are f := matrixReader, W₀ := FullSizeMatrix, Rc := (protocolAtFiles files).EncodingRandomness.
The rule's clause on queried positions (bud_of_keyReads) at D is owed beside. Nothing here says that anything is hidden.
-/
import E2E.KeyK1.KeyK1Rows
import E2E.KeyArgumentsAt
import AtFullSide.K1.KeyBookClear
import Johnson.SendSim.Seat.KeyReadsAtLive
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyK1
open OnBytes OnBytes.Params OnBytes.SendSim.At OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending)
open AtPublicFiles.KeyBook (keyBook fullPub atFull KeyPub)
open Johnson.KB4 (ChainPins)
open Lk6.AtPlan (keyFull)

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

variable {files : VerifierAndGoals.PublicFiles} {D : OfflineDescription}

/-- **ChainPins at the offline description.** -/
theorem chainPins_at_description (hZ : VerifierAndGoals.InScope files = true)
    (h : offlineDescription files = .ok D) : ChainPins D.source D.numbers D.later := by
  unfold offlineDescription at h
  obtain ⟨X₀, hX, h⟩ := bind_ok h
  obtain ⟨m, hm, h⟩ := bind_ok h
  obtain ⟨s, r1, h⟩ := bind_ok h
  obtain ⟨n, r2, h⟩ := bind_ok h
  obtain ⟨l, r3, h⟩ := bind_ok h
  obtain rfl : (⟨s, n, l⟩ : OfflineDescription) = D := Except.ok.inj h
  exact chainPins_at_made hZ hX hm r1 r2 r3

/-- **Where the library's gate accepts, the offline description is there and passes its tests on the plan**: the payer of
the premise h of this file's laws. -/
theorem description_of_live (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ D : OfflineDescription, offlineDescription files = .ok D ∧
      (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).planOk = true := by
  obtain ⟨X₀, m, X, N, Q, hX, hm, r1, r2, r3, -, -, hp⟩ := keyMakers_of_live hL
  refine ⟨⟨X, N, Q⟩, ?_, hp⟩
  unfold offlineDescription
  rw [hX]
  show (VerifiableInference.Desc.Key.madeAt X₀ files.lay VerifiableInference.Desc.Key.fixedDigest >>= _) = _
  rw [hm]
  show (VerifiableInference.Desc.Key.sourceOf m >>= _) = _
  rw [r1]
  show (VerifiableInference.Desc.Key.rangesNumbers m >>= _) = _
  rw [r2]
  show (VerifiableInference.Desc.Key.laterPlaces m >>= _) = _
  rw [r3]
  rfl

/-- So at every return of the description, where the gate accepts. -/
theorem planOk_at_description (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : offlineDescription files = .ok D) :
    (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).planOk = true := by
  obtain ⟨D', h', hp⟩ := description_of_live hL
  obtain rfl : D' = D := Except.ok.inj (h'.symm.trans h)
  exact hp

/-- **The value's book is the offline file's book.** -/
theorem book_at_value : (thePartsAt files).book = offlineProverCoinCounts := by
  simp only [thePartsAt]

/-- fullPub returns: key_fast accepts, and atFull rejects where fullPub is none. -/
theorem fullPub_some : ∃ K : KeyPub, fullPub = some K := by
  have h := AtFullSide.K1.key_fast
  unfold atFull at h
  cases e : fullPub with
  | none =>
    rw [e] at h
    exact nomatch h
  | some K => exact ⟨K, rfl⟩

theorem offlineBook_is {K : KeyPub} (hK : fullPub = some K) : offlineProverCoinCounts = keyBook K := by
  unfold offlineProverCoinCounts
  rw [hK]

/-- At partsOfDescription: by unfolding. -/
theorem prover_k1_halves_of (D : OfflineDescription) :
    ((partsOfDescription (files := files) D).prover D).first[0]? =
        some (K1.proverSideOfSending (indexMaskSending D.source)) ∧
      ((partsOfDescription (files := files) D).prover D).first[1]? =
        some (K1.proverSideOfSending (multiplicitiesSending matrixReader D.source)) ∧
      ((partsOfDescription (files := files) D).prover D).first[6]? =
        some (K1.proverSideOfSending (batchedRowsSending matrixReader D.source D.numbers)) :=
  ⟨rfl, rfl, rfl⟩

/-- **AT THE VALUE: the offline prover's first chain holds the three sendings.** -/
theorem prover_k1_halves (h : offlineDescription files = .ok D) :
    ((thePartsAt files).prover D).first[0]? = some (K1.proverSideOfSending (indexMaskSending D.source)) ∧
      ((thePartsAt files).prover D).first[1]? =
        some (K1.proverSideOfSending (multiplicitiesSending matrixReader D.source)) ∧
      ((thePartsAt files).prover D).first[6]? =
        some (K1.proverSideOfSending (batchedRowsSending matrixReader D.source D.numbers)) := by
  rw [thePartsAt_of h]
  exact prover_k1_halves_of D

/-- At letters that bear the key file's places: the first chain's halves at places of the kind K1, in order. -/
theorem filter_k1 {W₁ R₁ X₀ X₁ Wk : Type} (K : AtPublicFiles.KeyFile.KeyParts W₁ R₁ X₀ X₁ Wk) (h : K.AtPlaces) :
    ((AtPublicFiles.KeyFile.keyProver K).first.filter fun H => H.place.kind == .K1) =
      [K1.proverSideOfSending K.idx, K1.proverSideOfSending K.msg, K1.proverSideOfSending K.w] := by
  have p := AtPublicFiles.KeyFile.first_places K h
  rw [AtPublicFiles.KeyFile.keyProver_first] at p ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at p
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := p
  simp only [List.filter_cons, List.filter_nil, p0, p1, p2, p3, p4, p5, p6]
  rfl

/-- The shape has a message W, under ChainPins. -/
theorem hasW_of_pins {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {Pl : VerifiableInference.Desc.Key.LaterPlaces} (h : ChainPins Xs N Pl) :
    (OnBytes.linMessageW (AtPublicFiles.KeyValues.oneOf Xs).lin).isSome = true := by
  show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
  rw [h.lin]
  have := AtPublicFiles.KeyBook.rides_full.2.2
  cases hm : OnBytes.linMessageW keyFull.once.shape with
  | none =>
    rw [hm] at this
    cases this
  | some _ => rfl

/-- **AT THE VALUE: the halves at places of the kind K1, in order, ARE these three.** -/
theorem prover_k1_filter (hZ : VerifierAndGoals.InScope files = true) (h : offlineDescription files = .ok D) :
    (((thePartsAt files).prover D).first.filter fun H => H.place.kind == .K1) =
      [K1.proverSideOfSending (indexMaskSending D.source), K1.proverSideOfSending (multiplicitiesSending matrixReader D.source),
        K1.proverSideOfSending (batchedRowsSending matrixReader D.source D.numbers)] := by
  rw [thePartsAt_of h]
  exact filter_k1 _ (AtPublicFiles.KeyValueHolds.atPlaces_value _ D.source D.numbers D.later _ _ _ _ _ _ _ _ _
    (hasW_of_pins (chainPins_at_description hZ h)))

variable {V W₀ Rc X Pb : Type}

/-- **Good AT THE THREE ROWS AT THE VALUE's OWN BOOK AND THE FRAME's ORDER.** -/
theorem key_k1_good_at_term {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hZ : VerifierAndGoals.InScope files = true) (h : offlineDescription files = .ok D) (f : W₀ → Weights)
    (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb) (chain ft : Nat)
    (T : AtPublicFiles.KeyFile.In1 W₀ Rc → Thread (thePartsAt files).book
      (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).Cl V
      (AtPublicFiles.KeyFile.In1 W₀ Rc) X Pb)
    (Sd : AtPublicFiles.KeyFile.In1 W₀ Rc → Nat → Coins (thePartsAt files).book →
      Mid (AtPublicFiles.KeyFile.In1 W₀ Rc) X → Prop)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).S₁)) :
    KeyGood D.source D.numbers D.later pre φ (thePartsAt files).book
        (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later)) chain ft
        T Sd fs (indexMaskSending D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyGood D.source D.numbers D.later pre φ (thePartsAt files).book
        (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later)) chain ft
        T Sd fs (multiplicitiesSending f D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyGood D.source D.numbers D.later pre φ (thePartsAt files).book
        (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later)) chain ft
        T Sd fs (batchedRowsSending f D.source D.numbers : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) := by
  obtain ⟨K, hK⟩ := fullPub_some
  refine key_k1_good_written (chainPins_at_description hZ h) f φ (thePartsAt files).book chain ft T Sd
    fs ?_
  rw [book_at_value, offlineBook_is hK]
  exact AtFullSide.K1.key_clear hK

/-- The three jobs fit, at the description's return, in scope, where the gate accepts. -/
theorem key_k1_fit_at_term (hZ : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : offlineDescription files = .ok D) (f : W₀ → Weights) :
    sendFits (indexMaskSending D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (indexMaskSending D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true ∧
      sendFits (multiplicitiesSending f D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (multiplicitiesSending f D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true ∧
      sendFits (batchedRowsSending f D.source D.numbers : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (batchedRowsSending f D.source D.numbers : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true :=
  key_k1_fit (chainPins_at_description hZ h) (planOk_at_description hL h) f

/-- At every coin the sender shows and its simulator tells something, likewise. -/
theorem key_k1_shows_at_term (hZ : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (h : offlineDescription files = .ok D) (f : W₀ → Weights)
    (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource D.source D.numbers D.later).S₁)) :
    KeyShows D.source D.numbers D.later φ fs (indexMaskSending D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyShows D.source D.numbers D.later φ fs
        (multiplicitiesSending f D.source : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyShows D.source D.numbers D.later φ fs
        (batchedRowsSending f D.source D.numbers : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) :=
  key_k1_shows (chainPins_at_description hZ h) (planOk_at_description hL h) f φ fs

end AtPublicFiles.KeyK1

#print axioms AtPublicFiles.KeyK1.chainPins_at_description
#print axioms AtPublicFiles.KeyK1.description_of_live
#print axioms AtPublicFiles.KeyK1.prover_k1_halves
#print axioms AtPublicFiles.KeyK1.prover_k1_filter
#print axioms AtPublicFiles.KeyK1.key_k1_good_at_term
#print axioms AtPublicFiles.KeyK1.key_k1_fit_at_term
#print axioms AtPublicFiles.KeyK1.key_k1_shows_at_term
