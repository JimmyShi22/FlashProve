-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyK1/KeyK1Rows.lean: AT THE THREE PLACES OF THE KIND K1 IN THE FIRST CHAIN OF THE KEY FILE (the
index-mask message, the multiplicities, W; the file has other sendings, of other kinds and in other
chains), THE SENDER BESIDE ITS SIMULATOR: a member stands at the place; every side seated there has fits and exact; and, where the
book is clear at that sender (BookClearAny, A NAMED PREMISE), fresh: the law fieldsAtKey_all, handAtKey
(Johnson/SendSim/Seat/AtKey.lean) at indexMaskSending, multiplicitiesSending, batchedRowsSending (E2E/KeyFirstSends.lean), by KeyJobsAtPars.

  KeyRow         what the law says at a job.
  **key_k1_fields**   KeyRow at the three jobs, under ChainPins.
  **key_k1_good**     Good at every side of each of the three rows, each under its own BookClearAny.
  order_written       orderOf at the written sizes.
  **key_k1_good_written**   Good at the frame's order, from one premise at the written numbers.
  key_k1_fit, KeyShows, **key_k1_shows**   the three jobs fit; at every coin the sender shows
                      something and the simulator tells something: exact and fresh are not idle.
  chainPins_at_made   ChainPins at what the makers return, in scope: the premise's payer.

Limits. The written sizes: ChainPins, which holds in scope where the key file's makers return
(keyPins_in_scope, Johnson/SendSim/Seat/KeyReadsAtLive.lean, through its Pins). THAT BookClearAny HOLDS AT ANY BOOK IS NOT SHOWN HERE. Statements
at Key.descriptionFromSource Xs N Pl at any letters: THAT THESE THREE JOBS ARE THE HONEST PROVER's HALVES AT THE VALUE THAT
COUNTS (offlineDescription's source, numbers, later; Parts.senders) IS NOT AN EQUATION HERE: by reading
of KeyFifteen's withSendingsAndLookups alone: until it is, this is a law beside the prover, not of it. Owed
beside for the rule: bud (bud_of_keyReads), On := True. The index-mask row holds no datum: exact has
content at two of the three. Limits of AtKey.lean stand: the coins are taken as drawn uniformly for
this one run, independently of the input. Nothing here says that anything is hidden.
-/
import E2E.KeyK1.KeyJobsAtPars
import Johnson.SendSim.Seat.AtKey
import Johnson.SendSim.Seat.FitsAtKey
import Johnson.SendSim.Seat.KeyReadsAtLive
import Johnson.SendSim.At.Shows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyK1
open OnBytes OnBytes.Params OnBytes.SendSim.At OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending)
open Johnson.KB4 (ChainPins)

variable {V W₀ Rc X Pb : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **What the law says at a job**: a member at the job's place; at every side seated there fits and
exact, and fresh at every book and order at which the book is clear at the sender. -/
def KeyRow {W : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (φ : Face V W Pb)
    (chain ft : Nat) (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁))
    (J : SendJob W X) : Prop :=
  (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder.any (fun b => b.place == J.P.place) = true ∧
    ∀ σ : Side (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁
        (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V W X Pb,
      Side.seated (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder
          (sendRow (V := V) (Pb := Pb) J.P.place J).place (sendRow J.P.place J).row fs = some σ →
        σ.fits = true ∧
          ExactAt φ σ chain ft (sendRow (V := V) (Pb := Pb) J.P.place J).On
            (sendRow (V := V) (Pb := Pb) J.P.place J).bud ∧
          ∀ (Bk : ProverCoinCounts) (ord : List Place),
            BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
            FreshAt φ σ Bk ord (sendRow (V := V) (Pb := Pb) J.P.place J).bud

/-- **THE LAW AT THE THREE SENDINGS.** -/
theorem key_k1_fields (h : ChainPins Xs N Pl) (f : W₀ → Weights)
    (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb) (chain ft : Nat)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) :
    KeyRow Xs N Pl φ chain ft fs (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyRow Xs N Pl φ chain ft fs (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyRow Xs N Pl φ chain ft fs (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) := by
  obtain ⟨h1, h2, h3⟩ := keyJobs_in_pars (W₀ := W₀) (Rc := Rc) (X := X) h f
  exact ⟨fieldsAtKey_all Xs N Pl φ chain ft fs h1 _ rfl rfl,
    fieldsAtKey_all Xs N Pl φ chain ft fs h2 _ rfl rfl,
    fieldsAtKey_all Xs N Pl φ chain ft fs h3 _ rfl rfl⟩

/-- What the rule asks of one row, at a job of these three. -/
def KeyGood {W : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain ft : Nat)
    (T : W → Thread Bk (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) (J : SendJob W X) : Prop :=
  ∀ σ, ((sendRow (V := V) (Pb := Pb) J.P.place J).lay T Sd
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder).side
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder fs = some σ →
    ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁
      ((sendRow J.P.place J).lay T Sd (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder).On
      ((sendRow J.P.place J).lay T Sd (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder).bud

/-- **Good AT THE THREE ROWS, each row under its own premise on the book alone.** -/
theorem key_k1_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)} (h : ChainPins Xs N Pl)
    (f : W₀ → Weights) (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain ft : Nat)
    (T : AtPublicFiles.KeyFile.In1 W₀ Rc → Thread Bk (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V (AtPublicFiles.KeyFile.In1 W₀ Rc) X Pb)
    (Sd : AtPublicFiles.KeyFile.In1 W₀ Rc → Nat → Coins Bk → Mid (AtPublicFiles.KeyFile.In1 W₀ Rc) X → Prop)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) :
    (BookClearAny (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride Bk ord
        ⟨(indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.place, 0⟩ →
      KeyGood Xs N Pl pre φ Bk ord chain ft T Sd fs
        (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X)) ∧
    (BookClearAny (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride Bk ord
        ⟨(multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.place, 0⟩ →
      KeyGood Xs N Pl pre φ Bk ord chain ft T Sd fs
        (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X)) ∧
    (BookClearAny (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride Bk ord
        ⟨(batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.place, 0⟩ →
      KeyGood Xs N Pl pre φ Bk ord chain ft T Sd fs
        (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X)) := by
  obtain ⟨h1, h2, h3⟩ := keyJobs_in_pars (W₀ := W₀) (Rc := Rc) (X := X) h f
  exact ⟨fun hI => handAtKey Xs N Pl φ Bk ord chain ft T Sd fs h1 _ rfl rfl hI,
    fun hM => handAtKey Xs N Pl φ Bk ord chain ft T Sd fs h2 _ rfl rfl hM,
    fun hW => handAtKey Xs N Pl φ Bk ord chain ft T Sd fs h3 _ rfl rfl hW⟩

/-- **The order of places at the written sizes.** -/
theorem order_written (h : ChainPins Xs N Pl) :
    ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) = ProofFile.Honest.orderOf Johnson.KB4.WK := by
  unfold ProofFile.Honest.orderOf
  rw [Johnson.KB4.first_of h, Johnson.KB4.shared_of h, Johnson.KB4.second_of h]
  rfl

/-- **Good AT THE THREE ROWS, at the frame's order, from one premise on the book at the written
public numbers.** -/
theorem key_k1_good_written {pre : List (Nat × Nat × List Fmt.DeclaredRound)} (h : ChainPins Xs N Pl)
    (f : W₀ → Weights) (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb) (Bk : ProverCoinCounts) (chain ft : Nat)
    (T : AtPublicFiles.KeyFile.In1 W₀ Rc → Thread Bk (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V (AtPublicFiles.KeyFile.In1 W₀ Rc) X Pb)
    (Sd : AtPublicFiles.KeyFile.In1 W₀ Rc → Nat → Coins Bk → Mid (AtPublicFiles.KeyFile.In1 W₀ Rc) X → Prop)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁))
    (hC : ∀ x ∈ keyParsW, BookClearAny x.1 x.2 Bk (ProofFile.Honest.orderOf Johnson.KB4.WK) ⟨x.1.place, 0⟩) :
    KeyGood Xs N Pl pre φ Bk (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)) chain ft T Sd fs
        (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyGood Xs N Pl pre φ Bk (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)) chain ft T Sd fs
        (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyGood Xs N Pl pre φ Bk (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)) chain ft T Sd fs
        (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) := by
  obtain ⟨h1, h2, h3⟩ := keyJobs_in_pars (W₀ := W₀) (Rc := Rc) (X := X) h f
  rw [keyPars_written h] at h1 h2 h3
  have e := order_written h
  obtain ⟨g1, g2, g3⟩ := key_k1_good (pre := pre) (X := X) h f φ Bk
    (ProofFile.Honest.orderOf (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)) chain ft T Sd fs
  exact ⟨g1 (by rw [e]; exact hC _ h1), g2 (by rw [e]; exact hC _ h2),
    g3 (by rw [e]; exact hC _ h3)⟩

/-- **The three jobs fit their places**, where the description passes its tests on the plan: so exact
and fresh at these rows do not read "none = none". -/
theorem key_k1_fit (h : ChainPins Xs N Pl)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true) (f : W₀ → Weights) :
    sendFits (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true ∧
      sendFits (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true ∧
      sendFits (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P
        (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = true := by
  obtain ⟨h1, h2, h3⟩ := keyJobs_in_pars (W₀ := W₀) (Rc := Rc) (X := X) h f
  exact ⟨fits_at_key Xs N Pl hp _ h1, fits_at_key Xs N Pl hp _ h2, fits_at_key Xs N Pl hp _ h3⟩

/-- At every coin the sender of a job that fits shows something, and its simulator tells something. -/
def KeyShows {W : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (φ : Face V W Pb)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) (J : SendJob W X) : Prop :=
  ∀ σ : Side (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V W X Pb,
    Side.seated (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).first.blocksInOrder
        (sendRow (V := V) (Pb := Pb) J.P.place J).place (sendRow J.P.place J).row fs = some σ →
      σ.members = [memberAt σ J] ∧
      ∀ (m : Mid W X) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
        (c : Cs (dueR J.P J.ride)), drawsFit σ.block.rounds ds = true →
        σ.shows φ (memberAt σ J) (c, (), ()) m ds asks =
            some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks c) ∧
          (memberAt σ J).tells φ c m.st.input front ds asks =
            some (shownR J.P J.first J.ride (fun _ _ _ => none) ds asks c)

theorem keyShows_of {W : Type} (φ : Face V W Pb)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) {x : VerifiableInference.Desc.K1.Par × (Nat → Option Ride)}
    (hx : x ∈ keyPars Xs) (J : SendJob W X) (hP : J.P = x.1) (hR : J.ride = x.2)
    (hf : sendFits J.P J.ride = true) : KeyShows Xs N Pl φ fs J := by
  intro σ hσ
  have hSe : Seated σ J := seatedAt_key Xs N Pl hx hP hσ
  refine ⟨members_seated hSe, fun m front ds asks c hd => ⟨?_, ?_⟩⟩
  · have e := showsAt _ _ _ _ _ _ φ σ J hSe m ds asks c hd
    rw [if_pos hf] at e
    exact e
  · have e := tellsAt _ _ _ _ _ _ φ σ J hSe m.st.input front ds asks c hd
    rw [if_pos hf] at e
    exact e

/-- **At the three rows, at every coin, the sender shows something and its simulator tells
something.** -/
theorem key_k1_shows (h : ChainPins Xs N Pl)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true) (f : W₀ → Weights)
    (φ : Face V (AtPublicFiles.KeyFile.In1 W₀ Rc) Pb)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₁)) :
    KeyShows Xs N Pl φ fs (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyShows Xs N Pl φ fs (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) ∧
      KeyShows Xs N Pl φ fs (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) := by
  obtain ⟨h1, h2, h3⟩ := keyJobs_in_pars (W₀ := W₀) (Rc := Rc) (X := X) h f
  obtain ⟨f1, f2, f3⟩ := key_k1_fit (W₀ := W₀) (Rc := Rc) (X := X) h hp f
  exact ⟨keyShows_of φ fs h1 _ rfl rfl f1, keyShows_of φ fs h2 _ rfl rfl f2,
    keyShows_of φ fs h3 _ rfl rfl f3⟩

/-- **ChainPins at what the key file's makers return, in scope**: the payer of this file's premise. -/
theorem chainPins_at_made {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray}
    {X₀ : OnBytes.Model.Verify.Public} {m : Johnson.G.OfPlan.Made}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hX : VerifiableInference.PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : VerifiableInference.Desc.Key.madeAt X₀ Z.lay VerifiableInference.Desc.Key.fixedDigest = .ok m)
    (r1 : VerifiableInference.Desc.Key.sourceOf m = .ok Xs)
    (r2 : VerifiableInference.Desc.Key.rangesNumbers m = .ok N)
    (r3 : VerifiableInference.Desc.Key.laterPlaces m = .ok Pl) : ChainPins Xs N Pl :=
  Johnson.KB4.chainPins_of (keyPins_in_scope hZ hX hm r1 r2 r3)

end AtPublicFiles.KeyK1

#print axioms AtPublicFiles.KeyK1.order_written
#print axioms AtPublicFiles.KeyK1.key_k1_good_written
#print axioms AtPublicFiles.KeyK1.key_k1_good
#print axioms AtPublicFiles.KeyK1.key_k1_fit
#print axioms AtPublicFiles.KeyK1.key_k1_shows
#print axioms AtPublicFiles.KeyK1.chainPins_at_made
#print axioms AtPublicFiles.KeyK1.key_k1_fields
