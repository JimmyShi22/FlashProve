-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHRows.lean: the debts of a row of `OwesS` and the acceptance at the two sendings in front of
the lookups, and what the three sendings have in common, at the thread `T₁`, at every letter `Said`.

  `order_of`: the statement is in order where the thread's clause on the state holds.
  `rideKind`, `ride_any`: the items that ride over a step that keeps the older messages.
  `accepted_send`: the sub-protocol accepts.
  `behind_send`, `exchange_send`, `rides_send`: the three debts, at a sending that owes a pin and sample
    rows and whose row keeps the older messages.
  `rows_idx`, `rows_msg`: numbers 0 and 1, whole.

Limits. Conditional on `FirstPublic` and, as every debt, on the thread in front. W's row and the
batching's are in other files. Nothing says that the thread stands at any run.
-/
import E2E.FirstHSeats
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRow
import E2E.KeyShapeFirstAccepted
import E2E.KeyRest

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Means
open VerifiableInference.Desc (Block OpenedColumn Strs)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces start₁)
open AtPublicFiles.KeyThread (D one₀ rowsFirst form_behind₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (accepted_first)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob proverSideOfSending)
open ProofFile.Honest.Small (Listed lists_of_shaped)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles} {b n : Nat} {J : SendJob (In1 W₀ Rc) X'}

/-- **The statement is in order.** -/
theorem order_of {c : Nat} {k : Coins Bk} {s : FirstState} {m : Mid (In1 W₀ Rc) X'}
    (h : (Th Xs N Pl K f Q w₀ rc x).Form c k s m) : InOrder s.d.st :=
  h.2.1.1.1.2.2.1

/-- The items that ride over a step that keeps the older messages. -/
def rideKind : KItem → Bool
  | .unmarked | .pinT | .inRange _ | .pin _ | .srow _ => true
  | _ => false

/-- **They ride.** -/
theorem ride_any {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState} {y y' : Strs} {v}
    (hs : StaysK s s') (hord : InOrder s.d.st) {i : KItem} (hi : rideKind i = true) :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input i ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input i ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v := by
  cases i with
  | unmarked => exact ride_unmarked
  | pinT => exact ride_pinT
  | inRange l => exact ride_range
  | pin q => exact ride_pin hs
  | srow q => exact ride_srow hs hord
  | _ => cases hi

/-- **The sub-protocol accepts**, at a sending, from the thread alone. -/
theorem accepted_send (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) (hb : b < 19) (h15 : b ≠ 15)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Accepted (Th Xs N Pl K f Q w₀ rc x) fall b := by
  obtain ⟨blk, hblk, hsh, -⟩ := h.member
  have hl : Listed blk := lists_of_shaped
    ((planOk_all hs.named.plan).1 blk (List.mem_of_getElem? hblk)).2
  refine accepted_first hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
    (fun _ _ _ _ _ hbeg => ⟨_, hbeg⟩) fall hb h15
    (fitsAt_half (Th Xs N Pl K f Q w₀ rc x) hblk (g := proverSideOfSending J) ?_ ?_ hl.1.symm)
  · rw [hsh.1]
    exact h.half
  · rw [hsh.2.1]
    rfl

/-- **Behind a sending.** -/
theorem behind_send (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) (hb : b < 19)
    (hk : ∀ s s', StaysK s s' → (Th Xs N Pl K f Q w₀ rc x).keeps b s s') :
    Behind (Th Xs N Pl K f Q w₀ rc x) b := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  exact ⟨form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope hb hblk hT hS, trivial,
    hk _ _ (seat_stays h hblk hT hd hS)⟩

/-- **What a sending owes, where that is its pin and its sample rows.** -/
theorem exchange_send (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) (hb : b < 19)
    (ho : (rowsFirst b).owes = [.pin n, .srow n]) :
    Exchange (Th Xs N Pl K f Q w₀ rc x) b := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  have hF := form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope hb hblk hT hS
  have hP := seat_pin h (E := E.add y.1) hF
  have hR := seat_srow h hblk hT hd hS hF (order_of hF)
  show (Th Xs N Pl K f Q w₀ rc x).Items (rowsFirst b).owes k s' y.2 (E.add y.1)
  rw [ho]
  intro ds' i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hP ds' _ (List.mem_singleton.2 rfl)
  · obtain rfl := List.mem_singleton.1 hi
    exact hR ds' _ (List.mem_singleton.2 rfl)

/-- **What rides past a member that keeps the older messages.** -/
theorem rides_send (hk : ∀ s s', (Th Xs N Pl K f Q w₀ rc x).keeps b s s' → StaysK s s')
    (hO : ∀ i ∈ ProofFile.Honest.fwdOpen (start₁ 2) rowsFirst b, i ∉ (rowsFirst b).shuts →
      i ∉ (rowsFirst b).owes → rideKind i = true) :
    RidesPast (Th Xs N Pl K f Q w₀ rc x) b := by
  intro k s m E s' ps i v hT hkeep hi hn ho hm
  exact ride_any (hk _ _ hkeep) (order_of hT.2.2.1) (hO i hi hn ho) hm

/-- **Number 0, whole, at every letter `Said`.** -/
theorem rows_idx (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 0 ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said 0 ∧
      ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 0 ∧ RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said 0 ∧
      AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 0 :=
  have h := seat_idx (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  ⟨playsS_of _ _ (seat_plays h), behindS_of _ _ (behind_send hs scope h (by decide) fun _ _ e => e),
    exchangeS_of _ _ (exchange_send hs scope h (by decide) (by decide)),
    ridesPastS_of _ _ (rides_send (fun _ _ e => e) (by decide)),
    acceptedS_of _ _ (accepted_send hs scope h (by decide) (by decide) fall)⟩

/-- **Number 1, whole, at every letter `Said`.** -/
theorem rows_msg (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 1 ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said 1 ∧
      ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 1 ∧ RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said 1 ∧
      AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 1 :=
  have h := seat_msg (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  ⟨playsS_of _ _ (seat_plays h), behindS_of _ _ (behind_send hs scope h (by decide) fun _ _ e => e),
    exchangeS_of _ _ (exchange_send hs scope h (by decide) (by decide)),
    ridesPastS_of _ _ (rides_send (fun _ _ e => e) (by decide)),
    acceptedS_of _ _ (accepted_send hs scope h (by decide) (by decide) fall)⟩

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.order_of
#print axioms AtPublicFiles.FirstH.ride_any
#print axioms AtPublicFiles.FirstH.accepted_send
#print axioms AtPublicFiles.FirstH.behind_send
#print axioms AtPublicFiles.FirstH.exchange_send
#print axioms AtPublicFiles.FirstH.rides_send
#print axioms AtPublicFiles.FirstH.rows_idx
#print axioms AtPublicFiles.FirstH.rows_msg
