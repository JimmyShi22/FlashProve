-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OStep.lean: the frame's three other sentences at the test on G_omega, member 10
of the filled key thread: `BehindS`, `ExchangeS`, `RidesPastS`; and the five together.

  `sampled_at_door`, `one_not_sampled`   messages 0, 2 and 3 of the door's state are sampled; control: message 1 is not
  `enterAtTen`, `step_parts`   what the seat's way in makes of a state; a yes of the member's step rests on a yes of
                 the test's decision at that state
  `sample_goes_forward`   a sampled message's constraints go forwards, where the statement grows and samples stay
  `open_at_ten`, `owes_at_ten`   the table at 10: every open item is shut or owed; the row owes o_omega's pin
  `ridesPastS_at_ten`   `RidesPastS` at 10: empty by the table
  `keeps_at_ten`, `shape_at_stand`, `sampled_at_stand`, `codes_at_stand`   what the stand and the letter give
  `behindS_at_ten`, `pin_rides_at_ten`, `exchangeS_at_ten`   the two other sentences
  `five_at_ten_key`   the five

The filled key thread `TR` (E2E/TableFilled.lean) is `threadKey` at `PF`, at the prover `keyProver (withTestsOnUAndOmega K₁ pU pO)`,
the table `tbKey` with the letter `ttF`, and own 7 at `ownTbl` (K12/OwnTbl.lean), whose head holds the terms on which it
may be used.

The premises of `five_at_ten_key`, with who pays them. e, hK₀, hs, hsp, B: as in OAccepted.lean's head. hQ: `plan_key`
with `later_sourced`. hfield: `field_of_letter` (OField.lean). hKp: the letter keeps at member 10: what the member leaves
is that the statement grows and the sampled messages stay; the filling of `Kp` lays it so.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `behindS_at_ten`, `pin_rides_at_ten`, `exchangeS_at_ten`, `ridesPastS_at_ten`, `shape_at_stand`,
  `five_at_ten_key` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread's pair is a
  premise, the sentences the ends.
- The field is a premise (hfield): which letter gives it is not said here.
- The five count for the chain only where the other members' sentences stand at the same `TR`, `Kp` and `Said`.
- The row at 10 shuts the rows of G_omega, the sample rows of o_omega and o_sp and o_sp's pin: `AcceptedS` spends them.
- That a stand at 10 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OSays
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.K12Keeps
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey Group Statement)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Grows Place)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS sharedPlaces Msg2)
open VerifiableInference.Desc.Key (Source)
open Desc.K14 (St)
open Desc.K14.Honest (SmpOwn Eight)
open ProofFile.Honest
open ProofFile.Honest.K14 (num form2 keepsAll Plan2 WitLens)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (colsOpened)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm codes_O)
open ProofFile.Honest.Sh (TestSh testSh)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.HalvesAreJobs (pU pO JO)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.TableFilled (TR ttF plays_ten_thr_real)
open AtPublicFiles.TreesAtTenKey (block_ten)
open H2K.JointK (keyOmega)

theorem sampled_at_door :
    ([0, 2, 3].all fun o => (shapeOm.core.st.oracles[o]?).map (·.sampled) == some true) = true := by
  decide +kernel

/-- Control: message 1, the mask that goes out with o_u, is not sampled. -/
theorem one_not_sampled : (shapeOm.core.st.oracles[1]?).map (·.sampled) ≠ some true := by
  decide +kernel

/-- Read off a state's shape: whether a message is sampled. -/
theorem sampled_of_shape (t : T12) (N : TestSh) (h : testSh t = N) (i : ℕ) :
    (t.st.oracles[i]?).map (·.sampled) = (N.core.st.oracles[i]?).map (·.sampled) := by
  subst h
  show _ = ((t.st.oracles.toList.map VerifiableInference.Desc.Ground.Sh.orcSh)[i]?).map (·.sampled)
  rw [List.getElem?_map, Array.getElem?_toList, Option.map_map]
  rfl

/-- What the seat's way in makes of a state. -/
def enterAtTen (s : St) : T12 :=
  { st := s.st, book := s.book, roots := s.roots, g := s.loc.gOmega, pass := .nothing, mask := none }

/-- **A yes of the member's step rests on a yes of the test's decision at the state that the way in makes, and
the statement behind is the decision's.** -/
theorem step_parts {W X Cl : Type} {blk : Block St Cl} {J : TestJob W X}
    (hseat : SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave)
    {ft : ℕ} {s s' : St} {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn} {n : ℕ}
    (h : blk.step ft s rs cols = .ok (s', n)) :
    ∃ rs' gs' t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterAtTen s) rs' gs' = .ok t' ∧
      s'.st = t'.st := by
  obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ h
  rw [hseat.decide] at hd
  have hd' : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterAtTen s) rs' gs').bind
      (VerifiableInference.Desc.K12.Seat.leave s) = .ok s' := hd
  cases hk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterAtTen s) rs' gs' with
  | error e =>
    rw [hk] at hd'
    cases hd'
  | ok t' =>
    rw [hk] at hd'
    have e : ({ s with st := t'.st, book := t'.book, roots := t'.roots } : St) = s' :=
      Except.ok.inj hd'
    exact ⟨rs', gs', t', hk, by rw [← e]⟩

/-- **A sampled message's constraints go forwards**, where the statement in front is in order, it grows, and
the sampled messages stay. -/
theorem sample_goes_forward {o : ℕ} {a b : St} {m : Words Cb.Gl.E} (hI : OnBytes.Means.InOrder a.st)
    (hG : Grows a.st b.st) (hS : SmpStay a.st b.st)
    (hs : ∀ x, a.st.oracles[o]? = some x → x.sampled = true) (h : SmpOwn o a m) : SmpOwn o b m := by
  obtain ⟨x, hx, hall⟩ := h
  obtain ⟨x', hx', -, -, e⟩ := hS.2 o x hx (hs x hx)
  refine ⟨x', hx', ?_⟩
  rw [e]
  exact fun r hr => (OnBytes.Means.says_extends rdE (OnBytes.Means.extends_of_grows hG)
    (hI.samples o x hx r hr) m).2 (hall r hr)

/-- At 10 every open item is shut or owed. -/
theorem open_at_ten : ∀ i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10,
    i ∈ (SharedRows.rows true 10).shuts ∨ i ∈ (SharedRows.rows true 10).owes := by
  decide

/-- The row at 10 owes o_omega's pin alone. -/
theorem owes_at_ten : (SharedRows.rows true 10).owes = ([.pin .oOmega] : List ItemS) := by decide

/-- O_omega's pin is open at 10. -/
theorem pin_open_at_ten : (ItemS.pin .oOmega) ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10 := by
  decide

/-- The messages 0, 2 and 3 are sampled, at a state of the door's shape. -/
theorem sampled_at_stand (t : T12) (ht : testSh t = shapeOm) {i : ℕ} (hi : i ∈ [0, 2, 3])
    (x : OnBytes.Oracle) (hx : t.st.oracles[i]? = some x) : x.sampled = true := by
  have a := List.all_eq_true.1 sampled_at_door i hi
  simp only [beq_iff_eq] at a
  have e2 := sampled_of_shape t _ ht i
  rw [hx] at e2
  exact Option.some.inj (e2.trans a)

/-- The state's codes are the plan's, at a state of the door's shape. -/
theorem codes_at_stand (t : T12) (ht : testSh t = shapeOm) : t.st.codes = QK.codes := by
  have h1 : (testSh t).core.st.codes = t.st.codes := rfl
  rw [← h1, ht]
  exact codes_O

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)

/-- **`RidesPastS` at 10: every open item is shut or owed.** -/
theorem ridesPastS_at_ten : RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 := by
  intro k s m E s' ps i v _ _ h1 h2 h3 _
  have h1' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10 := h1
  have h2' : i ∉ (SharedRows.rows true 10).shuts := h2
  have h3' : i ∉ (SharedRows.rows true 10).owes := h3
  rcases open_at_ten i h1' with h | h
  · exact absurd h h2'
  · exact absurd h h3'

/-- The letter keeps at member 10 is the one that the thread reads there. -/
theorem keeps_at_ten (s s' : St) :
    (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).keeps 10 s s' ↔ Kp 10 s s' := by
  show keepsAll (parKey Xs PF) (sentKey Xs PF) Kp 10 s s' ↔ _
  unfold keepsAll
  rw [if_neg (by omega)]

/-- At a stand whose field holds the columns that the fold read, the state that the way in makes has the door's
shape. -/
theorem shape_at_stand (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E)
    (hfield : ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols) : testSh (enterAtTen s) = shapeOm := by
  have hen := enters_at_ten_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w B u hfield
  have hrec := Except.ok.inj hen
  have hsh := accepted_shape_written (W := Common W₀ Rc TableKey) (X := X₀) e place_full
    [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (by rw [B.made]) (fun v => v.key)
    colsOpened m.st.input (frontOf m)
  have e' : ProofFile.Honest.K12.Light.doorOmegaF (parKey Xs PF) (sentKey Xs PF)
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] pU (fun v => v.key) colsOpened m.st.input
      (frontOf m) = enterAtTen s := hrec.symm
  rw [← e']
  exact hsh

/-- **`BehindS` at 10.** -/
theorem behindS_at_ten (e : parKey Xs PF = QK)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st) :
    BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 := by
  intro blk' hblk' k s m E ds y cols s' u hd hS
  have hb10 : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[10]? =
      some (keyOmega (PF.O.getD PF.U)) :=
    block_ten Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w B
  obtain rfl : blk' = keyOmega (PF.O.getD PF.U) := Option.some.inj (hblk'.symm.trans hb10)
  have hseat : SeatOf (keyOmega (PF.O.getD PF.U)) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  obtain ⟨rs', gs', t', hdec, est⟩ := step_parts hseat hS.2
  have hsh := shape_at_stand K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u.1 (hfield k s m E u)
  have hI : OnBytes.Means.InOrder s.st := u.1.2.2.1.2
  have hlen : (enterAtTen s).st.codes.lengthsOk = true := by
    rw [codes_at_stand _ hsh]
    exact lengths_at_key
  have hsI : OnBytes.Means.InOrder s'.st := by
    rw [est]
    exact Johnson.RunOne.Law.K12Order.k12_inOrder _ _ _ _ _ hdec hlen hI
  have hG : Grows s.st s'.st := by
    rw [est]
    exact Johnson.RunOne.Law.K12Keeps.k12_keeps VerifiableInference.Desc.Ground.groundKeeps_grows
      Johnson.RunOne.KeyWalk.begin_grows _ _ _ _ _ hdec
  have hSt : SmpStay s.st s'.st := by
    rw [est]
    exact Johnson.RunOne.Law.K12Keeps.k12_keeps VerifiableInference.Desc.K1.groundKeeps_smpStay
      Johnson.RunOne.KeyWalk.begin_smp _ _ _ _ _ hdec
  refine ⟨⟨?_, hsI⟩, trivial, (keeps_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ s s').2
    ((hKp s s').2 ⟨hG, hSt⟩)⟩
  show (form2 (parKey Xs PF) (fun _ _ => true) 11 s' &&
    (!decide ((sharedPlaces true).length ≤ 11) || true)) = true
  unfold form2
  rw [if_neg (by omega)]
  simp

/-- O_omega's pin says behind the member what it says in front. -/
theorem pin_rides_at_ten (e : parKey Xs PF = QK)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st) :
    RidesPastAtS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 (ItemS.pin .oOmega) := by
  intro k s m E s' ps v u hK h0
  obtain ⟨hG, hSt⟩ := (hKp s s').1 ((keeps_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ s s').1 hK)
  have hsh := shape_at_stand K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u.1 (hfield k s m E u)
  have hI : OnBytes.Means.InOrder s.st := u.1.2.2.1.2
  have hs : ∀ n : Msg2, ∀ x, s.st.oracles[num n]? = some x → x.sampled = true := by
    intro n x hx
    refine sampled_at_stand (enterAtTen s) hsh ?_ x hx
    cases n <;> decide
  have e₀ : ∀ n, Nm.tenant n = Nm.tenant .oOmega → SmpOwn (num n) s (ℓ.get v) := h0
  show ∀ n, Nm.tenant n = Nm.tenant .oOmega → SmpOwn (num n) s' (ℓ.get v)
  intro n hn
  exact sample_goes_forward hI hG hSt (hs n) (e₀ n hn)

/-- **`ExchangeS` at 10.** -/
theorem exchangeS_at_ten (e : parKey Xs PF = QK)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st) :
    ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 := by
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  have hi' : i ∈ (SharedRows.rows true 10).owes := hi
  rw [owes_at_ten] at hi'
  obtain rfl := List.mem_singleton.1 hi'
  exact exchangeAtS_again _ Said pin_open_at_ten
    (behindS_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said e hfield hKp)
    (pin_rides_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said e hfield hKp)

include hK₀ in
/-- **The five sentences at member 10 of the filled key thread.** -/
theorem five_at_ten_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 ∧
      BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 ∧
      ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 ∧
      RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 ∧
      AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said fall 10 := by
  have hop : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      m.opened.isSome = true := fun k s m E u => by
    obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, -, hc, -⟩, -, -⟩ := u.1
    rw [hfield k s m E u cols hc]
    rfl
  exact ⟨plays_ten_thr_real K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hs hsp Said hop,
    behindS_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said e hfield hKp,
    exchangeS_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said e hfield hKp,
    ridesPastS_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said,
    accepted_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hQ hs hsp Said hfield fall⟩

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.sampled_at_door
#print axioms ProofFile.Honest.K12.AtKey.one_not_sampled
#print axioms ProofFile.Honest.K12.AtKey.sampled_of_shape
#print axioms ProofFile.Honest.K12.AtKey.step_parts
#print axioms ProofFile.Honest.K12.AtKey.sample_goes_forward
#print axioms ProofFile.Honest.K12.AtKey.open_at_ten
#print axioms ProofFile.Honest.K12.AtKey.owes_at_ten
#print axioms ProofFile.Honest.K12.AtKey.pin_open_at_ten
#print axioms ProofFile.Honest.K12.AtKey.sampled_at_stand
#print axioms ProofFile.Honest.K12.AtKey.codes_at_stand
#print axioms ProofFile.Honest.K12.AtKey.ridesPastS_at_ten
#print axioms ProofFile.Honest.K12.AtKey.keeps_at_ten
#print axioms ProofFile.Honest.K12.AtKey.shape_at_stand
#print axioms ProofFile.Honest.K12.AtKey.behindS_at_ten
#print axioms ProofFile.Honest.K12.AtKey.pin_rides_at_ten
#print axioms ProofFile.Honest.K12.AtKey.exchangeS_at_ten
#print axioms ProofFile.Honest.K12.AtKey.five_at_ten_key
