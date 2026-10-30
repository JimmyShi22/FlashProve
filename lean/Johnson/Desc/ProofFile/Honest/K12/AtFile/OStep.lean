-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OStep.lean: the frame's three other sentences at the proximity test on
G_omega, member 10 of the proof file's shared thread: `BehindS`, `ExchangeS`, `RidesPastS`. What the test's step leaves
of the verifier's state, and what the items at border 10 say behind it.

  `smp_real`, `smp_real_bent`   the messages 0, 2 and 3 of the door's state are sampled; control: message 1 is not
  `sampled_of_shape`, `sampled_at_stand`, `codes_at_stand`   read off the shape
  `enterO`, `seat_parts`   what the seat's way in makes of a state; a yes of the member's step rests on a yes of the
                 test's decision at that state, and the statement behind is the decision's
  `smpOwn_ten`   a sampled message's constraints go forwards, where the statement grows and the samples stay
  `open_ten`, `owes_ten`   the table at 10: every open item is shut or owed; the row owes o_omega's pin
  `ridesPastS_ten`   `RidesPastS` at 10: empty by the table
  `LettersTen`   what these sentences ask of the letters, at a stand and behind the step
  `behindS_head_O`, `ridesAt_pin`, `exchangeS_head_O`   the statements

The letters (`LettersTen`), each at a stand and behind the step. form, rides: at border 11 the form's letter and the
rider's say yes. keepsIn: a step whose statement grows and whose sampled messages stay meets the letter `keeps` at 10;
keepsOut: that letter holds no less. Nothing behind it reads more. It is the letters' to lay: `Kp₀` is free at that
place (`kp2`, Honest/K14/AskedAtShared.lean).

By what. `k12_inOrder` (Johnson/RunOne/Law/K12Order.lean), `k12_keeps` (K12Keeps.lean) at `Grows` and `SmpStay`;
`exchangeAtS_again`, `exchangeS_iff` (Honest/Thread/SharesS.lean); `step_decide` (Johnson/Desc/ChainEndFold.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, the sentences the ends.
- That a stand is reached is not said.
- The row at 10 shuts the rows of G_omega, the sample rows of o_omega and o_sp and o_sp's pin: `AcceptedS` is what
  spends them; o_omega's pin alone goes on.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OSays
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.RunOne.Law.K12Order
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey Group Statement)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (InOrder Words)
open VerifiableInference.Desc (Block Grows)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized SmpStay)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS sharedPlaces Msg2)
open Desc.K14 (St blocks frontBlock first)
open Desc.K14.Honest (SmpOwn Like)
open ProofFile.Honest
open ProofFile.Honest.K14 (num mgWords WitLens)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.SharedThread (Letters)
open Johnson.G (codesFull2 proofSendsFull)
open ProofFile.Honest.Sh (TestSh testSh)

-- Foretold: yes. Control: message 1, the mask that goes out with o_u, is not sampled.
#eval realSized.map fun q => (omegaShape q).core.st.oracles.map (·.sampled)
#guard realSized.all fun q =>
  [0, 2, 3].all fun o => ((omegaShape q).core.st.oracles[o]?).map (·.sampled) == some true
#guard realSized.all fun q => ((omegaShape q).core.st.oracles[1]?).map (·.sampled) != some true

theorem smp_real : (realSized.all fun q =>
    [0, 2, 3].all fun o => ((omegaShape q).core.st.oracles[o]?).map (·.sampled) == some true) = true := by
  decide +kernel

theorem smp_real_bent : (realSized.all fun q =>
    ((omegaShape q).core.st.oracles[1]?).map (·.sampled) != some true) = true := by
  decide +kernel

/-- Read off a state's shape: whether a message is sampled. -/
theorem sampled_of_shape (t : T12) (N : TestSh) (h : testSh t = N) (i : ℕ) :
    (t.st.oracles[i]?).map (·.sampled) = (N.core.st.oracles[i]?).map (·.sampled) := by
  subst h
  show _ = ((t.st.oracles.toList.map VerifiableInference.Desc.Ground.Sh.orcSh)[i]?).map (·.sampled)
  rw [List.getElem?_map, Array.getElem?_toList, Option.map_map]
  rfl

/-- What the seat's way in makes of a state. -/
def enterO (s : St) : T12 :=
  { st := s.st, book := s.book, roots := s.roots, g := s.loc.gOmega, pass := .nothing, mask := none }

/-- **A yes of the member's step rests on a yes of the test's decision at the state that the way in makes, and
the statement behind is the decision's.** -/
theorem seat_parts {W X Cl : Type} {blk : Block St Cl} {J : TestJob W X}
    (hseat : SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave)
    {ft : ℕ} {s s' : St} {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn} {n : ℕ}
    (h : blk.step ft s rs cols = .ok (s', n)) :
    ∃ rs' gs' t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterO s) rs' gs' = .ok t' ∧
      s'.st = t'.st := by
  obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ h
  rw [hseat.decide] at hd
  have hd' : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterO s) rs' gs').bind
      (VerifiableInference.Desc.K12.Seat.leave s) = .ok s' := hd
  cases hk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (enterO s) rs' gs' with
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
theorem smpOwn_ten {o : ℕ} {a b : St} {m : Words Cb.Gl.E} (hI : OnBytes.Means.InOrder a.st)
    (hG : Grows a.st b.st) (hS : SmpStay a.st b.st)
    (hs : ∀ x, a.st.oracles[o]? = some x → x.sampled = true) (h : SmpOwn o a m) : SmpOwn o b m := by
  obtain ⟨x, hx, hall⟩ := h
  obtain ⟨x', hx', -, -, e⟩ := hS.2 o x hx (hs x hx)
  refine ⟨x', hx', ?_⟩
  rw [e]
  exact fun r hr => (OnBytes.Means.says_extends rdE (OnBytes.Means.extends_of_grows hG)
    (hI.samples o x hx r hr) m).2 (hall r hr)

/-- At 10 every open item is shut or owed. -/
theorem open_ten : ∀ i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10,
    i ∈ (SharedRows.rows true 10).shuts ∨ i ∈ (SharedRows.rows true 10).owes := by
  decide

/-- The row at 10 owes o_omega's pin alone. -/
theorem owes_ten : (SharedRows.rows true 10).owes = ([.pin .oOmega] : List ItemS) := by decide

/-- O_omega's pin is open at 10. -/
theorem pin_open_ten : (ItemS.pin .oOmega) ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10 := by
  decide

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ Cl P₁ Wt : Type} {Bk : ProverCoinCounts}

/-- The state's codes are the plan's, at a state of the door's shape. -/
theorem codes_at_stand (h : P5J.AtMg o Z D r Zp Np cF) (t : T12) (ht : testSh t = headShape Zp Np) :
    t.st.codes = (K1.qAt Zp Np).codes := by
  obtain ⟨x, hx, e, eC, -⟩ := omegaShape_head h
  have k₁ := codes_real_O
  rw [hx] at k₁
  simp only [Option.all_some, beq_iff_eq] at k₁
  have h1 : (testSh t).core.st.codes = t.st.codes := rfl
  rw [← h1, ht.trans e, k₁, eC]

/-- The messages 0, 2 and 3 are sampled, at a state of the door's shape. -/
theorem sampled_at_stand (h : P5J.AtMg o Z D r Zp Np cF) (t : T12) (ht : testSh t = headShape Zp Np)
    {i : ℕ} (hi : i ∈ [0, 2, 3]) (x : OnBytes.Oracle) (hx : t.st.oracles[i]? = some x) :
    x.sampled = true := by
  obtain ⟨x₀, hx₀, e, -, -⟩ := omegaShape_head h
  have k := smp_real
  rw [hx₀] at k
  simp only [Option.all_some] at k
  have a := List.all_eq_true.1 k i hi
  simp only [beq_iff_eq] at a
  have e2 := sampled_of_shape t _ (ht.trans e) i
  rw [hx] at e2
  exact Option.some.inj (e2.trans a)

section
variable (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)

/-- **`RidesPastS` at 10: every open item is shut or owed.** -/
theorem ridesPastS_ten (hsp : L.split = true)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop) : RidesPastS L.thread Said 10 := by
  intro k s m E s' ps i v _ _ h1 h2 h3 _
  have e1 : L.thread.opened 10 = fwdOpen SharedRows.start (SharedRows.rows true) 10 := by
    show fwdOpen SharedRows.start (SharedRows.rows L.split) 10 = _
    rw [hsp]
  have e2 : L.thread.row 10 = SharedRows.rows true 10 := by
    show SharedRows.rows L.split 10 = _
    rw [hsp]
  rw [e1] at h1
  rw [e2] at h2 h3
  rcases open_ten i h1 with h | h
  · exact absurd h h2
  · exact absurd h h3

/-- **What the three sentences ask of the letters**: each at a stand and behind the step of member 10 itself, so
that a letter that says more of a state than that step gives is not barred. -/
structure LettersTen (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop) : Prop where
  split : L.split = true
  order : ∀ s, L.order s ↔ OnBytes.Means.InOrder s.st
  form : ∀ blk, L.thread.bs[10]? = some blk → ∀ k s m E ds y cols s',
    ThrS L.thread Said 10 k s m E → L.thread.Stepped blk k s m E ds y cols s' → L.shape 11 s' = true
  rides : ∀ blk, L.thread.bs[10]? = some blk → ∀ k s m E ds y cols s',
    ThrS L.thread Said 10 k s m E → L.thread.Stepped blk k s m E ds y cols s' →
    L.rides 11 y.2.st.input s'
  keepsIn : ∀ blk, L.thread.bs[10]? = some blk → ∀ k s m E ds y cols s',
    ThrS L.thread Said 10 k s m E → L.thread.Stepped blk k s m E ds y cols s' →
    Grows s.st s'.st → SmpStay s.st s'.st → L.thread.keeps 10 s s'
  keepsOut : ∀ k s m E s', ThrS L.thread Said 10 k s m E → L.thread.keeps 10 s s' →
    Grows s.st s'.st ∧ SmpStay s.st s'.st

end

section
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
  (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
  (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs)
  {blk : Block St Cl} (H : StandO Zp Np pO L.thread Said wts rnd JU own₀ c₀ bs blk)
  (K : LettersTen L Said)

include h H hb in
/-- At a stand the job's state on entry is what the way in makes of the stand's state, and has the door's shape. -/
theorem rec_at_stand {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : ThrS L.thread Said 10 k s m E) :
    (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m) = enterO s ∧
      testSh (enterO s) = headShape Zp Np := by
  have hen := enters_at_ten L.thread c₀ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U H.front
    H.ahead H.ft H.begun u.1 (H.field _ s m E u)
  have hrec := Except.ok.inj hen
  have hsh : testSh ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)) =
      headShape Zp Np := by
    rw [rec_door]
    exact shape_head_OmegaF h bs hb _ _ _ _
  have e : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m) = enterO s := by
    rw [rec_door]
    exact hrec.symm
  exact ⟨e, by rw [← e]; exact hsh⟩

include h hO H hb K in
/-- **`BehindS` at 10.** -/
theorem behindS_head_O : BehindS L.thread Said 10 := by
  intro blk' hblk' k s m E ds y cols s' u hd hS
  rw [H.member] at hblk'
  cases hblk'
  obtain ⟨rs', gs', t', hdec, est⟩ := seat_parts H.seat hS.2
  obtain ⟨-, hsh⟩ := rec_at_stand h L Said wts rnd JU own₀ c₀ bs hb H u
  have hI : OnBytes.Means.InOrder s.st := (K.order s).1 u.1.2.2.1.2
  have hlen : (enterO s).st.codes.lengthsOk = true := by
    rw [codes_at_stand h _ hsh]
    exact lengths_head h
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
  refine ⟨⟨?_, ?_⟩, K.rides _ H.member k s m E ds y cols s' u hS,
    K.keepsIn _ H.member k s m E ds y cols s' u hS hG hSt⟩
  · show (L.shape 11 s' && (!decide ((sharedPlaces L.split).length ≤ 11) || L.nothingLeft s')) = true
    rw [K.form _ H.member k s m E ds y cols s' u hS, K.split]
    rfl
  · exact (K.order s').2 hsI

include h H hb K in
/-- O_omega's pin says behind the member what it says in front. -/
theorem ridesAt_pin (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hMg : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w)) :
    RidesPastAtS L.thread Said 10 (ItemS.pin .oOmega) := by
  intro k s m E s' ps v u hK h0
  obtain ⟨hG, hSt⟩ := K.keepsOut k s m E s' u hK
  obtain ⟨-, hsh⟩ := rec_at_stand h L Said wts rnd JU own₀ c₀ bs hb H u
  have hI : OnBytes.Means.InOrder s.st := (K.order s).1 u.1.2.2.1.2
  have hs : ∀ n : Msg2, ∀ x, s.st.oracles[num n]? = some x → x.sampled = true := by
    intro n x hx
    refine sampled_at_stand h (enterO s) hsh ?_ x hx
    cases n <;> decide
  have e : ∀ n, L.N.tenant n = L.N.tenant .oOmega →
      SmpOwn (num n) s (ℓ.get v) := by
    have e₀ := h0
    change ItemS.holdsSh L.N (L.Mg m.st.input) (ItemS.pin .oOmega) s (L.thread.strs E) v at e₀
    rw [hMg] at e₀
    exact e₀
  change ItemS.holdsSh L.N (L.Mg m.st.input) (ItemS.pin .oOmega) s' (L.thread.strs (E.add ps)) v
  rw [hMg]
  intro n hn
  exact smpOwn_ten hI hG hSt (hs n) (e n hn)

include h hO H hb K in
/-- **`ExchangeS` at 10.** -/
theorem exchangeS_head_O (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hMg : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w)) : ExchangeS L.thread Said 10 := by
  refine (exchangeS_iff L.thread Said).2 fun i hi => ?_
  have e2 : L.thread.row 10 = SharedRows.rows true 10 := by
    show SharedRows.rows L.split 10 = _
    rw [K.split]
  rw [e2, owes_ten] at hi
  obtain rfl := List.mem_singleton.1 hi
  have hin : (ItemS.pin .oOmega) ∈ L.thread.opened 10 := by
    show _ ∈ fwdOpen SharedRows.start (SharedRows.rows L.split) 10
    rw [K.split]
    exact pin_open_ten
  exact exchangeAtS_again L.thread Said hin (behindS_head_O h hO L Said wts rnd JU own₀ c₀ bs hb H K)
    (ridesAt_pin h L Said wts rnd JU own₀ c₀ bs hb H K ℓ Mg₀ hMg)

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.smp_real
#print axioms ProofFile.Honest.K12.AtFile.smp_real_bent
#print axioms ProofFile.Honest.K12.AtFile.sampled_of_shape
#print axioms ProofFile.Honest.K12.AtFile.seat_parts
#print axioms ProofFile.Honest.K12.AtFile.smpOwn_ten
#print axioms ProofFile.Honest.K12.AtFile.open_ten
#print axioms ProofFile.Honest.K12.AtFile.owes_ten
#print axioms ProofFile.Honest.K12.AtFile.pin_open_ten
#print axioms ProofFile.Honest.K12.AtFile.codes_at_stand
#print axioms ProofFile.Honest.K12.AtFile.sampled_at_stand
#print axioms ProofFile.Honest.K12.AtFile.ridesPastS_ten
#print axioms ProofFile.Honest.K12.AtFile.rec_at_stand
#print axioms ProofFile.Honest.K12.AtFile.behindS_head_O
#print axioms ProofFile.Honest.K12.AtFile.ridesAt_pin
#print axioms ProofFile.Honest.K12.AtFile.exchangeS_head_O
