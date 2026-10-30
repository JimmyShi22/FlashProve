-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesRides.lean: behind the key file's test on the ranges,
the three debts of the first chain's thread (laid₁, E2E/KeyRest.lean) at member 15 that read the
verifier's step: BehindS, ExchangeS, RidesPastS. On the verifier's states alone: no prover is read.

  RngYes         the test's own step says yes from s to s'
  RngKept        the sampled messages and the key file's small record are kept from s to s'
  rng_keeps      the step keeps them
  six15          the items that ride across: unmarked, pinT, pin 0, srow 0, kclaims 0, kclaims 1
  riders15       at 15 nothing else is open and neither shut nor owed: by evaluation
  rider_rng      each of the six, true in front at any witness, is true behind at that witness
  behindS_rng, exchangeS_rng, ridesPastS_rng   the three debts

What is asked of the letters. hkind, hkept: kind₁ at 15 lies between RngYes and RngKept: the step
makes it true, and it keeps what the riders read. hSm, horc, hArr: the reading's sample
reads of a message what the test keeps (BaseSt.SmOnly), under the plan's numbers, and the seats are
the messages' own. hsame: the letter for sameness is "the two read as one element".

By what. form_behind₁ (E2E/KeyBehind.lean): the clause on the state. ranges_smpStay
(Johnson/RunOne/KeySmpStay.lean), keyD_passes (Johnson/RunOne/Law/RngAtKeyD.lean): what the step
keeps. rowHolds_reads (Johnson/RunOne/Law/KeyRideTools.lean): a sample row reads its own message's
tables alone, so that it holds behind, where the statement has grown. smp₁_of_smpStay
(Johnson/RunOne/KeySmStay.lean): the pin's sample. exchange_of_nil (E2E/KeyExchangeEmpty.lean): the
row owes nothing.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each debt has the pair ThrS as a premise.
- What the row owes is nothing, by the table's rows: ExchangeS is empty here.
- The two closed items, grows and pin 1, are not carried: the test shuts them.
- In scope; at the written sizes. That the pair holds at any run is not said here.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyBehind
import E2E.KeyExchangeEmpty
import E2E.KeyKeepsAt
import E2E.KeyRangesK12
import E2E.KeyRangesShape15
import Johnson.Top.H0.Walk.ReachInv
import Johnson.RunOne.KeySmpStay
import Johnson.RunOne.KeySmStay
import Johnson.RunOne.Law.RngAtKeyD
import Johnson.RunOne.Law.KeyRideTools

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block Place Strs Wit)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem start₁ enterRanges leaveRanges
  rangesTest ArrOk offTables_of_rowIn names_of_rowIn)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of)
open OnBytes.Slice (readE rdE)
open H2K.JointK (rngEntry)
open AtPublicFiles.AtFiles (KeySourced)
open Johnson.RunOne.KeyRows1 (meaning₁At plan₁ readers₁)
open Johnson.RunOne.KeyRows23 (smp₁_of_smpStay)
open Johnson.RunOne.Law.KeyRideTools (rowHolds_reads)
open AtPublicFiles.KeyThread (KeyFill laid₁ D one₀ holdsH rowsFirst member15 stepYes_of_step exchange_of_nil)
open Johnson.RunOne.KeyRows23 (atSix)
open VerifierAndGoals (InScope)

/-- **The test's own step says yes from s to s'.** -/
def RngYes (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums) (s s' : FirstState) :
    Prop :=
  Johnson.Desc.First.Walk.Tied.StepYes 0 (rngEntry Xs.Y.k.oneTime N) s s'

/-- **What the riders read stays**: the sampled messages, and the key file's small record. -/
def RngKept (s s' : FirstState) : Prop :=
  VerifiableInference.Desc.K1.SmpStay s.d.st s'.d.st ∧ s'.base = s.base

/-- **The step keeps it.** -/
theorem rng_keeps {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {Pl : VerifiableInference.Desc.Key.LaterPlaces} (hsrc : KeySourced Z Xs N Pl)
    {s s' : FirstState} (h : RngYes Xs N s s') : RngKept s s' := by
  obtain ⟨rs, gs, e⟩ := Johnson.Desc.First.Walk.Tied.stepYes_decide h
  have e' : (rangesTest (enterRanges Xs.Y.k.oneTime) leaveRanges N :
      Block FirstState Claim).decide s rs gs = .ok s' := e
  exact ⟨Johnson.RunOne.KeySmp.ranges_smpStay _ N
      (Johnson.RunOne.KeySmp.rng_planOk hsrc.named.plan) s rs gs s' e',
    (Johnson.RunOne.Law.RngAtKeyD.keyD_passes e').1⟩

/-- The items that ride across the test. -/
def six15 : List KItem := [.unmarked, .pinT, .pin 0, .srow 0, .kclaims 0, .kclaims 1]

/-- **At the border 15 nothing else is open and neither shut nor owed.** By evaluation. -/
theorem riders15 : ∀ i ∈ fwdOpen (start₁ 2) rowsFirst 15, i ∉ (rowsFirst 15).shuts →
    i ∉ (rowsFirst 15).owes → i ∈ six15 := by decide

theorem owes15 : (rowsFirst 15).owes = [] := by decide

theorem srow0_open : KItem.srow 0 ∈ fwdOpen (start₁ 2) rowsFirst 15 := by decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀)
  (rc : Rc) (x : Xi) (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **Each of the six, true in front at a witness, is true behind at that witness.** -/
theorem rider_rng {s s' : FirstState} (hy : RngKept s s')
    (hord : OnBytes.Means.InOrder s.d.st) (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (hz : ∃ o y₀, (plan₁ (one₀ Xs)).orc 0 = some o ∧ s.d.st.oracles[o]? = some y₀ ∧
      y₀.sampled = true)
    (p : Xi) (y y' : Strs) (v : Wit Cells Unit M) (i : KItem) (hi : i ∈ six15)
    (hu : holdsH (D Xs N Pl) L.base.h₁ atSix L.meetsT (meaning₁At (one₀ Xs) L.R) i (p, s) y v) :
    holdsH (D Xs N Pl) L.base.h₁ atSix L.meetsT (meaning₁At (one₀ Xs) L.R) i (p, s') y' v := by
  obtain ⟨hS, hb⟩ := hy
  unfold six15 at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hu
  · obtain ⟨o, z, h1, h2, h3⟩ := hu
    refine ⟨o, z, h1, ?_, h3⟩
    refine (smp₁_of_smpStay L.base hSm (p, s) (p, s') _ _ hS fun o₁ ho => ?_).trans h2
    obtain ⟨o₀, y₀, ho₀, hx₀, hs₀⟩ := hz
    have e0 : L.base.arr (atSix 0).1 (atSix 0).2 = 0 := hArr 0 (by simp)
    rw [e0, horc] at ho
    obtain rfl : o₀ = o₁ := Option.some.inj (ho₀.symm.trans ho)
    exact ⟨y₀, hx₀, hs₀⟩
  · obtain ⟨o, y₀, ho, hx, h1, h2, h3⟩ := hu
    obtain ⟨y₁, hx₁, e1, e2, e3⟩ := hS.2 o y₀ hx h1
    refine ⟨o, y₁, ho, hx₁, e2, by rw [e3]; exact h2, fun r hr => ?_⟩
    have hr' : r ∈ y₀.sampleRows.toList := by
      rw [← e3]
      exact hr
    have hh := h3 r hr'
    have hin : OnBytes.Means.RowIn s.d.st { code := 0, members := #[o] } r :=
      (hord.samples o y₀ hx r hr').isIn (by simp)
    rw [hsame] at hh ⊢
    refine (rowHolds_reads rdE s.d.st s'.d.st r _ _ (offTables_of_rowIn rdE _ _ r hin)
      (fun o' ho' pt => ?_) (fun _ _ _ _ => rfl)).1 hh
    have e : o' = o := by simpa using names_of_rowIn hin o' ho'
    rw [e]
    exact (VerifiableInference.Desc.Third.Law.tableSize_same s.d.st s'.d.st o o y₀ y₁ hx hx₁ e1
      hS.1 pt).symm
  · obtain ⟨Lk, ks, h1, h2, h3, h4⟩ := hu
    have e : (readers₁ (one₀ Xs)).keysAt s' 0 = (readers₁ (one₀ Xs)).keysAt s 0 := by
      show (s'.base.keys[0]?).bind _ = (s.base.keys[0]?).bind _
      rw [hb]
    exact ⟨Lk, ks, h1, e.trans h2, h3, h4⟩
  · obtain ⟨Lk, ks, h1, h2, h3, h4⟩ := hu
    have e : (readers₁ (one₀ Xs)).keysAt s' 1 = (readers₁ (one₀ Xs)).keysAt s 1 := by
      show (s'.base.keys[1]?).bind _ = (s.base.keys[1]?).bind _
      rw [hb]
    exact ⟨Lk, ks, h1, e.trans h2, h3, h4⟩

/-- **BehindS at member 15.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem behindS_rng (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hkind : ∀ s s', RngYes Xs N s s' → L.kind₁ 15 s s') (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    BehindS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 := by
  intro blk hblk k s m E ds y cols s' hT _ hS
  have hb : blk = rngEntry Xs.Y.k.oneTime N :=
    Option.some.inj (hblk.symm.trans (member15 scope hsrc.named))
  subst hb
  refine ⟨AtPublicFiles.KeyThread.form_behind₁ Xs N Pl L w₀ rc x hsrc scope (by decide) hblk hT.1 hS,
    trivial, ?_⟩
  exact hkind s s' (stepYes_of_step hS.2)

/-- **ExchangeS at member 15**: the row owes nothing. NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchangeS_rng (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ExchangeS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 :=
  exchangeS_of _ _ (exchange_of_nil _ owes15)

/-- **RidesPastS at member 15.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem ridesPastS_rng (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hkept : ∀ s s', L.kind₁ 15 s s' → RngKept s s') (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    RidesPastS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 := by
  intro k s m E s' ps i v hT hk hi hsh how hu
  have hk' : RngKept s s' := hkept s s' hk
  have hsh15 := AtPublicFiles.AtFiles.Full.shape15_of_thr hsrc scope (laid₁ Xs N Pl L w₀ rc x hs tb) rfl
    (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT.1
  have hTidy : stTidyB s.d.st = true :=
    (congrArg (·.2.tidy) hsh15).trans AtPublicFiles.AtFiles.Full.loc15.2.2
  have h0 := hT.1.2.2.2.1 [] (KItem.srow 0) srow0_open
  obtain ⟨o, y₀, ho, hx, hsamp, -, -⟩ := h0
  exact rider_rng Xs N Pl L hk' (tidy_of hTidy).inOrder hSm horc hArr hsame
    ⟨o, y₀, ho, hx, hsamp⟩ m.st.input.x _ _ _ i (riders15 i hi hsh how) hu

end

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.rng_keeps
#print axioms ProofFile.Honest.K12.AtKey.riders15
#print axioms ProofFile.Honest.K12.AtKey.owes15
#print axioms ProofFile.Honest.K12.AtKey.srow0_open
#print axioms ProofFile.Honest.K12.AtKey.rider_rng
#print axioms ProofFile.Honest.K12.AtKey.behindS_rng
#print axioms ProofFile.Honest.K12.AtKey.exchangeS_rng
#print axioms ProofFile.Honest.K12.AtKey.ridesPastS_rng
