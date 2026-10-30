-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/FiveAtNine.lean: three of the frame's sentences at member 9 of a
shared thread, behind the test on G_u: `BehindS`, `ExchangeS`, `RidesPastS` (Honest/Thread/PaysS.lean); the
two others are `playsS_at_test`, `acceptedS_head_U`. What the thread's field `keeps` at that member must
hold: a yes of the test's decision: the rows that ride past are carried by that yes alone.

  `keepsU` (AtFullSide/K12/LaterJobs.lean)   the letter of `keeps` at member 9: the test on G_u said yes
  `step_loc`, `inOrder_past`, `smp_past`, `rowsO_past`   what a yes leaves: the chain's own numbers; the
                 order of the statement; the sample rows of a message that is not the mask handed in;
                 the open rows of G_omega
  `moved_state`  a played half turns nothing of the state but what has been heard
  `behindS_nine`, `exchangeS_nine`, `ridesPastS_nine`   the three sentences

By what. `seat_extends`, `allSay_onGu`, `samples_onGu` (Johnson/Desc/K12/Coin/RowsBack.lean), `k12_inOrder`
(Johnson/RunOne/Law/K12Order.lean), `half_tables` (K12/TableOfRun.lean), `behind_fold` (K12/PubAtDoor.lean).

Which items. Row 9 of the shared table shuts the rows of G_u and o_u's pin and owes o_sp's pin as context.
What rides past it: o_omega's pin, the sample rows of o_omega and o_sp, the open row on G_omega: `rest_nine`
says so by evaluation. `mgWords` (Honest/K14/Thread2.lean) reads of a record these and no table of the
chain, so the trees that the member adds do not touch them.

The premises. hB9: at a stand the state is `Behind`: `ProofFile.Honest.K12.Light.behind_fold` at the fold of `stand_at_nine`. he, ha: the
place's flags. hcl: the codes' lengths. hother, hnl, hord, hrd, hkp: the thread's letters `shape`, `nothingLeft`,
`order`, `rides`, `keeps` at member 10 and 9.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each statement has the thread's pair as a premise.
- `rides` at 10 is a letter: what the test on G_omega's field will ask of it is that letter's.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysAtTest
import AtFullSide.K12.LaterJobs
import Johnson.Desc.ProofFile.Honest.K12.PubAtDoor
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.K14.Thread2
import Johnson.Desc.ProofFile.Honest.Thread.Shared
import Johnson.Desc.K12.Coin.RowsBack
import Johnson.RunOne.Law.K12Order
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey OracleNotice)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay Words)
open VerifiableInference.Desc (Block OpenedColumn step_iff)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (seat_extends allSay_onGu samples_onGu)
open VerifiableInference.Desc.Shared (MeaningS ItemS Msg2 sharedPlaces)
open Desc.K14 (St)
open Desc.K14.Law (rowsOn RowsO)
open Desc.K14.Honest (SmpOwn)
open ProofFile.Honest
open ProofFile.Honest.K14 (mgWords form2 WitLens num)
open ProofFile.Honest.K12

section
variable {p : P12} {d d' : St} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}

theorem step_loc (h : (SeatU (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d') :
    d'.loc = d.loc := by
  have h' : ((VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind
        (VerifiableInference.Desc.K12.Seat.leave d)) = .ok d' := h
  obtain ⟨t, -, h'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', -, hl⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  cases hl
  rfl

theorem inOrder_past (h : (SeatU (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (hI : OnBytes.Means.InOrder d.st) : OnBytes.Means.InOrder d'.st := by
  have h' : ((VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind
        (VerifiableInference.Desc.K12.Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  cases hl'
  obtain ⟨rfl⟩ : t = _ := by
    unfold VerifiableInference.Desc.K12.Seat.enter at ht
    exact (Except.ok.inj ht).symm
  exact Johnson.RunOne.Law.K12Order.k12_inOrder p _ t' rs gs ht' hl hI

theorem smp_past (he : p.early = true) (ha : p.answers = 1)
    (h : (SeatU (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d') (hI : OnBytes.Means.InOrder d.st)
    {o : ℕ} (lt : o < d.st.oracles.size) (hm : d.loc.firstMask ≠ some o) {w : Words GE}
    (hs : SmpOwn o d w) : SmpOwn o d' w := by
  obtain ⟨x, hx, ha'⟩ := hs
  obtain ⟨x', hx', -⟩ := (seat_extends (·.gU) (·.firstMask) p he ha d d' rs gs h).shape o x hx
  refine ⟨x', hx', fun r hr => ?_⟩
  refine (samples_onGu rdE p he ha d d' rs gs h hI o lt hm w).2 (fun y hy r' hr' => ?_) x' hx' r hr
  rw [hx] at hy
  obtain rfl := Option.some.inj hy
  exact ha' r' hr'

theorem rowsO_past (he : p.early = true) (ha : p.answers = 1)
    (h : (SeatU (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d') (hI : OnBytes.Means.InOrder d.st)
    (lt : d.loc.gOmega < d.st.groups.size) (hq : d.loc.gOmega ≠ d.loc.gU) {w : Words GE}
    (hs : RowsO rdE 0 1 d w) : RowsO rdE 0 1 d' w := by
  unfold RowsO at hs ⊢
  rw [step_loc h]
  exact (allSay_onGu rdE p he ha d d' rs gs h hI _ lt hq 0 1 w).2 hs

end

/-- **What rides past member 9**, by evaluation. -/
theorem rest_nine : (ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start
    (ProofFile.Honest.SharedRows.rows true) 9).all (fun i =>
            (ProofFile.Honest.SharedRows.rows true 9).shuts.contains i ||
            (ProofFile.Honest.SharedRows.rows true 9).owes.contains i ||
            [ItemS.pin .oOmega, ItemS.row (.sample .oOmega), ItemS.row (.sample .oSp),
              ItemS.row .foldOmega].contains i) = true := by
  decide

/-- Control: o_omega's pin rides, and is shut or owed by nothing. -/
theorem rest_nine_bent : (ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start
    (ProofFile.Honest.SharedRows.rows true) 9).all (fun i =>
            (ProofFile.Honest.SharedRows.rows true 9).shuts.contains i ||
            (ProofFile.Honest.SharedRows.rows true 9).owes.contains i ||
            [ItemS.row (.sample .oOmega), ItemS.row (.sample .oSp),
              ItemS.row .foldOmega].contains i) = false := by
  decide

theorem owes_nine : (ProofFile.Honest.SharedRows.rows true 9).owes = [ItemS.pin .oSp] := by decide

theorem num_small (m : Msg2) : num m < 4 ∧ num m ≠ 1 := by
  cases m <;> decide

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (Q : Desc.K14.P14) (sentU : Array OracleNotice)
  (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop) (p : P12)
  (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)

theorem means_eq (hMg : L.Mg = fun w => mgWords ℓ Q L.N (Mg₀ w)) (w : Common W₀ Rc TableKey)
    (i : ItemS) (a : Unit × St) (y : VerifiableInference.Desc.Strs) (v : Wt) :
    L.thread.means w i a y v = ItemS.holdsSh L.N (mgWords ℓ Q L.N (Mg₀ w)) i a.2 y v := by
  show ItemS.holdsSh L.N (L.Mg w) i a.2 y v = _
  rw [hMg]

/-- **A played half turns nothing of the state but what has been heard.** -/
theorem moved_state {S V W X Pb : Type} {Cl' : Type} (T : Thread Bk S Cl' V W X Pb) {blk : Block S Cl'}
    (J : TestJob W X) (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J))
    (s₁ t₁ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s₁ :: t₁ :: rest)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    {k : Coins Bk} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X}
    {cols : List OpenedColumn} (hMv : T.Moved blk k m E ds y cols) :
    y.2.st = { m.st with heard := m.st.heard ++ ds } := by
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨c, hc, rfl⟩ := steps_one_half hhalf hl
  rw [hpl] at hc
  have hy' : play (rowSteps blk.name J.p.place (T.φ.sees m.st.input)
      [(firstPart J : Part V W X), restPart J] 0 (blk.rounds.zip blk.oracles) c) ds [] m =
      .ok y := by
    have e := hy
    unfold Placed.steps at e
    rw [hpl] at e
    exact e
  exact (half_tables J s₁ t₁ rest hst blk.name (T.φ.sees m.st.input) _ hrs c ds [] m y hy').2

/-- A step of the seated block is a yes of the test. -/
theorem keeps_of_step {blk : Block St Cl} {J : TestJob (Common W₀ Rc TableKey) X₀}
    (hseat : SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave)
    {ft : ℕ} {s s' : St} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (h : blk.step ft s rs cols = .ok (s', n)) : keepsU J.p s s' := by
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols n).1 h
  rw [hseat.decide] at hd
  exact ⟨_, _, hd⟩

/-- **`BehindS` at member 9.** -/
theorem behindS_nine (hsp : L.split = true) {blk : Block St Cl} (hblk : L.thread.bs[9]? = some blk)
    (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hseat : SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave)
    (other : ℕ → St → Bool) (hsh : L.shape = form2 Q other)
    (hoth : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → other 10 s' = true)
    (hord : ∀ s, L.order s ↔ OnBytes.Means.InOrder s.st)
    (hrd : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → L.thread.rides 10 y.2.st.input s')
    (hkp : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → L.thread.keeps 9 s s')
    (hcl : ∀ k s m E, Thr L.thread 9 k s m E → s.st.codes.lengthsOk = true) :
    BehindS L.thread Said 9 := by
  intro blk' hblk' k s m E ds y cols s' u _ hSt
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨hyr, hyg, hy⟩ : keepsU J.p s s' := keeps_of_step hseat hSt.2
  refine ⟨⟨?_, ?_⟩, hrd k s m E ds y cols s' u hSt, hkp k s m E ds y cols s' u hSt⟩
  · show (L.shape 10 s' && (!decide ((sharedPlaces L.split).length ≤ 10) || L.nothingLeft s')) = true
    have e : form2 Q other 10 s' = other 10 s' := if_neg (by omega)
    have hlen : (sharedPlaces true).length = 12 := rfl
    rw [hsh, e, hoth k s m E ds y cols s' u hSt, hsp, hlen]
    rfl
  · exact (hord s').2 (inOrder_past hy (hcl k s m E u.1) ((hord s).1 u.1.2.2.1.2))

/-- **`ExchangeS` at member 9.** -/
theorem exchangeS_nine (hMg : L.Mg = fun w => mgWords ℓ Q L.N (Mg₀ w)) (hsp : L.split = true)
    {blk : Block St Cl} (hblk : L.thread.bs[9]? = some blk) (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hseat : SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave)
    (hhalf : (L.thread.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J))
    (s₁ t₁ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s₁ :: t₁ :: rest)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (he : J.p.early = true) (ha : J.p.answers = 1)
    (hB9 : ∀ k s m E, Thr L.thread 9 k s m E → ProofFile.Honest.K12.Light.Behind Q sentU s)
    (hsz : (sentU ++ Desc.K14.withOmega Q.S).size = 4)
    (hord : ∀ s, L.order s → OnBytes.Means.InOrder s.st) : ExchangeS L.thread Said 9 := by
  intro blk' hblk' k s m E ds y cols s' u _ hSt ds₂ i hi
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨_, _, hy⟩ : keepsU J.p s s' := keeps_of_step hseat hSt.2
  have hyS := moved_state L.thread J hseat.place hhalf s₁ t₁ rest hst hrs hSt.1
  have hrow : (L.thread.row 9) = ProofFile.Honest.SharedRows.rows true 9 := by
    show ProofFile.Honest.SharedRows.rows L.split 9 = _
    rw [hsp]
  rw [hrow, owes_nine] at hi
  have hi' := List.mem_singleton.1 hi
  subst hi'
  have B := hB9 k s m E u.1
  have hI : OnBytes.Means.InOrder s.st := hord s u.1.2.2.1.2
  have hsize : ∀ m' : Msg2, num m' < s.st.oracles.size := fun m' => by
    have e := congrArg Array.size B.mid.shapes
    simp only [Array.size_map] at e
    rw [hsz] at e
    rw [e]
    exact (num_small m').1
  have hmask : ∀ m' : Msg2, s.loc.firstMask ≠ some (num m') := fun m' => by
    rw [B.mask]
    intro e
    exact (num_small m').2 (Option.some.inj e).symm
  have hopen : ItemS.pin .oSp ∈ L.thread.opened 9 := by
    show _ ∈ ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start (ProofFile.Honest.SharedRows.rows L.split) 9
    rw [hsp]
    decide
  have hIt := u.1.2.2.2.1 (ds ++ ds₂) _ hopen
  have e1 : y.2.st.input = m.st.input := by rw [hyS]
  have e2 : y.2.st.heard = m.st.heard ++ ds := by rw [hyS]
  rw [means_eq L Q ℓ Mg₀ hMg] at hIt ⊢
  rw [e1, e2, List.append_assoc]
  intro m' hm'
  exact smp_past he ha hy hI (hsize m') (hmask m') (hIt m' hm')

/-- **`RidesPastS` at member 9.** -/
theorem ridesPastS_nine (hMg : L.Mg = fun w => mgWords ℓ Q L.N (Mg₀ w)) (hsp : L.split = true)
    (he : p.early = true) (ha : p.answers = 1)
    (hkp : ∀ k s m E s', ThrS L.thread Said 9 k s m E → L.thread.keeps 9 s s' → keepsU p s s')
    (hB9 : ∀ k s m E, Thr L.thread 9 k s m E → ProofFile.Honest.K12.Light.Behind Q sentU s)
    (hsz : (sentU ++ Desc.K14.withOmega Q.S).size = 4)
    (hord : ∀ s, L.order s → OnBytes.Means.InOrder s.st) : RidesPastS L.thread Said 9 := by
  intro k s m E s' ps i v u hk hi hs ho hm
  obtain ⟨rs, gs, hy⟩ := hkp k s m E s' u hk
  have B := hB9 k s m E u.1
  have hI : OnBytes.Means.InOrder s.st := hord s u.1.2.2.1.2
  have hi' : i ∈ ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start (ProofFile.Honest.SharedRows.rows true) 9 := by
    have e : i ∈ ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start
      (ProofFile.Honest.SharedRows.rows L.split) 9 := hi
    rw [hsp] at e
    exact e
  have hrow : (L.thread.row 9) = ProofFile.Honest.SharedRows.rows true 9 := by
    show ProofFile.Honest.SharedRows.rows L.split 9 = _
    rw [hsp]
  rw [hrow] at hs ho
  have hc := List.all_eq_true.1 rest_nine i hi'
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
  have hcase : i ∈ [ItemS.pin .oOmega, ItemS.row (.sample .oOmega), ItemS.row (.sample .oSp),
      ItemS.row .foldOmega] := by
    rcases hc with (h1 | h1) | h1
    · exact absurd h1 hs
    · exact absurd h1 ho
    · exact h1
  have hsize : ∀ m' : Msg2, num m' < s.st.oracles.size := fun m' => by
    have e := congrArg Array.size B.mid.shapes
    simp only [Array.size_map] at e
    rw [hsz] at e
    rw [e]
    exact (num_small m').1
  have hmask : ∀ m' : Msg2, s.loc.firstMask ≠ some (num m') := fun m' => by
    rw [B.mask]
    intro e
    exact (num_small m').2 (Option.some.inj e).symm
  rw [means_eq L Q ℓ Mg₀ hMg] at hm ⊢
  rcases List.mem_cons.1 hcase with rfl | hcase
  · intro m' hm'
    exact smp_past he ha hy hI (hsize m') (hmask m') (hm m' hm')
  rcases List.mem_cons.1 hcase with rfl | hcase
  · exact smp_past he ha hy hI (hsize _) (hmask _) hm
  rcases List.mem_cons.1 hcase with rfl | hcase
  · exact smp_past he ha hy hI (hsize _) (hmask _) hm
  obtain rfl := List.mem_singleton.1 hcase
  refine rowsO_past he ha hy hI ?_ ?_ hm
  · rw [B.gOmega, B.mid.groups]
    decide
  · rw [B.gOmega, B.gU]
    decide

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.step_loc
#print axioms ProofFile.Honest.K12.AtFile.inOrder_past
#print axioms ProofFile.Honest.K12.AtFile.smp_past
#print axioms ProofFile.Honest.K12.AtFile.rowsO_past
#print axioms ProofFile.Honest.K12.AtFile.rest_nine
#print axioms ProofFile.Honest.K12.AtFile.rest_nine_bent
#print axioms ProofFile.Honest.K12.AtFile.owes_nine
#print axioms ProofFile.Honest.K12.AtFile.moved_state
#print axioms ProofFile.Honest.K12.AtFile.keeps_of_step
#print axioms ProofFile.Honest.K12.AtFile.behindS_nine
#print axioms ProofFile.Honest.K12.AtFile.exchangeS_nine
#print axioms ProofFile.Honest.K12.AtFile.ridesPastS_nine
