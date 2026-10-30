-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OStand.lean: at the filled key thread, where the invariant holds at border 10 the
half of the test on G_omega plays, the verifier's step says yes, and the invariant holds at border 11, at every list of
challenges that fits the test. So the five sentences of OStep.lean are spent once.

  `steps_at_ten`   at member 10 the chain's steps return
  `step_at_ten`    from border 10 to border 11: the play, the state behind it, a yes of the test

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `step_at_ten` bears this label; the rule is at its home, the head of
  Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread's pair is a premise.
- hno, hfield and hN are premises: the no-stop, the field and the letter's carrying at member 10.
- That a stand at 10 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OLetter
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift
import E2E.KeyStandStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source descriptionFromSource)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey)
open AtPublicFiles.KeySharedQuiet (over_key fits_key)
open AtPublicFiles.KeyStandStep (step_pair)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega hk_O)
open AtPublicFiles.KeyDepthsAt (lays_O_at)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO find_O)
open AtPublicFiles.TableFilled (TR ttF)
open AtPublicFiles.PlaysAtNine (mems_at fresh_at)
open AtPublicFiles.TreesAtTenKey (block_ten)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.Stops (NoStop chainStopAt_none)
open Desc.K14 (St)
open Desc.K14.Honest (Eight)
open H2K.JointK (keyOmega)
open H2K.Member (piKOFull)

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

include hK₀ in
/-- **At member 10 the chain's steps return.** -/
theorem steps_at_ten (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (k : Coins (keyBook K₀))
    (v : Option Empty) :
    ∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) v [keyOmega (PF.O.getD PF.U)]
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs = .ok l := by
  have hP : (JO Xs K₁ B).p = piKOFull := pO_full
  have hseat : SeatOf (keyOmega (PF.O.getD PF.U)) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  obtain ⟨st0, st1, st2, hs₀⟩ : ∃ a b r, piKOFull.nums.stages = a :: b :: r := ⟨_, _, _, rfl⟩
  have hst : (JO Xs K₁ B).p.nums.stages = st0 :: st1 :: st2 := by
    rw [hP]
    exact hs₀
  have hlays := lays_O_at K₀ hK₀ (JO Xs K₁ B) hP (mems_at _ e _ _ _) (fresh_at _ e _ _ _)
  have hplace : ((proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀).place ==
      (JO Xs K₁ B).p.place) = true := beq_self_eq_true _
  have f1 : ([(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)].find? fun g =>
      g.place == (JO Xs K₁ B).p.place) = some (proverSideOfProximityTest (JO Xs K₁ B)) := by
    simp [List.find?, hplace]
  have f2 : ([(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)].find? fun g =>
      g.place == (keyOmega (PF.O.getD PF.U)).place) = some (proverSideOfProximityTest (JO Xs K₁ B)) := by
    rw [hseat.place]
    exact f1
  obtain ⟨c, -, hl⟩ := lays_of_B (keyBook K₀) 1 (Or.inr rfl) (JO Xs K₁ B) st0 st1 st2 hst hlays
    (keyOmega (PF.O.getD PF.U)) (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
    VerifiableInference.Desc.K12.Seat.leave hseat
    [(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)] f1 k v
  have eg := chainSteps_guarded (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) v
    (keyOmega (PF.O.getD PF.U)) (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs
    [(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)] (proverSideOfProximityTest (JO Xs K₁ B))
    (find_O Xs K₁ B hs hsp) f2
  rw [hl] at eg
  exact ⟨_, eg⟩

include hK₀ in
/-- **From a stand at 10 to a stand at 11**, at every list that fits, with a yes of the test on G_omega. -/
theorem step_at_ten (hpl : (descriptionFromSource Xs Nr PF).planOk = true) (e : parKey Xs PF = QK)
    {layO : OnBytes.TreeLay} (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (hKp : ∀ s s', Kp 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (hN : SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10)
    (hno : NoStop (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs)
    {k : Coins (keyBook K₀)} {s : St} {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E) (ds : List Fmt.Drawn)
    (hd : drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds = true) :
    ∃ (s' : St) (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (cols : List VerifiableInference.Desc.OpenedColumn),
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).Moved (keyOmega (PF.O.getD PF.U)) k m E ds y cols ∧
        ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 11 k s' (y.2.took cols) (E.add y.1) ∧
        (y.2.took cols).st.heard = m.st.heard ++ ds ∧ Grows s.st s'.st ∧ SmpStay s.st s'.st := by
  have hblk : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[10]? =
      some (keyOmega (PF.O.getD PF.U)) :=
    block_ten Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w B
  have hfit := fits_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w hpl
  have hO := over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w
  have hM : MadeNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 :=
    made_next _ hfit (by rw [hO.bs]; exact (planOk_all hpl).2.1) 10
  obtain ⟨hP, hB, hX, hR, hA⟩ := five_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ Said e
    hQ hs hsp hfield hKp (fun _ _ _ => none)
  obtain ⟨l, hsteps⟩ := steps_at_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hs hsp k
    ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).φ.sees m.st.input)
  obtain ⟨s', m', E', u', hh, hk, y, cols, hMv, rfl, rfl⟩ :=
    step_pair (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said (fun _ _ _ => none) hfit
      (by omega) hblk hN hP hA hB hX hR hM u hd (chainStopAt_none _ hno [_] _ _) hsteps rfl
  exact ⟨s', y, cols, hMv, u', hh,
    (hKp s s').1 ((keeps_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ s s').1 hk)⟩

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.steps_at_ten
#print axioms ProofFile.Honest.K12.AtKey.step_at_ten
