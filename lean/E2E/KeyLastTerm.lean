-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyLastTerm.lean: the last thread of the key file as one term, and `PlaysS` at its own test.

Main names.
  `DoorAsks`: what the door asks of an earlier thread and its letter, as one structure.
  `startKey`: where the chain's run begins: `startBy` over the pairs of stands of the two earlier threads.
  `tableKey`: the tables: a tree taken over is its sender's (`tableLast`); an own tree is what the play from `startKey` sends
    (`tableBy`, taken at the same thread at a default table, so no circle).
  `threadFull`: the thread at these tables.
  `tables_key`: at its own trees its table is `tableBy` at itself.
  `fixed_key`: its field `fixed` at an own tree.
  `playsS_own`: `PlaysS` at member 2, at the letter `saidKey`.

What stays open. `RunPlays` at each stand, the whole chain's steps, that every member is listed: premises of `playsS_own`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastDoor
import E2E.KeyLastStart
import E2E.KeyLastTrees
import E2E.KeyOwnPlays
import E2E.KeyOwnSeat
import E2E.KeyOwnLines
import E2E.KeyOwnAccepted

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (K12PlayedGuarded playsS_guarded playsS_mono proverSideOfProximityTest firstPart restPart RunPlays planPlays_of_B)
open ProofFile.Honest.Small (PlayedTo tableBy tableBy_congr sent_of_tableBy Listed)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Place Wit OpenedColumn)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁ decl₁ decl₂ decl₃ sentIn)
open AtPublicFiles.KeyDoorItems (commonOf)
open AtPublicFiles.KeyLay (pWK jobKWAt)
open H2K.Member (piKWFull)

/-- **What the door asks of an earlier thread and its letter**, at its last border n. -/
structure DoorAsks {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (T : Thread Bk S Cl V W Y Pb)
    (Said : Nat → Coins Bk → Mid W Y → Prop) (n : Nat) : Prop where
  one : OneStand Said n
  state : OneState T Said n
  field : ∀ k e m E, ThrS T Said n k e m E → T.Field [] n m E
  next : ∀ b, SaidNext T Said b

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **Where the last chain's run begins.** -/
def startKey : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Mid (Local W₀ Rc Xi Unit) X :=
  startBy (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
    (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₁ Said₂ 19 12 commonOf dfltM

/-- The thread at a default table: the play reads none of its tables. -/
abbrev threadBare :=
  T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML
    (fun _ _ _ _ => dfltT) n₁ n₂ Vd Rd Kp w

/-- **The tables of the last thread.** -/
def tableKey : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table :=
  tableLast (descriptionFromSource Xs Nr Pl) commonOf tb₁ tb₂ fun σ k v h =>
    match σ with
    | .own j => tableBy (threadBare Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁
        n₂ Vd Rd Kp w dfltT) (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM) dfltT j
        k v h
    | .taken _ _ => dfltT

/-- **The last thread.** -/
abbrev threadFull :=
  T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML
    (tableKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT dfltM)
    n₁ n₂ Vd Rd Kp w

/-- **At its own trees the table is what the play sends.** -/
theorem tables_key (j : Nat) (k : Coins Bk) (v : Local W₀ Rc Xi Unit) (h : List Fmt.Drawn) :
    (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT
      dfltM).table (.own j) k v h =
    tableBy (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
      dfltT dfltM) (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM) dfltT j k v h :=
  tableBy_congr rfl rfl rfl rfl rfl _ _ _ _ _ _

/-- **Its field `fixed` at an own tree.** -/
theorem fixed_key (j : Nat) :
    (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT
      dfltM).fixed (.own j) =
    (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT
      dfltM).front +
      sentIn ((threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
        dfltT dfltM).bs.flatMap (·.rounds)) j := by
  have hf : (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
      dfltT dfltM).front = (decl₁ (descriptionFromSource Xs Nr Pl)).length + (decl₂ (descriptionFromSource Xs Nr Pl)).length := by
    show (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
      declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length).length = _
    unfold declsTo
    rw [List.take_length, List.take_length, List.length_append]
  rw [hf]
  rfl

variable {Wd : Type} (JI JW : ProofFile.Honest.K1.SendJob Wd X) (A : ProofFile.Honest.K14.SendPub)
  (lift : Local W₀ Rc Xi Unit → Wd) (ask : Local W₀ Rc Xi Unit → ProofFile.Honest.K14.Ask)

/-- **It plays, and its new trees are the thread's tables**, at member 2, at the letter `saidKey`. -/
theorem playsS_own (hpl : pWK Pl = piKWFull) (hdM : dfltM.opened.isSome = true)
    (hfr : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.fresh.isNone = false)
    (hhalf : ((threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
        dfltT dfltM).hs.find? fun g => g.place == (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place) =
      some (proverSideOfProximityTest (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X).needsField)
    (hrun : ∀ k st m E ds
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]),
      ThrS (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
        dfltT dfltM) (PlayedTo (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁
        n₂ Vd Rd Kp w dfltT dfltM) (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM))
        2 k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p : Block T12 Unit).rounds ds = true →
      ProofFile.Honest.lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c →
      RunPlays (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest 0 m E c)
    (hlisted : ∀ b ∈ (descriptionFromSource Xs Nr Pl).second.blocksInOrder, Listed b)
    (hlaid : ∀ (k : Coins Bk) (v : Local W₀ Rc Xi Unit), ∃ Lall,
      chainSteps Bk (Bk.rowsOf 2) (k.look 2) (Face.own.sees v) (descriptionFromSource Xs Nr Pl).second.blocksInOrder
        (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT
          dfltM).hs = .ok Lall) :
    PlaysS (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT
        dfltM)
      (saidKey (descriptionFromSource Xs Nr Pl) (threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁
                         n₂ Vd Rd Kp w dfltT dfltM) (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM)) 2 := by
  refine playsS_mono (fun k m h => h.2 (Nat.le_refl 2)) ?_
  have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = piKWFull := hpl
  obtain ⟨s, t, rest, hst, hk⟩ := stages_KW
  refine playsS_guarded _ _ 2 (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn 0
    ⟨?_, hhalf, startBy_opened dfltM hdM, ⟨s, t, rest, by rw [hp]; exact hst, hk, ?_⟩, hrun,
      sent_of_tableBy _ _ dfltT fun j _ => tables_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁
        Said₂ d Dt ML n₁ n₂ Vd Rd Kp w dfltT dfltM j,
      fun j _ => fixed_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd Rd Kp w
        dfltT dfltM j, hlisted, hlaid⟩
  · exact seat_own Xs Nr Pl JI JW A lift ask
  · refine planPlays_of_B _ s (t :: rest) (by rw [hp]; exact hst) 0 ?_
    rw [hfr, hp]
    exact planPlays_KW

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.tables_key
#print axioms AtPublicFiles.KeyLastChain.fixed_key
#print axioms AtPublicFiles.KeyLastChain.playsS_own
