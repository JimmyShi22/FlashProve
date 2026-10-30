-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UFive.lean: the frame's five sentences (Honest/Thread/PaysS.lean) at
member 9 of a shared thread of the key file, the proximity test on G_u: `PlaysS`, `BehindS`, `ExchangeS`,
`RidesPastS`, `AcceptedS`, at one thread (`TU`, E2E/TableFilled.lean; what is fixed in it: UAccepted.lean's
head), at any second condition `Said` and any falls.

  `front_nine_at_key`   the first nine members are the front block and the eight
  `facts_behind_at_key`   where the invariant holds at border 9 the state has the facts behind the eight
                     (`Behind`, K12/PubAtDoor.lean)
  `masks_at_key`, `codes_lengths_at_key`, `zip_at_key`   closed lines, by the kernel
  `five_at_key`      the statement
  `five_of_invariant_at_key`   the same five from the invariant alone

Two premises on the thread's letters.
  hKp: Kp at member 9 says that the test on G_u said yes (`keepsU`, K12/AtFile/FiveAtNine.lean): the rows that
  ride past the member are carried by that yes alone.
  htt: the table's letter at the trees 3 to 6 is the test's own (`testTbl`): `PlaysS` alone spends it.

What `BehindS` says here. This thread's letters `shape` off the borders 2 to 9, `nothingLeft` and `rides` say yes
everywhere: so behind member 9 it is: the statement is in order, and the test on G_u said yes.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: all five have the thread's pair as a premise.
- That the invariant holds at border 9 at any run is not said here: UStep.lean.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UAccepted
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FieldsAtU
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveAtNine
import Johnson.Desc.ProofFile.Honest.K12.PubAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (behind_fold)
open ProofFile.Honest.K12.AtFile (keepsU keeps_of_step stand_at_nine behindS_nine exchangeS_nine ridesPastS_nine)
open OnBytes (TableKey)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Claim keyAsProof sharedTests)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey lettersKey parKey sentKey randKey)
open _root_.Desc.K14 (St frontBlock)
open _root_.Desc.K14.Honest (Eight Like flatOf_carried)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyDoorNine (seat_nine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.HalvesAreJobs (pU pO find_U)
open AtPublicFiles.TableFilled (TU)
open AtPublicFiles.PlaysAtNine (plays_at_nine)
open H2K.Member (piKUFull)

/-- The masks go ahead, at the written key's shape. By the kernel. -/
theorem masks_at_key : QK.S.masksAhead = true := by decide +kernel

/-- The codes' lengths fit, at the written key's codes. By the kernel. -/
theorem codes_lengths_at_key : QK.codes.lengthsOk = true := by decide +kernel

/-- The test's rounds with their messages are as many as its two parts' moves. By the kernel. -/
theorem zip_at_key : ((proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds.zip
    (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).oracles).length =
      firstLen piKUFull.nums.stages + restLen piKUFull.nums.stages := by decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- The first nine members are the front block and the eight. -/
theorem front_nine_at_key (B : Eight (parKey Xs PF)) :
    List.Forall₂ Like ((threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs.take 9)
      [frontBlock (keyAsProof Xs.chains), B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs PF) B.b1 B.b2 B.b3 B.b4 B.b5
      B.b6 B.b7 B.b8 (sharedTests PF) VerifiableInference.Desc.K12.Seat.last B.made
  have hbs : (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := hxs
  rw [hbs]
  exact .cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
    (.cons l8 .nil))))))))

/-- **At a stand at 9 the state has the facts behind the eight.** -/
theorem facts_behind_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (B : Eight (parKey Xs PF)) {k : Coins Bk} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) :
    ProofFile.Honest.K12.Light.Behind (parKey Xs PF) (sentKey Xs PF) s := by
  obtain ⟨⟨vr, vo, rest', more, hf8⟩, -, -⟩ := stand_at_nine
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w) (keyAsProof Xs.chains) (parKey Xs PF)
    (sentKey Xs PF) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
    (front_nine_at_key Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w B) rfl rfl rfl (fun _ _ _ _ h => h)
    (keyProver K).storedWords (fun _ => rfl) u
  exact behind_fold (parKey Xs PF) _ B.made hQ.facts.two (by rw [e]; exact masks_at_key)
    (sentKey Xs PF) hQ.facts.goes _ vr vo (s, rest', more) hf8

end

variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ in
/-- **The five sentences at member 9 of a shared thread of the key file.** -/
theorem five_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (hKp : ∀ s s', Kp 9 s s' ↔ keepsU pU s s') (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9 ∧
      BehindS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9 ∧
      ExchangeS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9 ∧
      RidesPastS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9 ∧
      AcceptedS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said fall 9 := by
  have hseat := (seat_nine Xs Nr PF K₁ ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).2
  have hblk := (seat_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).1
  have hp : (JN Xs K₁ B).p = piKUFull := place_full
  have hok : (proximityTestKind guardedProximityTestParts (JN Xs K₁ B).p : Block T12 Unit).planOk = true := by
    rw [hp]
    exact H2K.Pub.piKUFull_planOk
  have he : (JN Xs K₁ B).p.early = true := H2K.JointK.early_of_planOk _ hok
  have ha : (JN Xs K₁ B).p.answers = 1 := H2K.JointK.answers_of_planOk _ hok
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, (JN Xs K₁ B).p.nums.stages = a :: b :: r := by
    have h2 : 2 ≤ (JN Xs K₁ B).p.nums.stages.length := by
      rw [hp]
      exact AtPublicFiles.KeyPlaysAt.stages_two
    cases hh : (JN Xs K₁ B).p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a t =>
      cases t with
      | nil =>
        rw [hh] at h2
        simp only [List.length_cons, List.length_nil] at h2
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hhalf : ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hs.find? fun g =>
      g.place == (H2K.JointK.keyGu PF).place) = some (proverSideOfProximityTest (JN Xs K₁ B)) :=
    find_U Xs K₁ B hs hsp
  have hrs : ((H2K.JointK.keyGu PF).rounds.zip (H2K.JointK.keyGu PF).oracles).length =
      firstLen (JN Xs K₁ B).p.nums.stages + restLen (JN Xs K₁ B).p.nums.stages := by
    rw [hseat.rounds, hseat.oracles, hp]
    exact zip_at_key
  have hB9 : ∀ k s m E, Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E →
      ProofFile.Honest.K12.Light.Behind (parKey Xs PF) (sentKey Xs PF) s := fun _ _ _ _ u =>
    facts_behind_at_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ _ rest Kp Vd w e hQ B u
  have hsz : (sentKey Xs PF ++ _root_.Desc.K14.withOmega (parKey Xs PF).S).size = 4 := by
    have h2 : (_root_.Desc.K14.withOmega (parKey Xs PF).S).size = 2 :=
      (_root_.Desc.K14.Honest.withOmega_two hQ.facts.two).1
    rw [Array.size_append, hQ.facts.goesTwo, h2]
  have hkeep : ∀ s s', (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).keeps 9 s s' ↔
      keepsU pU s s' := fun s s' => by
    show keepsAll (parKey Xs PF) (sentKey Xs PF) Kp 9 s s' ↔ _
    unfold keepsAll
    rw [if_neg (by omega)]
    exact hKp s s'
  refine ⟨playsS_of _ Said (plays_at_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest Kp Vd w e B
      hs hsp own₀ htt),
    ?_, ?_, ?_,
    acceptedS_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ hs hsp Said fall⟩
  · exact behindS_nine (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w)
      (parKey Xs PF) Said rfl hblk (JN Xs K₁ B) hseat (fun _ _ => true) rfl (fun _ _ _ _ _ _ _ _ _ _ => rfl)
      (fun _ => Iff.rfl) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ s _ _ _ _ _ s' _ hSt => (hkeep s s').2 (keeps_of_step hseat hSt.2))
      (fun k s m E u => by
        rw [(hB9 k s m E u).mid.codes, e]
        exact codes_lengths_at_key)
  · exact exchangeS_nine (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w)
      (parKey Xs PF) (sentKey Xs PF) Said ℓ Mg₀ rfl rfl hblk (JN Xs K₁ B) hseat hhalf st0 st1 st2 hst
      hrs he ha hB9 hsz (fun _ h => h)
  · exact ridesPastS_nine (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w)
      (parKey Xs PF) (sentKey Xs PF) Said pU ℓ Mg₀ rfl rfl he ha (fun _ s _ _ s' _ h => (hkeep s s').1 h) hB9
      hsz (fun _ h => h)

include hK₀ in
/-- **The same five from the invariant alone** (Honest/Thread/Pays.lean): no second condition is spent. -/
theorem five_of_invariant_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (hKp : ∀ s s', Kp 9 s s' ↔ keepsU pU s s') (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    Plays (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 ∧
      ProofFile.Honest.Behind (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 ∧
      Exchange (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 ∧
      RidesPast (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 ∧
      Accepted (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) fall 9 := by
  obtain ⟨hP, hB, hX, hR, hA⟩ := five_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ hs hsp hKp
    own₀ htt (fun _ _ _ => True) fall
  exact ⟨fun blk hb k s m E ds l u => hP blk hb k s m E ds l ⟨u, trivial⟩,
    fun blk hb k s m E ds y cols s' u => hB blk hb k s m E ds y cols s' ⟨u, trivial⟩,
    fun blk hb k s m E ds y cols s' u => hX blk hb k s m E ds y cols s' ⟨u, trivial⟩,
    fun k s m E s' ps i v u => hR k s m E s' ps i v ⟨u, trivial⟩,
    fun blk hb k s m E ds y cols u => hA blk hb k s m E ds y cols ⟨u, trivial⟩⟩

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.masks_at_key
#print axioms ProofFile.Honest.K12.AtKey.codes_lengths_at_key
#print axioms ProofFile.Honest.K12.AtKey.zip_at_key
#print axioms ProofFile.Honest.K12.AtKey.front_nine_at_key
#print axioms ProofFile.Honest.K12.AtKey.facts_behind_at_key
#print axioms ProofFile.Honest.K12.AtKey.five_at_key
#print axioms ProofFile.Honest.K12.AtKey.five_of_invariant_at_key
