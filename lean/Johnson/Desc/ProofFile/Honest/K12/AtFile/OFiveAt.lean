-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OFiveAt.lean: `five_at_ten` (OAtTen.lean) at the thread `lettersShared`
(Honest/Thread/SharedHead.lean) at a prover H: each premise on the list, the seat, the trees and the book paid,
those on the letters named; and the half at the base filling.

  `sent_one`, `front_ten`, `front_ten_bent`   closed lines: own 1's round; 43 rounds in front of member 10
  `LetterO`      what the five sentences ask of the letters of `lettersShared`
  `fixedO_at`, `lettersTen_plain`, `standO_at`   `FixedO`, `LettersTen` where the letters say no more, `StandO` at that thread
  `five_at_letters`   the five sentences at member 10 of that thread
  `half_found_O`, `half_at_fill`   at the filling's shared list; at the prover that the maker returns at `onlineProverPartsInUse` the search at the test's place finds
                 the job's half behind the guard

The letters (`LetterO`). Any `lettersShared` whose meaning is `mgWords`, whose witness reads as `witAll` at `holds2`, whose
tables and counts are `tableShared` and `fixedShared`; beside them `LettersTen` (OStep.lean), at a stand and behind the
step. All other places of `Kp` are free, so the one term of the shared thread can lay at the test on G_u what that test
asks.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the pair stands behind all five sentences.
- At the prover H, W₀ and Rc letters: the half is a premise of `five_at_letters`; `half_at_fill` pays it at the base
  filling, at IndexCommitterCoins, where `wts` is the input's reader of the index and `rnd` is `randAt`.
- The field is a premise: the letter `Said`'s.
- Nothing here says that a stand is reached. Nothing on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OAtTen
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OSeat
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.BookLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.StandNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K14.NoStray
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import AtFullSide.K12.ReturnsAtFillW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open OnBytes.Means (InOrder Words)
open VerifiableInference.Desc (Block Place Alike₂ Grows Chain)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS sharedPlaces)
open Desc.K14 (St blocks frontBlock first p14Of beforePointOf)
open Desc.K14.Honest (Like FlatOf flatOf_carried)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendingPart mgWords WitLens holds2 witAll form2 place)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (sentOf)
open ProofFile.Honest.K12.AtProof (fourOf placeO placeU halfO sharedWithUO randAt)
open ProofFile.Honest.SharedThread (Letters lettersShared)
open P2Law.ProofPlan (WP declProofFull)
open Johnson.G (proofSendsFull)

/-- Own 1 goes out in round 4. -/
theorem sent_one : ProofFile.Honest.Small.sentIn declProofFull.2.1 1 = 4 := by decide +kernel

/-- 43 rounds stand in front of member 10. -/
theorem front_ten : ((sharedR.take 10).flatMap (·.1)).length = 43 := by decide +kernel

/-- Control: not 8. -/
theorem front_ten_bent : ((sharedR.take 10).flatMap (·.1)).length ≠ 8 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} {Bk : ProverCoinCounts}

section
variable (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X) (N : NumbersS)
  (Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (shape : ℕ → St → Bool) (nothingLeft : St → Bool)
  (order : St → Prop) (wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (n₁ n₂ : ℕ) (Vd : Common W₀ Rc TableKey → Prop)
  (Rd : ℕ → Common W₀ Rc TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc TableKey)

/-- The thread's letters. -/
local notation "𝐋" => lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w

/-- **What the five sentences ask of the letters.** -/
structure LetterO (Zp : ProofFile.Pub) (Np : H2U.Places4) (pO : P12) (bs : List (Block St Unit))
    (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (wts : W₀ → Weights)
    (rnd : Rc → TableRand) (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀) : Prop where
  meaning : Mg = fun v => mgWords ℓ (K1.qAt Zp Np) N (Mg₀ v)
  witness : ∀ k v hd, ℓ.get (wit k v hd) = witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
    (holds2 (K1.qAt Zp Np) wts rnd) rest k v hd
  table : table = tableShared (K1.qAt Zp Np) wts rnd JU
    (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest own₀
  fixed : fixed = fixedShared declProofFull.2.1

variable {H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w}
  {bs : List (Block St Unit)} {ℓ : WitLens Wt} {Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
  {wts : W₀ → Weights} {rnd : Rc → TableRand}
  {rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E}
  {JU : TestJob (Common W₀ Rc TableKey) X₀} {own₀ : X₀}

/-- **The thread's counts.** -/
theorem fixedO_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (G : LetterO N Mg wit table fixed Zp Np pO bs ℓ Mg₀
      wts rnd rest JU own₀) : FixedO (𝐋).thread := by
  refine ⟨G.fixed, rfl, ?_⟩
  have hl := ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid
  show roundsTo (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 10 = 43
  unfold roundsTo
  rw [decls_rounds, ← rounds_alike hl]
  exact front_ten

/-- **`LettersTen` where the letters say no more of a state than a step gives**: form and rider yes at 11 at every
state, `Kp` at the test's place the relation itself. -/
theorem lettersTen_plain (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hf : ∀ s, shape 11 s = true) (ho : ∀ s, order s ↔ OnBytes.Means.InOrder s.st) (hr : ∀ v s, Rd 11 v s)
    (hk : ∀ s s', Kp ⟨2, none, 10, .K12⟩ s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st) :
    LettersTen (𝐋) Said := by
  have e : (sharedPlaces true)[10]? = some ⟨2, none, 10, .K12⟩ := rfl
  refine ⟨rfl, ho, fun _ _ _ _ _ _ _ _ _ s' _ _ => hf s', fun _ _ _ _ _ _ _ y _ s' _ _ => hr _ s',
    fun _ _ _ s _ _ _ _ _ s' _ _ g₁ g₂ p hp => ?_, fun _ s _ _ s' _ g => (hk s s').1 (g _ e)⟩
  obtain rfl := Option.some.inj (e.symm.trans hp)
  exact (hk s s').2 ⟨g₁, g₂⟩

/-- **`StandO` at the thread of these letters**, at the prover H: the member is there. -/
theorem standO_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (G : LetterO N Mg wit table fixed Zp Np pO
      [b1, b2, b3, b4, b5, b6, b7, b8] ℓ Mg₀ wts rnd rest JU own₀)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hhalf : (H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest :
        Placed Empty _ X₀).needsField)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hfield : ∀ k s m E, ThrS (𝐋).thread Said 10 k s m E → ∀ cols,
      (𝐋).thread.colsTo 10 m E = .ok cols → m.opened = some cols) :
    ∃ blk, StandO Zp Np pO (𝐋).thread Said wts rnd JU own₀ Zp.p.chains
      [b1, b2, b3, b4, b5, b6, b7, b8] blk := by
  obtain ⟨nO, h1, rfl⟩ := ProofFile.Honest.K12.Light.omega_of_four hO
  have TL := ProofFile.Honest.K14.tailLike_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
    n₂ Vd Rd Kp w b1 b2 b3 b4 b5 b6 b7 b8 nO h1 hb
  obtain ⟨x, hx, hlike⟩ := TL.ten
  obtain ⟨x9, hx9, hlike9⟩ := TL.nine
  have hS : SeatOf x
      (jobDoorO (X₀ := X₀) Zp Np (H2K.JointK.pGomega nO) [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := seat_of_like_O hlike
  have hl := ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid
  have F : FlatOf (𝐋).thread.bs Zp.p.chains b1 b2 b3 b4 b5 b6 b7 b8 := by
    show FlatOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder _ _ _ _ _ _ _ _ _
    rw [ProofFile.Honest.K14.shared_flat_at]
    exact flatOf_carried Zp.p.chains _ b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have hfront : List.Forall₂ Like ((𝐋).thread.bs.take 10) (frontBlock Zp.p.chains ::
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++
        [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)])) := by
    obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, tl, e, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
    rw [e] at hx9 ⊢
    cases tl with
    | nil => cases hx9
    | cons z tl' =>
      obtain rfl : z = x9 := Option.some.inj hx9
      exact .cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 (.cons l8
        (.cons hlike9 .nil)))))))))
  refine ⟨x, { member := hx, seat := hS, half := ?_, front := hfront, ahead := rfl, chain := rfl, ft := rfl
               begun := fun _ _ _ _ e => e, trees := ?_, taken := rfl, table := G.table
               fixedOne := ?_, oneU := treesU_head h.toAtMg, cover := c5, field := hfield }⟩
  · rw [hS.place]
    exact hhalf
  · show treesTo (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 10 = 7
    rw [trees_rounds, ← rounds_alike hl]
    exact trees_nine_bent
  · show 1 ≤ fixed (.own 1)
    rw [G.fixed]
    show 1 ≤ ProofFile.Honest.Small.sentIn declProofFull.2.1 1
    rw [sent_one]
    omega

set_option maxHeartbeats 1000000 in
/-- **The five sentences at member 10 of the thread of these letters.** -/
theorem five_at_letters (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hO : (fourOf Np).O = some pO)
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (G : LetterO N Mg wit table fixed Zp Np pO
      [b1, b2, b3, b4, b5, b6, b7, b8] ℓ Mg₀ wts rnd rest JU own₀)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop) (K : LettersTen (𝐋) Said)
    (hhalf : (H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest :
        Placed Empty _ X₀).needsField)
    (hfield : ∀ k s m E, ThrS (𝐋).thread Said 10 k s m E → ∀ cols,
      (𝐋).thread.colsTo 10 m E = .ok cols → m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (𝐋).thread Said 10 ∧ BehindS (𝐋).thread Said 10 ∧ ExchangeS (𝐋).thread Said 10 ∧
      RidesPastS (𝐋).thread Said 10 ∧ AcceptedS (𝐋).thread Said fall 10 := by
  obtain ⟨B₀, h₀, -⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  have eB : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ h.scope h.laid).symm.trans hB)
  rw [eB] at h₀
  obtain ⟨c2, c5, -, n5⟩ := covers_head h.toAtMg h₀
  obtain ⟨blk, H'⟩ := standO_at h hO b1 b2 b3 b4 b5 b6 b7 b8 hb G Said hhalf c5 hfield
  have hfirst : ∀ key, (𝐋).first key = first (K1.qAt Zp Np).codes key := fun _ => rfl
  have H₀ := five_at_ten h.toAtMg hO h hB (𝐋) ℓ Mg₀ (ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid)
    G.meaning Said wts rnd rest G.witness hfirst JU own₀ Zp.p.chains _ hb H' (fixedO_at h G)
    K c2 n5 fall
  exact H₀

end

/-- **The shared list of the base filling finds the job's half at the test's place, behind the guard.** The job is
at the input's reader of the index and at `randAt`. -/
theorem half_found_O (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (I : WiderIn W₀) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ((sharedWithUO I Zp).find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := Unit) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp)
                         (randAt (K1.qAt Zp Np))).toRun.toTest : Placed Empty _ Unit).needsField := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)
  have hp : pO.place = placeO := place_of_four hO
  rw [ProofFile.Honest.K12.AtProof.sharedWithUO_ok I h6, ProofFile.Honest.sharedWithU_ok I h6,
    ProofFile.Honest.K12.AtProof.halfO_at_head h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb _ hO]
  refine find_half _ _ [] pO.place rfl fun x hx => ?_
  rw [hp]
  rcases List.mem_append.1 hx with hx | hx
  · have q := ProofFile.Honest.K14.six_places _ _ _ _ x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at q
    rcases q with e | e | e | e | e | e | e | e <;> (rw [e]; decide)
  · rw [AtFullSide.K12.halfU_place _ _ Zp x hx]
    decide

/-- **At the prover that the maker returns at the base filling the search at the test's place finds the job's
half, behind the guard.** -/
theorem half_at_fill {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (A.H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := Unit) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp)
                         (randAt (K1.qAt Zp Np))).toRun.toTest : Placed Empty _ Unit).needsField := by
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, e2, -⟩ := atPure_ok hA
  have es : A.H.shared = sharedWithUO I Zp := by
    rw [e2, hZ] <;> rfl
  rw [es]
  exact half_found_O h hO I b1 b2 b3 b4 b5 b6 b7 b8 hb

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.sent_one
#print axioms ProofFile.Honest.K12.AtFile.front_ten
#print axioms ProofFile.Honest.K12.AtFile.front_ten_bent
#print axioms ProofFile.Honest.K12.AtFile.LetterO
#print axioms ProofFile.Honest.K12.AtFile.fixedO_at
#print axioms ProofFile.Honest.K12.AtFile.lettersTen_plain
#print axioms ProofFile.Honest.K12.AtFile.standO_at
#print axioms ProofFile.Honest.K12.AtFile.five_at_letters
#print axioms ProofFile.Honest.K12.AtFile.half_found_O
#print axioms ProofFile.Honest.K12.AtFile.half_at_fill
