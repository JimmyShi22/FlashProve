-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TableFilled.lean: THE TABLE AS PLACED, AS A CALL: tbKey's letter
tt filled with the three arms at the two jobs of the key's chain, ok the constant yes, so that the arms
stand no more as premises at members 9 and 10.

  ttF            tt: ttPlaced (KeyDepthsAt.lean) at JN and JO, with own 7 := ownTbl
  TF             the thread at that table, at the parts with the two halves
  arm_U, arm_7, arm_O   the three arms, by unfolding
  JN_is_JKU, JO_is_JKO   JN and JO are JKU, JKO at ⟨QK, 0⟩ under e: what trial (e) was told at is this
  plays_filled   Plays at 9 at that thread
  trees_ten_filled   hT at 10 at that thread, to the sign; plays_ten_filled   PlaysS at 10, under hop
  TU             the thread at the two halves and the parts' own readers, tt free
  TR, plays_real, trees_ten_real, plays_ten_hop_real, plays_ten_thr_real, depths_real   the same at the
                 parts' own readers; at 10 with the older hop, and with hop from the pair
  depths_filled, opens_filled   DepthsAt at every n ≤ 12, opensAvailable at every n < 13 at that thread

PREMISES. hK₀: full_made. e, B: par_sourced, plan_key. hs, hsp: as HalvesAreJobs.lean. own₀: any value.
Plays at 10 stands bare nowhere; PlaysS asks hop of its letter.

WHAT IT IS: a filling by call: one letter fewer: tbKey (E2E/KeyTreesKey.lean) stands as it does. ownTbl carries (0-1) to (0-3) (K12/OwnTbl.lean's head).
NOT IN FRONT OF A LAW OVER COINS: the laws called bear that label.

A YES WOULD NOT SHOW: that Thr stands at 9 or 10 at this thread · that the field is some · that Moved is had
at 10 · that the laws at free wts, rnd mean anything but at TR · anything at the sendings but what their tables are · anything over coins, and nothing on hiding.
Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.PlaysAtLetters
import E2E.TreesAtTenKey
import E2E.KeyOpensAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.TableFilled
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey randKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (JKU JKO jobKU jobKO withTestsOnUAndOmega wtOf rdOf)
open AtPublicFiles.KeyPlaysAt (memsOf members_closed fresh_closed)
open AtPublicFiles.KeyDepthsAt (ttPlaced declared_twelve)
open AtPublicFiles.KeyDepthsClosed (AQ)
open AtPublicFiles.KeyOpensAll (declared_le opens_key_all)
open AtPublicFiles.PlaysAtNine (plays_at_nine plays_at_ten plays_at_ten_thr)
open AtPublicFiles.TreesAtNine (JN TN)
open AtPublicFiles.TreesAtTenKey (trees_ten_sign)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO)
open H2K.Member (piKUFull piKOFull)
open H2K.JointK (keyOmega)

/-- The members of the test on G_omega, at a value. -/
def memsOQ (Q : _root_.Desc.K14.P14) : List (Addr × Nat × Due) :=
  [(⟨sendPlace 5, 0⟩, 0, ⟨0, dueOf (K14.jobOmega ⟨Q, 0⟩).Q.codes
      ((K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape ((K14.jobOmega ⟨Q, 0⟩).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, dueOf (K14.jobOmega ⟨Q, 0⟩).Q.codes
      ((K14.jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape ((K14.jobOmega ⟨Q, 0⟩).sort 1)⟩)]

theorem memsOQ_closed : memsOQ QK = AtPublicFiles.KeyTest.jobOmega.members := by
  decide +kernel

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- **The letter, filled.** -/
abbrev ttF : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table :=
  ttPlaced K₀ (JN Xs K₁ B) (JO Xs K₁ B) own₀
    (ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))

/-- **The thread at that table.** -/
abbrev TF :=
  TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w

theorem arm_U {τ : ℕ} (hτ : τ < 4) : ttF K₀ Xs K₁ B own₀ (3 + τ) =
    testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ := by
  show (if 3 + τ < 7 then testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) (3 + τ - 3) else _) = _
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem arm_7 : ttF K₀ Xs K₁ B own₀ 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) := by
  show (if 7 < 7 then _ else if 7 = 7 then ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true)
    else _) = _
  rw [if_neg (by omega), if_pos rfl]

theorem arm_O {τ : ℕ} (hτ : τ < 3) : ttF K₀ Xs K₁ B own₀ (8 + τ) =
    testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ := by
  show (if 8 + τ < 7 then _ else if 8 + τ = 7 then _
    else testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) (8 + τ - 8)) = _
  rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **JN is JKU at ⟨QK, 0⟩, under e.** -/
theorem JN_is_JKU (e : parKey Xs PF = QK) : JN Xs K₁ B =
    JKU (X := X₀) AQ [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (keyProver K₁).storedWords
      (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc) := by
  have hA : (⟨parKey Xs PF, 0⟩ : SendPub) = AQ := by rw [e]
  have hP : pU = piKUFull := place_full
  show (jobKU (X := X₀) ⟨parKey Xs PF, 0⟩ pU [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
    (keyProver K₁).storedWords (fun c => K₁.weights c.w₀)
    (fun c => randKey K₁ c.rc)).toRun.toTest = _
  rw [hA, hP]

/-- **JO is JKO at ⟨QK, 0⟩, under e.** -/
theorem JO_is_JKO (e : parKey Xs PF = QK) : JO Xs K₁ B =
    JKO (X := X₀) AQ [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (wtOf K₁) (rdOf K₁) := by
  have hA : (⟨parKey Xs PF, 0⟩ : SendPub) = AQ := by rw [e]
  have hP : pU = piKUFull := place_full
  show (jobKO (X := X₀) ⟨parKey Xs PF, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
    (wtOf K₁) (rdOf K₁)).toRun.toTest = _
  rw [hA, hP, pO_full]

include hK₀ in
/-- **Plays at 9 at the filled thread: no arm is a premise.** -/
theorem plays_filled (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    Plays (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀) 9 :=
  plays_at_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w e B hs hsp own₀
    fun _ hτ => arm_U K₀ Xs K₁ B own₀ hτ

/-- **hT at 10 at the filled thread: no arm is a premise, and no field.** -/
theorem trees_ten_filled (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ∀ k s m E ds y cols,
      Thr (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀) 10 k s m E →
      drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds = true →
      (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀).Moved
        (keyOmega (PF.O.getD PF.U)) k m E ds y cols →
      (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀).Trees
        ((TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀).fresh 10) k y.2 (E.add y.1) :=
  trees_ten_sign Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w e B hs hsp own₀
    (arm_7 K₀ Xs K₁ B own₀) fun _ hτ => arm_O K₀ Xs K₁ B own₀ hτ

include hK₀ in
/-- **PlaysS at 10 at the filled thread, at any letter that holds the field: no arm is a premise.** -/
theorem plays_ten_filled (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k m, Said 10 k m → m.opened.isSome = true) :
    PlaysS (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀) Said 10 :=
  plays_at_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w e B hs hsp own₀
    (arm_7 K₀ Xs K₁ B own₀) (fun _ hτ => arm_O K₀ Xs K₁ B own₀ hτ) Said hop

/-- opensAvailable at every border, at the filled thread. -/
theorem opens_filled (e : parKey Xs PF = QK) {n : ℕ} (hn : n < 13) :
    (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀).opensAvailable n = true :=
  opens_key_all Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ _ rest Kp Vd w e hn

include hK₀ in
/-- **DepthsAt at every border up to 12, at the filled thread.** -/
theorem depths_filled (e : parKey Xs PF = QK) {n : ℕ} (hn : n ≤ 12) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (TF K₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk rest Kp Vd w B own₀) n k m := by
  have hq : ∀ t, tbKey (parKey Xs PF) wts rnd tk t = tbKey QK wts rnd tk t := fun t => by rw [e]
  have hpO : (JO Xs K₁ B).p = piKOFull := pO_full
  have hmU : (JN Xs K₁ B).members = AtPublicFiles.KeyTest.jobFolded.members := by
    show memsOf (parKey Xs PF) = _
    rw [e]
    exact members_closed
  have hmO : (JO Xs K₁ B).members = AtPublicFiles.KeyTest.jobOmega.members := by
    show memsOQ (parKey Xs PF) = _
    rw [e]
    exact memsOQ_closed
  have h7 : ∀ (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn),
      (ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) k w h).2.logLength = 13 :=
    ownTbl_depth (JO Xs K₁ B) rfl 1 (Or.inr rfl)
      (AtPublicFiles.KeyDepthsAt.lays_O_at K₀ hK₀ (JO Xs K₁ B) hpO hmO AtPublicFiles.KeyDepthsClosed.fresh_words.2.symm)
      own₀ 43 (AtPublicFiles.KeyLay.own_O (JO Xs K₁ B) hpO rfl)
  show DepthsAt (threadKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) wts rnd tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w) n k m
  rw [hq]
  exact depthsAt_of_declared (declared_le hn (declared_twelve K₀ hK₀ wts rnd tk Xs Nr
    (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ rest Kp Vd w e _ _ own₀ _ place_full hmU fresh_closed.symm hpO hmO
    AtPublicFiles.KeyDepthsClosed.fresh_words.2.symm h7)) k m

end

/-! ## At the parts' own readers -/

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- The thread at the two halves and at the parts' own readers, the table's letter for the tests' own
trees free. -/
abbrev TU (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table) :=
  TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ K₁.weights (randKey K₁) tk tt rest Kp Vd w

/-- **THE THREAD AT THE REAL HALVES**: the filled thread at the parts' own readers: wts := K₁.weights,
rnd := randKey K₁, as tableKey lays them. Where they differ Hand at own 0 to 2 asks tables that the
sendings do not send: so it is here that the laws above have their meaning. -/
abbrev TR :=
  TF K₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀

include hK₀ in
theorem plays_real (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    Plays (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 9 :=
  plays_filled K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e hs hsp

theorem trees_ten_real (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ∀ k s m E ds y cols,
      Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E →
      drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds = true →
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).Moved
        (keyOmega (PF.O.getD PF.U)) k m E ds y cols →
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).Trees
        ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fresh 10) k y.2 (E.add y.1) :=
  trees_ten_filled K₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e hs hsp

include hK₀ in
theorem plays_ten_hop_real (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k m, Said 10 k m → m.opened.isSome = true) :
    PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 :=
  plays_ten_filled K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e hs hsp
    Said hop

include hK₀ in
/-- **PlaysS at 10 at the real thread, with hop from the pair: the form that a letter ∀ E, Hand → Field pays.** -/
theorem plays_ten_thr_real (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      m.opened.isSome = true) :
    PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 :=
  plays_at_ten_thr K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w K₁.weights (randKey K₁) e B
    hs hsp own₀ (arm_7 K₀ Xs K₁ B own₀) (fun _ hτ => arm_O K₀ Xs K₁ B own₀ hτ) Said hop

include hK₀ in
theorem depths_real (e : parKey Xs PF = QK) {n : ℕ} (hn : n ≤ 12) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) n k m :=
  depths_filled K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk rest Kp Vd w B own₀ e hn k m

end

end AtPublicFiles.TableFilled

end

#print axioms AtPublicFiles.TableFilled.memsOQ
#print axioms AtPublicFiles.TableFilled.memsOQ_closed
#print axioms AtPublicFiles.TableFilled.ttF
#print axioms AtPublicFiles.TableFilled.TF
#print axioms AtPublicFiles.TableFilled.arm_U
#print axioms AtPublicFiles.TableFilled.arm_7
#print axioms AtPublicFiles.TableFilled.arm_O
#print axioms AtPublicFiles.TableFilled.JN_is_JKU
#print axioms AtPublicFiles.TableFilled.JO_is_JKO
#print axioms AtPublicFiles.TableFilled.plays_filled
#print axioms AtPublicFiles.TableFilled.trees_ten_filled
#print axioms AtPublicFiles.TableFilled.opens_filled
#print axioms AtPublicFiles.TableFilled.depths_filled
#print axioms AtPublicFiles.TableFilled.plays_ten_filled
#print axioms AtPublicFiles.TableFilled.TR
#print axioms AtPublicFiles.TableFilled.plays_real
#print axioms AtPublicFiles.TableFilled.trees_ten_real
#print axioms AtPublicFiles.TableFilled.plays_ten_hop_real
#print axioms AtPublicFiles.TableFilled.plays_ten_thr_real
#print axioms AtPublicFiles.TableFilled.depths_real
