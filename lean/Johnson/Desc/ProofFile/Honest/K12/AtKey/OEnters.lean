-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OEnters.lean: at a stand of the key's shared thread at border 10, whose field
holds the columns that the fold read, the seat's way in is the job's state on entry.

  `front_at_ten`       the first ten members are like the front block, the eight and the test on G_u
  `enters_at_ten_key`  the statement

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `enters_at_ten_key` bears this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the
  thread from Thr as a premise.
- The field is a premise: which letter gives it is not said here.
- It does not say that the state differs from the door's fall-back.
- That a stand at 10 is reached is not said.
- Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyDoorNine
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (frontOf)
open ProofFile.Honest.K12.Light (doorOmegaF colsOpened door_of_opened)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block foldBlocks)
open VerifiableInference.Desc.K12 (Seat.enter proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedTests keyAsProof)
open _root_.Desc.K14 (St first frontBlock)
open _root_.Desc.K14.Honest (Eight Like flatOf_carried)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey threadKey)
open AtPublicFiles.KeyDoorNine (seat_nine)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The first ten members are like the front block, the eight and the test on G_u.** -/
theorem front_at_ten (B : Eight (parKey Xs Pl)) :
    List.Forall₂ Like ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs.take 10)
      (frontBlock (keyAsProof Xs.chains) :: ([B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] ++
        [VerifiableInference.Desc.K12.Seat.onGu
          (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U))])) := by
  have F := flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs Pl) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last B.made
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have hbs : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := hxs
  have h9 := (seat_nine (X₀ := X₀) Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w B).1
  rw [hbs] at h9 ⊢
  cases tl with
  | nil =>
    cases h9
  | cons x9 tl =>
    have e9 : x9 = H2K.JointK.keyGu Pl := Option.some.inj h9
    subst e9
    exact .cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 (.cons ⟨rfl, rfl, rfl, rfl⟩ .nil)))))))))

/-- **At a stand at border 10, whose field holds the columns that the fold read, the seat's way in is the
job's state on entry.** -/
theorem enters_at_ten_key (B : Eight (parKey Xs Pl)) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 10 k s m E)
    (hfield : ∀ cols, (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).colsTo 10 m E = .ok cols →
      m.opened = some cols) :
    Seat.enter (·.gOmega) (fun _ => none) s =
      .ok (doorOmegaF (parKey Xs Pl) (sentKey Xs Pl) [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U) (fun v => v.key) colsOpened m.st.input (frontOf m)) := by
  obtain ⟨-, -, -, -, made, -, -⟩ := u
  obtain ⟨-, -, -, -, s₀, cols, hbeg, hcols, hfold⟩ := made
  have e₀ : s₀ = first (parKey Xs Pl).codes m.st.input.key := hbeg
  subst e₀
  exact door_of_opened (keyAsProof Xs.chains) (parKey Xs Pl) (sentKey Xs Pl)
    [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U)
    ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs.take 10)
    (front_at_ten Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w B) m.st.input.key m.seen cols s hfold
    (fun v => v.key) m.st.input (frontOf m) rfl rfl (hfield cols hcols)

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.front_at_ten
#print axioms ProofFile.Honest.K12.AtKey.enters_at_ten_key
