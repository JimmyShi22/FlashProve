-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOpensAll.lean: opensAvailable at EVERY border 0 to 12 of the
key's shared thread, and DepthsAt at every border up to 12: for the ∀ form of the letter, which spends
the two premises of colsTo_congr_at at each border behind a step.

  opensR_all     BY THE KERNEL: the closed test at every border 0 to 12
  front_opens_nothing   BY THE KERNEL: members 0 to 8 open nothing: it can say no
  opens_key_all  at threadKey, through opens_key, general in its letters
  mem_declsTo_of_le, declared_le   DepthsDeclared at a border gives it at every earlier one: by the
                 definition: declsTo at n' is among declsTo at n, and nothing else is read
  depths_key_all DepthsAt at every n ≤ 12, at every k and m, table as placed

Limits. As KeyDepthsClosed.lean's head. opensAvailable is not monotone by its text, since hand grows
with the border: so each border is its own closed line. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyDepthsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

namespace AtPublicFiles.KeyOpensAll
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.AtFiles.Full (PF QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyOpens (keyR opensR srcNum opens_key)
open AtPublicFiles.KeyDepthsAt (declared_twelve)
open AtPublicFiles.KeyDepthsClosed (AQ tbPlaced t7K seven_depth members_U fresh_U members_O fresh_O)
open AtPublicFiles.KeyLay (JKU JKO)

-- What each member opens, as printed: source, depth.
#eval keyR.map fun x => (x.1.flatMap (·.opens)).map fun o => (srcNum o.2, o.1.a)

/-- **The closed test at every border 0 to 12.** By the kernel. -/
theorem opensR_all : ∀ n, n < 13 → opensR keyR n = true := by
  decide +kernel

/-- **Members 0 to 8 open nothing.** By the kernel. -/
theorem front_opens_nothing :
    ((keyR.take 9).flatMap (·.1)).all (fun d => d.opens.length == 0) = true := by
  decide +kernel

/-- Control: with member 9 in, something is opened. -/
theorem nine_opens :
    ((keyR.take 10).flatMap (·.1)).all (fun d => d.opens.length == 0) = false := by
  decide +kernel

theorem mem_declsTo_of_le {S Cl : Type} {bs : List (Block S Cl)} {n' n : ℕ} (h : n' ≤ n)
    {d : Fmt.DeclaredRound} (hd : d ∈ declsTo bs n') : d ∈ declsTo bs n := by
  unfold declsTo at hd ⊢
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.1 hd
  refine List.mem_flatMap.2 ⟨b, ?_, hdb⟩
  have e : bs.take n' = (bs.take n).take n' := by rw [List.take_take, Nat.min_eq_left h]
  rw [e] at hb
  exact List.mem_of_mem_take hb

/-- **DepthsDeclared at a border gives it at every earlier one.** -/
theorem declared_le {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb} {n' n : ℕ}
    (h : n' ≤ n) (hd : DepthsDeclared T n) : DepthsDeclared T n' :=
  fun d hdm o ho k w hh => hd d (mem_declsTo_of_le h hdm) o ho k w hh

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **opensAvailable at every border 0 to 12, at threadKey, general in its letters.** -/
theorem opens_key_all (e : parKey Xs PF = QK) {n : ℕ} (hn : n < 13) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).opensAvailable n = true :=
  (opens_key Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e n).trans (opensR_all n hn)

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
  (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
  (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand)
  (own₀ : X₀) (weights : W₀ → Weights) (rand : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w₁ : Common W₀ Rc TableKey)

include hK₀ in
/-- **DepthsAt at every border up to 12, at every k and m**, table as placed. -/
theorem depths_key_all (e : parKey Xs PF = QK) {n : ℕ} (hn : n ≤ 12) (k : Coins (keyBook K₀))
    (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbPlaced K₀ bs st wts rnd own₀ weights rand tk) rest Kp Vd
      w₁) n k m :=
  depthsAt_of_declared (declared_le hn (declared_twelve K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp
    Vd w₁ e _ _ own₀ _ rfl members_U fresh_U rfl members_O fresh_O
    (seven_depth K₀ hK₀ bs wts rnd own₀))) k m

end

end AtPublicFiles.KeyOpensAll

#print axioms AtPublicFiles.KeyOpensAll.opensR_all
#print axioms AtPublicFiles.KeyOpensAll.front_opens_nothing
#print axioms AtPublicFiles.KeyOpensAll.nine_opens
#print axioms AtPublicFiles.KeyOpensAll.mem_declsTo_of_le
#print axioms AtPublicFiles.KeyOpensAll.declared_le
#print axioms AtPublicFiles.KeyOpensAll.opens_key_all
#print axioms AtPublicFiles.KeyOpensAll.depths_key_all
