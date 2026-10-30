-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOpensLaw.lean

`Thread.opensAvailable` AT THE KEY's SHARED THREAD IS THE CLOSED TEST, at every border, general in the
thread's letters: table, Kp, Vd, the witness and the rest. So at borders 10, 11, 12 it is true.

  `decls_ro`, `trees_ro`   what the test reads of a list of blocks is read off `ro`
  `opensAvailable_eq`   at a thread with no tree taken over, the test is `opensR` at the list
  `pre_ro`, `flat_ro`   the shared chain's list at the written places, by `ro`, is `keyR`
  `opens_key`, `opens_key_ten`, `opens_key_eleven`, `opens_key_twelve`   at `threadKey`

Premises. e: the linear claim's parameters at the key are `QK`: in the goals' scope `par_sourced`. The
places are `PF`: `later_sourced`. Nothing else: no coin, no state, no letter of the thread's.

Limits. It answers `opensAvailable` alone: L2 asks `DepthsAt` too. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.KeyOpensKernel
import E2E.KeySharedThread
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyOpens
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Claim sharedChain sharedPar beforeSharedPoint)
open _root_.Desc.K14 (St blocksOr)
open AtPublicFiles.AtFiles.Full (PF QK omega_full)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey sits_two)
open H2K.JointK (keyGu keyOmega keySharedPre keySharedEnd keyShared_cut_omega)

theorem decls_ro {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    declsTo bs n = ((bs.map ro).take n).flatMap (·.1)
  | [], _ => by simp [declsTo]
  | _ :: _, 0 => by simp [declsTo]
  | b :: bs, n + 1 => by
    have ih := decls_ro bs n
    unfold declsTo at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.flatMap_cons]
    rw [ih]
    rfl

theorem trees_ro {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    treesTo bs n = (((bs.map ro).take n).map (·.2)).sum
  | [], _ => by simp [treesTo]
  | _ :: _, 0 => by simp [treesTo]
  | b :: bs, n + 1 => by
    have ih := trees_ro bs n
    unfold treesTo at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.flatMap_cons, List.length_append,
      List.sum_cons]
    rw [ih]
    rfl

/-- **At a thread with no tree taken over, `opensAvailable` is `opensR` at the list.** -/
theorem opensAvailable_eq {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (R : List (List Fmt.DeclaredRound × Nat)) (ht : T.taken = []) (hR : T.bs.map ro = R) (n : Nat) :
    T.opensAvailable n = opensR R n := by
  subst hR
  unfold Thread.opensAvailable opensR Thread.hand
  rw [ht, List.nil_append, decls_ro, trees_ro]

theorem pre_ro (c : OnBytes.Model.Verify.Chains) (P : VerifiableInference.Desc.Key.LaterPlaces) :
    (keySharedPre c P).map ro =
      ([], 0) :: (blocksOr (sharedPar c (beforeSharedPoint P))).map ro := by
  unfold keySharedPre
  rw [List.map_cons, List.map_map]
  exact congrArg₂ List.cons rfl (List.map_congr_left fun _ _ => rfl)

/-- The shared chain's list at the written places, by `ro`. -/
theorem flat_ro (c : OnBytes.Model.Verify.Chains)
    (hq : sharedPar c (beforeSharedPoint PF) = QK) :
    ((sharedChain c PF).retype (Cl' := Claim)).blocksInOrder.map ro = keyR := by
  rw [keyShared_cut_omega c PF (PF.O.getD PF.U) omega_full, List.map_append, List.map_append,
    List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_nil, pre_ro, hq]
  rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : K14.WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **At the key's shared thread, at every border, general in its letters, the test is the closed
one.** -/
theorem opens_key (e : parKey Xs PF = QK) (n : Nat) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).opensAvailable n = opensR keyR n :=
  opensAvailable_eq _ keyR rfl
    (((sits_two Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1 ▸ flat_ro Xs.chains e :)) n

theorem opens_key_ten (e : parKey Xs PF = QK) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).opensAvailable 10 = true :=
  (opens_key Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e 10).trans opens_ten

theorem opens_key_eleven (e : parKey Xs PF = QK) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).opensAvailable 11 = true :=
  (opens_key Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e 11).trans opens_eleven

theorem opens_key_twelve (e : parKey Xs PF = QK) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).opensAvailable 12 = true :=
  (opens_key Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e 12).trans opens_twelve

end

end AtPublicFiles.KeyOpens

#print axioms AtPublicFiles.KeyOpens.decls_ro
#print axioms AtPublicFiles.KeyOpens.trees_ro
#print axioms AtPublicFiles.KeyOpens.opensAvailable_eq
#print axioms AtPublicFiles.KeyOpens.pre_ro
#print axioms AtPublicFiles.KeyOpens.flat_ro
#print axioms AtPublicFiles.KeyOpens.opens_key
#print axioms AtPublicFiles.KeyOpens.opens_key_ten
#print axioms AtPublicFiles.KeyOpens.opens_key_eleven
#print axioms AtPublicFiles.KeyOpens.opens_key_twelve
