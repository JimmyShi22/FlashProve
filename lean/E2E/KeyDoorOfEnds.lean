--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDoorOfEnds.lean: THE DOOR BETWEEN THE KEY FILE's CHAINS, FROM THE PAIRS: OF THE NINE CLAUSES
THAT THE THIRD CHAIN's START ASKS (`Start₃`, E2E/KeyStartThird.lean) TWO ARE PUBLIC AND ONE IS
GRANTED BY THE SHARED CHAIN's OWN END; the six that are left are named, as two premises. Statements
and proofs. On the verifier's side alone. NOTHING IS CLAIMED OF ANY PROVER.

  **`shared_end_gives`**: from the acceptance of the shared chain's last sub-protocol
    (`K12.Seat.last`): the state behind is the state in front, and `K14.tested` holds of it. The
    twin of `end_gives` (E2E/KeyEndGives.lean), by the same steps: the two ends ask the same two
    named clauses, and `K14.tested` has the formula of `fin₃`.
  **`tested_of_thr`**: so at every thread over the key file's shared chain: where it stands at the
    border 12, its state passes `K14.tested`: by `granted_behind` (E2E/EndsGive.lean). No premise on
    the thread but its list and that list's length.
  **`doorYesS_of_two`**: `DoorYesS` (Johnson/Desc/ProofFile/Honest/Thread/FileD.lean) at the key
    file's description, from the description's own test on its plan and TWO NAMED PREMISES: `Last₁`
    (E2E/KeyThreadsLaid.lean: five clauses) at the first chain's last state; and that the shared
    chain's last statement has the public codes, which may be shown from BOTH chains' last borders.

WHO PAYS WHICH OF THE NINE. lawful, arm: public: `third_public`, from the plan's test. tested: here.
claim, ahead, numbers, codes₁, roots (`Last₁`) and codes₂: PREMISES.

Limits.
- "Where the thread stands": nothing on whether it does.
- The two premises are paid nowhere here. No end's decision grants them.

-/
import E2E.EndsGive
import E2E.KeyThreadsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc (Block ChainEnd.refuse ChainEnd.untestedL)

/-- **What the acceptance of the shared chain's end gives.** -/
theorem shared_end_gives (front : List (Block _root_.Desc.K14.St Unit)) (s s' : _root_.Desc.K14.St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide s rs gs = .ok s') :
    s' = s ∧ _root_.Desc.K14.tested s' = true := by
  have h' : (ChainEnd.refuse (ChainEnd.untestedL s.st)).map (fun _ => s) = .ok s' := h
  cases hr : ChainEnd.refuse (ChainEnd.untestedL s.st) with
  | error e =>
    rw [hr] at h'
    cases h'
  | ok u =>
    rw [hr] at h'
    obtain rfl : s = s' := Except.ok.inj h'
    refine ⟨rfl, ?_⟩
    unfold ChainEnd.refuse at hr
    split at hr
    · cases hr
    · rename_i hn
      have hall := List.find?_eq_none.1 hn
      have a1 : s.st.groups.all (·.inRun) = true :=
        of_not_not (hall ("end: a proximity test has begun on every group", _) List.mem_cons_self)
      have a2 : (s.st.oracles.all fun x =>
          !x.sampled || x.groups.any fun g => (s.st.groups[g]?).any (·.inRun)) = true :=
        of_not_not (hall ("end: every sampled message is in a tested group", _)
          (List.mem_cons_of_mem _ List.mem_cons_self))
      unfold _root_.Desc.K14.tested
      rw [a1, Bool.true_and]
      refine Array.all_eq_true_iff_forall_mem.2 fun x hx => ?_
      have b := Array.all_eq_true_iff_forall_mem.1 a2 x hx
      cases hsm : x.sampled with
      | false => rfl
      | true =>
        rw [hsm] at b
        cases hg : x.groups with
        | nil =>
          rw [hg] at b
          cases b
        | cons a l => rfl

variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The shared chain's last state passes `K14.tested`.** -/
theorem tested_of_thr
    (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hl : (keyFileDescription X N P).shared.blocksInOrder.length = 11 + 1) {k : Coins Bk} {e₂ : (keyFileDescription X N P).S₂}
    {m : Mid (Common W₀ Rc Ky) X₀} {E : Env} (h : Thr U₂ (11 + 1) k e₂ m E) :
    _root_.Desc.K14.tested e₂ = true := by
  obtain ⟨blk, e, -, -, -, hd⟩ := flat_last (keyFileDescription X N P).shared
  rw [hl, Nat.add_sub_cancel] at e
  refine granted_behind U₂ 11 blk (by rw [hbs]; exact e)
    (fun s => _root_.Desc.K14.tested s = true) (fun s rs gs s' hdd => ?_) h
  rw [hd] at hdd
  exact (shared_end_gives [] s s' rs gs hdd).2

/-- **The door says yes, from the pairs: two named premises are left.** -/
theorem doorYesS_of_two
    (U₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) Xh KeyInst)
    (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc KeyInst Tr) Xh → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop) (x : KeyInst) (k : Coins Bk)
    (hp : (keyFileDescription X N P).planOk = true) (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hl : (keyFileDescription X N P).shared.blocksInOrder.length = 11 + 1)
    (h₁ : ∀ e₁ m₁ E₁, ThrS U₁ S₁ (keyFileDescription X N P).first.blocksInOrder.length k e₁ m₁ E₁ →
      Last₁ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape e₁)
    (h₂ : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS U₁ S₁ (keyFileDescription X N P).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS U₂ S₂ (keyFileDescription X N P).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (show _root_.Desc.K14.St from e₂).st.codes = X.chains.made.sized.key.codes) :
    DoorYesS (keyFileDescription X N P) U₁ U₂ S₁ S₂ x k := fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ => by
  obtain ⟨l, hs⟩ := start₃_of_lasts X N P hp (h₁ e₁ m₁ E₁ u₁)
    ⟨tested_of_thr X N P U₂ hbs hl (hl ▸ u₂).1, h₂ e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂⟩
  exact ⟨_, start₃_passes X N P x e₁ e₂ l hs⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.shared_end_gives
#print axioms AtPublicFiles.AtFiles.tested_of_thr
#print axioms AtPublicFiles.AtFiles.doorYesS_of_two
