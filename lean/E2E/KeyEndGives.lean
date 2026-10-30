--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEndGives.lean: THE THIRD CHAIN's END GIVES THE LAST TEST. Where the key file's third chain's
last sub-protocol accepts, it hands the state on as it is, and that state passes `fin₃`
(Johnson/Desc/Third/State.lean): the part of the description's last test that reads the third
chain's last state. So the own step of that sub-protocol keeps ALL of `Form₃`
(E2E/KeyThreadsLaid.lean): `StepKeeps` (E2E/KeyFormKept.lean) at number 3, WITH NO PREMISE. By
unfolding. On the verifier's step alone.

  `of_not_not`: a Boolean whose negation is not true is true.
  **`end_gives`**: from the acceptance of `Third.end₃`: the state behind is the state in front, and
    `fin₃` holds of it. Its decision asks two named clauses (`ChainEnd.untestedL`): "a proximity
    test has begun on every group", which is the first half of `fin₃`; "every sampled message is in
    a tested group", which gives the second half: it is in a group.
  **`form₃_kept_end`**: `StepKeeps U₃ (Form₃ X N P q) 3` at every thread over `(keyFileDescription X N
    P).second.blocksInOrder`.

Limits.
- "Gives" speaks of a step that has accepted: nothing on whether it accepts.
- At numbers 0 and 2 of the third chain, and at the last two sub-protocols of the first and of the
  shared chain, `StepKeeps` of the form stays open.

-/
import E2E.KeyFormKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc (Block ChainEnd.refuse ChainEnd.untestedL)
open VerifiableInference.Desc.Third (S₃ end₃ fin₃)

/-- A Boolean whose negation is not true is true. -/
theorem of_not_not {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

/-- **What the acceptance of the third chain's end gives.** -/
theorem end_gives {Cl : Type} (front : List (Block S₃ Cl)) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (end₃ front).decide s rs gs = .ok s') :
    s' = s ∧ fin₃ s' = true := by
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
      unfold fin₃
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

variable {W₀ Rc Tr Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces) (q : KeyNums)
  (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
    (Local W₀ Rc KeyInst Tr) Xh KeyInst)

/-- **All of `Form₃` is kept at the third chain's last sub-protocol**: no premise. -/
theorem form₃_kept_end (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) :
    StepKeeps U₃ (Form₃ X N P q) 3 := by
  intro blk hk s rs cols s' n h0 hs
  obtain ⟨blk₀, e, hd₀⟩ : ∃ b₀, (keyFileDescription X N P).second.blocksInOrder[3]? = some b₀ ∧
      b₀.decide = (end₃ (Cl := Unit) []).decide := ⟨_, rfl, rfl⟩
  have hk' : (keyFileDescription X N P).second.blocksInOrder[3]? = some blk := by
    rw [← hbs]
    exact hk
  obtain rfl : blk₀ = blk := Option.some.inj (e.symm.trans hk')
  obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ blk₀ s s' rs cols n hs
  rw [hd₀] at hd
  exact ⟨listed_kept₃ X N P U₃ hbs 3 blk₀ hk s rs cols s' n h0.1 hs, fun e => by omega,
    fun e => by omega, fun e => by omega, fun _ => (end_gives [] s s' rs' gs' hd).2⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.of_not_not
#print axioms AtPublicFiles.AtFiles.end_gives
#print axioms AtPublicFiles.AtFiles.form₃_kept_end
