-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/ZeroTie.lean: the closing of a segment (K10): the three lemmas on the filler at
made-up columns (Honest/K10/StAtZero.lean) joined: what the closing hands to the fold (`closeAsk`, Honest/K10/Job.lean)
at that filler is what it hands at the verifier's own statement. Lemmas; no definition.

  `front_of_fold`   where the description's fold over a whole list of members returns, `frontState` returns at each
                   place at which a member of the list stands, at the same rounds and columns
  `front_of_chain`  so where a chain's decision (`chainAt`, Johnson/Desc/Block.lean) says yes at a view: at the view's
                   rounds and opened columns
  **`closeAsk_zero`**   every member in front of the closing's place keeps (`Keeps wipeS 0`); `frontState` returns t at
                   the rounds seen and at some columns ⊢ `closeAsk` at the job whose statement is made by `stAtZero` is
                   `closeAsk` at the job that is handed t's own statement and t's live group's number

Limits. `Keeps wipeS 0 b` is a premise here; Honest/K10/Wipe/SeatWipe.lean pays it at each closing's place
(`closeAsk_at_closing`). That the rounds which a part has seen begin as the rounds that the verifier folds, as far as
the members in front take rounds, is the frame's matter and is not said here; from that premise `front_same`
(Honest/K10/RoundsStretch.lean) has this file's premise on `frontState` wherever the chain's decision says yes
(`front_of_chain`). bs, start, xi and P are letters, and J's own place is not tied to P: that t is the verifier's state
is said only as far as the premise on `frontState` says it. The right side is written at the job whose field is
constant, because the law on `closeAsk` (Honest/K10/AskLaw.lean) asks that `stAt` yields the statement itself, which the
filler does not. Nothing on whether `closeAsk` returns. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeS
import Johnson.Desc.ProofFile.Honest.K10.AskWipe
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks chainAt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- **Where the fold over a whole list returns, the state in front of each member's place is there.** -/
theorem front_of_fold {σ Cl : Type} {ft : Nat} {bs : List (Block σ Cl)} {s : σ} {rs : List Fmt.RoundView} {c : List OpenedColumn}
    {r : σ × List Fmt.RoundView × List OpenedColumn} (h : foldBlocks ft bs s rs c = .ok r) (a : Place)
    (ha : bs.any (·.place == a) = true) : ∃ t, frontState ft bs s a rs c = .ok t := by
  rw [← List.takeWhile_append_dropWhile (p := fun b : Block σ Cl => b.place != a) (l := bs)] at h
  obtain ⟨t, rs', c', h1, -⟩ := (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  refine ⟨t, ?_⟩
  unfold frontState
  rw [ha]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [h1]
  rfl

/-- **Where a chain's decision says yes.** -/
theorem front_of_chain {σ Cl : Type} {name : String} {ft : Nat} {bs : List (Block σ Cl)} {s e : σ} {v : Fmt.View}
    (h : chainAt name ft bs s v = .ok e) (a : Place) (ha : bs.any (·.place == a) = true) :
    ∃ t, frontState ft bs s a v.rounds v.opened = .ok t := by
  unfold chainAt at h
  split at h
  · cases h
  · cases hf : foldBlocks ft bs s v.rounds v.opened with
    | error x => rw [hf] at h; cases h
    | ok r => exact front_of_fold hf a ha

/-- **What the closing hands to the fold, at the filler at made-up columns.** -/
theorem closeAsk_zero {W Cl Xi : Type} (J : CloseJob W) (bs : List (Block S Cl)) (start : Xi → S) (xi : W → Xi)
    (P : Par) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → OnBytes.E) (ca : CsAll (closeCarries J.pub))
    (hk : ∀ b ∈ bs.takeWhile (·.place != closePlace P), Keeps wipeS 0 b) {cols : List OpenedColumn} {t : S}
    (h : frontState 0 bs (start (xi w)) (closePlace P) seen.rounds cols = .ok t) :
    closeAsk { J with stAt := fun w' s f => stAtZero bs start (xi w') P s f } w seen front x u ca =
      closeAsk { J with stAt := fun _ _ _ => .ok (t.st, t.live.frame.group) } w seen front x u ca := by
  refine closeAsk_congr J _ _ w seen front x u ca ?_
  show (stAtZero bs start (xi w) P seen front).toOption.map wipeAt = _
  rw [stAtZero_is bs start (xi w) P seen front hk h]
  show some (wipeSt (wipeSt t.st), t.live.frame.group) = some (wipeSt t.st, t.live.frame.group)
  rw [wipeSt_idem]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.front_of_fold
#print axioms ProofFile.Honest.K10.front_of_chain
#print axioms ProofFile.Honest.K10.closeAsk_zero
