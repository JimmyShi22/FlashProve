--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/EndsGive.lean: WHAT A SUB-PROTOCOL's OWN DECISION GRANTS HOLDS OF THE VERIFIER's STATE AT THE
BORDER BEHIND IT, WHEREVER THE THREAD STANDS THERE; so the third chain's last state passes `fin₃`,
and the key file's last test says yes from ONE premise, on the first chain's last state. Statements
and proofs. On the verifier's side alone. NOTHING IS CLAIMED OF ANY PROVER.

Why. E2E/KeyEndGives.lean has: where the third chain's last sub-protocol accepts, the state behind
passes `fin₃`. That is a sentence on one step. The last test is asked of the state at which the
thread stands at its last border. The thread's own clause on how its state was made (`Thread.Made`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) holds the verifier's fold up to that border.

  **`granted_behind`**: at any thread, any number n of a sub-protocol e of its list, any P that e's
    decision grants of the state that it returns: where the thread stands at the border n + 1, P
    holds of the state. By `ChainEnd.foldBlocks_last` (Johnson/Desc/ChainEndFold.lean).
  **`fin₃_of_thr`**, `fin₃_of_thrS`: at every thread over the key file's third chain: where it
    stands at the border 4, its state passes `fin₃`. NO PREMISE on the thread but its list.
  **`finYesS_of_first`**: `FinYesS` (Johnson/Desc/ProofFile/Honest/Thread/FileD.lean) at the key
    file's description, from: the third thread's list; that list's length is 4; and, of the first
    chain's last state, the book-keeping of border 19.

Limits.
- "Where the thread stands": nothing on whether it does.
- `finYesS_of_first`'s premise on the first chain is paid nowhere here.
- Nothing on the door between the chains.

-/
import E2E.KeyEndGives
import E2E.KeyThreads
import Johnson.Desc.ChainEndFold
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Thread.FileD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (end₃ fin₃)

/-- **What a sub-protocol's own decision grants holds at the border behind it.** -/
theorem granted_behind {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W Y Pb) (n : Nat)
    (e : Block S Cl) (hk : T.bs[n]? = some e) (P : S → Prop)
    (he : ∀ s rs gs s', e.decide s rs gs = .ok s' → P s') {k : Coins Bk} {s : S} {m : Mid W Y}
    {E : Env} (h : Thr T (n + 1) k s m E) : P s := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, -, -, hf⟩, -, -⟩ := h
  rw [take_succ_some hk] at hf
  exact VerifiableInference.Desc.ChainEnd.foldBlocks_last T.ft e P he _ s₀ _ cols _ hf

variable {W₀ Rc Ky Tr X₀ Xh : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The third chain's last state passes `fin₃`.** -/
theorem fin₃_of_thr
    (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) Xh KeyInst)
    (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) {k : Coins Bk} {e₃ : (keyFileDescription X N P).S₃}
    {m : Mid (Local W₀ Rc KeyInst Tr) Xh} {E : Env} (h : Thr U₃ (3 + 1) k e₃ m E) :
    fin₃ e₃ = true := by
  obtain ⟨b₀, e, hd₀⟩ : ∃ b₀, (keyFileDescription X N P).second.blocksInOrder[3]? = some b₀ ∧
      b₀.decide = (end₃ (Cl := Unit) []).decide := ⟨_, rfl, rfl⟩
  refine granted_behind U₃ 3 b₀ (by rw [hbs]; exact e) (fun s => fin₃ s = true)
    (fun s rs gs s' hd => ?_) h
  rw [hd₀] at hd
  exact (end_gives [] s s' rs gs hd).2

theorem fin₃_of_thrS
    (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) Xh KeyInst)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc KeyInst Tr) Xh → Prop)
    (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) {k : Coins Bk} {e₃ : (keyFileDescription X N P).S₃}
    {m : Mid (Local W₀ Rc KeyInst Tr) Xh} {E : Env} (h : ThrS U₃ S₃ (3 + 1) k e₃ m E) :
    fin₃ e₃ = true :=
  fin₃_of_thr X N P U₃ hbs h.1

open Johnson.RunOne.KeyRows1 in
/-- **The last test says yes, from the pairs: one premise is left, on the first chain's last
state.**
-/
theorem finYesS_of_first
    (U₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) Xh KeyInst)
    (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) Xh KeyInst)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc KeyInst Tr) Xh → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc KeyInst Tr) Xh → Prop) (x : KeyInst) (k : Coins Bk)
    (hbs : U₃.bs = (keyFileDescription X N P).second.blocksInOrder) (hl : (keyFileDescription X N P).second.blocksInOrder.length = 3 + 1)
    (h₁ : ∀ e₁ m₁ E₁, ThrS U₁ S₁ (keyFileDescription X N P).first.blocksInOrder.length k e₁ m₁ E₁ →
      VerifiableInference.Desc.Key.shape₁ (plan₁ X.Y.k.oneTime) (readers₁ X.Y.k.oneTime)
        (book₁ X.Y.k.oneTime) 2 (slots₁ X.Y.k.oneTime) 19 e₁ = true) :
    FinYesS (keyFileDescription X N P) U₁ U₂ U₃ S₁ S₂ S₃ x k :=
  fun e₁ m₁ E₁ e₂ _ _ e₃ _ _ u₁ _ u₃ =>
    fin_of_shape X N P x e₁ e₂ e₃ (h₁ e₁ m₁ E₁ u₁) (fin₃_of_thrS X N P U₃ S₃ hbs (hl ▸ u₃))

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.granted_behind
#print axioms AtPublicFiles.AtFiles.fin₃_of_thr
#print axioms AtPublicFiles.AtFiles.fin₃_of_thrS
#print axioms AtPublicFiles.AtFiles.finYesS_of_first
