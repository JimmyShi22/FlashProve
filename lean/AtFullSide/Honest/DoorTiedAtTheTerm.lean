-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorTiedAtTheTerm.lean: THE SECOND CHAIN's COMPANION WITH THE TIE TO THE TWO EARLIER
CHAINS' ENDS. A stand of the second chain's thread does not remember the two earlier chains' stands.
The clause TiedToEnds (Honest/K14/TiedToEnds.lean) says that it comes behind such a pair. Here it
stands beside saidThree.

  saidThreeTied     the second chain's companion with the clause
  door_tied_at_term    the door gives it, where it gives saidThree
  next_tied_at_term    it is carried past a sub-protocol, where saidThree is

What these are. Conditional lemmas. None is one of the library's goals. They say nothing of
soundness, completeness or hiding.

Limits. Each keeps the door, or the step, at saidThree as a premise.
-/
import AtFullSide.Honest.TheThreeThreads
import Johnson.Desc.ProofFile.Honest.Thread.DoorAndClause
import Johnson.Desc.ProofFile.Honest.K14.TiedToEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K14 (TiedToEnds tied_next tied_at_door_ready)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **The second chain's companion with the tie.** -/
abbrev saidThreeTied : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop :=
  fun b k m => saidThree h first reads last R b k m ∧
    TiedToEnds (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length
      (threadTwo h reads shared R) (saidTwo h reads shared R) h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (threadThree h first reads last R).front b k m

/-- **The door with the tie.** -/
theorem door_tied_at_term {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (hd : DoorBehindS h.description A.H (threadOne h first R) (threadTwo h reads shared R)
      (threadThree h first reads last R) (saidOne h first R) (saidTwo h reads shared R)
      (saidThree h first reads last R) x k R) :
    DoorBehindS h.description A.H (threadOne h first R) (threadTwo h reads shared R)
      (threadThree h first reads last R) (saidOne h first R) (saidTwo h reads shared R)
      (saidThreeTied h first reads shared last R) x k R :=
  doorBehindS_and hd fun _ _ _ _ _ _ o u₁ u₂ =>
    tied_at_door_ready h first reads shared last hR R.own _ _ u₁ u₂ 0 o

/-- **The step with the tie.** -/
theorem next_tied_at_term {b : Nat}
    (hn : SaidNext (threadThree h first reads last R)
      (saidThree h first reads last R) b) :
    SaidNext (threadThree h first reads last R)
      (saidThreeTied h first reads shared last R) b :=
  saidNext_and _ _ hn (tied_next _ _ _ _ _ _ _ _ _ _ b)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.door_tied_at_term
#print axioms AtFullSide.Honest.next_tied_at_term
