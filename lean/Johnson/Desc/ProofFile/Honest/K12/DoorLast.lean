-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorLast.lean: a state on entry to a proximity test in the last
chain, made of the columns that the frame hands a part (`Seen.opened`). The last chain's start is
made of the ends of the two earlier chains (`FileDescription.start₃`, Johnson/Desc/Block.lean), so the
state is the description's own three folds over what a front shows: the first chain's, the shared
chain's, the last chain's blocks in front of the test: in `runCore`'s order and at its arguments,
but on one list: each on what the one before left over; then the way in.

  `doorLastTry`, `atHandLast`, `doorLast`   the text that may refuse; the test that it returned; its
                   value or a default
  `doorW`          the same at a description: `F.first.blocksInOrder`, `F.shared.blocksInOrder`, the last chain's
                   blocks in front of the place a, the first tree's number `F.lastChainFirstTreeNumber`, the
                   starts; the reader `colsOpened` (DoorOpened.lean in this folder)
  `doorLastTry_of_folds`, `doorLast_of_folds`   where the three folds and the start return, the
                   text is the way in at the third fold's state; where that returns, `doorLast` is
                   what it returned

Why not `doorOf` (JobShared.lean). That is one fold, from a start of the input. Why not the blind
door (Blind/DoorL.lean): at the test on G_omega a fold at made-up columns fell at the test in front
(at the small example: SmallRunO.lean in this folder), and the shared chain stands in front of this
test too. The columns of a front in the last chain are the first chain's, then the shared
chain's, then its own (`Seen.opened`, Honest/Frame.lean).

What may be said here on hiding, and no more
(a rule of use for whoever builds on this file;
no theorem):
«The state on entry reads the instance's public part, the rounds shown, and ALL columns opened in
front of this test, in the order of reading: the first chain's, the shared chain's, the last
chain's own. They are computed from the witness, the index, the stored tables' pads and encoding
randomness, AND THE RUN's COINS. Never a word on a simulator at this place without «given the
instance's public part, the rounds shown and all columns opened in front, in all three chains».
But for the stored tables' columns no one can hand a simulator these from outside: the simulators
of EVERY part in front must have made them: this test stands last, and its «given» is the whole
view in front. At a called part of the walk the field begins with the two earlier chains' views'
own columns (door_last_at_called); that what follows them are the last chain's view's is not
typed, and that each tree's budget counts them is typed by nobody.»

Limits.
- `doorLast` HAS A SILENT DEFAULT (`fall`), as `doorOf` has: `TestJob.rec₀` has no room for an
  error; at `opened = none` the door reads [], and is expected to fall (shown at one front of the
  small plan, at the test on G_omega; not here). The door does not keep `Seen`'s duty «AT none IT
  ERRS»: behind the guard (FieldGuard.lean; `halfW`, AtProof/HalfW.lean) the pair does.
- WHERE NO BLOCK STANDS AT a, `doorW` takes the whole last chain, without a word.
- That the folds return on an honest run, and that the sealing round that a front holds is what
  `runCore` lays back, is not said here: DoorLastAtRun.lean in this folder says it, of the walk.
  Nothing here shows that the state is the verifier's.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription Place foldBlocks)
open VerifiableInference.Desc.K12 (T12)

variable {Xi W X S₁ S₂ S₃ C₁ C₂ C₃ : Type}

/-- **The state on entry, tried**: the three folds and the way in. -/
def doorLastTry (b₁ : List (Block S₁ C₁)) (b₂ : List (Block S₂ C₂)) (pre : List (Block S₃ C₃))
    (ft : Nat) (s₁ : W → S₁) (s₂ : W → S₂) (st₃ : W → S₁ → S₂ → Except String S₃)
    (enter : S₃ → Except String T12) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    Except String T12 :=
  (foldBlocks 0 b₁ (s₁ w) fr.seen.rounds (cols w fr)).bind fun a₁ =>
  (foldBlocks 0 b₂ (s₂ w) a₁.2.1 a₁.2.2).bind fun a₂ =>
  (st₃ w a₁.1 a₂.1).bind fun s =>
  (foldBlocks ft pre s a₂.2.1 a₂.2.2).bind fun a₃ => enter a₃.1

/-- **The state on entry is at hand**: the text returns. A test with code. -/
def atHandLast (b₁ : List (Block S₁ C₁)) (b₂ : List (Block S₂ C₂)) (pre : List (Block S₃ C₃))
    (ft : Nat) (s₁ : W → S₁) (s₂ : W → S₂) (st₃ : W → S₁ → S₂ → Except String S₃)
    (enter : S₃ → Except String T12) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    Bool :=
  (doorLastTry b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr).toOption.isSome

/-- **The state on entry**, of the type of `TestJob.rec₀`: `fall` where the text refuses. -/
def doorLast (b₁ : List (Block S₁ C₁)) (b₂ : List (Block S₂ C₂)) (pre : List (Block S₃ C₃))
    (ft : Nat) (s₁ : W → S₁) (s₂ : W → S₂) (st₃ : W → S₁ → S₂ → Except String S₃)
    (enter : S₃ → Except String T12) (cols : W → Front X → List OpenedColumn) (fall : T12) (w : W)
    (fr : Front X) : T12 :=
  (doorLastTry b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr).toOption.getD fall

/-- **At a description.** xOf: the instance, of the input. a: the test's place. -/
def doorW (F : FileDescription Xi) (xOf : W → Xi) (enter : F.S₃ → Except String T12) (a : Place)
    (fall : T12) : W → Front X → T12 :=
  doorLast F.first.blocksInOrder F.shared.blocksInOrder (F.second.blocksInOrder.takeWhile (·.place != a)) F.lastChainFirstTreeNumber
    (fun w => F.start₁ (F.pub (xOf w))) (fun w => F.start₂ (F.pub (xOf w)))
    (fun w => F.start₃ (F.pub (xOf w))) enter colsOpened fall

/-- **Where the three folds and the start return, the text is the way in at the third fold's
state.** -/
theorem doorLastTry_of_folds (b₁ : List (Block S₁ C₁)) (b₂ : List (Block S₂ C₂))
    (pre : List (Block S₃ C₃)) (ft : Nat) (s₁ : W → S₁) (s₂ : W → S₂)
    (st₃ : W → S₁ → S₂ → Except String S₃) (enter : S₃ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X)
    {e₁ : S₁} {r₁ : List Fmt.RoundView} {c₁ : List OpenedColumn} {e₂ : S₂} {r₂ : List Fmt.RoundView} {c₂ : List OpenedColumn}
    {s : S₃} {e₃ : S₃} {r₃ : List Fmt.RoundView} {c₃ : List OpenedColumn}
    (h₁ : foldBlocks 0 b₁ (s₁ w) fr.seen.rounds (cols w fr) = .ok (e₁, r₁, c₁))
    (h₂ : foldBlocks 0 b₂ (s₂ w) r₁ c₁ = .ok (e₂, r₂, c₂))
    (hs : st₃ w e₁ e₂ = .ok s) (h₃ : foldBlocks ft pre s r₂ c₂ = .ok (e₃, r₃, c₃)) :
    doorLastTry b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr = enter e₃ := by
  unfold doorLastTry
  rw [h₁]
  show ((foldBlocks 0 b₂ (s₂ w) r₁ c₁).bind fun a₂ => (st₃ w e₁ a₂.1).bind fun s =>
    (foldBlocks ft pre s a₂.2.1 a₂.2.2).bind fun a₃ => enter a₃.1) = _
  rw [h₂]
  show ((st₃ w e₁ e₂).bind fun s =>
    (foldBlocks ft pre s r₂ c₂).bind fun a₃ => enter a₃.1) = _
  rw [hs]
  show ((foldBlocks ft pre s r₂ c₂).bind fun a₃ => enter a₃.1) = _
  rw [h₃]
  rfl

/-- **Where the three folds, the start and the way in return, the state is what the way in
returned.** -/
theorem doorLast_of_folds (b₁ : List (Block S₁ C₁)) (b₂ : List (Block S₂ C₂))
    (pre : List (Block S₃ C₃)) (ft : Nat) (s₁ : W → S₁) (s₂ : W → S₂)
    (st₃ : W → S₁ → S₂ → Except String S₃) (enter : S₃ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (fall : T12) (w : W) (fr : Front X)
    {e₁ : S₁} {r₁ : List Fmt.RoundView} {c₁ : List OpenedColumn} {e₂ : S₂} {r₂ : List Fmt.RoundView} {c₂ : List OpenedColumn}
    {s : S₃} {e₃ : S₃} {r₃ : List Fmt.RoundView} {c₃ : List OpenedColumn} {t : T12}
    (h₁ : foldBlocks 0 b₁ (s₁ w) fr.seen.rounds (cols w fr) = .ok (e₁, r₁, c₁))
    (h₂ : foldBlocks 0 b₂ (s₂ w) r₁ c₁ = .ok (e₂, r₂, c₂))
    (hs : st₃ w e₁ e₂ = .ok s) (h₃ : foldBlocks ft pre s r₂ c₂ = .ok (e₃, r₃, c₃))
    (he : enter e₃ = .ok t) :
    doorLast b₁ b₂ pre ft s₁ s₂ st₃ enter cols fall w fr = t := by
  unfold doorLast
  rw [doorLastTry_of_folds b₁ b₂ pre ft s₁ s₂ st₃ enter cols w fr h₁ h₂ hs h₃, he]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.doorLastTry
#print axioms ProofFile.Honest.K12.Light.atHandLast
#print axioms ProofFile.Honest.K12.Light.doorLast
#print axioms ProofFile.Honest.K12.Light.doorW
#print axioms ProofFile.Honest.K12.Light.doorLastTry_of_folds
#print axioms ProofFile.Honest.K12.Light.doorLast_of_folds
