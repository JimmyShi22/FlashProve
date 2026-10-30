-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotBegunFirst.lean: THE LETTER OF THE KEY FILE's FIRST CHAIN: what is said of the prover's run beside the thread
Th (E2E/FirstHSeat.lean): the letter WalkedFrom (E2E/WalkedFrom.lean) from the walk's start, IN THE FORM IN WHICH
E2E/KeyStandWalked.lean lays the shared chain's (walkedLetter): so MembersS and AtRunS get one kind of letter on both
chains. With it: AtRunS's sixth clause, and SaidNext at every member.

  (The three definitions' text lies in E2E/LotLetters.lean.)
  `inFirst w₀ rc x`, `startFirst K o v`: the first chain's input at an instance; the state in which its run begins, with
    the field opened at o (none at the frame's play, some [] at the walk): twins of inK, startAt (E2E/KeyStandOne.lean).
  `walkedFirst`: THE LETTER: what the thread's steps reach from startFirst K (some []) (inFirst w₀ rc x).
  `LotBegunFirst`, **`lotBegunFirst`**: where ready returns R, the letter holds at border 0 of
    { R.start₁ (keyProver K) with opened := some [] }: AtRunS's sixth clause at S₁ := walkedFirst.
  `LotSaidNextFirst`, **`lotSaidNextFirst`**: SaidNext at every member: saidNext_walked.
  `begun_field`, `begun_one`: at a state that begins the field is some []; and there is one such state: the premises
    hBegun of walked_field (E2E/WalkedField.lean) and "Begun is one-valued" of walked_unique.
  `LotBegunFirstAtValue`, `LotSaidNextFirstAtValue`: both at the offline prover's own senders and the index's reader.

Limits. THE LETTER BY ITSELF PAYS NOTHING (E2E/WalkedFrom.lean's head): it is the least letter that begins there and is
carried. That a state has it says nothing on whether a run reaches it. What it gives at a border (the field, one
state for each run) is for walked_field and walked_unique, whose other premises are not here. lotBegunFirst is under
«ready returns». Calls and one rewriting: no new content. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotLetters
import E2E.FirstHSeat
import E2E.WalkedFrom
import E2E.KeyStandWalked
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open VerifierAndGoals (PublicFiles)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **The letter at the walk's start**: AtRunS's sixth clause. -/
def LotBegunFirst : Prop :=
  ∀ (k : Coins Bk) R, ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R →
    walkedFirst Xs N Pl K f Q w₀ rc x 0 k { R.start₁ (keyProver K) with opened := some [] }

theorem lotBegunFirst : LotBegunFirst Xs N Pl K f Q w₀ rc x := by
  intro k R hR
  obtain ⟨-, ⟨⟩, -, hown, -⟩ := ready_ok hR
  refine .begun ?_
  show (⟨⟨R.own, [], (keyProver K).own₀⟩, [], [], some []⟩ : Mid (In1 W₀ Rc) X') = _
  rw [hown]

/-- **The letter is carried over every member.** -/
def LotSaidNextFirst : Prop :=
  ∀ b, SaidNext (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b

theorem lotSaidNextFirst : LotSaidNextFirst Xs N Pl K f Q w₀ rc x := fun b => saidNext_walked _ _ b

/-- At a state that begins, the field is some []. -/
theorem begun_field (m : Mid (In1 W₀ Rc) X') (h : m = startFirst K (some []) (inFirst w₀ rc x)) :
    m.opened = some [] := by
  rw [h]

/-- There is one state that begins. -/
theorem begun_one (m m' : Mid (In1 W₀ Rc) X') (h : m = startFirst K (some []) (inFirst w₀ rc x))
    (h' : m' = startFirst K (some []) (inFirst w₀ rc x)) : m = m' := h.trans h'.symm

end

/-- The letter at the walk's start, at the offline prover's own senders and the index's reader. -/
def LotBegunFirstAtValue : Prop :=
  ∀ {files : PublicFiles} {Bk : ProverCoinCounts} (d : OfflineDescription) (Q : LaterFill Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix)
    (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    LotBegunFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x

theorem lotBegunFirstAtValue : LotBegunFirstAtValue := fun d Q w₀ rc x =>
  lotBegunFirst d.source d.numbers d.later _ matrixReader Q w₀ rc x

/-- The letter is carried, there. -/
def LotSaidNextFirstAtValue : Prop :=
  ∀ {files : PublicFiles} {Bk : ProverCoinCounts} (d : OfflineDescription) (Q : LaterFill Bk FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix)
    (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    LotSaidNextFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc
      x

theorem lotSaidNextFirstAtValue : LotSaidNextFirstAtValue := fun d Q w₀ rc x =>
  lotSaidNextFirst d.source d.numbers d.later _ matrixReader Q w₀ rc x

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.lotBegunFirst
#print axioms AtPublicFiles.FirstH.Lots.lotSaidNextFirst
#print axioms AtPublicFiles.FirstH.Lots.begun_field
#print axioms AtPublicFiles.FirstH.Lots.begun_one
#print axioms AtPublicFiles.FirstH.Lots.lotBegunFirstAtValue
#print axioms AtPublicFiles.FirstH.Lots.lotSaidNextFirstAtValue
