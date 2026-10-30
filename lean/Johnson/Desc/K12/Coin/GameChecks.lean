-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameChecks.lean: THE GAME's FORM (`GameAt`, `GameAtO`, Game.lean) TRIED
AGAINST THE TWO SILLY VERIFIERS. Statements and proofs.

  `yesAll_not_game`: a piece that puts out at every transcript from one statement without a group
    whose record counts n roots, at errors below its rounds' numbers of challenges, has not the
    first arm's form.
  `yesAll_not_gameO`: a piece that puts out at every transcript from (tOx, y): the record of the
    smaller stored proof's own-mask place with the group's one open row replaced by "0 = 1": has not
    the second arm's form at that place's letters. The whole promise holds there.
  `noAll_has_game`, `noAll_has_gameO`: **A PIECE THAT NEVER PUTS OUT HAS BOTH FORMS.** So the form
    alone is not the whole of what is owed.
  `Live`: what shuts that verifier out: some statement inside the promise at which the piece puts
    out. `noAll_not_live`: a piece that never puts out is not live.
  `K12GameLiveO`: STATED, NOT PROVED: the proximity test's piece is live at the second arm's
    promise, at the smaller stored proof's own-mask place, at the stored record tO itself.
Limits. Nothing on soundness: checks of a statement's form. The first arm's form is tried at no
statement with a group. tOx is no record that a verifier reaches. `K12GameLiveO` has no proof: what
stands for it today is the block's listed run at that place, a run's word.

-/
import Johnson.Desc.K12.Coin.Game
import Johnson.Desc.K12.Coin.ChecksAtO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Member (piO tO)
open H2K.Pin (NTuple PayRec)

theorem yesAll_not_game {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (dB : RDT) (p : Piece (ckP .two) F T12 Unit W)
    (x : T12 × F.E.Str) (hg : x.1.st.groups[x.1.g]? = none) (hn : x.1.roots = n)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ GameAt F π num no rad rd base n p :=
  yesAll_failsRecFree F π num no rad rd base dB n p x hg hn hyes hs

theorem yesAll_not_gameO {W : Type} (F : Frame) (t₁ t₂ : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (y : F.E.Str)
    (hyes : ∀ τ, ∃ b, p.ior.red.out (tOx, y) τ = some b) (hs : Small p.err) :
    ¬ GameAtO F piO (numAt t₁ t₂ 1) (fun z => t₁ + z) rad rd (t₁ + 5) 5 p :=
  yesAll_bites_Ox F t₁ t₂ rad rd p y hyes hs

theorem noAll_has_game {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W)
    (hno : ∀ a τ, p.ior.red.out a τ = none) : GameAt F π num no rad rd base n p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

theorem noAll_has_gameO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W)
    (hno : ∀ a τ, p.ior.red.out a τ = none) : GameAtO F π num no rad rd base n p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

/-- Some statement inside the promise at which the piece puts out. -/
def Live {W : Type} {F : Frame} (p : Piece (ckP .two) F T12 Unit W)
    (on : T12 × F.E.Str → Prop) : Prop :=
  ∃ a τ b, on a ∧ p.ior.red.out a τ = some b

theorem noAll_not_live {W : Type} {F : Frame} (p : Piece (ckP .two) F T12 Unit W)
    (on : T12 × F.E.Str → Prop) (hno : ∀ a τ, p.ior.red.out a τ = none) : ¬ Live p on := by
  rintro ⟨a, τ, b, _, hb⟩
  rw [hno a τ] at hb
  cases hb

/-- STATED, NOT PROVED: at some frame, stretch and oracles the proximity test's piece at the smaller
stored proof's own-mask place puts out from the stored record itself. (The promise holds at tO
whatever the oracles: `promise_O`, MemberProm.lean.) -/
def K12GameLiveO : Prop :=
  ∃ (F : Frame) (t₁ : ℕ) (dB : RDT) (dt : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str),
    (pieceOf (C := ckP .two) (F := F) (W := Unit) (proximityTestKind guardedProximityTestParts piO : Block T12 Unit) (t₁ + 5)
      (dB :: dt) []
      ⟨fun _ _ w => w, Err.zero _⟩).ior.red.out (tO, y) τ = some b

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_game
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_gameO
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_game
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_gameO
#print axioms VerifiableInference.Desc.K12.Coin.noAll_not_live
