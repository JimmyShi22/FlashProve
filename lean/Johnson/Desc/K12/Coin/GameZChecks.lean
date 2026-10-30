-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameZChecks.lean: THE GAME's FORMS WITH A SMALLER PROMISE (`GameAtY` |
`GameAtYO`, GameYes.lean; `GameAtZ` | `GameAtZO`, GameZ.lean) TRIED AGAINST THE TWO SILLY VERIFIERS.
Statements and proofs.

A form with a smaller promise says more: whoever has it has the form with the larger promise. So the
verifier that says yes to all, which has not Game.lean's forms, has none of these.

  `game_of_gameY` | `gameO_of_gameYO`; `gameY_of_gameZ` | `gameYO_of_gameZO`: for every piece: from
    the smaller promise to the larger.
  `yesAll_not_gameY` | `_gameZ`: first arm, at a statement without a group.
  `yesAll_not_gameYO` | `_gameZO`: second arm, at (tOx, y): a statement with a group.
  `noAll_has_gameZ` | `noAll_has_gameZO`: **A PIECE THAT NEVER PUTS OUT HAS THESE FORMS TOO.**
Limits: those of GameChecks.lean. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.GameZ
import Johnson.Desc.K12.Coin.GameChecks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Member (piO)

section
variable {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
  (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W)

theorem game_of_gameY (h : GameAtY F π num no rad rd base n p) :
    GameAt F π num no rad rd base n p :=
  Reduction.Leads.conseq h (fun _ hx => ⟨hx.1, hx.2.1⟩) (fun _ _ _ _ _ q => q)

theorem gameO_of_gameYO (h : GameAtYO F π num no rad rd base n p) :
    GameAtO F π num no rad rd base n p :=
  Reduction.Leads.conseq h (fun _ hx => ⟨hx.1, hx.2.1⟩) (fun _ _ _ _ _ q => q)

theorem gameY_of_gameZ (h : GameAtZ F π num no rad rd base p) :
    GameAtY F π num no rad rd base n p :=
  Reduction.Leads.conseq h (fun _ hx => hx.2) (fun _ _ _ _ _ q => q)

theorem gameYO_of_gameZO (h : GameAtZO F π num no rad rd base p) :
    GameAtYO F π num no rad rd base n p :=
  Reduction.Leads.conseq h (fun _ hx => hx.2) (fun _ _ _ _ _ q => q)

theorem yesAll_not_gameY (dB : RDT) (x : T12 × F.E.Str) (hg : x.1.st.groups[x.1.g]? = none)
    (hn : x.1.roots = n) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ GameAtY F π num no rad rd base n p := fun h =>
  yesAll_not_game F π num no rad rd base n dB p x hg hn hyes hs
    (game_of_gameY F π num no rad rd base n p h)

theorem yesAll_not_gameZ (dB : RDT) (x : T12 × F.E.Str) (hg : x.1.st.groups[x.1.g]? = none)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ GameAtZ F π num no rad rd base p := fun h =>
  yesAll_not_gameY F π num no rad rd base x.1.roots p dB x hg rfl hyes hs
    (gameY_of_gameZ F π num no rad rd base x.1.roots p h)

theorem noAll_has_gameZ (hno : ∀ a τ, p.ior.red.out a τ = none) :
    GameAtZ F π num no rad rd base p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

theorem noAll_has_gameZO (hno : ∀ a τ, p.ior.red.out a τ = none) :
    GameAtZO F π num no rad rd base p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

end

theorem yesAll_not_gameYO {W : Type} (F : Frame) (t₁ t₂ : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (y : F.E.Str)
    (hyes : ∀ τ, ∃ b, p.ior.red.out (tOx, y) τ = some b) (hs : Small p.err) :
    ¬ GameAtYO F piO (numAt t₁ t₂ 1) (fun z => t₁ + z) rad rd (t₁ + 5) 5 p := fun h =>
  yesAll_not_gameO F t₁ t₂ rad rd p y hyes hs (gameO_of_gameYO F _ _ _ rad rd _ _ p h)

theorem yesAll_not_gameZO {W : Type} (F : Frame) (t₁ t₂ : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (y : F.E.Str)
    (hyes : ∀ τ, ∃ b, p.ior.red.out (tOx, y) τ = some b) (hs : Small p.err) :
    ¬ GameAtZO F piO (numAt t₁ t₂ 1) (fun z => t₁ + z) rad rd (t₁ + 5) p := fun h =>
  yesAll_not_gameYO F t₁ t₂ rad rd p y hyes hs (gameYO_of_gameZO F _ _ _ rad rd _ 5 p h)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_gameY
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_gameZ
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_gameYO
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_gameZO
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_gameZ
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_gameZO
