-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendEarlierMessages.lean: behind a piece the oracles' columns at the trees in front of
its stretch are as they were: so a reader of such columns returns, for an older message, the word
that it returned in front of the piece, and a sealed older message stays sealed with its word read
off the oracles. And the written errors of the piece of a sending whose block goes on, as shares.

Main names: cols_older; ReadsBelow, words_older; sealed_rides; open_below.

What is not claimed. Which reader of columns gives the library's word of a message. In open_below no
price is named: c and the bound are letters. Nothing on soundness of a protocol, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendWords
import Johnson.Desc.K1.Law.GoodSendBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open scoped ENNReal

variable {T Cl W : Type} {C : _root_.Run.PQ.CK} {F : Frame}

/-- **Behind a piece, at a tree in front of its stretch, the column is as it was.** -/
theorem cols_older (p : Piece C F T Cl W) (y : F.E.Str) (τ : Tr (uLT C p.ds)) (j x : Nat)
    (hj : j < p.base) : colsOf F (p.ior.imp y τ) j x = colsOf F y j x := by
  unfold colsOf
  cases hp : posL F.all j x with
  | none => rfl
  | some q =>
    obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hp
    show (sCol C p.stage y τ (.tree (F.all.get q.1).no q.2.val)).getD [] = y.2 q
    rw [h1, h2]
    show (if j < p.base then (posL F.all j x).map y.2 else _).getD [] = _
    rw [if_pos hj, hp]
    rfl

/-- A reader of columns reads trees below a number alone. -/
def ReadsBelow {α : Type} (n : Nat) (G : (Nat → Nat → List UInt64) → α) : Prop :=
  ∀ c c', (∀ j, j < n → ∀ x, c j x = c' j x) → G c = G c'

/-- **An older message's word, read off the oracles, stays.** -/
theorem words_older {α : Type} (G : (Nat → Nat → List UInt64) → α) (p : Piece C F T Cl W)
    (hG : ReadsBelow p.base G) (y : F.E.Str) (τ : Tr (uLT C p.ds)) :
    G (colsOf F (p.ior.imp y τ)) = G (colsOf F y) :=
  hG _ _ fun j hj x => cols_older p y τ j x hj

/-- **A sealed older message rides past a piece**, with its word read off the oracles: where the
piece says yes and its block keeps the older messages. -/
theorem sealed_rides (p : Piece C F T Cl W) (stOf : T → Statement) (hb : KeepsOld stOf p.b)
    (cs : Codes) (s : OracleShape) (e : Nat)
    (G : (Nat → Nat → List UInt64) → (portOmZ cs s e).Str) (hG : ReadsBelow p.base G) (o : Nat)
    (a x : T × F.E.Str) (τ : Tr (uLT C p.ds)) (hx : p.ior.red.out a τ = some x)
    (h : Sealed cs s e (G (colsOf F a.2)) (stOf a.1) o) :
    Sealed cs s e (G (colsOf F x.2)) (stOf x.1) o := by
  obtain ⟨hx2, gs, hdec⟩ := Desc.K14.Law.piece_yes p a τ x hx
  rw [hx2, words_older G p hG]
  exact h.old (hb _ _ _ _ hdec)

/-- **The written errors of the piece of a sending whose block goes on**, as shares. -/
theorem open_below (P : Par) (h1 : P.seeds = 1) (b : Block T Cl) (base : Nat) (d₁ : RDT)
    (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds)
    (e : Nat) (c εs : ℝ≥0∞)
    (hc : (e : ℝ≥0∞) ≤ c * (Fintype.card ((Fin P.coordinates → GE) × GEˣ) : ℝ≥0∞))
    (hε : kapSl 128 ^ (bsRound .two d₁.entry d₁.kind).b * (c / 2 ^ d₁.entry.work) ≤ εs) :
    Err.Below (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).err εs := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he₁ hk₁
  show Err.Below ((seedMapsL d₁ ds P.coordinates).err ((e, ()) : Nat × Unit)) εs
  refine Maps.below_err (seedMapsL d₁ ds P.coordinates) (seedMapsL_ok ds a1 a2 a3 a4 a5)
    ((e, ()) : Nat × Unit) ?_
  refine ⟨⟨c, ?_, hε⟩, Maps.held_skips εs ds⟩
  rw [vals_seed P h1 d₁ he₁ hk₁]
  exact hc

end VerifiableInference.Desc.K1
