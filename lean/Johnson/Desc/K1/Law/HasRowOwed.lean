-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HasRowOwed.lean: K01_law, row P.hasRow: the statements alone,
as Props by def.

  `KeepsHasRow B`: a yes of the block B, on any rounds, keeps a yes of the test `hasRow`
    (Johnson/Top/H0/Walk/FrameRow.lean): "the state holds a pending row".
  `HasRowAtCommit`: every later moment's block `commitAtS` (Johnson/Desc/K1/AtS.lean) keeps it.
  `HasRowSameAtCommit`: the test answers behind as in front, where the index masks' message is there
    in front. Without that premise the equation is not meant: a message that the block sends could
    take the number that the state holds for the index masks' message, and a no could turn to a yes.
  `HasRowPubAtCommit`: the first, at the layer's function with code (`pubP1`,
    Johnson/Top/H0/Fill/PubP1.lean).

Limits. Nothing on the reads' place's joined block. K01_law is not proved by this. Nothing on
soundness.
-/
import Johnson.Top.H0.Fill.PubP1
import Johnson.Desc.K1.Law.GoodSend5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub)
open Johnson.Desc.First.Walk.Law (hasRow)

/-- A yes of B, on any rounds, keeps a yes of the test "the state holds a pending row". -/
def KeepsHasRow {Cl : Type} (B : Block S Cl) : Prop :=
  ∀ (lay : WsLay) (n : Nat) (lin : Params.LinShape) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))), B.decide s rs gs = .ok s' →
      hasRow lay n lin s = true → hasRow lay n lin s' = true

/-- **ROW P.hasRow, at a segment's later moment.** -/
def HasRowAtCommit : Prop :=
  ∀ (Cl : Type) (P : Par) (link moment : Nat) (arrays : Option (List Nat)),
    KeepsHasRow (commitAtS P link moment arrays : Block S Cl)

/-- The same as an equation, where the index masks' message is there in front. -/
def HasRowSameAtCommit : Prop :=
  ∀ (Cl : Type) (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (lay : WsLay) (n : Nat)
    (lin : Params.LinShape) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s' →
      s.out.indexMasks < s.st.oracles.size → hasRow lay n lin s' = hasRow lay n lin s

/-- In the form of the table's field on public items, at the layer's own function with code. -/
def HasRowPubAtCommit : Prop :=
  ∀ (Cl Pp : Type) (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (d : First.FillP1.PubData) (f : Pub → Pp × S → Bool) (m : Nat) (x x' : Pp × S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (commitAtS P link moment arrays : Block S Cl).decide x.2 rs gs = .ok x'.2 →
      First.FillP1.pubP1 d f (.hasRow m) x = true → First.FillP1.pubP1 d f (.hasRow m) x' = true

end VerifiableInference.Desc.K1
