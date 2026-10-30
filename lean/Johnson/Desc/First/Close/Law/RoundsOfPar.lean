-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RoundsOfPar.lean: THE ROUNDS THAT THE KIND K10 DECLARES AT A PLACE
WITHOUT PROOF OF WORK ARE THE FORMAT's OWN ROUNDS OF WHICH K10's LAW SPEAKS. A definition,
statements and proofs.

Why. K10's law asks of its rounds' data `IsRd (toRD dB) (Fmt.M2.rBatN n)`, `IsRd (toRD dE)
(Fmt.M1.rEps na)`, `IsRd (toRD dR) (Fmt.M1.rTwo nb)` (OnBytes/Slice/RoundsOf.lean): the entry, the
kind and the items of three rounds of the format, which have no proof of work. The kind (Kind.lean)
declares `(entries Q).map fun e => { entry := e }`, with the place's two numbers of proof of work
and its number of rows.
  `roundsOf rows k`: "BAT" at rows rows, "FOLD epsilon", k times "FOLD round", as written rounds
    that open no stored table.
  `bat_round`, `eps_round`, `two_round`: each declared round, as the readers take it
    (`Fmt.DeclaredRound.round`: the kind from the name, the items from the entry's words), is that round
    of the format.
  `kind_written`: at Q.workField = 0 and Q.workClose = 0: `WrittenAs e (kind Q).rounds (roundsOf
    Q.rows Q.k)` (Johnson/Desc/Sound/Tiles.lean): OF THIS ONE BLOCK's DECLARED ROUNDS. The library's
    road takes `WrittenAs` of a WHOLE CHAIN's declared rounds.
    It is spent in CutAtK10.lean (beside this file):
    there it names, round by round, which written round of the chain's list each of the block's
    declared rounds is. `kind_rounds_length`: 2 + Q.k.
Limits. That the data which the road makes of these written rounds satisfy the law's three premises
is CutAtK10.lean's. The two numbers of proof of work are premises. Nothing on soundness.



-/
import Johnson.Desc.First.Close.Kind
import Johnson.Desc.Sound.Tiles
import Fmt.M2Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open VerifiableInference.Desc.Sound (WrittenAs)

/-- The format's rounds of a closing with rows batched rows and k fold rounds, none opening a stored
table. -/
def roundsOf (rows k : ℕ) : List (Fmt.Round × List Fmt.Stored) :=
  (Fmt.M2.rBatN rows, []) :: (Fmt.M1.rEps "FOLD epsilon", []) ::
    List.replicate k (Fmt.M1.rTwo "FOLD round", [])

theorem bat_round (e : List (List ByteArray × ByteArray)) (rows : ℕ) :
    ({ entry := { name := "BAT", work := 0, drawE := 1, rows := rows } } : Fmt.DeclaredRound).round e =
      some (Fmt.M2.rBatN rows) := by
  have hk : Fmt.kindOf "BAT" = some .elems := by decide
  unfold Fmt.DeclaredRound.round
  rw [hk]
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, Fmt.M2.rBatN]

theorem eps_round (e : List (List ByteArray × ByteArray)) :
    ({ entry := { name := "FOLD epsilon", work := 0, msg := 24, drawE := 1 } } :
      Fmt.DeclaredRound).round e = some (Fmt.M1.rEps "FOLD epsilon") := rfl

theorem two_round (e : List (List ByteArray × ByteArray)) :
    ({ entry := { name := "FOLD round", work := 0, msg := 48, drawE := 1 } } :
      Fmt.DeclaredRound).round e = some (Fmt.M1.rTwo "FOLD round") := rfl

/-- **The rounds that the kind declares at a place without proof of work ARE the format's own rounds
"BAT" (at the place's rows), "FOLD epsilon", and k times "FOLD round"**, as the readers take
them. -/
theorem kind_written {Cl : Type} (Q : Par) (e : List (List ByteArray × ByteArray))
    (h1 : Q.workField = 0) (h2 : Q.workClose = 0) :
    WrittenAs e (kind (Cl := Cl) Q).rounds (roundsOf Q.rows Q.k) := by
  show List.Forall₂ _ ((entries Q).map fun x => ({ entry := x } : Fmt.DeclaredRound)) _
  unfold entries roundsOf
  rw [h1, h2]
  simp only [List.map_cons, List.map_replicate]
  refine List.Forall₂.cons ⟨bat_round e Q.rows, rfl⟩ (List.Forall₂.cons ⟨eps_round e, rfl⟩ ?_)
  induction Q.k with
  | zero => exact List.Forall₂.nil
  | succ n ih =>
    rw [List.replicate_succ, List.replicate_succ]
    exact List.Forall₂.cons ⟨two_round e, rfl⟩ ih

theorem kind_rounds_length {Cl : Type} (Q : Par) : (kind (Cl := Cl) Q).rounds.length = 2 + Q.k := by
  show ((entries Q).map _).length = _
  simp only [List.length_map, entries, List.length_cons, List.length_replicate]
  omega

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.kind_written
#print axioms VerifiableInference.Desc.First.Close.kind_rounds_length
