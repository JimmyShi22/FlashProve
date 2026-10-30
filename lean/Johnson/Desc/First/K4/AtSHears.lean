-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/AtSHears.lean: FROM THE YES OF K4's BLOCK AT THE CARRIED RECORD TO WHAT K4's
HEARING RETURNED, ON THE TAPE OF THE ROUNDS SHOWN. Statements and proofs. It is K4's half of the
road from a piece's yes (`p.ior.red.out a τ = some a'`) to the plain function `hearFl`: the other
half is general in the block (from a piece's yes to its block's `decide`'s yes).

`blockAtS_hears`: where `(blockAtS p).decide s rs cols` returns s': the chain stands in a layers'
link a; no row is owed; the lookup's return fo is laid; the rounds shown fit K4's own table of
rounds and pass the strict reading; `hearFl` AT THE PLACE's PUBLIC PARAMETERS, WITH THE REQUEST's
TOKENS OFF THE RECORD, FROM THE LINK's LEDGER, ON THE TAPE `paired rs (entries …)`, RETURNS (o, G,
[]): it uses the tape up; and s' is s with the ledger G and o laid in the link, and no row owed. All
else of s is untouched.
`bare_decide`: the block without its claims decides alike.

It joins `decide_ok` (Johnson/Desc/First/K4/BlockLaws.lean) and the seat
(Johnson/Desc/First/K4/AtS.lean). One direction, from a yes. An equation on what texts return: no
error term. Nothing on soundness.
-/
import Johnson.Desc.First.K4.BlockLaws
import Johnson.Desc.First.K4.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)

/-- The block without its claims decides alike. -/
theorem bare_decide {T Cl Cl' : Type} (b : VerifiableInference.Desc.Block T Cl) :
    (bare (Cl' := Cl') b).decide = b.decide := rfl

/-- **From the block's yes at the carried record to the hearing's return.** -/
theorem blockAtS_hears {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    ∃ (a : LayOwn) (fo : Forest.Heard) (o : Own) (G : Fork),
      s.here = .lay a ∧ (if s.noneWaits then none else s.rowsOwed).isNone = true ∧
      a.fo = some fo ∧
      fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true ∧
      Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true ∧
      hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F (paired rs (entries p.P p.hp p.g)) =
        some (o, G, []) ∧
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } := by
  have h' : ((named "the part is not there" (part? s)).bind fun q =>
      ((block seatOwn p).decide q rs cols).map (setPart s)) = .ok s' := h
  cases hq : part? s with
  | none => simp [hq, named, Except.bind] at h'
  | some q =>
    cases hd : (block seatOwn p).decide q rs cols with
    | error e => simp [hq, named, Except.bind, hd, Except.map] at h'
    | ok q' =>
      simp only [hq, named, Except.bind, hd, Except.map, Except.ok.injEq] at h'
      obtain ⟨d1, d2, d3, fo, o, G, d4, d5, d6⟩ := decide_ok seatOwn hd
      cases hs : s.here with
      | lay a =>
        have hq1 : q = (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
          simp only [part?, hs, Option.some.injEq] at hq
          exact hq.symm
        subst hq1
        refine ⟨a, fo, o, G, rfl, d1, d4, d2, d3, d5, ?_⟩
        rw [← h', d6]
        rfl
      | between => simp [part?, hs] at hq
      | att _ => simp [part?, hs] at hq
      | head _ => simp [part?, hs] at hq
      | fin _ => simp [part?, hs] at hq
      | mem _ => simp [part?, hs] at hq

end OnBytes.Desc.First.K4
