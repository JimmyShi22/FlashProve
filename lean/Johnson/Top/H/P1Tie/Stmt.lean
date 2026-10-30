-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Stmt.lean: the tie of the two texts of the masked sumcheck: the statements.
Definitions alone: each statement is a proposition with a name (`Spec.…`). Nothing is proved in this
file.

The statements by number: (1) `whole_cut`: the part's yes gives the flat course; (2) `cut_whole`:
the flat course gives the part's yes; (3a) `hear_open` and (3b) `open_hear`: the same two ways for a
sumcheck that is left open. Where the proofs stand: `whole_cut` in Johnson/Top/H/P1Tie/Tie1.lean;
`cut_took` and `cut_whole` in Johnson/Top/H/P1Tie/Tie2.lean; `hear_open`, `open_hear` and `tape_is`
in Johnson/Top/H/P1Tie/Tie3.lean; the two members that decide nothing in
Johnson/Top/H/P1Tie/Silly.lean. Beneath them: Johnson/Top/H/P1Tie/Words.lean (the words),
Johnson/Top/H/P1Tie/FlatMk.lean (the flat steps on a written-out tape),
Johnson/Top/H/P1Tie/Part.lean (where the part's functions return).

The two texts: the part's own (Johnson/Desc/Part/MaskedSum4.lean: `whole`, `hear`, on the rounds of
a view) and the flat functions of the library (OnBytes/K/Kc/Flat.lean: `Fl.pscBegin`, `Fl.roundIn`,
`Fl.pscEnds`, `Fl.pscRow`, on a tape), the second as the course `WholeCut`
(Johnson/Top/H/Cut/CutWhole.lean). Each statement says: where the one says yes, so does the other,
with the same record, the same row and the same ledger, as machine words. No premise says that a
word is below the prime (why none is needed: Johnson/Top/H/P1Tie/Words.lean).

What the tape must be. `IsTape rs t`: round for round, the tape's round holds the view's round's
items as scalars and its drawn elements, unturned. Of the three words of the plan's entry that a
tape's round bears (name; number of never-0 draws; rows) it says nothing. `Named k t`: the rounds
bear the names and the numbers of never-0 draws of the call's own entries (`entries k`). The rows
are free: no flat function of a sumcheck reads them. From the part's yes to the flat course both are
premises; from the flat course to the part's yes `IsTape` alone: the flat functions have tested the
names. `Spec.tape_is`: the strict maker of a tape (`tapeT`, Johnson/Desc/First/Tape/Tape.lean) gives
such a tape, with the entries' names and numbers.

Limits. Calls without a lead alone; variables summed at a point alone; with ends: three coefficients
a variable (the stand-in's own bound: `stepW` is `Fl.roundIn .eq2`). In `Spec.cut_whole` the end
term must read the first n end values alone (`ReadsFirst`): `WholeCut` says of its list of end
values no more than these. The part's `whole` does not ask that no position or matrix entry is
drawn, or that Y's draw is not 0: so its yes does not give `tapeT`'s yes: that needs the caller's
tests (the level of Johnson/Desc/First/ProdV/Level.lean; `sumV` of
Johnson/Desc/First/Look/Via/Rounds.lean). A tie has no error term.
The statements tried at members that decide nothing: (1) and (2) are said of a letter W in `whole`'s
place (`WholeCutOf`, `CutWholeOf`). A W that says yes to all fails (1): a theorem
(Johnson/Top/H/P1Tie/Silly.lean): at three rounds that send nothing, on their named tape,
`Fl.pscBegin` finds no sum to receive. A W that says no to all meets (1) idly and fails (2) wherever
the flat course returns on the tape of some rounds: a theorem with that as its premise; that the
premise is met no theorem says. For (3a) and (3b) the like is not stated.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Words
import Johnson.Top.H.Cut.CutWhole
import Johnson.Desc.First.Tape.Tape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork Psc)
open VerifiableInference.Desc.First.Prod (Whole)
open VerifiableInference.Desc.K3Cut (WholeCut)

/-- x is the tape's round of the view's round r: the same scalars, the same draws, unturned. -/
def IsRound (r : Fmt.RoundView) (x : FlatRound) : Prop :=
  scalars r.vals = some x.sent ∧ x.drawn = r.drawn.elems.map E.ofTriple

/-- t is the tape of the rounds rs: round for round; as many. -/
def IsTape : List Fmt.RoundView → Tape → Prop
  | [], [] => True
  | r :: rs, x :: t => IsRound r x ∧ IsTape rs t
  | _, _ => False

/-- What a flat function tests of the plan's entry: the name, and the number of never-0 draws. -/
def keyOf (x : FlatRound) : Option String × Nat := (x.name, x.nz)

/-- The tape's rounds bear the names and the numbers of never-0 draws of the call's own entries. -/
def Named (k : Call) (t : Tape) : Prop := t.map keyOf = (entries k).map fun e =>
    (some e.name, e.drawNZ)

/-- The call that the stand-in makes: no lead; a variable for each coordinate, three coefficients
each; ends. -/
def callOf (zs : List E) (dY n : Nat) : Call :=
  { lead := 0, vs := zs.map fun z => Var.point z 3, ends := some ⟨dY, n⟩ }

/-- The call of a sumcheck that is left open: no lead; for each pair a variable summed at the
coordinate, of that degree. -/
def openCall (zs : List (E × Nat)) : Call :=
  { lead := 0, vs := zs.map fun x => Var.point x.1 (x.2 + 1), ends := none }

/-- The end term reads the first n end values alone. -/
def ReadsFirst (n : Nat) (e : List E → E) : Prop :=
  ∀ l l' : List E, (∀ i, i < n → l.getD i zeroE = l'.getD i zeroE) → e l = e l'

namespace Spec

/-- The type of `whole`. -/
abbrev WholeT : Type :=
  Aff → Call → (List E → List E → E) → Fork → List Fmt.RoundView → Option (Heard × Aff × Fork)

/-- (1), of a letter W in `whole`'s place. -/
def WholeCutOf (W : WholeT) : Prop :=
  ∀ (C : Aff) (zs : List E) (dY n : Nat) (e : List E → E) (F G : Fork) (rs : List Fmt.RoundView)
    (h : Heard) (row : Aff)
    (t u : Tape),
    W C (callOf zs dY n) (fun _ sh => e sh) F rs = some (h, row, G) → IsTape rs t →
      Named (callOf zs dY n) t →
      WholeCut C zs dY n e F (t ++ u) ⟨h.r, h.sEnd, row⟩ G u

/-- **(1) The part's yes gives the flat course.** -/
def whole_cut : Prop := WholeCutOf whole

/-- (2), of a letter W in `whole`'s place. -/
def CutWholeOf (W : WholeT) : Prop :=
  ∀ (C : Aff) (zs : List E) (dY n : Nat) (e : List E → E) (F G : Fork) (rs : List Fmt.RoundView)
    (w : Whole) (t u : Tape),
    ReadsFirst n e → IsTape rs t → WholeCut C zs dY n e F (t ++ u) w G u →
      ∃ h : Heard, W C (callOf zs dY n) (fun _ sh => e sh) F rs = some (h, w.row, G) ∧
        h.r = w.challenges ∧ h.sEnd = w.sEnd

/-- **(2) The flat course gives the part's yes**: the same challenges, end slot, row and ledger. -/
def cut_whole : Prop := CutWholeOf whole

/-- **How much of the tape the flat course takes.** -/
def cut_took : Prop :=
  ∀ (C : Aff) (zs : List E) (dY n : Nat) (e : List E → E) (F G : Fork) (T : Tape) (w : Whole)
    (u : Tape),
    WholeCut C zs dY n e F T w G u → ∃ t : Tape, T = t ++ u ∧ t.length = zs.length + 3

/-- **(3a) A sumcheck left open: the part's yes gives the flat beginning and rounds**, with the
record of what was heard, as the program `verify-on-bytes` keeps it. -/
def hear_open : Prop :=
  ∀ (C : Aff) (zs : List (E × Nat)) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard) (t u : Tape),
    hear C (openCall zs) F rs = some (h, G) → IsTape rs t → Named (openCall zs) t →
      ∃ (p0 : Psc) (F0 : Fork) (t0 : Tape), Fl.pscBegin C F (t ++ u) = some (p0, F0, t0) ∧
        Fl.roundsIn .eq p0 zs F0 t0 = some ((h.r.toArray, h.psc false), G, u)

/-- **(3b) The converse.** There is a variable at least: the part refuses a call without a variable
and without ends. -/
def open_hear : Prop :=
  ∀ (C : Aff) (zs : List (E × Nat)) (F G : Fork) (rs : List Fmt.RoundView) (t u : Tape) (p0 : Psc)
    (F0 : Fork) (t0 : Tape)
    (r : Array E) (p : Psc),
    zs ≠ [] → IsTape rs t → Fl.pscBegin C F (t ++ u) = some (p0, F0, t0) →
      Fl.roundsIn .eq p0 zs F0 t0 = some ((r, p), G, u) →
      ∃ h : Heard, hear C (openCall zs) F rs = some (h, G) ∧ h.r.toArray = r ∧ h.psc false = p

/-- **The strict maker's tape is such a tape**, and bears its entries' names and numbers. -/
def tape_is : Prop :=
  ∀ (rule : First.Tape.TapeRule) (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    First.Tape.tapeT rule rs es = some t →
      IsTape rs t ∧ t.map keyOf = es.map fun e => (some e.name, e.drawNZ)

end Spec

end VerifiableInference.Desc.Part.MaskedSum
