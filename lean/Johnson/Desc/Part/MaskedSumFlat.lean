-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumFlat.lean: THE PART "THE MASKED SUMCHECK": ITS TEXT AND THE FLAT TEXT OF
THE SAME SUMCHECK, TIED: STATEMENTS ALONE: two definitions, and five statements, each a definition
of a proposition. NOTHING IS PROVED IN THIS FILE (the proofs: Johnson/Desc/Part/
MaskedSumFlatProofs.lean), and none of the five is one of the library's goals: they are lemmas'
statements. No kind is named, and no prover: both texts are the verifier's.

Why. The verifier's masked sumcheck stands in the library in more than one text. A law that is
stated against the part's text (Johnson/Desc/Part/MaskedSum4.lean: `hear`, `row`) does not reach a
kind whose own text calls the flat functions (OnBytes/K/Kc/Flat.lean: `Fl.pscBegin`, `Fl.pscRound`,
`Fl.pscEnds`, `Fl.pscRow`), which keep the older record `Psc` (OnBytes/Model/Psc.lean). These
statements carry such a law over: the value of the row that is left, and the ledger behind it.

  `SameLetters p h`  a flat record p and a record h of the part's text hold the same claimed form,
                     public target, eps, first slot, variables and challenges; their two running
                     claims read alike. The end values' slot and the flat record's three flags are
                     not compared.
  `heardAs`          the part's record, written of what was heard. (What `hear` hands back is said
                     by `hear_spec`, Johnson/Desc/Part/MaskedSumShape.lean, with all variables and
                     all rounds in one list each: a caller splits the last off.)
  `FlatEnded`        a flat record that has ended (`Ended`, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean) has
                     the letters of `heardAs` at the same letters. `Ended` speaks of a call WITH end
                     values alone. It does not hold how many scalars a round sent: the premise
                     `LensT` the caller brings from its own hearing.
  `FlatRowTie`       records with the same letters leave rows of one value, in every world.
  `FlatRowLaid`      at such records `Fl.pscRow` returns just where `row` returns, with the same
                     ledger behind. Its four premises on the flat record's flags and sizes the
                     caller brings from its own hearing too.
  `FlatWeight`       every weight that the flat text makes of a round's form is a variable's weight
                     (`Var.weight`, Johnson/Desc/Part/MaskedSumTie.lean).
  `FlatWeights`      so a list of such weights is `vs.map Var.weight` for some variables vs: the
                     form in which `FlatEnded` takes a flat record's weights.

Every equation between values is an equation between readings (`Reading K`,
OnBytes/Model/HideLaws.lean): the two texts complete a round's polynomial by other terms.
Beneath them, proved, in Johnson/Desc/Part/MaskedSumTie.lean: `complete_read`, `after_read`,
`hidingAt_read`, `zip_weight`, `row_spec`, `rowAff_value`; in OnBytes/Model/HideLaws.lean:
`Psc.rowForm_value`.

Limits. Nothing on the flat hearing's return: that is each kind's own. Nothing on soundness, on an
honest prover or on any property.

-/
import Johnson.Desc.Part.MaskedSumTie
import Johnson.Desc.Part.MaskedSumMore
import OnBytes.Tie.Pv.Psc.Run.PscSeam
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes (E addE mulE zeroE)
open OnBytes.Model (Reading World Aff Fork Psc RoundForm)
open OnBytes.Model.Road (Ended)
open OnBytes.K.Kc (Fl Tape weightT)

/-- A record of the flat text and a record of the part's text hold the same letters. -/
structure SameLetters (p : Psc) (h : Heard) : Prop where
  start : p.start = h.start
  target : p.target = h.target
  eps : p.eps = h.eps
  first : p.first = h.first
  vars : p.vars.toList = h.vars.map Var.weight
  r : p.r.toList = h.r
  /-- the two running claims, as they are read -/
  claim : ∀ (K : Type) [CommRing K] (ρ : Reading K), ρ.val p.claim = ρ.val h.claim

/-- The part's record of what was heard. C: the claimed sum; τ: its public part; mu: the hiding
polynomial's sum; vs: the variables in front of the further one; rs: for each what was sent and the
challenge; dY, sentY, beta: the further variable's degree, what was sent, the challenge. -/
def heardAs (C : Aff) (τ mu eps : E) (first : Nat) (vs : List Var) (rs : List (List E × E))
    (dY : Nat) (sentY : List E) (beta : E) : Heard :=
  { start := C, target := τ, eps := eps
    claim := after (vs ++ [.point zeroE (dY + 1)]) (rs ++ [(sentY, beta)]) (addE mu (mulE eps τ))
    first := first, vars := vs ++ [.point zeroE (dY + 1)], r := rs.map (·.2) ++ [beta]
    sEnd := first + ownSlots (vs ++ [.point zeroE (dY + 1)]) }

/-- The statement that a flat record which has ended holds the letters of the part's record of what
was heard, where each round sent as many scalars as its variable asks. Not proved here; a lemma's
statement, none of the library's goals. -/
def FlatEnded : Prop :=
  ∀ (p : Psc) (C : Aff) (τ mu eps : E) (first : Nat) (vs : List Var) (rs : List (List E × E))
    (dY : Nat) (sentY : List E) (beta : E),
    Ended p C τ mu eps first (vs.map Var.weight) rs dY sentY beta →
    LensT (vs ++ [.point zeroE (dY + 1)]) (rs ++ [(sentY, beta)]) →
    SameLetters p (heardAs C τ mu eps first vs rs dY sentY beta)

/-- The statement that records with the same letters leave rows of one value in every world. Not
proved here; a lemma's statement, none of the library's goals. -/
def FlatRowTie : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K) (p : Psc) (h : Heard) (S0 : E)
    (kept : Aff), SameLetters p h →
    (p.rowForm S0 kept).value ρ W = (rowForm h S0 kept).value ρ W

/-- The statement that, at records with the same letters, the flat text's row is made just where the
part's is, and leaves the same ledger: where the flat record is begun, its row is not yet made, and
it has a challenge for each of its variables, of which there is one at least. t: whatever is left of
the tape, which stays. Not proved here; a lemma's statement, none of the library's goals. -/
def FlatRowLaid : Prop :=
  ∀ (p : Psc) (h : Heard) (S0 : E) (kept : Aff) (F G : Fork) (t : Tape), SameLetters p h →
    p.started = true → p.rowMade = false → p.vars.isEmpty = false → p.r.size = p.vars.size →
    (Fl.pscRow p S0 kept F t = some ((p.rowForm S0 kept, { p with rowMade := true }), G, t) ↔
      row h S0 kept F = some (rowForm h S0 kept, G))

/-- The statement that every weight which the flat text makes of a round's form is a variable's
weight. Not proved here; a lemma's statement, none of the library's goals. -/
def FlatWeight : Prop :=
  ∀ (form : RoundForm) (z : E) (d : Nat) (w : OnBytes.Psc.Weight),
    weightT form z d = some w → ∃ v : Var, w = v.weight

/-- The statement that a list of weights, each of which the flat text makes of a round's form, is
the list of some variables' weights. Not proved here; a lemma's statement, none of the library's
goals. -/
def FlatWeights : Prop :=
  ∀ ws : List OnBytes.Psc.Weight,
    (∀ w ∈ ws, ∃ (form : RoundForm) (z : E) (d : Nat), weightT form z d = some w) →
    ∃ vs : List Var, ws = vs.map Var.weight

end VerifiableInference.Desc.Part.MaskedSum
