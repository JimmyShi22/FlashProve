-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumMore.lean: the masked sumcheck's short text
(Johnson/Desc/Part/MaskedSum4.lean): WHAT ITS CALLERS ASKED FOR
BESIDE IT. IT TURNS NO LINE OF THAT TEXT: it imports it and adds names to its namespace. Definitions with code. No theorem.
On six things that a calling kind (K6) asks for:
  1. `row` ties the form to a writing into the ledger  ->  `rowLaid` (the writing) and `rowForm` (the form, pure). THEY SAY
     `row`'s LINES A SECOND TIME. That `row` is the two in a row is held by evaluation (a harness file that is not in this library), not by the making.
  2. `Heard` has no default and no ==                  ->  the two instances; == for Var, Ends, Call too.
  3. beta rides last in r                               ->  `challenges`, `betaOf`: projections, over the Call.
  4. `entries` leaves the work bits 0                   ->  `entriesW work`: the one number on every round that draws. In the
     program `verify-on-bytes`'s planner the three kinds of round that draw are priced alike, as errors of the field,
     and "PSC values" has none (OnBytes/Params/Planner.lean: close ... .field; closeNone).
  5. beta is not 0: NOT MET HERE, AND NOT OURS TO DECIDE. It is no test on what the prover sends: it is the entry's rule of
     drawing (never0 = 1 in `entries`). Whose test it could be: the strict reading's of a round against its entry, once for
     all kinds; or each caller's.
  6. the caller must look at the lead without taking the round  ->  `leadScalars`, in the text itself.

-/
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork)

/-! ## 1. The row in two -/

/-- The writing of `row`: H's coefficients are laid under the sumcheck's own slots: 0 shown, the factor -1. -/
def rowLaid (h : Heard) (F : Fork) : Option Fork :=
  F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE)

/-- The form of `row`: it reads no ledger. -/
def rowForm (h : Heard) (S0 : E) (kept : Aff) : Aff :=
  let (u, P) := hidingAt (h.vars.zip h.r)
  let f := Aff.ofConst (subE zeroE (subE h.claim (mulE h.eps S0)))                  -- - (c - eps S0)
  let f := onSlots f h.first u                                                      -- + <u(r), H's coefficients>
  let f := Aff.addMul f (Aff.ofConst h.target - h.start) (mulE h.eps P)             -- + eps P (T - C)
  Aff.addMul f kept h.eps                                                           -- + eps kept

/-! ## 2. A default and == -/

deriving instance BEq for Var, Ends, Call

/-- Two forms are written alike: the same terms in the same order. (Not: they are equal as forms.) -/
def sameForm (a b : Aff) : Bool :=
  (a.ents.map fun x => (x.tree, x.row, x.idx, x.coef)) == (b.ents.map fun x => (x.tree, x.row, x.idx, x.coef)) &&
    a.slots == b.slots && a.const == b.const

instance : BEq Heard :=
  ⟨fun a b => sameForm a.start b.start && a.target == b.target && a.eps == b.eps && a.claim == b.claim &&
    a.first == b.first && a.vars == b.vars && a.r == b.r && a.sEnd == b.sEnd⟩

instance : Inhabited Heard :=
  ⟨{ start := {}, target := zeroE, eps := zeroE, claim := zeroE, first := 0, vars := [], r := [], sEnd := 0 }⟩

/-! ## 3. The challenges without beta -/

/-- The variables' challenges, in the order of the rounds. -/
def challenges (k : Call) (h : Heard) : List E := h.r.take k.vs.length

/-- beta, where there are ends. -/
def betaOf (k : Call) (h : Heard) : Option E := if k.ends.isSome then h.r.getLast? else none

/-! ## 4. ROUNDS with the work bits -/

/-- ROUNDS, as entries of the plan, with the given bits of work on every round that draws. -/
def entriesW (work : Nat) (k : Call) : List Fmt.Entry :=
  (entries k).map fun e => if e.drawE == 0 then e else { e with work := work }

end VerifiableInference.Desc.Part.MaskedSum
