-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5AttentionKind.lean: the kind K5, an attention segment's own rounds, as a block over the
part "the masked sumcheck" (Johnson/Desc/Part/MaskedSum4.lean).

What the kind is for. The prover states values of the segment's committed matrices at random points
and proves, by masked sumchecks, the relations between them: each score is a query times a key; the
output is the weighted sum of the values divided by the softmax denominator; the stated row maximum
is the score at a committed index, whose cells are bits. Nothing is compared in these rounds: every
relation leaves as a linear claim, which a later kind batches.

Main names:
  `Par`: the place's public numbers: the planner's record of these rounds and the policy's bits of work.
    `Par.before`: what is fixed before the draws: the segment's commitments to the matrices of which
    these rounds speak; given by whoever lays the segment.
  `script`, `rounds`: the stages in order (scalars that wait for the next message; a masked sumcheck;
    a batching element; a point), and the rounds made of them.
  `hear`: what the verifier does, stage by stage: it numbers each scalar in the ledger, runs the
    part's hearing, and takes the drawn elements. It hands on the record `Heard` (Att/K5Heard.lean).
  `planOk`: the tests on the plan alone. `decide`, `attentionKind`: the decision and the block, over a seat that
    says where the ledger lies in the carried state.
A refusal bears its test's name: "K5.owed", "K5.ledger", "K5.hear", "K5.left-over", "K5.lay".

`rounds` and `planOk` are folded over `script`; `hear` is typed beside it, stage for stage, and does
not read it. That the two agree is not shown in this file or in what it imports. What a round holds or draws is asked twice: by the general step (Block.step: roundsFit)
and again here, at lines marked so.
Not asked here: that a sent or a drawn word is below the prime (the general fold's); that an element
which an entry counts as drawn "never 0" is not 0 (the general step asks only that its three words are
not all 0). No round stores or opens anything. SENDS: Johnson/Desc/ProofFile/Honest/K5/Row.lean.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.Att.K5Heard
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block named need)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

/-! ## The script -/

/-- A stage of the stretch. -/
inductive Stage where
  /-- n scalars, sent at the front of the next message -/
  | scalars (n : Nat)
  /-- a masked sumcheck: its variables; its ends -/
  | sum (vs : List Var) (e : Ends)
  /-- one element is drawn; its powers batch so many rows -/
  | batch (rows : Nat)
  /-- so many elements are drawn -/
  | point (n : Nat)

/-- A sumcheck of products of two maps: n variables, m pairs of maps. -/
def products (n m : Nat) : Stage := .sum (List.replicate n (.plain 4)) ⟨2, 2 * m⟩

/-- **The stretch, stage by stage.** -/
def script (x : Params.AttentionRounds) : List Stage :=
  let (lgk, lt, NP) := (x.lgk, x.lt, x.pairs)
  List.replicate x.planeMessages (.scalars 3) ++                                 -- the remainder units' values
  x.score.flatMap (fun u => [.scalars 7, products u.1 u.2]) ++                   -- a softmax-table unit: query · key
  [.scalars 5, .scalars lt, .scalars 2, products x.e NP,                         -- denominator × output
   .batch 2, .scalars 2, products x.valueM NP, products x.valueD NP,             -- the value product: below, on the diagonal
   .point (2 * lgk + 2 * lt + 4), .scalars NP, .batch NP, products x.attained NP, -- the score at the index
   .batch NP,
   .sum ((List.replicate lt 3 ++ List.replicate lgk (lt + 3) ++ List.replicate lt (lt + 2)).map .plain)
     ⟨lt + 1, x.Lam + NP * lt⟩,                                                  -- the key at the index
   .batch NP, products x.bits NP]                                                -- the index's cells are bits

/-! ## ROUNDS -/

/-- The stages' entries. lead: the scalars that wait. -/
def entriesOf : Nat → List Stage → List Fmt.Entry
  | _, [] => []
  | lead, .scalars n :: l => entriesOf (lead + n) l
  | lead, .sum vs e :: l => MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l
  | lead, .batch rows :: l => { name := "BAT-sigma", msg := 24 * lead, drawE := 1, rows := rows } :: entriesOf 0 l
  | lead, .point n :: l => MaskedSum.entry "ZERO" lead n 0 :: entriesOf 0 l

structure Par where
  /-- the segment's number in the first chain; the block's number inside it -/
  link : Nat
  piece : Nat
  /-- the policy's bits of work at a round that draws field elements -/
  work : Nat
  /-- the planner's record of these rounds -/
  own : Params.AttentionRounds
  /-- the oracle messages that must have been sent before the first draw: (chain, number of sending) -/
  before : List (Nat × Nat)

/-- ROUNDS: a round that draws bears the policy's work. -/
def rounds (p : Par) : List Fmt.DeclaredRound :=
  (entriesOf 0 (script p.own)).map fun e => { entry := if e.drawE == 0 then e else { e with work := p.work } }

/-- TESTS ON THE PLAN ALONE. -/
def planOk (p : Par) : Bool :=
  !p.own.score.isEmpty && p.own.pairs != 0 &&
    (script p.own).all fun
      | .sum vs e => MaskedSum.shapeOk ⟨0, vs, some e⟩
      | _ => true

/-! ## DECIDES -/

/-- While hearing: the ledger, the rounds not yet used up, and how many items of the first are taken (the lead). -/
abbrev M := StateT (Fork × List Fmt.RoundView × Nat) Option

/-- n waiting scalars get the next n numbers. Returns the first. -/
def take (n : Nat) : M Nat := fun (F, rs, lead) =>
  match rs with
  | [] => none
  | r :: _ => do
    let v ← MaskedSum.scalars ((r.vals.drop lead).take n)
    guard (v.length == n)                                                        -- also asked by roundsFit
    let G ← ({ F with next := F.next + n } : Fork).hideRun F.next v.toArray oneE
    pure (F.next, G, rs, lead + n)

/-- A masked sumcheck from the start form C; its hiding polynomial's coefficients are put under their numbers. -/
def sum (C : Aff) (st : Stage) : M MaskedSum.Heard := fun (F, rs, lead) =>
  match st with
  | .sum vs e => do
    let k := vs.length + 3
    let (h, G) ← MaskedSum.hear C ⟨lead, vs, some e⟩ F (rs.take k)
    let (_, G) ← MaskedSum.row h zeroE {} G
    pure (h, G, rs.drop k, 0)
  | _ => none

/-- The round is closed: all its items are taken; n elements were drawn. -/
def close (n : Nat) : M (List E) := fun (F, rs, lead) =>
  match rs with
  | r :: rest =>
    if r.vals.length == lead && r.drawn.elems.length == n then                   -- both also asked by roundsFit
      some (r.drawn.elems.map E.ofTriple, F, rest, 0)
    else none
  | [] => none

/-- The powers, from power 0, of the batching element. -/
def batch (rows : Nat) : M (Array E) := do
  match ← close 1 with
  | [x] => pure (MaskedSum.powersFrom x rows oneE).toArray
  | _ => failure

/-- The form Σ_b w_b · (scalar number first + step · b + off), over n members. -/
def batched (n : Nat) (w : Array E) (first step off : Nat) : Aff :=
  (List.range n).foldl (fun a b => a.addMul (.slot (first + (step * b + off))) (w.getD b zeroE)) (.ofConst zeroE)

/-- **What the verifier does while it hears.** -/
def hear (x : Params.AttentionRounds) : M Heard := do
  let (lgk, lt, NP) := (x.lgk, x.lt, x.pairs)
  let remainders ← (Array.range x.planeMessages).mapM fun _ => take 3
  let scores ← x.score.toArray.mapM fun u => do
    let seven ← take 7
    pure (seven, ← sum (.slot (seven + 6)) (products u.1 u.2))
  let five ← take 5
  let bits ← take lt
  let two ← take 2
  let division ← sum (.slot (five + 1)) (products x.e NP)
  let gam ← batch 2
  let values ← take 2
  let below ← sum (.slot values) (products x.valueM NP)
  let on ← sum (.slot (values + 1)) (products x.valueD NP)
  let point ← close (2 * lgk + 2 * lt + 4)
  let maxima ← take NP
  let om ← batch NP
  let atIndex ← sum (batched NP om maxima 1 0) (products x.attained NP)
  let om' ← batch NP
  let key ← sum (batched NP om' atIndex.sEnd 2 1)
    (.sum ((List.replicate lt 3 ++ List.replicate lgk (lt + 3) ++ List.replicate lt (lt + 2)).map .plain) ⟨lt + 1, x.Lam + NP * lt⟩)
  let om'' ← batch NP
  let cells ← sum (.ofConst zeroE) (products x.bits NP)
  pure { remainders, scores, five, bits, two, division, gam, values, below, on, point := point.toArray, maxima, om,
         atIndex, om', key, om'', cells }

/-! ## The block -/

/-- What K5 takes of the state, and what it lays back. -/
structure Seat (S : Type) where
  ledger : S → Option Fork
  /-- the rows that the round closed last still owes -/
  owed : S → Option Nat
  lay : S → Heard → Fork → Option S

/-- DECIDES: nothing waits in front; the hearing; the stretch is used up. -/
def decide {S : Type} (seat : Seat S) (p : Par) (s : S) (rs : List Fmt.RoundView) : Except String S := do
  need "K5.owed" (seat.owed s).isNone
  let F ← named "K5.ledger" (seat.ledger s)
  let (h, G, rest, _) ← named "K5.hear" (hear p.own (F, rs, 0))
  need "K5.left-over" rest.isEmpty
  named "K5.lay" (seat.lay s h G)

/-- **K5.** -/
def attentionKind {S Cl : Type} (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) :
    Block S Cl :=
  { name := s!"an attention segment's own rounds, segment {p.link}"
    place := ⟨1, some p.link, p.piece, .K5⟩
    planOk := planOk p
    rounds := rounds p
    oracles := (rounds p).map fun _ => []
    before := p.before
    decide := fun s rs _ => decide seat p s rs
    claims := claims
    after := [] }

end VerifiableInference.Desc.First.Att.P
