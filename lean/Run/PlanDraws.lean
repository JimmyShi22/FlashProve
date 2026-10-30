-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanDraws.lean: a round's verifier message as a function of the plan's entry and the round's
kind: its type, its block sampler and the sampler's bias. Seen through the untyped view, the
sampler is the format's own function on the bytes of the blocks.
(docs/format/FORMAT.md, section 6: R6.2, R6.9 to R6.11, as Fmt/Rules6*.lean render them;
not held against that page.)

This file is about how one round's verifier message is made from blocks of 256 bits. Definitions,
statements (each a `Prop` in `Run.Spec`) and proofs.
A plan (`Fmt.Plan`, Fmt/Plan.lean) has a list of entries (`Fmt.Entry`), one for a round or a run of
like rounds. An entry says, among other numbers, how many elements, positions and matrix entries
the verifier draws. The kind (`Fmt.Kind`, same file) says what a round's verifier message consists
of; it is no field of an entry.
A block sampler (`Iop.BS`, Iop/Draw.lean) is a function from b blocks to the values, with a bound
on its fibres. Under its law `BS.Good s κ` one value of a finite type of values takes at most κ
times its even share of all tuples of b blocks: κ bounds the bias.

The type of a round's verifier messages is the values of its draws: `Vals f (Fmt.dsOf e k)`, a
nested product by recursion on the list of draws that the entry e and the kind k give
(Fmt/Rules6Draws.lean). These values are: numbers below 2^logN; triples of numbers below p; such
triples other than 0 for the elements that must not be 0; pairs of bits for the matrix entries;
four words for a sealing. On this type "uniform" is what the protocol means: a matrix entry (0 with
probability 1/2, 1 and -1 with 1/4 each) is a function of its pair of bits, and an element that
must not be 0 is not 0 by its type.

Main names:
  Instances for `DVal` and `Vals`, by recursion. (They compute; nobody should evaluate a list of
    all values of a field.)
  `drawnOf f e k v`: the untyped view: the format's record of what a round draws (`Fmt.Drawn`:
    elements, positions as drawn, matrix entries, the sealed digest).
  `bsRound f e k`: the block sampler: `bsOf` at the entry's draws.
  `Spec.planDraws_law`: logN ≤ 64 ⇒ `(bsRound f e k).Good (kapSl 128 ^ b)`, and b =
    `Fmt.blocksFor (Fmt.wordsAtMost e k)`: the blocks that the plan fixes for the round (R6.11).
    `kapSl 128` (Iop/DrawOf.lean) is 1 + 2^-128.
  `Spec.planDraws_tie`: the sampler on whose bias a bound is proved (for logN ≤ 64:
    `Spec.planDraws_law`), seen through the view, is the format's `drawRound` on the words read off
    the blocks' bytes (`rowOfDigs`, Run/ToyChal.lean).

Limits: this file says nothing on the shape of a protocol from a plan, or on its samplers round by
round: the shape stands in Run/PlanQTypes.lean (`PQ.shapeOf`), the samplers in Run/PlanDrawsQ.lean
(`drawsQ`).
It does not say that an entry is one of the format's. R6.2 rules which draws a kind may have;
`dsOf` is total and gives a list for every entry.

Terms: lean/GLOSSARY.md.
-/
import Run.DrawPlan
import Run.ToyChalLaw
import Fmt.Rules6Draws

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

instance fintypeDVal (f : _root_.Fmt.Fld) : (d : _root_.Fmt.Draw) → Fintype (DVal f d)
  | .elem => inferInstanceAs (Fintype (EV f))
  | .elemNZ => inferInstanceAs (Fintype (NZ f))
  | .pos k => inferInstanceAs (Fintype (Fin (2 ^ k)))
  | .trits n => inferInstanceAs (Fintype (Fin n → Bool × Bool))
  | .sealed => inferInstanceAs (Fintype (Fin 4 → UInt64))

instance decDVal (f : _root_.Fmt.Fld) : (d : _root_.Fmt.Draw) → DecidableEq (DVal f d)
  | .elem => inferInstanceAs (DecidableEq (EV f))
  | .elemNZ => inferInstanceAs (DecidableEq (NZ f))
  | .pos k => inferInstanceAs (DecidableEq (Fin (2 ^ k)))
  | .trits n => inferInstanceAs (DecidableEq (Fin n → Bool × Bool))
  | .sealed => inferInstanceAs (DecidableEq (Fin 4 → UInt64))

/-- a value of each draw -/
def dfltDVal (f : _root_.Fmt.Fld) : (d : _root_.Fmt.Draw) → DVal f d
  | .elem => (zF f, zF f, zF f)
  | .elemNZ => oE f
  | .pos k => ⟨0, Nat.two_pow_pos k⟩
  | .trits _ => fun _ => (false, false)
  | .sealed => fun _ => 0

instance fintypeVals (f : _root_.Fmt.Fld) : (ds : List _root_.Fmt.Draw) → Fintype (Vals f ds)
  | [] => inferInstanceAs (Fintype Unit)
  | d :: ds => haveI := fintypeVals f ds; inferInstanceAs (Fintype (DVal f d × Vals f ds))

instance decVals (f : _root_.Fmt.Fld) : (ds : List _root_.Fmt.Draw) → DecidableEq (Vals f ds)
  | [] => inferInstanceAs (DecidableEq Unit)
  | d :: ds => haveI := decVals f ds; inferInstanceAs (DecidableEq (DVal f d × Vals f ds))

def dfltVals (f : _root_.Fmt.Fld) : (ds : List _root_.Fmt.Draw) → Vals f ds
  | [] => ()
  | d :: ds => (dfltDVal f d, dfltVals f ds)

instance neVals (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) : Nonempty (Vals f ds) :=
  ⟨dfltVals f ds⟩

/-- The type of a round's verifier messages. -/
abbrev Ch (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) : Type :=
  Vals f (_root_.Fmt.dsOf e k)

/-- The untyped view. -/
def drawnOf (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (v : Ch f e k) :
    _root_.Fmt.Drawn :=
  _root_.Fmt.collect (outAll f (_root_.Fmt.dsOf e k) v)

/-- The block sampler of the round. -/
def bsRound (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) : BS 256 (Ch f e k) :=
  bsOf f (_root_.Fmt.dsOf e k)

namespace Spec

def planDraws_law : Prop :=
  ∀ (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind), e.logN ≤ 64 →
    (bsRound f e k).Good (kapSl 128 ^ (bsRound f e k).b) ∧
    (bsRound f e k).b = _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost e k)

def planDraws_tie : Prop :=
  ∀ (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry)
      (k : _root_.Fmt.Kind) (u : Fin (bsRound f e k).b → Dig 256),
    drawnOf f e k ((bsRound f e k).φ u) = _root_.Fmt.drawRound f e k (rowOfDigs u)

end Spec

/-- no position among the draws of a round's elements -/
theorem pos_not_elems (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (k' : ℕ) :
    _root_.Fmt.Draw.pos k' ∉ _root_.Fmt.dsElems e k := by
  unfold _root_.Fmt.dsElems _root_.Fmt.dsSeeds
  split <;> simp [List.mem_replicate, List.mem_flatten]

theorem lawful_dsOf (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (h : e.logN ≤ 64) :
    ∀ d ∈ _root_.Fmt.dsOf e k, Lawful d := by
  intro d hd
  cases d with
  | pos k' =>
    show k' ≤ 64
    unfold _root_.Fmt.dsOf at hd
    rcases List.mem_append.1 hd with h1 | h1
    · have := (List.mem_replicate.1 h1).2
      cases this
      exact h
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact absurd h2 (pos_not_elems e k k')
      · rcases List.mem_cons.1 h2 with h3 | h3
        · cases h3
        · split at h3
          · rcases List.mem_cons.1 h3 with h4 | h4
            · cases h4
            · cases h4
          · cases h3
  | elem => trivial
  | elemNZ => trivial
  | trits n => trivial
  | sealed => trivial

theorem planDraws_law : Spec.planDraws_law := fun f e k h =>
  ⟨(drawPage_bs f _ (lawful_dsOf e k h)).1,
    (drawPage_bs f _ (lawful_dsOf e k h)).2.trans
      (congrArg _root_.Fmt.blocksFor (_root_.Fmt.most_list e k))⟩

theorem planDraws_tie : Spec.planDraws_tie := by
  intro f e k u
  show _root_.Fmt.collect (outAll f (_root_.Fmt.dsOf e k) ((bsOf f (_root_.Fmt.dsOf e k)).φ u)) =
    (_root_.Fmt.drawRoundD f e k (rowOfDigs u) 0).1
  rw [bs_bytes f (_root_.Fmt.dsOf e k) u, _root_.Fmt.round_list f e k (rowOfDigs u) 0]
  rfl

end Run
