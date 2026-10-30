-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinAtSet.lean: the join of three checkers for a verifier that asks the oracle for
values which the three parts hold as constants.

OnBytes/Slice/JoinId.lean (`join_id`) takes three parts, a reading `key` of the prover's output and
an event `Yes`, and asks `hYes` under every oracle. All of these are fixed before the oracle is
drawn. A verifier that forms digests BY THE ORACLE does not meet that: its checkers, the codes
beneath them and the key that it tests hold the oracle's values at certain strings. The digest of
the public files is asked at a string that is fixed beforehand; the digests of the chains' parameter
bytes at strings that are fixed only once that first value is, since these bytes hold it.

Here everything that may hold such values is a family over two tables: T₀, of the values at a fixed
finite set S₀, and T₁, of the values at a finite set S₁ T₀ that may depend on T₀. These are the
three parts, `key`, `Good`, a further rare event X' and `FineT`. `join_id_at` asks `join_id`'s
hypotheses at every pair of tables, with `hYes` in this form: a yes UNDER THE ORACLE g WITH BOTH
TABLES PUT OVER IT gives, at the parts and the key that hold these tables, what `join_id` asks under
g. Its conclusion is on an event under the drawn oracle itself: "yes under g, and not `Fine` under
g".

The clause on the published digest is asked under the oracle with the tables put over it, as a
verifier sees it; `hid` asks that no key's code is among the strings.

The bound. B, any bound on `join_id`'s six terms at all tables.



What is asked beside `join_id`'s hypotheses at all tables. `hFine`: `FineT` at the tables gives
`Fine` under the oracle with the tables put over it. `hm`: for each outcome, the oracles under which
it lies in "yes and not `Fine`" are a measurable set. `hoff₀`, `hoff₁`: that event does not get lost
when the entries at the strings are left out of both logs. For what a part reads off a log through
walks that holds if the strings are read neither as vertices nor as leaves
(OnBytes/Slice/WalkOff.lean).

What an instance owes, in one place.
 1. The three parts as families over the tables, with `PartO.OK` at EVERY table. Where a table's
    value stands in a description (its configuration digest, its parameter bytes), what was closed
    at one description by evaluation is wanted at all, by structure.

 2. The checkers' values under g, as those of a verifier's steps under the oracle with the tables
    put over it. (A part whose checker answers by the tables has, by `det_pinOn`, its value under g
    as the value of the checker within under the oracle with the tables put over it:
    `Part.on`, OnBytes/Slice/PartChainOn.lean. That a verifier's step
    has that value is owed beside, and the like of all three parts.)
 3. `hoff₀`, `hoff₁`. (For what a part of the library's compiler reads: OnBytes/Slice/WalkOff.lean;
    for the first key of a digest, and `hid`: OnBytes/Slice/OffSetGlue.lean. A `Fine` that reads
    the whole log, or that asks that a log has no clash, does not meet them by these.)
 4. `hm` (for a yes that is a value of an algorithm, and a `Fine` that does not read the oracle:
    `measurableSet_det`, OnBytes/Slice/AtSet.lean).
 5. One bound on the six terms at all tables.
 6. S₀ and S₁ themselves, as written functions.
None of these is shown here.
The checker of OnBytes/Slice/OneWorldChain.lean answers its
own query for the digest of the parameter bytes by one constant, the format's own digest of these
bytes (`Fmt.paramsDigest`). It is no family over tables.


What is not claimed. What the heads of OnBytes/Slice/JoinId.lean, PartO.lean and AtSet.lean do not
claim. That a verifier which asks for its digests is covered: no such verifier stands here. At a
table at which a verifier always refuses (a digest of 32 zero bytes), `hYes` holds for free;
`PartO.OK` is asked there too. A checker at a table that asks the oracle at one of the strings all
the same sees g's value there and not the table's: then `hYes` can be shown only if its value does
not depend on that answer. `dig`, bS, bX', B and the two counts are one for all tables. `hYes`,
`hoff₀` and `hoff₁` are asked of every outcome w, not only of outcomes of a run: in showing `hYes`
it may not be used that the logs lack the entries at the strings. `hoff₁` is asked for every T₀
under every oracle: more than the proof uses. S₁ and the families are handed whole tables and may
read them anywhere; only the values at the strings reach the oracle. A set of tables at which a part
has no bound can be paid for outside: cut `Yes` by "the oracle's own tables are not among them", and
put there parts whose checkers return nothing. Nothing on a string that the maker chooses. Nothing
on the program (the Lean port built from OnBytes/), on the C++ verifier or on BLAKE2b. The bound
says nothing once it reaches 1.

-/
import OnBytes.Slice.JoinId
import OnBytes.Slice.Decoder
import OnBytes.Slice.AtSet

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

variable {Sg β δ : Type}

/-- A table of values of the oracle. -/
abbrev Tab : Type := List Bool → Dig 256

/-- **The join, for a yes that depends on the oracle's values at finitely many strings, in two
steps.** The experiment is `join_id`'s. S₀ is a finite set of strings, fixed before the oracle is
drawn; S₁ T₀ a finite set that may depend on the table T₀ of the oracle's values at S₀. The three
parts, `key`, `Good`, X' and `FineT` are families over the tables T₀, T₁. With probability at most
B: w lies in `Yes g` and `Fine g w` fails. Asked: `join_id`'s hypotheses on the parts at all tables;
X' at the tables has probability at most bX' for the committer and the prover that answer by the
tables; `hid`: no key's code is among the strings; `hFine`; `hm`; `hoff₀`, `hoff₁`; `hYes`: for all
tables and every g, a yes under g with the tables put over it gives, outside X', what `join_id` asks
under g of the parts and the key at these tables, the clause on the published digest being asked
under g with the tables put over it; `hB`: B bounds `join_id`'s six terms at all tables. See the
head. All of these are variables or hypotheses. By `hm` the probability is a true average. The bound
says nothing once it reaches 1. -/
theorem join_id_at (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (key : Tab → Tab → δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) Sg)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (Good : ∀ T₀ T₁, (F T₀ T₁).Out → Raw Sg → Prop)
    (hpath : ∀ T₀ T₁ (oK : (K T₀ T₁).Out) (oE : (E T₀ T₁).Out) (oF : (F T₀ T₁).Out)
      (Y₀ Y₁ : Raw Sg), (K T₀ T₁).Lang oK [Y₀] → (E T₀ T₁).Lang oE [Y₀, Y₁] →
      (F T₀ T₁).Lang oF [Y₁] → Good T₀ T₁ oF Y₀)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (Yes : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (Fine : Fam (rom 256) → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (FineT : Tab → Tab → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hFine : ∀ T₀ T₁ g w, FineT T₀ T₁ w → Fine (over S₀ T₀ (over (S₁ T₀) T₁ g)) w)
    (hm : ∀ w, MeasurableSet {g | w ∈ Yes g ∧ ¬ Fine g w})
    (hoff₀ : ∀ g w, w ∈ Yes g → ¬ Fine g w → offBoth S₀ w ∈ Yes g ∧ ¬ Fine g (offBoth S₀ w))
    (hoff₁ : ∀ T₀ g w, w ∈ Yes g → ¬ Fine g w →
      offBoth (S₁ T₀) w ∈ Yes g ∧ ¬ Fine g (offBoth (S₁ T₀) w))
    (hYes : ∀ T₀ T₁ g w, w ∈ Yes (over S₀ T₀ (over (S₁ T₀) T₁ g)) → w ∉ X' T₀ T₁ g →
      (∃ s, idCode (key T₀ T₁ w.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk w.1).det g = some oK ∧ ((E T₀ T₁).chk w.1).det g = some oE ∧
        ((F T₀ T₁).chk w.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root] ∧
        (E T₀ T₁).roots oE = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key T₀ T₁ w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          Good T₀ T₁ oF
            ((K T₀ T₁).raw w.1.1.2 (Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root)) →
          FineT T₀ T₁ w))
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine g w}) ≤ B := by
  refine Pr_twoExp_le_of_pinned₂ S₀ S₁ C P _ B hm (fun g w hw => hoff₀ g w hw.1 hw.2)
    (fun T₀ g w hw => hoff₁ T₀ g w hw.1 hw.2) fun T₀ T₁ => ?_
  have h := join_id (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C)) dig
    (fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))) (key T₀ T₁) tC tP
    (queryBound_pinOn _ _ _ tC (queryBound_pinOn _ _ C tC hC))
    (fun b => queryBound_pinOn _ _ _ tP (queryBound_pinOn _ _ (P b) tP (hP b)))
    (K T₀ T₁) (E T₀ T₁) (F T₀ T₁) (hK T₀ T₁) (hE T₀ T₁) (hF T₀ T₁) bS (hS T₀ T₁) (hKE T₀ T₁)
    (hEF T₀ T₁) (Good T₀ T₁) (hpath T₀ T₁) (X' T₀ T₁) bX' (hX' T₀ T₁)
    (fun g => Yes (over S₀ T₀ (over (S₁ T₀) T₁ g))) (FineT T₀ T₁) fun g w hy hx => by
      obtain ⟨⟨s, hs, hg⟩, rest⟩ := hYes T₀ T₁ g w hy hx
      refine ⟨⟨s, hs, ?_⟩, rest⟩
      rw [over_not_mem _ _ (hid _ s hs).1, over_not_mem _ _ ((hid _ s hs).2 T₀)] at hg
      exact hg
  refine le_trans (Rom.Pr_mono _ fun g w hw => ?_) (h.trans (hB T₀ T₁))
  exact ⟨hw.1, fun hf => hw.2 (hFine T₀ T₁ g w hf)⟩

end OnBytes.Slice
