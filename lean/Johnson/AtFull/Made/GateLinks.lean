-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateLinks.lean: the planner's first gate: what it reads, a twin without the
sub-proofs' routines, and that the twin says no at the written values. Five definitions, five
theorems, one plant.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses unless `missedInTheLinks`
(OnBytes/Params/Gate.lean) returns false. It is the premise f₁ of `configure_of_parts`
(Johnson/AtFull/Made/Ledger.lean). It is the one gate that is not closed at the written sizes: it
calls the run's sub-proofs' own routines (`sub.plan i m`: closures over the public part) and reads
the proof file's first plan.

What it reads. OF THE SUB-PROOFS: for each segment i ONE NUMBER: how many scalars its moments'
rounds send (`scalarsOf z.set (forEach (List.range moments) fun m => sub.plan i m)`). OF THE FIRST
PLAN: its lists of positions (`listsOf first`). Nothing else of either.

What is said. `momentsOf x`: a segment's number of moments, in the gate's own words. `linksFromBy`,
`linksGateBy`: the gate's two routines with these numbers es and these lists as letters: tests with
code. `linksFrom_by`, `gate_links_by`: wherever each segment's count returns es's entry, the gate
returns the twin's answer. `scalarsFull`, `listsFull`: the written numbers. `gate_links`: at
`recordLines`, `writtenSized.proof` and these the twin says false: by an evaluation in Lean's
kernel. `gate_links_of`: so f₁, to the letter, under the two premises on sub and first.
`gate_links_plant`: with one segment's count at 100,000 the twin says true: the test can fail.

Limits. The written values alone. WHENCE THE NUMBERS: copied off a run of the library's own planner
at a stored full-size set's public files (an evaluation; no theorem): that the counts return them,
and that the first plan has these lists, are premises. Nothing on soundness.
-/
import Johnson.Goal.Written.Made
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- A segment's number of moments, in the gate's own words. -/
def momentsOf (x : ReqLink) : Nat := (x.messages.getLast?.map (·.moment + 1)).getD 0

/-- `missedInLinksFrom` with the segments' counts of scalars as a list. -/
def linksFromBy (z : ProofSized) (answers : Nat) :
    List Nat → List ReqLink → List ReqGroup → List Nat → Bool
  | e :: es, _ :: xs, g :: gs, t :: ts =>
    ((codeAt z.codes.base z.request.code).r < t || (codeAt z.codes.mask z.request.maskCode).r < t ||
      (codeAt z.codes.mask z.request.maskCode).ell < 2 * g.k + 1 - g.h ||
      (codeAt z.codes.mask z.request.maskCode).ell < e + answers) ||
      linksFromBy z answers es xs gs ts
  | _, [], _, _ => false
  | _, _ :: _, _, _ => true

/-- `missedInTheLinks` with these counts and the first plan's lists of positions as letters. -/
def linksGateBy (l : Lines) (z : ProofSized) (es lists : List Nat) : Bool :=
  if l.salt < 40 || (z.request.atStart.any fun n =>
      z.request.link.any fun x => x.messages.any fun m => m.leafClass == n.leafClass) ||
      lists.length != z.request.link.length + z.request.last.length then true
  else if linksFromBy z l.answers es z.request.link (reqGroups z.request).toList lists then true
  else missedInTest z.codes z.request.last (lists.drop z.request.link.length) 0 0

/-- Where each segment's count returns, the inner routine returns the twin's answer. -/
theorem linksFrom_by (z : ProofSized) (sub : Subproofs) (answers : Nat) :
    ∀ (xs : List ReqLink) (i : Nat) (es : List Nat) (gs : List ReqGroup) (ts : List Nat),
      es.length = xs.length →
      (∀ j (hj : j < xs.length) (hj' : j < es.length),
        scalarsOf z.set (forEach (List.range (momentsOf xs[j])) fun m => sub.plan (i + j) m) =
          .ok es[j]) →
      missedInLinksFrom z sub answers i xs gs ts = .ok (linksFromBy z answers es xs gs ts)
  | [], _, es, gs, ts, _, _ => by
    cases es <;> simp [missedInLinksFrom, linksFromBy, pure, Except.pure]
  | x :: xs, i, [], _, _, hl, _ => by simp at hl
  | x :: xs, i, e :: es, [], ts, _, _ => by
    simp [missedInLinksFrom, linksFromBy, pure, Except.pure]
  | x :: xs, i, e :: es, g :: gs, [], _, _ => by
    simp [missedInLinksFrom, linksFromBy, pure, Except.pure]
  | x :: xs, i, e :: es, g :: gs, t :: ts, hl, hE => by
    have h0 := hE 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero, momentsOf] at h0
    have ih := linksFrom_by z sub answers xs (i + 1) es gs ts (by simpa using hl)
      (fun j hj hj' => by
        have := hE (j + 1) (by simpa using hj) (by simpa using hj')
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
    unfold missedInLinksFrom
    simp only [h0, bind, Except.bind]
    unfold linksFromBy
    by_cases hc : ((codeAt z.codes.base z.request.code).r < t ||
        (codeAt z.codes.mask z.request.maskCode).r < t ||
        (codeAt z.codes.mask z.request.maskCode).ell < 2 * g.k + 1 - g.h ||
        (codeAt z.codes.mask z.request.maskCode).ell < e + answers) = true
    · simp only [hc, if_true, Bool.true_or, pure, Except.pure]
    · have hc' := Bool.eq_false_iff.2 hc
      simp only [hc', Bool.false_eq_true, if_false, Bool.false_or]
      exact ih

/-- **What the first gate reads.** -/
theorem gate_links_by (l : Lines) (z : ProofSized) (sub : Subproofs) (first : Planned)
    (es : List Nat) (hl : es.length = z.request.link.length)
    (hE : ∀ j (hj : j < z.request.link.length) (hj' : j < es.length),
      scalarsOf z.set (forEach (List.range (momentsOf z.request.link[j])) fun m => sub.plan j m) =
        .ok es[j]) :
    missedInTheLinks l z sub first = .ok (linksGateBy l z es (listsOf first)) := by
  have h := linksFrom_by z sub l.answers z.request.link 0 es (reqGroups z.request).toList
    (listsOf first) hl (fun j hj hj' => by simpa using hE j hj hj')
  unfold missedInTheLinks linksGateBy
  simp only [h, bind, Except.bind, pure, Except.pure]
  split <;> [rfl; (split <;> rfl)]

/-- The written counts of scalars, by segment. -/
def scalarsFull : List Nat :=
  4059 :: 4190 :: (List.replicate 11 [4058, 4190]).flatten ++ [3570]

/-- The written lists of positions of the proof file's first plan. -/
def listsFull : List Nat := List.replicate 26 219 ++ [55, 55, 55, 46, 44]

/-- **The twin at the written values.** -/
theorem gate_links : linksGateBy recordLines writtenSized.proof scalarsFull listsFull = false := by
  decide +kernel

theorem scalarsFull_length : scalarsFull.length = writtenSized.proof.request.link.length := by
  decide +kernel

/-- **f₁, in the ledger's own letters.** -/
theorem gate_links_of (sub : Subproofs) (first : Planned) (hL : listsOf first = listsFull)
    (hE : ∀ j (hj : j < writtenSized.proof.request.link.length) (hj' : j < scalarsFull.length),
      scalarsOf writtenSized.proof.set
        (forEach (List.range (momentsOf writtenSized.proof.request.link[j])) fun m =>
          sub.plan j m) = .ok scalarsFull[j]) :
    missedInTheLinks recordLines writtenSized.proof sub first = .ok false := by
  rw [gate_links_by recordLines writtenSized.proof sub first scalarsFull scalarsFull_length hE, hL,
    gate_links]

theorem gate_links_plant :
    linksGateBy recordLines writtenSized.proof (100000 :: scalarsFull.drop 1) listsFull = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.linksFrom_by
#print axioms Johnson.AtFull.Made.gate_links_by
#print axioms Johnson.AtFull.Made.gate_links
#print axioms Johnson.AtFull.Made.scalarsFull_length
#print axioms Johnson.AtFull.Made.gate_links_of
#print axioms Johnson.AtFull.Made.gate_links_plant
