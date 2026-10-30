-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinId.lean: the join of three checkers, with the first root led to by a published
digest.

OnBytes/Slice/PartO.lean (`join_verify`) joins three checkers over one random oracle for any
event "yes" that gives, outside a further event X, the three checkers' values and the tie between
their roots, the first of which a function `rt` reads off the committer's output and log. This file
puts for X the event of OnBytes/Slice/IdMaker.lean (`id_maker`), and for `rt` the root in the first
key that the committer's own log holds for the digest in the committer's output (`Tie.firstId`).

Here what a yes owes does not name `rt` (`hYes`): the key that is read off the prover's output has a
code at which the oracle answers the committer's digest; the three checkers return something; the
first checker's root, and the second's first, is that key's table's root; the second's second root
is the third's; and `Good` of the raw string under that root IN THE COMMITTER's OWN LOG gives
`Fine`. In showing that last clause it may be used that the key is the first that the committer's
own log holds for the digest, that no two strings of the whole log have one answer, and that the
whole log begins with the committer's: so `Fine` may speak of what an extractor finds that sees the
digest and the committer's log alone, and never the prover's key. Nothing is supposed on what the
committer's log holds.

Main theorem. `join_id`: "yes and not `Fine`" has probability at most the sum of the three parts'
bounds at tC + tP, of the first part's bound for stability, of (tC + tP + 2)^2 / 2^256 and of bX',
the bound of a further event X', outside which alone a yes owes anything (for a verifier whose yes
gives the three checkers' values only outside a rare event of its own; the empty event, with 0, is
allowed). The probability of `id_maker`'s event over the coins is a measurable function of the
oracle (OnBytes/Slice/IdMaker.lean: `measurable_id_maker`); so, for a yes that meets
`measurable_yes`'s condition, and an X' of which the like holds, the bound is on a true average.
Where X''s is not measurable, `hX'` asks less than its words.

What is not claimed. What the head of OnBytes/Slice/PartO.lean does not claim: parts, `Good`, `Yes`
and `Fine` are variables, and `hYes` is a hypothesis: that any verifier's yes meets it is not shown.
All limits in the heads of OnBytes/Slice/IdMaker.lean and OnBytes/Tie/IdKey.lean hold here too. A
yes on a digest for which the committer's log holds no key, or another key, is counted in the last
term; of `Fine` nothing is said there. The parts, `key` and `dig` are fixed before the oracle is
drawn, and `hYes` is asked under every oracle: a verifier that asks the oracle for a value which an
implementation holds as a constant (a digest of public files) does not meet it. For such a verifier:
OnBytes/Slice/JoinAtSet.lean. Nothing ties the shape and the digest in the key to the three parts:
that is a matter of `key` and of `hYes`. Nothing on the program (the Lean port built from OnBytes/),
on the C++ verifier or on BLAKE2b. The bound says nothing once it reaches 1.

-/
import OnBytes.Slice.PartO
import OnBytes.Slice.IdMaker

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

variable {Sg β δ : Type}

/-- The root that the committer's output and log name: that of the table in the first key which the
log holds for the digest in the output; none if the log holds no query with that answer that is a
key's code. -/
def rootOfId (dig : β → ZKCP.Digest 256) (x : β × Trace (rom 256)) : Option (Dig 256) :=
  (firstId (dig x.1) x.2).map fun k => Run.bytesToDig k.2.2.root

/-- **The join, with the first root led to by a published digest.** The experiment is that of
`join_verify`, at 256 bits: a committer C with at most tC queries, whose output holds a digest
(`dig`); then a prover P on C's output with at most tP, whose output holds a key (`key`: a shape, a
digest of public files, a table). With probability at most the sum of the three parts' bounds at tC
+ tP, of bS tC tP (the first part's bound for stability), of (tC + tP + 2)^2 / 2^256 and of bX': w
lies in `Yes g` and `Fine w` fails. Asked beside the hypotheses on the parts: X' has probability at
most bX'; and `hYes`: outside X' a yes under g gives a code s of the key with `g () s` the
committer's digest; values oK, oE, oF of the three checkers under g; a root cm' such that the roots
of oK, oE, oF are [cm], [cm, cm'], [cm'], where cm is the root of the key's table; and `Good oF` of
the raw string that K reads under cm off C's own log gives `Fine w`, where it may be used that the
key is the first that C's own log holds for the digest, that no two strings of the whole log have
one answer, and that the whole log begins with C's log. All of these are variables or hypotheses.
"Probability" is `Rom.Pr`, a lower integral: see the head of OnBytes/Slice/PartO.lean. The bound
says nothing once it reaches 1. -/
theorem join_id (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256)
    (P : β → OComp (rom 256) δ) (key : δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : PartO 256 ((β × Trace (rom 256)) × δ) Sg) (hK : K.OK) (hE : E.OK) (hF : F.OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : K.Stable bS)
    (hKE : SameRaw K E) (hEF : SameRaw E F) (Good : F.Out → Raw Sg → Prop)
    (hpath : ∀ (oK : K.Out) (oE : E.Out) (oF : F.Out) (Y₀ Y₁ : Raw Sg),
      K.Lang oK [Y₀] → E.Lang oE [Y₀, Y₁] → F.Lang oF [Y₁] → Good oF Y₀)
    (X' : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256))) (bX' : ℝ≥0∞)
    (hX' : Rom.Pr (twoExp C P).withTrace X' ≤ bX')
    (Yes : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hYes : ∀ g w, w ∈ Yes g → w ∉ X' g →
      (∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
        (F.chk w.1).det g = some oF ∧
        K.roots oK = [Run.bytesToDig (key w.1.2).2.2.root] ∧
        E.roots oE = [Run.bytesToDig (key w.1.2).2.2.root, cm'] ∧ F.roots oF = [cm'] ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          Good oF (K.raw w.1.1.2 (Run.bytesToDig (key w.1.2).2.2.root)) → Fine w)) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine w}) ≤
      K.bound (tC + tP) + (E.bound (tC + tP) + (F.bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) := by
  refine join_verify C P tC tP hC hP (rootOfId dig) K E F hK hE hF bS hS hKE hEF Good hpath
    (fun g => {w | ¬ NoClash w.2 ∨ ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
      firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)} ∪ X' g) _
    ((Pr_union_le _ _ _ (measurable_id_maker C dig P key)).trans
      (add_le_add (id_maker C dig P key tC tP hC hP) hX'))
    (fun g w hw => ?_) Yes Fine fun g w hy hw hsh => ?_
  · by_contra h
    exact hw (Or.inl (Or.inl h))
  · obtain ⟨⟨s, hs, hg⟩, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, hfine⟩ :=
      hYes g w hy fun h => hw (Or.inr h)
    have hfirst : firstId (dig w.1.1.1) w.1.1.2 = some (key w.1.2) := by
      by_contra h
      exact hw (Or.inl (Or.inr ⟨s, hs, hg, h⟩))
    refine ⟨oK, oE, oF, _, cm', cK, cE, cF, ?_, rK, rE, rF,
      hfine hfirst (by by_contra h; exact hw (Or.inl (Or.inl h))) hsh⟩
    show (firstId (dig w.1.1.1) w.1.1.2).map _ = _
    rw [hfirst]
    rfl

end OnBytes.Slice
