-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Defs.lean: the kind "lookup" (K3): five definitions for the
bound at the lookups' marks at a proof file's first chain (`k3Marks`, Honest/K3/Good/MarksList.lean)
in the form in which the frame's list of all marks asks it. Definitions alone; no theorem.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, share and
kit. In this file: f is a lookup's face; C is a kit of verifier's messages; cap is a letter for a
bound that hangs on a round's entry and kind; kap is a letter for one bound above these. In this
folder: an element of a round is drawn by the even rule if its draw is `Fmt.Draw.elem`: no element
of the field is left out; by the never-0 rule if its draw is `Fmt.Draw.elemNZ`: 0 is left out. How a
kit's challenges spread over the elements is not said by these words: it is what `KitCap` is about.

What is defined.
  `SpotLaid f p`: the verifier's list of the lookup's rounds has a round at the spot's number, and
    that round draws enough elements by the even rule.
  `capRounds f`: the numbers of the rounds whose bound the letter kap must sit above.
  `KitCap C cap`: a hypothesis on a kit.
  `CapsUnder cap f es kap`: the hypothesis on the letter kap.
  `LeafForm f`: the form of the factor of a bit in a leaf.

Imported. Honest/K3/Good/MarkOut.lean, for `outEvents`; it is a file of laws.
Johnson/P1K8R/KitCount.lean, for
`IsEl`, `Reduced` and `AtEl`.

Users. The files of this folder.

Limits. Nothing is shown here. Since the file stands over files of laws, no file that defines a part
of the description may import it. `KitCap` and `CapsUnder` are hypotheses: cap and kap are letters,
and no number is named or evaluated. `CapsUnder` asks nothing at a number at which the list es has
no entry, or whose entry's name has no kind: that there is an entry with a kind at every listed
number is `capRounds_laid` (Honest/K3/Good/H3/Guards.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkOut
import Johnson.P1K8R.KitCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open OnBytes (E oneE subE)
open VerifiableInference.Desc.K3 (entriesV)
open _root_.Run.PQ (CK)

/-- The verifier's list of the lookup's rounds has a round at the spot's number; that round draws no
element by the never-0 rule, and more elements than the spot's number. Public data alone. -/
def SpotLaid (f : LFace) (p : Spot) : Prop :=
  ∃ en : Fmt.Entry, (entriesV f)[firstRound f p.stage + p.round]? = some en ∧
    en.drawNZ = 0 ∧ p.draw < en.drawE

/-- The numbers, among the lookup's own rounds, of the rounds whose bound the letter must sit above:
each event's round, of both marks, AND ALPHA's, which is no spot's: the second mark's last event
(the leaf's factor is 0) is bounded at that round. -/
def capRounds (f : LFace) : List Nat :=
  (eventsOf f ++ outEvents f).map (Event.round f) ++ [firstRound f .alpha]

/-- **A hypothesis on a kit, by name.** cap e k sits above the share, among the kit's challenges at
the entry e and the kind k, of those that show a drawn value at which Q holds: for every Q that, at
drawn values with words below the prime AND WITH AN ELEMENT NUMBER i, pins element number i to ONE
field element y; i an element drawn by the even rule. A share of CHALLENGES: by the types, no input
and no coin stands in it. The left side is `shareAt` (Honest/K3/Good/MarkShare.lean) written out at
e and k. At the cap ⊤ it holds of every kit: a statement "there is a cap" pays hcap at no number
(`kitCap_fits`, Honest/K3/Good/H3/JoinForm.lean [not in this library]). -/
def KitCap (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) : Prop :=
  ∀ (e : Fmt.Entry) (k : Fmt.Kind), e.logN ≤ 64 → ∀ i : ℕ, P1K8.IsEl (Fmt.dsOf e k) i →
    ∀ (y : Cb.Gl.E) (Q : Fmt.Drawn → Prop),
      (∀ R, P1K8.Reduced R → i < R.elems.length → Q R → P1K8.AtEl i (· = y) R) →
      ((Prob.cnt fun c : C.Ch e k => Q (C.dr e k c) : ℕ) : ℝ≥0∞) / (Nat.card (C.Ch e k) : ℝ≥0∞) ≤
        cap e k

/-- **THE PREMISE ON THE LETTER: every listed round's bound is at most kap.** The listed rounds
(`capRounds`): the events' rounds of both marks, and alpha's. es: the plan's entries at the lookup.
-/
def CapsUnder (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (f : LFace) (es : List Fmt.Entry)
    (kap : ℝ≥0∞) : Prop :=
  ∀ n ∈ capRounds f, ∀ e : Fmt.Entry, es[n]? = some e →
    ∀ k : Fmt.Kind, Fmt.kindOf e.name = some k → cap e k ≤ kap

/-- The face's factor of a bit in a leaf is alpha - 1 - something that does not read alpha. -/
def LeafForm (f : LFace) : Prop :=
  ∃ T : E → Array E → E, ∀ (theta alpha : E) (z : Array E),
    f.leaf theta alpha z = subE (subE alpha oneE) (T theta z)

end ProofFile.Honest.K3.Good
