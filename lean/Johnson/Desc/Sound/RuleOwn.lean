-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleOwn.lean: FROM A KIND's RULE OF BAD ELEMENTS, WHICH READS COMPONENTS OF THE
WITNESS, TO THE BLOCK's OWN LAW AT THE TABLE (`Piece.Own`, Johnson/Desc/Sound/Spine.lean). A SHEET:
one proposition written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

Why. A kind's law has the form: "for these hidden objects d (cells, a mask row ...) there is a rule
from a front of the transcript to a list of elements, with a ceiling; at a transcript without a bad
element: what the block opens gives what it closes". The hidden objects are components of the
witness. The carrier to a block's errors (`GoodInOfRule`, Johnson/Desc/Sound/RuleErr.lean) wants the
rule to be a function of the STATEMENT and the front: a set of bad challenges must be fixed before
the witness is spoken of. What joins the two: the components that the rule reads are PINNED at that
boundary: inside the promise they are what a decoder makes of the statement's strings.

What is said. `OwnOfRule`. Letters: D: the type of the pinned components; comp: a witness's
components; dec: what the decoder makes of a statement; rule a d: the kind's rule at the statement a
(it may read the ledger in front) and the components d. Asked: (ceil) the ceiling, at every d; the
measures and the errors, as in `GoodInOfRule`; (pin) where the block says yes, a witness at which
all that the block opens holds behind has the components dec a; (promise) the promise behind, on
transcripts without a bad element at dec a; (law) THE KIND's OUT-LAW AS IT LIES, AT THE WITNESS's
OWN COMPONENTS. Then the block has its own law at the table's row. THE KIND's LAW NEVER NAMES dec;
THE BAD SETS NEVER SEE THE WITNESS.

Limits. (1) (pin) is a premise: it is the table's: the row's context holds the pins, the pins ride
back past the block, and two witnesses under one pin agree (Johnson/Desc/Sound/MeaningSig.lean:
`pinAt_one`); it wants the promise "no collision" inside `on`. (2) A rule that reads a component
which is NOT pinned at that boundary (an array that is sent behind the draw) is not served: there no
dec can be had. (3) (ceil) IS ASKED AT EVERY STATEMENT WITH `on`, A MARKED RECORD AMONG THEM IF THE
TABLE's CONDITION HOLDS SUCH: a rule that reads the ledger's sizes has no ceiling at a made-up
ledger: ONE LAYS rule a := the empty list AT A MARKED a (lawful: (pin) and (law) are free there:
what a block opens holds of no marked record: THIS LEANS ON TWO FACTS THAT ARE NOT SHOWN HERE:
"unmarked" stands in every set of items that a block opens, which is the table's; AND A MARK STAYS:
a marked a gives a marked b, which is a fact on each block's text, OWED WITH THAT BLOCK's LAW:
without it the promise's and the law's clauses are asked at an unmarked b behind a marked a, under a
rule that lists nothing); or the law is taken at the condition without a mark and carried through
the table's door for marked records. (4) dec IS TOTAL: outside the promise (no collision; shown;
held) the decoder gives nothing and a default stands there: harmless: (pin) is asked inside `on`.
(5) A member: Johnson/Desc/Sound/RuleOwnToy.lean: the commitment there is the identity. (6) Those of
RuleErr.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleErr
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)
open _root_.Run.PQ (CK SgX PlainOf)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

/-- **From a kind's rule at the witness's pinned components to the block's own law at the table.**
-/
def OwnOfRule : Prop :=
  ∀ (S Cl W ι D : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (comp : W → D)
    (dec : S × F.E.Str → D) (rule : S × F.E.Str → D → List Fmt.RoundView → List E) (ceil k f : ℕ → ℕ),
    (∀ a d g, on a → (rule a d g).length ≤ ceil (g.length - 1)) →
    (∀ j d, (toRDs p.ds)[j]? = some d → CoordMeasure C d (k j) (f j)) →
    ErrBears C (fun j => k j * (ceil j * f j)) (toRDs p.ds) 0 p.err →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → relAt means Out b w → comp w = dec a) →
    (∀ a τ b, on a → NoBad (rule a (dec a)) (rvSL C (toRDs p.ds) τ) →
      p.ior.red.out a τ = some b → on' b) →
    (∀ a τ b w, on a → NoBad (rule a (comp w)) (rvSL C (toRDs p.ds) τ) →
      p.ior.red.out a τ = some b → relAt means Out b w → relAt means In a (p.ext a τ w)) →
    p.Own on on' means In Out


end VerifiableInference.Desc.Sound
