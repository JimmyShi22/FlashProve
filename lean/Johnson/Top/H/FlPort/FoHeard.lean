-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoHeard.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  HCout2
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  HeardIs, PadLeft, ShapeOf, Sized, endsOf, rdRV
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

end

/-- On every run on a view that returns, the byte-level routine's record holds the flat function's
end values. -/
def HCout2 : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Tape) (g : Forest.Heard) (rv : List FlatRound),
    lkPad calls pub lid F c = .ok ((g, F'), c') → Sized F →
    Took c rv c' →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    HeardIs ρ g F' (endsOf g.shape lm F.next (rv.map (rdRV ρ)))


end Fo.Tp
