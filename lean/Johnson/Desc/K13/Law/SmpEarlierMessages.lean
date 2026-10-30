-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SmpEarlierMessages.lean: WHAT IS ASKED OF THE SAMPLE's READER AT W's COMMITMENT: at the
members at the index masks' seat it gives the same over a step that SENDS a message and leaves all
that is older. Two definitions: no theorem. Why in this form. The letter smp
(Johnson/Desc/Sound/MeaningSig.lean) is other files'. Which way its meant term goes from a member
to the member's message is those files' to say: through the record's own book, or by a number off
the plan. A PREMISE THAT FIXES ONE WAY IS FALSE OF THE OTHER AT A FAR CORNER. So the premise hands
the payer ALL THAT IS IN HAND at the two clauses that spend it, and fixes no way.
  `OlderStay s s'`: the code table stays; every message of s keeps its shape, mark "sampled", sample
  rows and pad (`sampleOf`, Johnson/Desc/K13/Law/PinDec.lean); every place and every tree of s's
  book stays.
  `SmpOld N p ms smp`: THE PREMISE: at a member of ms at the index masks' seat: one public part; the
  book in front stands where the plan says of the place p (`First.bookAt`: so the numbers of
  messages and trees in front are the plan's); the record in front holds that tenant's sample
  (`smpHeld`); `OlderStay`: then smp gives the same at both.
WHO CAN PAY IT. A reading through the book: the tenant whose sample is held has a number in the book
in front, and keeps it. A reading by a number off the plan: where that number is below the plan's
count of messages in front of p.
What is not claimed. That any filling's smp meets it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Sending Mem SitsAt)

/-- All that is older stays. -/
def OlderStay (s s' : S) : Prop :=
  s'.st.codes = s.st.codes ∧
    (∀ o, o < s.st.oracles.size → sampleOf s'.st o = sampleOf s.st o) ∧
    (∀ o, o < s.book.place.size → s'.book.place[o]? = s.book.place[o]?) ∧
    ∀ z, z < s.book.trees.size → s'.book.trees[z]? = s.book.trees[z]?

/-- **The premise on smp at W's commitment.** -/
def SmpOld {Pp : Type} {cs : Codes} (N : Numbers) (p : Option Place) (ms : List Mem)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) :
    Prop :=
  ∀ (x x' : Pp × S) (m : Mem), m ∈ ms → SitsAt m N.index.1 N.index.2 → x'.1 = x.1 →
    First.bookAt N p x.2 = true → smpHeld x.2.st x.2.book N.index.1 N.index.2 = true →
    OlderStay x.2 x'.2 → smp x' m.1 m.2 = smp x m.1 m.2

end VerifiableInference.Desc.K13.Law
