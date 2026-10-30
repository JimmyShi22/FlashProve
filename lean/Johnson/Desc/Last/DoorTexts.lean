-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/DoorTexts.lean: THE TWO TEXTS AT THE DOOR OF THE LAST CHAIN: what the joint
between the shared and the last chain (the premise on `PL.shape 0` of `OnZero₃OfEnd₂`,
Johnson/Desc/Sound/BordersLastQ.lean: "SH₃") needs to find in the two earlier chains' promises, as
tests with code on their own records. Definitions alone. THIN: it imports texts and tests, no law.

Why. At PL := `fillZ` (Johnson/Desc/Last/ShapeRowZero.lean) border 0's test is the start's yes,
tests that read the first chain's end alone, and tests that read the shared chain's end alone
(`shapeAt_zero_iff`, Johnson/Desc/Last/ShapeDoor.lean). For SH₃ to be stated without a letter in the
place of a text, the two earlier promises must bear these tests under names. Here they stand by
themselves, so that they can be laid into the tables' fillings and run at a chain's borders without
any law's cone.

Main names (namespace `VerifiableInference.Desc.Last`).
  `doorFirstL f`: six tests on what is handed of the first chain's last record, each with its name:
    tidy; the book fits; one pending row with lawful weights; the own group has two members; each
    has one sample row; the group has an open row. **`doorFirstB s`**: THE TEXT ON THE FIRST CHAIN'S
    RECORD: where `firstOfS s` hands something the six say yes; else yes.
  `doorSharedL p o`: five tests on the shared chain's end: in order; the book fits; Omega is part 0
    of its tree; Omega is there with the plan's shape; it has one sample row. **`doorSharedB p d`**:
    THE TEXT ON THE SHARED CHAIN'S RECORD: where `Desc.K14.ended d` gives an end the five say yes of
    what `sharedOfEnd` takes of it; else yes.
  `doorX p K`: the same by borders (`Nat → St → Bool`): at K the text, elsewhere yes: the shape in
    which a test is laid beside the shared table's `shape`.

Limits. (1) NEITHER TEXT HAS RUN AT A RECORD. (2) Both say yes where nothing is handed or the chain
has not ended: they are idle at every border but the last ones; the door asks them under the start's
yes alone. (3) BY THEIR TEXTS they can say yes, where something is handed, only at a plan with one
answer to a sample, and only where the own group has just two members (no split's message; one
message of masks): elsewhere the door is shut. (4) That they are the door's own tests:
`doorFirstL_eq`, `doorSharedL_eq` (Johnson/Desc/Last/ShapeDoorAtTexts.lean). (5) Who earns and keeps
them: nobody yet. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.Border
import Johnson.Desc.Sound.BookTests
import Johnson.Desc.Means.TestsB2
import Johnson.Desc.Means.TestsB3
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Sound (bookFitsB tenantB)
open _root_.Desc.K14 (St)

/-! ## 1 The first chain's side -/

/-- **What the last chain's door asks of what is handed of the first chain's last record**: six
tests, each with its name. -/
def doorFirstL (f : FirstEnd₃) : List (String × Bool) :=
  [("the first chain's last statement is tidy", Means.tidyB f.st && Means.sampledMembersB f.st),
   ("the first chain's book fits", bookFitsB f.book),
   ("one pending row, and its row weights are lawful",
      match f.pending with
      | [r] => r.g.all (·.ok)
      | _ => false),
   ("the own group that was handed has two members",
      match f.st.groups[f.own]? with
      | some G => G.members.size == 2
      | none => false),
   ("each of the two has one sample row",
      match f.st.groups[f.own]? with
      | some G => G.members.toList.all fun i =>
          match f.st.oracles[i]? with
          | some x => x.sampleRows.size == 1
          | none => false
      | none => false),
   ("the own group has an open row",
      match f.st.groups[f.own]? with
      | some G => !G.rows.isEmpty
      | none => false)]

/-- **THE TEXT ON THE FIRST CHAIN's RECORD**: where `firstOfS` hands something, the six say yes.
Where it hands nothing: yes (the door asks nothing there: `startAtEnds` refuses). -/
def doorFirstB (s : First.S) : Bool :=
  match firstOfS s with
  | some f => (doorFirstL f).all (·.2)
  | none => true

/-! ## 2 The shared chain's side -/

/-- **What the door asks of the shared chain's end**: five tests, each with its name. -/
def doorSharedL (p : P₁₄) (o : SharedOut) : List (String × Bool) :=
  [("the shared chain's last statement is in order", Means.inOrderB o.st),
   ("the shared chain's book fits", bookFitsB o.book),
   ("in the shared chain's book Omega is part 0 of its tree", tenantB o),
   ("Omega is there at the shared chain's end, with the plan's shape",
      match o.st.oracles[o.omega]? with
      | some y => decide (y.shape = p.S.omega)
      | none => false),
   ("Omega has one sample row at the shared chain's end",
      match o.st.oracles[o.omega]? with
      | some y => y.sampleRows.size == 1
      | none => false)]

/-- **THE TEXT ON THE SHARED CHAIN's RECORD**: where the chain has ended (`Desc.K14.ended`), the
five say yes of what `sharedOfEnd` takes of its end. Where it has not ended: yes (the door asks
nothing there: it asks under the start's yes, and a start that goes by `ended` refuses). -/
def doorSharedB (p : P₁₄) (d : St) : Bool :=
  match _root_.Desc.K14.ended d with
  | some e => (doorSharedL p (sharedOfEnd e)).all (·.2)
  | none => true

/-- **THE SAME AS A TEST BY BORDERS**, to be laid beside whatever stands in the shared table's
`shape`: at the border K the text; at every other border: yes. K: the chain's last border, as the
table writes it. -/
def doorX (p : P₁₄) (K : Nat) : Nat → St → Bool := fun k d => k != K || doorSharedB p d

end VerifiableInference.Desc.Last
