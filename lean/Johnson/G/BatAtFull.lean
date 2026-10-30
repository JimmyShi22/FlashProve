-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/BatAtFull.lean: the conditions of the round before a proximity test's first fold
(`BatOKAt`, Johnson/Top/H/Bat.lean) at the groups of a proof's first chain at the full-size
example: the tests on numbers, as theorems by evaluation in Lean's kernel.

Johnson/Pack/BatSize.lean brings the kind's three conditions down to a test on each member
(`MemberFits`) and the Johnson condition. Johnson/G/LinkLit.lean has, as a written list, the
sampled messages of each of the 25 links and of the last group, each with its radius. Here the two
tests are evaluated at these 26 lists, at one common length, one joint radius and one distance.
Statements and proofs.

Main names:
  `logFull`, `radFull`, `distFull`: 23; 2,433,820; 4,194,086: the logarithm of the common length,
    the joint radius, the distance.
  `links_fit`: every message of each of the 26 lists meets `MemberFits` at these numbers.
  `links_john`: the joint radius is below the Johnson radius of 2 ^ 23 and that distance.
  `links_listMax`: the bound on the lists is 54.
  `bat_ok_full`: so `BatOKAt` holds of `batSize` at each of the 26 lists, for every choice of
    members with at least one, of kept members, of open rows and of an injective numbering of the
    rows.

Limits: those of Johnson/Pack/BatSize.lean and Johnson/G/LinkLit.lean. That 23, 2,433,820 and
4,194,086 are the planner's numbers for these groups is not shown here: the radius is that of the
lists' own messages of the common length; the distance is the least of the members' as read at the
common length. Which messages of a list are members of the link's group and which are kept is left
to the caller: the conditions do not read it but for «at least one». A group of the programs also
holds a message that is not sampled (the closing fold's fresh mask), which is in no list here. The
open rows and their numbering are parameters.
-/
import Johnson.G.LinkLit
import Johnson.Pack.BatSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Johnson.Pack Cb Cb.Ood VerifiableInference.OnPublicFiles

/-- the logarithm of the common length -/
def logFull : ℕ := 23
/-- the joint radius -/
def radFull : ℕ := 2433820
/-- the distance -/
def distFull : ℕ := 4194086

theorem links_fit : ∀ l ∈ linksFullLit, ∀ x ∈ l,
    MemberFits codesFull2 logFull radFull distFull x.1 x.2 := by decide +kernel

theorem links_john : InJohnson (2 ^ logFull) distFull radFull := by decide +kernel

theorem links_listMax : listMax (2 ^ logFull) distFull radFull = 54 := by decide +kernel

/-- **The kind's conditions at each of the 26 lists.** -/
theorem bat_ok_full (l : List (OracleShape × ℕ)) (hl : l ∈ linksFullLit)
    (mem : Fin l.length → Prop) [DecidablePred mem] (hne : ∃ i, mem i)
    (keep : Fin l.length → Prop) [DecidablePred keep] (B : Type) [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (grpOf codesFull2 l mem logFull radFull).C.J) (rows : ℕ)
    (f : (grpOf codesFull2 l mem logFull radFull).Row B → Fin rows)
    (hf : Function.Injective f) :
    BatOKAt (batSize codesFull2 l mem logFull radFull keep B Sb sl distFull rows f) :=
  batSize_ok codesFull2 l mem logFull radFull keep B Sb sl distFull rows f hf hne
    (fun i _ => links_fit l hl (l.get i) (List.get_mem l i)) links_john

end Johnson.G

#print axioms Johnson.G.links_fit
#print axioms Johnson.G.links_john
#print axioms Johnson.G.bat_ok_full
