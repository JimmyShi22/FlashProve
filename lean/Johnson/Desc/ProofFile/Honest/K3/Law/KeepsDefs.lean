-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/KeepsDefs.lean: what the member at a lookup leaves of the
verifier's state as it was, and how the fields that it sets may have changed: seven sentences, on
the state in front of the member's step (`s`) and the state behind it (`s'`), or on the ledgers of
the two. Definitions.

Terms. Honest/K3/GLOSSARY.md. "Bears no mark" is `failed = none`. The ledger of a state is the
`Fork` that `S.fork?` reads off the part of the link that is open; `S.tl?` reads the structure of
the smallness test off the same part (Johnson/Desc/First/State.lean). A claim is owed while it
stands in the ledger's list `owed`, and added once its field `added` is set (`Fork`, `Owed`:
OnBytes/Model/Hide.lean). One ledger is later than another in the sense of `OnBytes.PscRun.Later`
(OnBytes/Tie/Pv/Psc/PscLater.lean).

What is defined.

  `Digits.Longer`   the second ledger's list of owed claims is the first's, lengthened by claims
                    that are not marked as added
  `CallsHere`   behind a lookup on the calls the state is the state in front with named fields of
                the open link's part set, one arm for each sort of link. A layers' link: `F`, `fo`
                and `lookHeard`. An attention link: `F`, `g` and `lookHeard`. The head's link,
                which must be open: `F` and `lookHeard`
  `LedgerKept`   what the hearing does to the ledger, at every sort: the ledger behind is later
                 (what lies under a slot that was filled is kept, and the number of slots stays);
                 its field `trees` stays; the number of its slots' coefficients stays; its count
                 has grown by the lookup's slots; `Digits.Longer`; and, where its three arrays had
                 their size, at least three claims are appended
  `DigitsArms`   behind a lookup on the digits the state is the state in front with `tl` and `F`
                 of the open link's part set, one arm for each sort of link
  `K3KeepsCalls`   at a lookup on the calls: the state behind bears no mark, `CallsHere` and
                   `LedgerKept`
  `K3KeepsDigits`   at a lookup on the digits: the state behind bears no mark, `DigitsArms` at
                    four fields of the structure of the smallness test and at the ledger with the
                    plan's number of claims, and `LedgerKept`
  `K3KeepsHead`   at the lookup on the digits of the head's link: the state behind bears no mark;
                  the ledger, the same four fields and the claim on the weights are set; and
                  `LedgerKept`

Users. A file on another kind that needs these sentences alone, to say what passes a lookup
unchanged, can import this file without any proof of this folder: it imports files of the library
alone. It is meant for the files under Honest/Thread/. In this folder:
`owed_grows` (Honest/K3/Law/DigitsBehind.lean) shows `Digits.Longer` where the lookup's hearing
returns; `calls_here` (Honest/K3/Law/Thread/StateHere.lean) shows `CallsHere`, and
`k3Keeps_calls`, `k3Keeps_digits` and `k3Keeps_head` (Honest/K3/Law/Thread/K3Keeps.lean) show the
three sentences `K3Keeps…`, each from the accepting step of the description's own member.

Kin. `DigitsArms` has, but for the bound letters, the text of `DigitsHere`
(Honest/K3/Law/Thread/DigitsParts.lean); the tie: `digitsHere_iff`
(Honest/K3/Law/Thread/TiesHere.lean [not in this library]).

Limits. Definitions alone: nothing is shown in this file. Of a slot that was not filled in front
and lies outside the lookup's own stretch the sentences say nothing. The heard structure and the
ledger behind stand under "there is": each is fixed by the equation on the state behind; in
`K3KeepsDigits` the ledger but for its field `planClaimsF`, which that equation sets and of which
`LedgerKept` says nothing. Of the ledger's other numbers and flags nothing is said. `K3KeepsDigits`
is meant for a layers' or an attention link, and is wider than that: `DigitsArms` has a third arm,
the head's link open. On the verifier's side alone.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Look.K3LookupGeneral
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Digits
open OnBytes.Model (Fork Owed)

/-- The list of owed claims of `G` is that of `F`, lengthened by claims that are not marked as
added. -/
def Longer (F G : Fork) : Prop :=
  ∃ l : List Owed, G.owed.toList = F.owed.toList ++ l ∧ ∀ o ∈ l, o.added = false

end ProofFile.Honest.K3.Law.Digits

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork HTailF2)
open OnBytes.PscRun (Sized Later)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Face faceOf)

/-- The state behind a lookup on the calls, field by field, by the sort of the link that is open.
`H`: the heard structure. `G`: the ledger behind. -/
def CallsHere (sj sj' : S) (H : OnBytes.Model.Forest.Heard) (G : Fork) : Prop :=
  (∃ a, sj.here = .lay a ∧
    sj' = { sj with here := .lay { a with F := G, fo := some H, lookHeard := some H } }) ∨
  (∃ a, sj.here = .att a ∧
    sj' = { sj with here := .att { a with F := G, g := some H, lookHeard := some H } }) ∨
  ∃ a, sj.here = .head a ∧ a.opened = true ∧
    sj' = { sj with here := .head { a with F := G, lookHeard := some H } }

/-- What the hearing does to the ledger. `f`: the lookup's face. `F`, `G`: the ledger in front and
behind. The library has a structure of this short name with other contents
(Johnson/Desc/Reads/KeptMoreCommit.lean). -/
def LedgerKept (f : Face) (F G : Fork) : Prop :=
  Later F G ∧ G.trees = F.trees ∧ G.LS.size = F.LS.size ∧ G.next = F.next + f.slots ∧
    ProofFile.Honest.K3.Law.Digits.Longer F G ∧ (Sized F → F.owed.size + 3 ≤ G.owed.size)

/-- The state behind a lookup on the digits, field by field, by the sort of the link that is open.
-/
def DigitsArms (s s' : S) (tl' : HTailF2) (G' : Fork) : Prop :=
  (∃ a, s.here = .lay a ∧ s' = { s with here := .lay { a with tl := tl', F := G' } }) ∨
  (∃ a, s.here = .att a ∧ s' = { s with here := .att { a with tl := tl', F := G' } }) ∨
  ∃ a, s.here = .head a ∧ a.opened = true ∧
    s' = { s with here := .head { a with tl := tl', F := G' } }

/-- At a lookup on the calls. `h`: the lookup's shape. -/
def K3KeepsCalls (h : Shape) (s s' : S) : Prop :=
  s'.failed = none ∧ ∃ F H G, s.fork? = some F ∧ CallsHere s s' H G ∧ LedgerKept (faceOf h) F G

/-- At a lookup on the digits of a layers' or an attention link. `claims`: the plan's number of
claims. -/
def K3KeepsDigits (h : Shape) (claims : Nat) (s s' : S) : Prop :=
  s'.failed = none ∧ ∃ tl F H G, s.tl? = some tl ∧ s.fork? = some F ∧
    DigitsArms s s' { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H }
      { G with planClaimsF := claims } ∧ LedgerKept (faceOf h) F G

/-- At the lookup on the digits of the head's link. -/
def K3KeepsHead (h : Shape) (s s' : S) : Prop :=
  s'.failed = none ∧ ∃ tl F H G a₀ claim, s.tl? = some tl ∧ s.fork? = some F ∧
    s.here = .head a₀ ∧ a₀.opened = true ∧
    s' = { s with here := .head { a₀ with
      tl := { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H },
      F := G, claim := some claim } } ∧ LedgerKept (faceOf h) F G

end ProofFile.Honest.K3.Law.AtThr
