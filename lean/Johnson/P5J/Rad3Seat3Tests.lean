-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/Rad3Seat3Tests.lean: THE NAMED TESTS ON rad3At | seat3At (Johnson/P5J/Rad3Seat3At.lean) AT THE CLOSED LETTERS, LINK BY LINK AND FOR ALL LINKS, AND WHAT THEIR ACCEPT GIVES AT THE CALLS' LOOKUP: THREE OF THE FIVE FIELDS OF THE LOOKUPS' STRUCTURE ListSits. Definitions and theorems.
  callsSomeB Zp lay l · callsSentB Zp cF lay l m: someB | sentB at the calls' list of link l (sigListCalls (sentAt Zp) (rad3At Zp lay) l), the seats seat3At Zp l false, the table's own members ms Zp lay and numbers N Zp cF; at the table's segment m; moments [0].
  digSomeB · digSentB: the like at the digits' list (sigList … l (lastMoment … l)), the seats seat3At Zp l true; moments [2, 0, 1].
  linkThereB Zp l: THE LISTS ARE NO SILENT DEFAULTS: the request's shape has a link l and a group l (else messagesAt | keptAt | bornAt answer the empty list, at which someB | sentB accept idly). NOT "the list is not empty": whether every link of the full size has a member at the calls is not known.
  alignedB Zp l: the lookups' own two: zeroFirst (the moment-0 messages stand first in the link's list: else the list's number of an own message and the planner's part) · bornFits (as many born entries as kept messages).
  k3SeatsB Zp cF lay: these two and the four at every link l below the number of links, AT THE SEGMENT m := l (a link's number is its segment's in the table: the planner's seats bear the link's number as their segment's: by reading; the structure ListSits takes m as a letter of its own): ONE NAMED TEST FOR THE LIST OF THE PLANNER's TESTS.
  calls_some | calls_sent | calls_fits: at a place x of the calls' lookup: ListSits' fields some · sent · fits, TO THE LETTER of that structure's text at seatT := fun j => seat3At Zp x.link false j.1 (fits: where the table's own members fit).
  k3SeatsB_at: the one test gives the four at a link below the number.

Limits. EVALUATED, NOT PROVED (a run of a harness that is not named here, at the release's full-size public files): at each of the 25 links all six parts accept; eight negative tests reject. At the small stored set the like at its 5 links. The digits' structure (DigSits) is not imported: digSomeB | digSentB have the general laws some_of_someB | sent_of_sentB alone. ListSits' other two fields (bySeat · smpIs) are not this file's: they belong to the files on the reader of samples (Johnson/Desc/Sound/SmpNamed.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent sigList sigListCalls lastMoment)
open VerifiableInference.Desc.Sound (Mem Alike SeatFits)
open VerifiableInference.OnPublicFiles (callsSending listSits_some listSits_sent)

variable (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (lay : ByteArray)

/-- The calls' list of link l, at the closed letters. -/
def callsListAt (l : ℕ) : List (OracleShape × ℕ) := sigListCalls (sentAt Zp) (rad3At Zp lay) l

/-- The digits' list of link l, at the closed letters. -/
def digListAt (l : ℕ) : List (OracleShape × ℕ) :=
  sigList (sentAt Zp) (rad3At Zp lay) l (lastMoment (sentAt Zp) l)

def callsSomeB (l : ℕ) : Bool := P5T.someB (ms Zp lay) (callsListAt Zp lay l) (seat3At Zp l false)

def callsSentB (l m : ℕ) : Bool :=
  P5T.sentB (N Zp cF) m [0] (callsListAt Zp lay l).length (seat3At Zp l false)

def digSomeB (l : ℕ) : Bool := P5T.someB (ms Zp lay) (digListAt Zp lay l) (seat3At Zp l true)

def digSentB (l m : ℕ) : Bool :=
  P5T.sentB (N Zp cF) m [2, 0, 1] (digListAt Zp lay l).length (seat3At Zp l true)

/-- The lists of link l are no silent defaults. -/
def linkThereB (l : ℕ) : Bool :=
  ((sentAt Zp).shape.link[l]?).isSome && ((reqGroups (sentAt Zp).shape)[l]?).isSome

/-- The lookups' own two tests on the numbering. -/
def alignedB (l : ℕ) : Bool := P6T.zeroFirst (sentAt Zp) l && P6T.bornFits (sentAt Zp) l

/-- **ONE NAMED TEST**: the two guards and the four at every link. -/
def k3SeatsB : Bool :=
  (List.range links.length).all fun l =>
    linkThereB Zp l && alignedB Zp l && callsSomeB Zp lay l && callsSentB Zp cF lay l l && digSomeB Zp lay l && digSentB Zp cF lay l l

theorem k3SeatsB_at (h : k3SeatsB Zp cF lay = true) (l : ℕ) (hl : l < links.length) :
    linkThereB Zp l = true ∧ alignedB Zp l = true ∧ callsSomeB Zp lay l = true ∧ callsSentB Zp cF lay l l = true ∧ digSomeB Zp lay l = true ∧
      digSentB Zp cF lay l l = true := by
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at h1
  exact ⟨h1.1.1.1.1.1, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2⟩

/-- **ListSits.some.** -/
theorem calls_some (x : VerifiableInference.Desc.First.Look.Place)
    (h : callsSomeB Zp lay x.link = true) :
    ∀ i, ∃ y ∈ ms Zp lay, Alike y
      ⟨callsSending x (sentAt Zp) (rad3At Zp lay) (fun j => seat3At Zp x.link false j.1), i⟩ :=
  listSits_some x (sentAt Zp) (rad3At Zp lay) (seat3At Zp x.link false) (ms Zp lay) h

/-- **ListSits.sent**, at the segment m that the caller names. -/
theorem calls_sent (x : VerifiableInference.Desc.First.Look.Place) (m : ℕ)
    (h : callsSentB Zp cF lay x.link m = true) :
    ∀ i : Fin (sigListCalls (sentAt Zp) (rad3At Zp lay) x.link).length,
      seat3At Zp x.link false i.1 ∈ (N Zp cF).sent m 0 :=
  listSits_sent x (sentAt Zp) (rad3At Zp lay) (seat3At Zp x.link false) (N Zp cF) m h

/-- **ListSits.fits**, where the table's own members fit. -/
theorem calls_fits {Xi : Type} (G : VerifiableInference.Desc.FileDescription Xi)
    (x : VerifiableInference.Desc.First.Look.Place)
    (hf : ∀ y ∈ ms Zp lay, SeatFits G (sentAt Zp).codes y.1.l y.1.seat)
    (h : callsSomeB Zp lay x.link = true) :
    SeatFits G (sentAt Zp).codes (sigListCalls (sentAt Zp) (rad3At Zp lay) x.link)
      (fun j => seat3At Zp x.link false j.1) :=
  P5T.fits_of_some G _ (ms Zp lay) _ _ hf (calls_some Zp lay x h)

end P5J.At

#print axioms P5J.At.k3SeatsB_at
#print axioms P5J.At.calls_some
#print axioms P5J.At.calls_sent
#print axioms P5J.At.calls_fits
