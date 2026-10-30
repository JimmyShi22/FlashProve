--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/QuietRide.lean (over
Johnson/Desc/First/PubFoot.lean: footOf, SameOn and Rdr.same take D; pubAll_same asks that base has
one value): THE PROMISE's PUBLIC TEST AT A BORDER (ePubAt, Johnson/Desc/First/EPubAt.lean) IS HANDED
ON ACROSS A STEP THAT LEAVES A LIST OF READERS OF THE VERIFIER's STATE: THE RIDE: for the public
items that are asked on both sides and are booked (footOf D) as reading readers of that list alone;
every other item that is asked behind is a premise. Definitions and theorems, proved.

  frontAt, behindAt   what is asked in front of number k of the list of places, and behind the place
    there: ePubAt's own two lists.
  ridesK D keeps A q   q is asked in front and its footprint lies inside keeps.
  madeAtK D keeps M links ps k p   WHAT DOES NOT RIDE: the items asked behind that are not so: new
    ones; ones whose footprint is not booked; ones that read a reader outside keeps.
  more_keeps   THE RIDE, AT ANY LIST: SameOn D keeps s s', base alike at s and s', the items of
    madeAtK true at s', ePubAt at k and s: then ePubAt at k + 1 and s'.
  keepsQ   five readers: the statement, what goes on to the later chains, the frame between
    segments, the open segment's link context, the book. keepsT: these and the approximate range
    proof's parameters.
  sameOn_keepsQ, sameOn_keepsT   from the relations Quiet (RecQuiet.lean: the statement, the book),
    Outer (OuterSeated.lean: out; the state's own field check, so its frame), SameLink
    (LinkSeated.lean), SameTl (TlSeated.lean).
  ridesQ, madeAtQ   the two at keepsQ. more_quiet, more_quietT: the ride at keepsQ and at keepsT.

OBJECT: ePubAt (pubAll D base) moreAll links pl. USER: Johnson/IMR/MadeOwed.lean. LETTERS: D, base,
links, pl, z, k, p, keeps: free: the theorems ask nothing of the place's kind.

What is not claimed. How many items ride: an evaluation, in another file. Any item of madeAtK. That
base is alike. No soundness.
-/
import Johnson.Desc.First.EPubAt
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.First.PubFoot
import Johnson.Desc.Sound.MoreAll
import Johnson.Goal.Meaning.OuterSeated
import Johnson.Goal.Meaning.LinkSeated
import Johnson.Goal.Meaning.TlSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Ride

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Item Pub More PubData Rdr SameOn footOf pubAll
  pubAll_same ePubAt start openSets stepOpen rowOf pubSets pubStep pubRowM pubOfItems
  openSets_succ pubSets_succ)
open Meaning.K2 (Quiet)
open Meaning.Out (Outer)
open Meaning.Lnk (SameLink)
open Meaning.Tl (SameTl)

/-! ## The rule, at any list of readers -/

/-- What is asked in front of number k. -/
def frontAt (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  (pubSets M links ps)[k]?.getD [] ++ pubOfItems ((openSets links ps (start links))[k]?.getD [])

/-- What is asked behind the place p at number k. -/
def behindAt (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place) : List Pub :=
  pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) ++
    pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))

/-- The item is asked in front and is booked as reading readers of the list alone. -/
def ridesK (D : PubData) (keeps : List Rdr) (A : List Pub) (q : Pub) : Bool :=
  A.contains q && (footOf D q).any fun R => R.all keeps.contains

/-- **WHAT DOES NOT RIDE**: the items that are asked behind the place and are not "asked in front
with a footprint inside the list": they are the kind's own to show. -/
def madeAtK (D : PubData) (keeps : List Rdr) (M : More) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (p : Place) : List Pub :=
  (behindAt M links ps k p).filter fun q => !ridesK D keeps (frontAt M links ps k) q

section
variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (links : List ModelPart) (pl : List Place)
  (z : P) (k : ℕ) (p : Place)

/-- **THE RIDE, AT ANY LIST OF READERS**: across a step that leaves them: where the promise's public
test holds in front of number k, and the items that do not ride hold behind, it holds behind. -/
theorem more_keeps (keeps : List Rdr) (hp : pl[k]? = some p) (s s' : S)
    (hs : SameOn D keeps s s') (alike : ∀ x, base x (z, s') = base x (z, s))
    (made : ∀ x ∈ madeAtK D keeps moreAll links pl k p, pubAll D base x (z, s') = true)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true := by
  unfold ePubAt at h ⊢
  rw [pubSets_succ moreAll links pl k p hp, openSets_succ links pl (start links) k p hp]
  rw [List.all_eq_true] at h ⊢
  intro x hx
  by_cases hr : ridesK D keeps (frontAt moreAll links pl k) x = true
  · obtain ⟨hin, hfoot⟩ := Bool.and_eq_true_iff.1 hr
    have hfront := h x (by simpa [frontAt] using hin)
    cases hf : footOf D x with
    | none => simp [hf] at hfoot
    | some R =>
      rw [hf] at hfoot
      have h4 : R.all keeps.contains = true := hfoot
      rw [pubAll_same D base x R hf z s s' (fun r hr' => hs r (by
        have := List.all_eq_true.1 h4 r hr'
        simpa using this)) (alike x)]
      exact hfront
  · exact made x (List.mem_filter.2 ⟨hx, by simpa using hr⟩)

end

/-! ## The six kinds -/

/-- The five readers of the verifier's state that the six kinds leave. -/
def keepsQ : List Rdr := [.st, .out, .frame, .link, .book]

/-- The six that they leave in front of the digits' lookup, but for the smallness test. -/
def keepsT : List Rdr := [.st, .out, .frame, .link, .book, .tl]

/-- **The three relations give the five readers.** -/
theorem sameOn_keepsQ (D : PubData) {s s' : S} (q : Quiet s s') (o : Outer s s')
    (l : SameLink s s') : SameOn D keepsQ s s' := by
  intro r hr
  simp only [keepsQ, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact q.1.1
  · exact o.1
  · exact congrArg (·.frame) o.2.1
  · exact l
  · exact q.1.2.2.1

/-- **With the fourth relation: the six.** -/
theorem sameOn_keepsT (D : PubData) {s s' : S} (q : Quiet s s') (o : Outer s s')
    (l : SameLink s s') (t : SameTl s s') : SameOn D keepsT s s' := by
  intro r hr
  simp only [keepsT, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact q.1.1
  · exact o.1
  · exact congrArg (·.frame) o.2.1
  · exact l
  · exact q.1.2.2.1
  · exact t

/-- One of the six kinds. -/
def quietKind (k : KindName) : Bool :=
  k == .K3 || k == .K4 || k == .K5 || k == .K6 || k == .K8 || k == .K11

/-- ridesK at the five readers. -/
abbrev ridesQ (D : PubData) (A : List Pub) (q : Pub) : Bool := ridesK D keepsQ A q

/-- madeAtK at the five readers. -/
abbrev madeAtQ (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place) :
    List Pub :=
  madeAtK D keepsQ M links ps k p

section
variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (links : List ModelPart) (pl : List Place)
  (z : P) (k : ℕ) (p : Place)

/-- **THE RIDE AT THE FIVE READERS.** -/
theorem more_quiet (hp : pl[k]? = some p) (s s' : S) (q : Quiet s s') (o : Outer s s')
    (l : SameLink s s') (alike : ∀ x, base x (z, s') = base x (z, s))
    (made : ∀ x ∈ madeAtQ D moreAll links pl k p, pubAll D base x (z, s') = true)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true :=
  more_keeps D base links pl z k p keepsQ hp s s' (sameOn_keepsQ D q o l) alike made h

/-- **THE RIDE AT THE SIX.** -/
theorem more_quietT (hp : pl[k]? = some p) (s s' : S) (q : Quiet s s') (o : Outer s s')
    (l : SameLink s s') (t : SameTl s s') (alike : ∀ x, base x (z, s') = base x (z, s))
    (made : ∀ x ∈ madeAtK D keepsT moreAll links pl k p, pubAll D base x (z, s') = true)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true :=
  more_keeps D base links pl z k p keepsT hp s s' (sameOn_keepsT D q o l t) alike made h

end

end Meaning.Ride

#print axioms Meaning.Ride.sameOn_keepsQ
#print axioms Meaning.Ride.more_keeps
#print axioms Meaning.Ride.more_quiet
#print axioms Meaning.Ride.more_quietT
