-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/K3KeepsAt.lean: the kind "lookup" (K3): the lookups'
clause of the thread's letter "keeps", given by the member's place: one function from a place to a
sentence on the verifier's state in front and behind, made of the three clauses `K3KeepsCalls`,
`K3KeepsDigits` and `K3KeepsHead` (Honest/K3/Law/KeepsDefs.lean), with one proof for all three sorts
of member. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md ("keeps"). In this file: the state bears no mark if `failed = none`.
The three sorts of member are: at a lookup on the calls; at a lookup on the digits of a layers' or
an attention link; at the lookup on the digits of the head's link.

What is shown.
  `k3ClauseAt`: the clause at a site: no mark behind, whatever the sort; and the sort's own clause.
  `k3KeepsAt`: the function: at a place, the clause at every site that stands there.
  `k3KeepsAt_pays`: the clause holds behind the accepting step of the description's own member at a
    site's place, at any state and on any rounds.
  `k3KeepsAt_mark`: for a user of the clause: at a site's place there is no mark behind; the sort is
    not asked.
  `k3KeepsAt_calls`, `k3KeepsAt_digits`, `k3KeepsAt_head`: for a user of the clause: at a site's
    place it gives that sort's clause.
  `k3KeepsAt_else`: at a place where no site stands it says nothing.
Why the clause is made of sentences and has no cases by code. Which step without a round stands
behind a lookup on the digits is a function on states (`quietAt`,
Johnson/Desc/First/Look/K3Whole.lean): code cannot ask which one it is. So the clause says:
whichever of the two public forms it has, that form's clause holds; the plan's number of claims is
bound by that equation.

Hypotheses that remain, in `k3KeepsAt_pays`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the place p.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts from sj to sj'.
In the theorems for a user: the clause at the site's place; the site; its sort; at the digits the
equation `hq` on `quietAt` (`ht`: t is a site of the public part; `hd`: its sort). `hp`: (in
`k3KeepsAt_else`) no site stands at the place p.

Users. The clause is for whoever gives "keeps" as a letter by place (Honest/Thread/FirstHead.lean).
`k3KeepsAt_pays` is called in these files under Honest/K3/Law/Thread/:
AtLink.lean, K3KeepsStep.lean, NextBehind.lean, RidersAtHead.lean, RidersAtPlace.lean.
`k3KeepsAt_digits` is called in K3KeepsStep.lean, NextBehind.lean, QuietAtLink.lean and
RidersAtHead.lean; `k3KeepsAt_calls` and `k3KeepsAt_head` in K3KeepsStep.lean, NextBehind.lean and
RidersAtHead.lean. KeepsKind.lean [not in this library] imports this file too.

Limits. At a site on the digits where that step has neither form the clause says "no mark behind"
and no more. That it has one of the two at every such site is shown in
Honest/K3/Law/Thread/QuietSorts.lean, under one public test; whoever uses the sort's own clause
brings the equation. On the verifier's side alone. No instance of these hypotheses is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietDigits quietHead)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The clause at a site**: no mark behind, whatever the sort; and the sort's own clause. -/
def k3ClauseAt (Z : Pub) (t : Site) (s s' : FS) : Prop :=
  s'.failed = none ∧
  (t.digits = false → K3KeepsCalls t.shape s s') ∧
  (t.digits = true → ∀ used claims,
    quietAt Z.p.X t.link true = some (quietDigits used claims) →
    K3KeepsDigits t.shape claims s s') ∧
  (t.digits = true → quietAt Z.p.X t.link true = some (quietHead Z.p.X) →
    K3KeepsHead t.shape s s')

/-- **The lookups' clause of "keeps", by place.** -/
def k3KeepsAt (Z : Pub) (p : Place) (s s' : FS) : Prop :=
  ∀ t ∈ lookSites Z, t.at_.place = p → k3ClauseAt Z t s s'

/-- **The clause holds behind the member's accepting step, for all three sorts of member.**
No instance of these hypotheses is exhibited in this file. -/
theorem k3KeepsAt_pays (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (p : Place)
    (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = p)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat)
    (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (h : m.step ft sj rs c = .ok (sj', n)) : k3KeepsAt Z p sj sj' := by
  intro t ht hp
  have hbt : lot.place = t.at_.place := hbs.trans hp.symm
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact ⟨((hst ft sj sj' n rs c).1 h).2.1,
    fun hd => k3Keeps_calls o pol lay KL Fd Z Bs base ch A B O t ht hd lot m hb hbt hm hmp hpk
      ft sj sj' n rs c h,
    fun hd used claims hq => k3Keeps_digits o pol lay KL Fd Z Bs base ch A B O t ht hd lot m hb hbt
      hm hmp hpk used claims hq ft sj sj' n rs c h,
    fun hd hq => k3Keeps_head o pol lay KL Fd Z Bs base ch A B O t ht hd lot m hb hbt hm hmp hpk hq
      ft sj sj' n rs c h⟩

/-- **No mark behind a lookup's member**: the site's sort is not asked. -/
theorem k3KeepsAt_mark {Z : Pub} {t : Site} {s s' : FS} (h : k3KeepsAt Z t.at_.place s s')
    (ht : t ∈ lookSites Z) : s'.failed = none :=
  (h t ht rfl).1

theorem k3KeepsAt_calls {Z : Pub} {t : Site} {s s' : FS} (h : k3KeepsAt Z t.at_.place s s')
    (ht : t ∈ lookSites Z) (hd : t.digits = false) : K3KeepsCalls t.shape s s' :=
  (h t ht rfl).2.1 hd

theorem k3KeepsAt_digits {Z : Pub} {t : Site} {s s' : FS} (h : k3KeepsAt Z t.at_.place s s')
    (ht : t ∈ lookSites Z) (hd : t.digits = true) {used claims : Nat}
    (hq : quietAt Z.p.X t.link true = some (quietDigits used claims)) :
    K3KeepsDigits t.shape claims s s' :=
  (h t ht rfl).2.2.1 hd used claims hq

theorem k3KeepsAt_head {Z : Pub} {t : Site} {s s' : FS} (h : k3KeepsAt Z t.at_.place s s')
    (ht : t ∈ lookSites Z) (hd : t.digits = true)
    (hq : quietAt Z.p.X t.link true = some (quietHead Z.p.X)) : K3KeepsHead t.shape s s' :=
  (h t ht rfl).2.2.2 hd hq

/-- At a place where no site stands it says nothing. -/
theorem k3KeepsAt_else {Z : Pub} {p : Place} (hp : ∀ t ∈ lookSites Z, t.at_.place ≠ p)
    (s s' : FS) : k3KeepsAt Z p s s' :=
  fun t ht e => absurd e (hp t ht)

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_pays
#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_mark
#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_head
#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_else
