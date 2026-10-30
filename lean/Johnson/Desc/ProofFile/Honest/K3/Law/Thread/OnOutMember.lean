-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OnOutMember.lean: the kind "lookup" (K3): the lookup's
promise behind (`k3OnOut`, Johnson/Desc/First/Look/K3Borders.lean) holds behind the accepting step
of the description's own member, where the lookup's promise in front (`k3OnIn`, there) held: at all
three sorts of member, at any state and on any rounds. The statements name no thread, no letters and
no honest prover. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the three sorts of member are the lookup on the calls,
the lookup on the digits of a layers' or an attention link, and the lookup on the digits of the
head's link.

What is shown.
  `site_pdigits`: at a site the parameters' sort is the site's.
  `ledger_onIn`: the promise in front, read at the ledger that the state holds.
  `onOut_atCalls`, `onOut_atDigits`, `onOut_atHead`: the title's sentence, one theorem for each sort
    of member.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: at the digits: which step without a round stands behind the lookup (a condition on public
    data).
  `hIn`: the promise in front.
  `h`: the member's step accepts.
  `hd`: the site's sort. `hF`: (in `ledger_onIn`) a ledger is open in front.

How the proof goes. By `onOut_of` (Honest/K3/Law/Thread/Out.lean), the state behind as an equation
(StateHere.lean, StateBehindDigits.lean and StateBehindHead.lean in this folder) and `hearVia_back`
(Honest/K3/Law/Thread/K3Keeps.lean).

Users. Honest/K3/Law/Thread/RidersAtSite.lean and Honest/K3/Law/Thread/QuietSorts.lean call the
three theorems on `k3OnOut`; `next_ofPlace` (Honest/K3/Law/Thread/NextBehind.lean) calls
`ledger_onIn`.

Limits. On the verifier's side alone. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Front
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OutSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt quietDigits quietHead k3OnIn k3OnOut heardAt)
open VerifiableInference.Desc.First (S)

local notation "FS" => VerifiableInference.Desc.First.S

/-- At a site the parameters' sort is the site's. -/
theorem site_pdigits {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) : s.p.digits = s.digits := by
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, _, f4, _⟩ := site_facts _ _ x s hsx
  exact (placeAt_digits f1).trans f4.symm

/-- **The promise in front, read at the ledger that the state holds.** -/
theorem ledger_onIn {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) {sj : FS} {F : Fork}
    (hIn : k3OnIn s.p sj = true) (hF : sj.fork? = some F) :
    Sized F ∧ F.next = s.p.first ∧ s.p.first + (faceOf s.shape).slots ≤ F.ns ∧
      ∀ j, F.next ≤ j → j < s.p.first + (faceOf s.shape).slots → ¬ Filled F j := by
  obtain ⟨hh, G, b1, _, _, b4, b5, b6, b7⟩ := onIn_parts hIn
  obtain rfl : hh = s.shape := Option.some.inj (b1.symm.trans (site_shape hs))
  obtain rfl : G = F := Option.some.inj (b4.symm.trans hF)
  obtain ⟨c1, c2, c3⟩ := ledger_of b6 b7
  rw [Spec.slots_elems]
  exact ⟨c1, b5, c2, fun j h1 h2 => c3 j (by rw [← b5]; exact h1) h2⟩

section
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
  (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
  (hs : s ∈ lookSites Z)
include O hs

/-- **At a lookup on the calls.** No instance of these hypotheses is exhibited in this file. -/
theorem onOut_atCalls (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (hIn : k3OnIn s.p sj = true)
    (h : m.step ft sj rs c = .ok (sj', n)) : k3OnOut s.p sj' = true := by
  obtain ⟨F, H, G, a1, _, a5, hC, _⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot
    m hb hbs hm hmp hpk ft sj sj' n rs c h
  obtain ⟨c1, c2, c3, c4⟩ := ledger_onIn hs hIn a1
  obtain ⟨g, hg, hH⟩ := hearVia_back (site_shape hs) a5
  refine onOut_of s.p s.shape (site_shape hs) c1 c2 c3 c4 hg hH sj' G.planClaimsF ?_ ?_
  · rw [site_pdigits hs, hd]
    show sj'.lookHeard? = some H
    rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
    · simp [S.lookHeard?]
    · simp [S.lookHeard?]
    · simp [S.lookHeard?, ho]
  · show sj'.fork? = some G
    rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
    · simp [S.fork?]
    · simp [S.fork?]
    · simp [S.fork?, ho]

/-- **At a lookup on the digits of a layers' or an attention link.** No instance of these hypotheses
is exhibited in this file. -/
theorem onOut_atDigits (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (hIn : k3OnIn s.p sj = true)
    (h : m.step ft sj rs c = .ok (sj', n)) : k3OnOut s.p sj' = true := by
  obtain ⟨tl, F, H, G, _, a1, _, _, _, a5, _, e, _⟩ := digits_state o pol lay KL Fd Z Bs base ch
    A B O s hs hd lot m hb hbs hm hmp hpk used claims hq ft sj sj' n rs c h
  obtain ⟨c1, c2, c3, c4⟩ := ledger_onIn hs hIn a1
  obtain ⟨g, hg, hH⟩ := hearVia_back (site_shape hs) a5
  have hC := digits_arms_of a1 e
  refine onOut_of s.p s.shape (site_shape hs) c1 c2 c3 c4 hg hH sj' claims ?_ ?_
  · rw [site_pdigits hs, hd]
    show sj'.tl?.bind (·.heard) = some H
    rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
    · simp [S.tl?]
    · simp [S.tl?]
    · simp [S.tl?, ho]
  · rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
    · simp [S.fork?]
    · simp [S.fork?]
    · simp [S.fork?, ho]

/-- **At the lookup on the digits of the head's link.** No instance of these hypotheses is exhibited
in this file. -/
theorem onOut_atHead (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (hIn : k3OnIn s.p sj = true)
    (h : m.step ft sj rs c = .ok (sj', n)) : k3OnOut s.p sj' = true := by
  obtain ⟨tl, F, H, G, a, claim, _, a1, _, _, _, a5, eh, _, e, _⟩ := headDigits_state o pol lay
    KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq ft sj sj' n rs c h
  obtain ⟨c1, c2, c3, c4⟩ := ledger_onIn hs hIn a1
  obtain ⟨g, hg, hH⟩ := hearVia_back (site_shape hs) a5
  cases hh : sj.here with
  | head a₀ =>
    have hF' : (if a₀.opened = true then some a₀.F else none) = some F := by
      have := a1
      unfold S.fork? at this
      rw [hh] at this
      exact this
    cases ho₀ : a₀.opened with
    | false =>
      rw [ho₀] at hF'
      exact nomatch hF'
    | true =>
      simp only [S.putTl, S.putFork, hh, ho₀, if_true] at eh e
      obtain rfl := VerifiableInference.Desc.First.Here.head.inj eh
      refine onOut_of s.p s.shape (site_shape hs) c1 c2 c3 c4 hg hH sj' G.planClaimsF ?_ ?_
      · rw [site_pdigits hs, hd]
        show sj'.tl?.bind (·.heard) = some H
        rw [e]
        simp [S.tl?]
      · show sj'.fork? = some G
        rw [e]
        simp [S.fork?]
  | lay a₀ => simp [S.putTl, S.putFork, hh] at eh
  | att a₀ => simp [S.putTl, S.putFork, hh] at eh
  | between => simp [S.putTl, S.putFork, hh] at eh
  | fin a₀ => simp [S.putTl, S.putFork, hh] at eh
  | mem a₀ => simp [S.putTl, S.putFork, hh] at eh

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.site_pdigits
#print axioms ProofFile.Honest.K3.Law.AtThr.ledger_onIn
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_atCalls
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_atDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_atHead
