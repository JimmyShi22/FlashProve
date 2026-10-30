-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StateBehind.lean: the kind "lookup" (K3): the state
behind an accepting step, as an equation in the state's own setters: where the step of a
sub-protocol of the lookups' form, or of the description's own member at a lookup's place, has
accepted, from whatever state and on whatever rounds: which tests on the state in front have passed,
that the seated hearing has returned, and what the state behind is. No honest prover is spoken of.
Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the seated decision and the seated hearing are
`decideVia` and `hearVia` (Johnson/Desc/First/Look/Via/Via.lean). The lookups' form is `FormAt`
(Honest/K3/Law/MemberOne.lean). The seat's put is the field put of `Seat`
(Johnson/Desc/First/Look/K3Lookup.lean), its writer behind the hearing.

What is shown.
  `decideVia_whole`: an accepting seated decision, taken apart, with all four tests in front.
  `form_state`: the title's sentence at a sub-protocol of the lookups' form.
  `calls_state`: at the description's own member at a lookup on the calls: the state behind is the
    state in front with the ledger set, then what was heard set.
  `digits_put`: the seat's put at the digits, written out.

Hypotheses that remain. The first two theorems assume the acceptance (and the form, `Fm`);
`digits_put` assumes `htl`, `hF`: the state holds the smallness test's structure; a ledger is open.
`calls_state` is conditional on:
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts.

Users. The file is there for this: a projection of the state onto its shape (flags, counts, lengths)
is carried over an accepting step by applying it to both sides of such an equation. `form_state` is
called in Honest/K3/Law/Thread/StateBehindDigits.lean, Honest/K3/Law/Thread/StateBehindHead.lean,
Honest/K3/Law/Thread/StandsBehind.lean, Honest/K3/Law/Thread/HeadDigitsBack.lean and
Honest/K3/Law/Thread/DigitsTlKept.lean; `calls_state` in Honest/K3/Law/Thread/StateHere.lean and
Honest/K3/Law/Thread/StandsAt.lean; `decideVia_whole` in Honest/K3/Law/Thread/K3Keeps.lean,
Honest/K3/Law/Thread/CarriesHeadDigits.lean and Honest/K3/Law/Thread/HeadReturnsOf.lean;
`digits_put` in Honest/K3/Law/Thread/StateBehindDigits.lean,
Honest/K3/Law/Thread/StateBehindHead.lean, Honest/K3/Law/Thread/DigitsTlKept.lean,
Honest/K3/Law/Thread/HeadDigitsBack.lean, Honest/K3/Law/Thread/CarriesHeadDigits.lean and
Honest/K3/Law/Thread/HeadReturnsOf.lean. `decideVia_back` (Honest/K3/Law/Thread/MemberBack.lean)
states the conclusion of `decideVia_whole` less two conjuncts. Honest/K3/Good/Live/ClauseMark.lean
and Honest/K3/Good/Live/Windows.lean import this file too.

Limits. On the verifier's side alone. Of what the hearing returns nothing is said here. The lookup
on the digits has its put written out, not the step without a round behind it. Another theorem bears
the short name `digits_put`: that of Honest/K3/Law/Seats.lean, in the namespace above this one.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn named need)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits quietAt)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **An accepting seated decision, taken apart, with all four tests in front.** Conditional on that
acceptance. -/
theorem decideVia_whole {S Cl : Type} (seat : Seat S Cl) (p : P) (s s' : S) (rs : List Fmt.RoundView)
    (h : decideVia seat p s rs = .ok s') :
    ∃ F H G, seat.fork s = some F ∧ (seat.heard s).isNone = true ∧
      (seat.owed s).noneWaits = true ∧ (F.next == p.first) = true ∧
      hearVia p F rs = some (H, G) ∧ s' = seat.put s H G := by
  unfold decideVia at h
  cases hF : seat.fork s with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    by_cases h1 : (seat.heard s).isNone = true
    · by_cases h2 : (seat.owed s).noneWaits = true
      · by_cases h3 : (F.next == p.first) = true
        · cases hv : hearVia p F rs with
          | none => simp [hF, h1, h2, h3, hv, named, need, bind, Except.bind] at h
          | some x =>
            simp [hF, h1, h2, h3, hv, named, need, bind, Except.bind, pure, Except.pure] at h
            exact ⟨F, x.1, x.2, rfl, h1, h2, h3, hv, h.symm⟩
        · simp [hF, h1, h2, h3, named, need, bind, Except.bind] at h
      · simp [hF, h1, h2, named, need, bind, Except.bind] at h
    · simp [hF, h1, named, need, bind, Except.bind] at h

/-- **At a sub-protocol of the lookups' form**: the four tests in front, the hearing's return on the
step's own rounds, and the state behind: the seat's put, then the step without a round. Conditional
on the form and on the step's acceptance. -/
theorem form_state {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) (ft : Nat) (s t : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    ∃ F H G, (seatOf claim d).fork s = some F ∧ ((seatOf claim d).heard s).isNone = true ∧
      ((seatOf claim d).owed s).noneWaits = true ∧ (F.next == p.first) = true ∧
      hearVia p F rs = some (H, G) ∧ QuietBehind X i d ((seatOf claim d).put s H G) t := by
  have hl : rs.length = p.rounds.length := by rw [← Fm.rounds]; exact step_len b ft s t n rs c h
  obtain ⟨gs, hd⟩ := step_decide_at b ft s t n rs c h
  rcases Fm.form with ⟨hq, hb⟩ | ⟨f, hq, hb⟩
  · rw [hb, NoDigest.decideVia_noDigest] at hd
    obtain ⟨F, H, G, a1, a2, a3, a4, a5, rfl⟩ := decideVia_whole _ p s t rs hd
    refine ⟨F, H, G, a1, a2, a3, a4, a5, ?_⟩
    unfold QuietBehind
    rw [hq]
  · rw [hb, ← List.map_take, NoDigest.decideVia_noDigest, ← hl, List.take_length] at hd
    cases hs : decideVia (seatOf claim d) p s rs with
    | error e =>
      rw [hs] at hd
      exact nomatch hd
    | ok s' =>
      rw [hs] at hd
      have hf : f s' = .ok t := hd
      obtain ⟨F, H, G, a1, a2, a3, a4, a5, rfl⟩ := decideVia_whole _ p s s' rs hs
      refine ⟨F, H, G, a1, a2, a3, a4, a5, ?_⟩
      unfold QuietBehind
      rw [hq]
      exact hf

/-- **At the description's own member at a lookup on the calls: the state behind is the state in
front with the ledger set, then what was heard set; it bears no mark.** Conditional on the
hypotheses that the head of this file lists. No instance of these hypotheses is exhibited in this
file. -/
theorem calls_state (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, sj.fork? = some F ∧ sj.lookHeard?.isNone = true ∧
      VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      (F.next == s.p.first) = true ∧ hearVia s.p F rs = some (H, G) ∧
      sj' = (sj.putFork G).hearLook H ∧ sj'.failed = none := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  obtain ⟨hl, hf, _⟩ := (hst ft sj sj' n rs c).1 h
  rw [hd] at Fm
  obtain ⟨F, H, G, a1, a2, a3, a4, a5, hQ⟩ := form_state Fm ft sj sj' n rs c hl
  refine ⟨F, H, G, a1, a2, a3, a4, a5, ?_, hf⟩
  unfold QuietBehind at hQ
  cases hq : quietAt Z.p.X s.link false with
  | none =>
    rw [hq] at hQ
    exact hQ
  | some f =>
    rw [hq] at hQ
    exact quietAt_calls Z.p.X s.link f hq _ _ hQ

/-- **The seat's put at the digits, written out**, where a structure of the smallness test and a
ledger stand. -/
theorem digits_put {Cl : Type} (claim : Aff → Cl) (s : FS) {tl : OnBytes.Model.HTailF2} {F : Fork}
    (htl : s.tl? = some tl) (hF : s.fork? = some F) (H : OnBytes.Model.Forest.Heard) (G : Fork) :
    (seatDigits claim).put s H G =
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some H }).putFork G := by
  show (match s.tl?, s.fork? with
    | some tl, some F => _
    | _, _ => _ : FS) = _
  rw [htl, hF]

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.decideVia_whole
#print axioms ProofFile.Honest.K3.Law.AtThr.form_state
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_state
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_put
