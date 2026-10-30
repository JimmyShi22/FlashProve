-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/MemberBack.lean: the kind "lookup" (K3): from an
accepting step back to the hearing, at any state: where the step of the description's own member at
a lookup's place has accepted, from whatever state and on whatever rounds, the seated hearing has
returned on these very rounds, from the ledger that the seat reads at that state, and the seat reads
what it heard at the state that the step leaves. No honest prover is spoken of. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the seated decision and the seated hearing are
`decideVia` and `hearVia` (Johnson/Desc/First/Look/Via/Via.lean). The two seats of the first chain
are `seatOf claim d` (Honest/K3/Law/Stated.lean).

What is shown.
  `decideVia_back`: an accepting seated decision, taken apart.
  `seat_back`: the same at the two seats of the first chain: what the seat reads behind it.
  `fit_len`, `step_len`: an accepting step was shown as many rounds as the sub-protocol has.
  `form_back`: the title's sentence at a sub-protocol of the lookups' form (`FormAt`,
    Honest/K3/Law/MemberOne.lean).
  `member_back`: the same at the description's own member at a lookup of a public part.

Hypotheses that remain. The first four theorems assume the acceptance alone; `form_back` assumes the
form besides (`Fm`: `FormAt`). `member_back` is conditional on:
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts.

Imported. `member_back` rests on the files under Honest/Member/.

Users. `member_back` is called in CallsHeardFront.lean [not in this library], CallsHeardLink.lean
and DigitsHeardLink.lean in this folder; `decideVia_back` and `step_len` in CEndBelow.lean and
PutG.lean; `step_len` also in StateBehind.lean; `fit_len` in MemberDecides.lean. `decideVia_whole`
(Honest/K3/Law/Thread/StateBehind.lean) states the conclusion of `decideVia_back` with two more
conjuncts.

Limits. On the verifier's side alone. Nothing is said of the values that the rounds show.
No instance of the hypotheses of `member_back` together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Seats
import Johnson.Desc.ProofFile.Honest.K3.Law.NoDigest
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Honest.K3.Law.BehindHands
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn noDigest roundsFit named need)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **An accepting seated decision, taken apart.** Conditional on that acceptance. -/
theorem decideVia_back {S Cl : Type} (seat : Seat S Cl) (p : P) (s s' : S) (rs : List Fmt.RoundView)
    (h : decideVia seat p s rs = .ok s') :
    ∃ F H G, seat.fork s = some F ∧ (seat.heard s).isNone = true ∧
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
            exact ⟨F, x.1, x.2, rfl, h1, hv, h.symm⟩
        · simp [hF, h1, h2, h3, named, need, bind, Except.bind] at h
      · simp [hF, h1, h2, named, need, bind, Except.bind] at h
    · simp [hF, h1, named, need, bind, Except.bind] at h

/-- **Behind an accepting seated decision the seat reads what the hearing returned; the hearing
began at the ledger that the seat read in front.** Conditional on that acceptance. -/
theorem seat_back {Cl : Type} (claim : Aff → Cl) (d : Bool) (p : P) (s s' : FS)
    (rs : List Fmt.RoundView) (h : decideVia (seatOf claim d) p s rs = .ok s') :
    ∃ F H G, (seatOf claim d).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
      (seatOf claim d).heard s' = some H ∧ (seatOf claim d).fork s' = some G := by
  obtain ⟨F, H, G, hF, h0, hv, rfl⟩ := decideVia_back _ p s s' rs h
  cases d with
  | false =>
    obtain ⟨a1, a2, _⟩ := calls_put claim s H G hF h0
    exact ⟨F, H, G, hF, hv, a1, a2⟩
  | true =>
    obtain ⟨a1, a2, _⟩ := digits_put claim s H G hF
    exact ⟨F, H, G, hF, hv, a1, a2⟩

/-- The format's test on rounds accepts lists of one length alone. -/
theorem fit_len : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    rs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | d :: ds, r :: rs, h => by
    simp only [roundsFit, Bool.and_eq_true] at h
    simp [fit_len ds rs h.2]

/-- An accepting step was shown as many rounds as the sub-protocol has. Conditional on that
acceptance. -/
theorem step_len {Cl : Type} (b : Block FS Cl) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    rs.length = b.rounds.length := by
  by_cases hr : roundsFit b.rounds rs = true
  · exact fit_len _ _ hr
  · unfold Block.step at h
    simp [hr, need, bind, Except.bind] at h

/-- **At a sub-protocol of the lookups' form: where its step has accepted, the seated hearing has
returned on the step's own rounds, from the ledger that the seat reads at the state in front, and
the seat reads what it heard at the state that the step leaves.** Conditional on the form and on
that acceptance. -/
theorem form_back {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) (ft : Nat) (s t : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    ∃ F H G, (seatOf claim d).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
      (seatOf claim d).heard t = some H := by
  have hl : rs.length = p.rounds.length := by rw [← Fm.rounds]; exact step_len b ft s t n rs c h
  obtain ⟨gs, hd⟩ := step_decide_at b ft s t n rs c h
  rcases Fm.form with ⟨_, hb⟩ | ⟨f, hq, hb⟩
  · rw [hb, NoDigest.decideVia_noDigest] at hd
    obtain ⟨F, H, G, hF, hv, a1, _⟩ := seat_back claim d p s t rs hd
    exact ⟨F, H, G, hF, hv, a1⟩
  · rw [hb, ← List.map_take, NoDigest.decideVia_noDigest, ← hl, List.take_length] at hd
    cases hs : decideVia (seatOf claim d) p s rs with
    | error e =>
      rw [hs] at hd
      exact nomatch hd
    | ok s' =>
      rw [hs] at hd
      have hf : f s' = .ok t := hd
      obtain ⟨F, H, G, hF, hv, a1, a2⟩ := seat_back claim d p s s' rs hs
      have hB : QuietBehind X i d s' t := by
        unfold QuietBehind
        rw [hq]
        exact hf
      exact ⟨F, H, G, hF, hv, (behind_hands claim hB a2).1.trans a1⟩

/-- **At the description's own member at a lookup of a public part.** Conditional on the hypotheses
that the head of this file lists. No instance of these hypotheses is exhibited in this file. -/
theorem member_back (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView)
    (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, (seatOf K3Lot.ofForm s.digits).fork sj = some F ∧ hearVia s.p F rs = some (H, G) ∧
      (seatOf K3Lot.ofForm s.digits).heard sj' = some H := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact form_back Fm ft sj sj' n rs c ((hst ft sj sj' n rs c).1 h).1

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.decideVia_back
#print axioms ProofFile.Honest.K3.Law.AtThr.seat_back
#print axioms ProofFile.Honest.K3.Law.AtThr.fit_len
#print axioms ProofFile.Honest.K3.Law.AtThr.step_len
#print axioms ProofFile.Honest.K3.Law.AtThr.form_back
#print axioms ProofFile.Honest.K3.Law.AtThr.member_back
