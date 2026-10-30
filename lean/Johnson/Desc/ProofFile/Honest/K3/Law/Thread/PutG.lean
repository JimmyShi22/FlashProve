-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PutG.lean: the honest side of the kind "lookup" (K3):
behind the lookup on the calls at an attention link the link's own field g holds what was heard: the
seat on the calls reads the field lookHeard; the library's text that sets what was heard
(`S.hearLook`, Johnson/Desc/First/State.lean) sets the same value into g too. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: g is a field of the attention link's own part of the
state (the arm att of `Here`, Johnson/Desc/First/State.lean). The seat on the calls is `seatCalls`
(Johnson/Desc/First/Look/K3Seat.lean).

What is shown.
  `put_g`: the seat's writer: at an attention link g holds the value that is set.
  `quietAt_calls`: the step without a round behind a lookup on the calls leaves the state as it is.
  `form_back_g`: the title's sentence behind an accepting step of a sub-protocol of the lookups'
    form (`FormAt`, Honest/K3/Law/MemberOne.lean), on the calls.
  `member_back_g`: the same at the description's own member at a lookup of a public part.

Hypotheses that remain.
  In `put_g`: `hF`, `h0`: an open ledger, and nothing heard at the seat.
  In the others: `h`: the accepting step (in `quietAt_calls`: of the step without a round, which
    `hq` names; in `form_back_g` with `Fm`: the lookups' form).
  In `member_back_g` besides: the hypotheses that the head of Honest/K3/Law/Thread/MemberBack.lean
    lists (`O`, `hs`, `hb`, `hbs`, `hm`, `hmp`, `hpk`), and `hd`: the lookup is on the calls.

Users. `back_g_link` (Honest/K3/Law/Thread/AtLink.lean) calls `member_back_g`;
Honest/K3/Law/Thread/CEndBelow.lean and Honest/K3/Law/Thread/StateBehind.lean call `quietAt_calls`.

Limits. Conditional on the hypotheses above. At a link of another sort the statements say nothing.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.MemberBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (seatCalls quietAt isHead)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The seat on the calls sets what was heard into the attention link's field g too.** Conditional
on an open ledger and nothing heard at the seat. -/
theorem put_g {Cl : Type} (claim : Aff → Cl) (s : FS) {F : Fork} (H : OnBytes.Model.Forest.Heard)
    (G : Fork) (hF : (seatCalls claim).fork s = some F)
    (h0 : ((seatCalls claim).heard s).isNone = true) :
    ∀ att, ((seatCalls claim).put s H G).here = .att att → att.g = some H := by
  have hF' : s.fork? = some F := hF
  have h0' : s.lookHeard?.isNone = true := h0
  intro att hatt
  have hatt' : ((s.putFork G).hearLook H).here = .att att := hatt
  unfold VerifiableInference.Desc.First.S.fork? at hF'
  unfold VerifiableInference.Desc.First.S.lookHeard? at h0'
  cases hh : s.here with
  | lay a =>
    rw [hh] at h0'
    simp only [Option.isNone_iff_eq_none] at h0'
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook, hh,
      h0'] at hatt'
  | att a =>
    rw [hh] at h0'
    simp only [Option.isNone_iff_eq_none] at h0'
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook, hh,
      h0'] at hatt'
    rw [← hatt']
  | head a =>
    rw [hh] at h0' hF'
    by_cases ho : a.opened = true
    · simp only [ho, if_true, Option.isNone_iff_eq_none] at h0'
      simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook, hh,
        h0', ho] at hatt'
    · simp [ho] at hF'
  | between => rw [hh] at hF'; exact nomatch hF'
  | fin a => rw [hh] at hF'; exact nomatch hF'
  | mem a => rw [hh] at hF'; exact nomatch hF'

/-- The step without a round behind a lookup on the calls leaves the state as it is. Conditional on
its acceptance. -/
theorem quietAt_calls (X : OnBytes.Model.Verify.Public) (i : Nat) (f : FS → Except String FS)
    (hq : quietAt X i false = some f) (s' t : FS) (h : f s' = .ok t) : t = s' := by
  unfold quietAt at hq
  dsimp only at hq
  by_cases hH : isHead X i = true
  · rw [if_pos hH, if_neg (by simp)] at hq
    cases hq
  · rw [if_neg hH] at hq
    generalize (if X.p4 = true then 2 else 1) = st at hq
    by_cases hm : (i % st == 0) = true
    · rw [if_pos hm, if_neg (by simp)] at hq
      obtain rfl := Option.some.inj hq
      exact quietLook_keeps _ s' t h
    · rw [if_neg hm, if_neg (by simp)] at hq
      cases hq

/-- **Behind an accepting step of a sub-protocol of the lookups' form, on the calls**: the seated
hearing has returned on the step's own rounds, from the ledger that the seat reads in front; and at
an attention link g holds what it heard. Conditional on the form and on that acceptance. -/
theorem form_back_g {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {p : P} {b : Block FS Cl} (Fm : FormAt claim X i false p b) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    ∃ F H G, (seatCalls claim).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
      ∀ att, t.here = .att att → att.g = some H := by
  have hl : rs.length = p.rounds.length := by rw [← Fm.rounds]; exact step_len b ft s t n rs c h
  obtain ⟨gs, hd⟩ := step_decide_at b ft s t n rs c h
  have key : ∀ s', decideVia (seatCalls claim) p s rs = .ok s' →
      ∃ F H G, (seatCalls claim).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
        ∀ att, s'.here = .att att → att.g = some H := by
    intro s' hs'
    obtain ⟨F, H, G, hF, h0, hv, rfl⟩ := decideVia_back _ p s s' rs hs'
    exact ⟨F, H, G, hF, hv, put_g claim s H G hF h0⟩
  rcases Fm.form with ⟨_, hb⟩ | ⟨f, hq, hb⟩
  · rw [hb, NoDigest.decideVia_noDigest] at hd
    exact key t hd
  · rw [hb, ← List.map_take, NoDigest.decideVia_noDigest, ← hl, List.take_length] at hd
    cases hs : decideVia (seatOf claim false) p s rs with
    | error e =>
      rw [hs] at hd
      exact nomatch hd
    | ok s' =>
      rw [hs] at hd
      have hf : f s' = .ok t := hd
      rw [quietAt_calls X i f hq s' t hf]
      exact key s' hs

/-- **At the description's own member at a lookup on the calls of a public part.** Conditional on
the hypotheses that the head of Honest/K3/Law/Thread/MemberBack.lean lists, and on the lookup being
one on the calls. No instance of these hypotheses is exhibited in this file. -/
theorem member_back_g (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, (seatCalls K3Lot.ofForm).fork sj = some F ∧ hearVia s.p F rs = some (H, G) ∧
      ∀ att, sj'.here = .att att → att.g = some H := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  rw [hd] at Fm
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact form_back_g Fm ft sj sj' n rs c ((hst ft sj sj' n rs c).1 h).1

#print axioms ProofFile.Honest.K3.Law.AtThr.put_g
#print axioms ProofFile.Honest.K3.Law.AtThr.quietAt_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.form_back_g
#print axioms ProofFile.Honest.K3.Law.AtThr.member_back_g

end ProofFile.Honest.K3.Law.AtThr
