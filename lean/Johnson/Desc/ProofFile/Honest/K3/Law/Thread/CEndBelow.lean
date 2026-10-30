-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CEndBelow.lean: the honest side of the kind "lookup"
(K3): the form in which the lookup's key side ends names the lookup's own slots alone, from the
ledger's count in front of the hearing on and below its count behind, and no entry of a virtual row.
Shown from the hearing's return, on any rounds; and behind the accepting step of a lookup on the
calls. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the hearing is `hearVia p F rs`
(Johnson/Desc/First/Look/Via/Via.lean); `messagesV` (Johnson/Desc/First/Look/Via/Rounds.lean) is the
reading of the messages inside it. The form in which the key side ends is the field cEnd of the
heard structure. A sub-protocol of the lookups' form is one with `FormAt`
(Honest/K3/Law/MemberOne.lean).

What is shown.
  `messagesV_next`: behind the hearing the ledger's count is its count in front plus the number of
    the lookup's slots. This is the hearing's own last test; nothing is assumed of the ledger.
  `cEnd_below`: the statement above, of the field cEnd of what the hearing returns.
  `form_back_cEnd`: behind an accepting step of a sub-protocol of the lookups' form, on the calls:
    the seat reads what was heard and the ledger behind the hearing; and the same of cEnd.
  `member_back_cEnd`: the same at the description's own member at a lookup on the calls of a public
    part.

Hypotheses that remain.
  `h`: (in `messagesV_next`, `cEnd_below`) the return of `messagesV`, or of the hearing.
  `Fm`, `h`: (in `form_back_cEnd`) b has the lookups' form; its step accepts.
  In `member_back_cEnd`, what the head of Honest/K3/Law/Thread/MemberBack.lean lists, and that the
    lookup is on the calls:
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts from sj to sj'.

Users. `cEnd_below` is called in Honest/K3/Law/Thread/CallsHeardLink.lean and
Honest/K3/Law/Thread/DigitsHeardLink.lean; `member_back_cEnd` in `back_cEnd_link`
(Honest/K3/Law/Thread/AtLink.lean) and in Honest/K3/Law/Thread/LeftAtCalls.lean; `messagesV_next` in
Honest/K3/Law/Thread/K3Keeps.lean. Honest/K3/Good/Live/Windows.lean imports this file too.

Limits. Conditional on the hearing's return, or on the accepting step. That the ledger's count at a
later border is no smaller than the count behind the hearing is the caller's to show. The hearing
`hearVia` returns at a face with one part of keys alone: so these theorems speak of a proof file's
lookups. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutG
import Johnson.Desc.ProofFile.Honest.K3.Parts.NoEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV toHeard toHeardG faceOf seatCalls)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P)
open ProofFile.Honest.K3.Parts (heard_names hearV_ne)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Behind the hearing the ledger's count is its count in front plus the number of the lookup's
slots.** Conditional on the return of `messagesV`. -/
theorem messagesV_next {f : LFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV}
    (h : messagesV f F rs = some (g, G, rest)) : G.next = F.next + f.slots := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨_, hG, _⟩ := pure_spec h
  have a1 := slot_spec e1
  have a17 := slot_spec e17
  have a18 := must_spec e18
  have t : sl = slot0 + f.slots := by
    have q := a18.1
    simp only [Bool.and_eq_true, beq_iff_eq] at q
    exact q.1
  rw [hG, a18.2, a17.2, ← a17.1, t, a1.1]

/-- **The form in which the key side ends names the lookup's own slots alone, and no entry of a
virtual row.** Conditional on the hearing's return. -/
theorem cEnd_below {p : P} {F G : Fork} {rs : List Fmt.RoundView} {H : OnBytes.Model.Forest.Heard}
    (h : hearVia p F rs = some (H, G)) :
    H.cEnd.ents.isEmpty = true ∧ ∀ x ∈ H.cEnd.slots.toList, F.next ≤ x.1 ∧ x.1 < G.next := by
  unfold hearVia at h
  cases hs : p.shape with
  | none => rw [hs] at h; exact nomatch h
  | some sh =>
    rw [hs] at h
    dsimp only at h
    by_cases hc : 1 < sh.NC
    · rw [if_pos hc] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨g, G'⟩ := x
      obtain ⟨H', hH, e⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨hok, hm⟩ := hearV_messages hx
      have hn := messagesV_next hm
      obtain ⟨_, n2, _⟩ := heard_names (two_le_planes_of_ok _ hok) hm
      obtain ⟨_, m2, _⟩ := hearV_ne hx
      unfold toHeard at hH
      have hk : (toHeardG g).keys = g.keys := rfl
      rw [hk] at hH
      match hg : g.keys, hH with
      | [(point, form)], hH =>
        dsimp only at hH
        split at hH
        · obtain rfl := Option.some.inj hH
          have hmem : (point, form) ∈ g.keys := by rw [hg]; exact List.mem_singleton.2 rfl
          refine ⟨m2 _ hmem, fun x hx => ?_⟩
          rw [hn]
          exact n2 _ hmem x hx
        · exact nomatch hH
    · rw [if_neg hc] at h
      exact nomatch h

/-- **Behind an accepting step of a sub-protocol of the lookups' form, on the calls.** Conditional
on the form and on that acceptance. -/
theorem form_back_cEnd {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {p : P} {b : Block FS Cl} (Fm : FormAt claim X i false p b) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : b.step ft s rs c = .ok (t, n)) :
    ∃ F H G, (seatCalls claim).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
      (seatCalls claim).heard t = some H ∧ (seatCalls claim).fork t = some G ∧
      H.cEnd.ents.isEmpty = true ∧ ∀ x ∈ H.cEnd.slots.toList, F.next ≤ x.1 ∧ x.1 < G.next := by
  have hl : rs.length = p.rounds.length := by rw [← Fm.rounds]; exact step_len b ft s t n rs c h
  obtain ⟨gs, hd⟩ := step_decide_at b ft s t n rs c h
  have key : ∀ s', decideVia (seatCalls claim) p s rs = .ok s' →
      ∃ F H G, (seatCalls claim).fork s = some F ∧ hearVia p F rs = some (H, G) ∧
        (seatCalls claim).heard s' = some H ∧ (seatCalls claim).fork s' = some G ∧
        H.cEnd.ents.isEmpty = true ∧
        ∀ x ∈ H.cEnd.slots.toList, F.next ≤ x.1 ∧ x.1 < G.next := by
    intro s' hs'
    obtain ⟨F, H, G, hF, h0, hv, rfl⟩ := decideVia_back _ p s s' rs hs'
    obtain ⟨a1, a2, _⟩ := calls_put claim s H G hF h0
    obtain ⟨c1, c2⟩ := cEnd_below hv
    exact ⟨F, H, G, hF, hv, a1, a2, c1, c2⟩
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
what the head of Honest/K3/Law/Thread/MemberBack.lean lists, and on the lookup being one on the
calls. No instance of these hypotheses is exhibited in this file. -/
theorem member_back_cEnd (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, (seatCalls K3Lot.ofForm).fork sj = some F ∧ hearVia s.p F rs = some (H, G) ∧
      (seatCalls K3Lot.ofForm).heard sj' = some H ∧ (seatCalls K3Lot.ofForm).fork sj' = some G ∧
      H.cEnd.ents.isEmpty = true ∧ ∀ x ∈ H.cEnd.slots.toList, F.next ≤ x.1 ∧ x.1 < G.next := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  rw [hd] at Fm
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact form_back_cEnd Fm ft sj sj' n rs c ((hst ft sj sj' n rs c).1 h).1

#print axioms ProofFile.Honest.K3.Law.AtThr.messagesV_next
#print axioms ProofFile.Honest.K3.Law.AtThr.cEnd_below
#print axioms ProofFile.Honest.K3.Law.AtThr.form_back_cEnd
#print axioms ProofFile.Honest.K3.Law.AtThr.member_back_cEnd

end ProofFile.Honest.K3.Law.AtThr
