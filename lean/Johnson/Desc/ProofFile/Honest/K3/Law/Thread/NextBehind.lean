-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/NextBehind.lean: the kind "lookup" (K3): behind a lookup
the ledger's next free slot is exactly the lookup's first slot plus its number of hidden values:
"=", where the lookup's promise behind (`k3OnOut`, Johnson/Desc/First/Look/K3Borders.lean) has "≤".
At every sort of site. From the lookups' clause of "keeps" by place (`k3KeepsAt`,
Honest/K3/Law/Thread/K3KeepsAt.lean) and the lookup's promise in front (`k3OnIn`,
Johnson/Desc/First/Look/K3Borders.lean): the first theorem names no step, no thread and no letters.
Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a lookup's number of hidden values is
`OnBytes.Model.Forest.elems` of its shape (OnBytes/Model/Forest.lean).

What is shown.
  `next_ofPlace`: the title's sentence.
  `fork_head`: in the head's link the state's open ledger is that link's own.
  `next_atSite`: hence the same behind the accepting step of the description's own member.

Hypotheses that remain.
  `hs`: s is a site of the public part (`lookSites Z`).
  `hT3`: one test with code on public data. The proof uses it for `quiet_sorts`
    (Honest/K3/Law/Thread/QuietSorts.lean) alone.
  `h`: (in `next_ofPlace`) the lookups' clause `k3KeepsAt` at the site's place.
  `hIn`: the lookup's promise in front (`k3OnIn`).
  In `next_atSite`, in the place of the clause: the hypotheses of `k3KeepsAt_pays`
    (Honest/K3/Law/Thread/K3KeepsAt.lean): `O`, `hb`, `hbs`, `hm`, `hmp`, `hpk`, and `h`: the
    member's step accepts.
  `hh`, `hf`: (in `fork_head`) the state stands in the head's link; a ledger is open.
Beside it. `next_behind` (Honest/K3/Good/Live/Windows.lean) has the same equation behind an
accepting step of a sub-protocol of the lookups' form, from the form, the place's shape and the
acceptance alone: without `hIn` and `hT3`. It speaks of the lot's sub-protocol, `next_atSite` of the
description's own member.

How the proof goes. By the clause's `LedgerKept` (Honest/K3/Law/KeepsDefs.lean: the count behind is
the count in front plus the face's slots), `ledger_onIn` (Honest/K3/Law/Thread/OnOutMember.lean: the
count in front is the lookup's first slot) and `Spec.slots_elems` (Honest/K3/Law/SlotsElems.lean).

Users. `lays_of_next`, `lays_of_nextHead` and `lays_of_nextHeadCalls`
(Honest/K3/Law/Thread/LaysNext.lean) and `lays_of_nextHead_light`
(Honest/K3/Law/Thread/LaysNextLight.lean) call `next_atSite`; the last three also call `fork_head`.

Limits. On the verifier's side alone. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (k3OnIn)
open VerifiableInference.Desc.First (S)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Behind a lookup the ledger's next free slot is its first slot plus its number of hidden
values.** -/
theorem next_ofPlace {Z : Pub} {s : Site} {st st' : FS} (h : k3KeepsAt Z s.at_.place st st')
    (hs : s ∈ lookSites Z)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (hIn : k3OnIn s.p st = true) :
    ∃ G, st'.fork? = some G ∧ G.next = s.p.first + OnBytes.Model.Forest.elems s.shape := by
  cases hd : s.digits with
  | false =>
    obtain ⟨_, F, H, G, hF, hC, LK⟩ := k3KeepsAt_calls h hs hd
    obtain ⟨_, c2, _, _⟩ := ledger_onIn hs hIn hF
    refine ⟨G, ?_, by rw [LK.2.2.2.1, c2, Spec.slots_elems]⟩
    rcases hC with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
    · simp [S.fork?]
    · simp [S.fork?]
    · simp [S.fork?, ho]
  | true =>
    rcases quiet_sorts hs hd hT3 with hq | ⟨used, claims, hq⟩
    · obtain ⟨_, tl, F, H, G, a₀, claim, _, hF, _, ho, e, LK⟩ := k3KeepsAt_head h hs hd hq
      obtain ⟨_, c2, _, _⟩ := ledger_onIn hs hIn hF
      refine ⟨G, ?_, by rw [LK.2.2.2.1, c2, Spec.slots_elems]⟩
      rw [e]
      simp [S.fork?, ho]
    · obtain ⟨_, tl, F, H, G, _, hF, hA, LK⟩ := k3KeepsAt_digits h hs hd hq
      obtain ⟨_, c2, _, _⟩ := ledger_onIn hs hIn hF
      refine ⟨{ G with planClaimsF := claims }, ?_, ?_⟩
      · rcases hA with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, ho, rfl⟩
        · simp [S.fork?]
        · simp [S.fork?]
        · simp [S.fork?, ho]
      · show G.next = _
        rw [LK.2.2.2.1, c2, Spec.slots_elems]

/-- In the head's link the state's open ledger is that link's own. -/
theorem fork_head {t : FS} {a : VerifiableInference.Desc.First.HeadOwn} {G : Fork}
    (hh : t.here = .head a) (hf : t.fork? = some G) : a.F = G := by
  unfold S.fork? at hf
  rw [hh] at hf
  have hf' : (if a.opened = true then some a.F else none) = some G := hf
  cases ho : a.opened with
  | false =>
    rw [ho] at hf'
    exact nomatch hf'
  | true =>
    rw [ho] at hf'
    exact Option.some.inj hf'

/-- **The same behind the accepting step of the description's own member.** No instance of these
hypotheses is exhibited in this file. -/
theorem next_atSite (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (hIn : k3OnIn s.p sj = true) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ G, sj'.fork? = some G ∧ G.next = s.p.first + OnBytes.Model.Forest.elems s.shape :=
  next_ofPlace (k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O s.at_.place lot m hb hbs hm hmp
    hpk ft sj sj' n rs c h) hs hT3 hIn

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.next_ofPlace
#print axioms ProofFile.Honest.K3.Law.AtThr.fork_head
#print axioms ProofFile.Honest.K3.Law.AtThr.next_atSite
