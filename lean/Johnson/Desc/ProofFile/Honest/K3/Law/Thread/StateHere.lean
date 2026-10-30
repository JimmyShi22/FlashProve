-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StateHere.lean: the kind "lookup" (K3): the state behind
an accepting step of the description's own member at a lookup on the calls, written out field by
field: by the sort of the link that is open, the state behind is the state in front with the ledger
and what was heard set in the link's part, and nothing else changed. So every reader of the state
can be evaluated on both sides. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the sentence itself, `CallsHere`, is defined in
Honest/K3/Law/KeepsDefs.lean. Its three arms: at a layers' link F, fo and lookHeard are set; at an
attention link F, g and lookHeard; at the head's link, open, F and lookHeard alone.

What is shown.
  `calls_here_of`: `CallsHere` from the equation in the state's own setters (`calls_state`,
    Honest/K3/Law/Thread/StateBehind.lean).
  `calls_here`: the same at the description's own member.

Hypotheses that remain, in `calls_here`: those of `calls_state`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts.
In `calls_here_of`: `hF`, `hn`, `e`: a ledger is open in front; nothing is heard; the state behind
is the one in front with the ledger and what was heard written in.

Users. `calls_here` is called in Honest/K3/Law/Thread/CallsParts.lean,
Honest/K3/Law/Thread/CarriesCalls.lean, Honest/K3/Law/Thread/HeadCallsTie.lean,
Honest/K3/Law/Thread/K3Keeps.lean, Honest/K3/Law/Thread/K3KeepsOut.lean [not in this library],
Honest/K3/Law/Thread/K3KeepsSh.lean [not in this library], Honest/K3/Law/Thread/LayersTieHead.lean,
Honest/K3/Law/Thread/LaysAttHead.lean, Honest/K3/Law/Thread/LeftAtCalls.lean,
Honest/K3/Law/Thread/OnOutMember.lean, Honest/K3/Law/Thread/PutFo.lean and
Honest/K3/Law/Thread/StandsAt.lean; `calls_here_of` in Honest/K3/Law/Thread/K3Keeps.lean.

Limits. On the verifier's side alone. Of what the hearing returns nothing is said. No instance of
these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.KeepsDefs
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First (S)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **From the equation in the state's own setters** (`e`), where a ledger is open and nothing is
heard in front (`hF`, `hn`). -/
theorem calls_here_of {sj sj' : FS} {F G : Fork} {H : OnBytes.Model.Forest.Heard}
    (hF : sj.fork? = some F) (hn : sj.lookHeard?.isNone = true)
    (e : sj' = (sj.putFork G).hearLook H) : CallsHere sj sj' H G := by
  subst e
  unfold S.fork? at hF
  unfold S.lookHeard? at hn
  cases hh : sj.here with
  | lay a =>
    rw [hh] at hn
    have hn' : a.lookHeard.isNone = true := hn
    have h0 : a.lookHeard.isSome = false := by
      cases hx : a.lookHeard with
      | none => rfl
      | some v => rw [hx] at hn'; exact nomatch hn'
    refine Or.inl ⟨a, hh, ?_⟩
    simp [S.putFork, S.hearLook, hh, h0]
  | att a =>
    rw [hh] at hn
    have hn' : a.lookHeard.isNone = true := hn
    have h0 : a.lookHeard.isSome = false := by
      cases hx : a.lookHeard with
      | none => rfl
      | some v => rw [hx] at hn'; exact nomatch hn'
    refine Or.inr (Or.inl ⟨a, hh, ?_⟩)
    simp [S.putFork, S.hearLook, hh, h0]
  | head a =>
    rw [hh] at hn hF
    have hF' : (if a.opened = true then some a.F else none) = some F := hF
    have hn' : (if a.opened = true then a.lookHeard else none).isNone = true := hn
    cases ho : a.opened with
    | false =>
      rw [ho] at hF'
      exact nomatch hF'
    | true =>
      rw [ho] at hn'
      have hn2 : a.lookHeard.isNone = true := hn'
      have h0 : a.lookHeard.isSome = false := by
        cases hx : a.lookHeard with
        | none => rfl
        | some v =>
          rw [hx] at hn2
          exact nomatch hn2
      refine Or.inr (Or.inr ⟨a, hh, ho, ?_⟩)
      simp [S.putFork, S.hearLook, hh, ho, h0]
  | between =>
    rw [hh] at hF
    exact nomatch hF
  | fin a =>
    rw [hh] at hF
    exact nomatch hF
  | mem a =>
    rw [hh] at hF
    exact nomatch hF

/-- **At the description's own member at a lookup on the calls.** Conditional on the description's
return; the site, on the calls; the lookups' own sub-protocol at its place; the member there; the
member's test on the plan; the member's accepting step. No instance of these hypotheses is exhibited
in this file. -/
theorem calls_here (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ F H G, sj.fork? = some F ∧ (F.next == s.p.first) = true ∧
      hearVia s.p F rs = some (H, G) ∧ CallsHere sj sj' H G ∧ sj'.failed = none := by
  obtain ⟨F, H, G, a1, a2, _, a4, a5, e, hf⟩ := calls_state o pol lay KL Fd Z Bs base ch A B O s hs
    hd lot m hb hbs hm hmp hpk ft sj sj' n rs c h
  exact ⟨F, H, G, a1, a4, a5, calls_here_of a1 a2 e, hf⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.calls_here_of
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_here
