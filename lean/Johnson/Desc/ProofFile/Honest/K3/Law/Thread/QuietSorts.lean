-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/QuietSorts.lean: the kind "lookup" (K3): at every site
on the digits that passes one public test the step without a round behind the lookup (`quietAt`,
Johnson/Desc/First/Look/K3Whole.lean) has one of its two forms: the head's, or the other links' at
two numbers of the plan. So the theorems of this folder that take "which of the two" as a hypothesis
`hq` can be called by cases, and the clause by place (`k3KeepsAt`,
Honest/K3/Law/Thread/K3KeepsAt.lean) says something at every such site. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `quiet_sorts`: the title's sentence.
  `onOut_atSite`: hence the lookup's promise behind (`k3OnOut`,
    Johnson/Desc/First/Look/K3Borders.lean), at a site of whatever sort, with no `hq`: the three
    theorems of Honest/K3/Law/Thread/OnOutMember.lean in one.

Hypotheses that remain.
  `hs`: s is a site of the public part (`lookSites Z`).
  `hT3`: one test with code on public data, the third of Honest/K3/LotPublic.lean: "at the digits,
    but for the head's: first slot + hidden values = the plan's slots in use". The proof uses it for
    this alone: where it accepts, the plan has an entry for the link's group.
  `hd`: (in `quiet_sorts`) the site is on the digits.
  In `onOut_atSite` besides: the hypotheses of the three theorems of
    Honest/K3/Law/Thread/OnOutMember.lean: `O`, `hb`, `hbs`, `hm`, `hmp`, `hpk`, `hIn`, `h`.

Users. `quiet_sorts` is called in Honest/K3/Law/Thread/K3KeepsStep.lean,
Honest/K3/Law/Thread/NextBehind.lean and Honest/K3/Law/Thread/RidersAtHead.lean; `onOut_atSite` in
Honest/K3/Law/Thread/RidersAtHead.lean and Honest/K3/Law/Thread/RidersAtPlace.lean.

Limits. On public data and the verifier's side alone. No instance of these hypotheses is exhibited
in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OnOutMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietDigits quietHead isHead k3OnIn k3OnOut)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At a site on the digits the step without a round behind has one of its two forms.**
Conditional on the site and on the public test `hT3`. -/
theorem quiet_sorts {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) (hd : s.digits = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true) :
    quietAt Z.p.X s.link true = some (quietHead Z.p.X) ∨
      ∃ used claims, quietAt Z.p.X s.link true = some (quietDigits used claims) := by
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, _, f3, _, _, _, f7, f8⟩ := site_facts _ _ x s hsx
  rw [← f3] at f7 f8
  unfold quietAt
  dsimp only
  cases hH : isHead Z.p.X s.link with
  | true => exact Or.inl (by simp)
  | false =>
    refine Or.inr ?_
    by_cases hmod : (s.link % (if Z.p.X.p4 then 2 else 1) == 0) = true
    · have hc := caller_layers Z.p.X s.link hH hmod
      have hc1 : s.caller = .layers := by rw [f7, hc]
      have hc2 : s.group = s.link / (if Z.p.X.p4 then 2 else 1) := by rw [f8, hc]
      have hu : usedAt Z.p.X s = (Z.p.X.G[s.group]?).map (·.used) := by
        unfold usedAt
        rw [hc1]
      rw [hd, hc1, hu, hc2] at hT3
      cases hg : Z.p.X.G[s.link / (if Z.p.X.p4 then 2 else 1)]? with
      | none =>
        rw [hg] at hT3
        simp at hT3
      | some hp => exact ⟨hp.used, hp.nLin, by simp [hmod]⟩
    · have hc := caller_attention Z.p.X s.link hH hmod
      have hc1 : s.caller = .attention := by rw [f7, hc]
      have hc2 : s.group = s.link / (if Z.p.X.p4 then 2 else 1) := by rw [f8, hc]
      have hu : usedAt Z.p.X s = (Z.p.X.A[s.group]?).map (·.nMsg) := by
        unfold usedAt
        rw [hc1]
      rw [hd, hc1, hu, hc2] at hT3
      cases hg : Z.p.X.A[s.link / (if Z.p.X.p4 then 2 else 1)]? with
      | none =>
        rw [hg] at hT3
        simp at hT3
      | some a => exact ⟨a.nMsg, a.nLin, by simp [hmod]⟩

/-- **The lookup's promise behind, at a site of whatever sort.** Conditional on what the head lists.
No instance of these hypotheses is exhibited in this file. -/
theorem onOut_atSite (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (hIn : k3OnIn s.p sj = true) (h : m.step ft sj rs c = .ok (sj', n)) :
    k3OnOut s.p sj' = true := by
  cases hd : s.digits with
  | false =>
    exact onOut_atCalls o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk ft sj sj'
      n rs c hIn h
  | true =>
    rcases quiet_sorts hs hd hT3 with hq | ⟨used, claims, hq⟩
    · exact onOut_atHead o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq ft sj
        sj' n rs c hIn h
    · exact onOut_atDigits o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk used
        claims hq ft sj sj' n rs c hIn h

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.quiet_sorts
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_atSite
