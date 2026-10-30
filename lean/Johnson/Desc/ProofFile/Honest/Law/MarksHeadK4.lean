-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/MarksHeadK4.lean: K4's authors' shares of three lemmas on
`marksHead` (Honest/Law/MarksHead.lean), paid by K4's authors' own lemmas. `marksHead_seat`,
`marksHead_member` and `marksHead_hM` take each owner's lemma as a hypothesis. Here the hypotheses
on `K4.k4MarksWide` are struck from the first two, and the hypothesis on the kinds of its places in
the third is proved.

  1  `marksHead_seat_k4`   `marksHead_seat` without `h₄`, by `K4.k4MarksWide_kind`
  2  `marksHead_member_k4`   `marksHead_member` at the proof file's first chain without `h₄`, under
    `P5J.AtMgA`, by `K4.k4MarksWide_places` and `K4.k4Marks_member`
  3  `k4_kinds`   the hypothesis `k₄` of `marksHead_hM`, by `K4.k4MarksWide_kind`

Limits.
  * One owner's shares of five. With K6's authors' share of `hseat`, which `marksHead_seat` pays
    inside, two of the five shares of the field `hseat` of `FirstAsks` are proved. The three others
    stay hypotheses.
  * The bound for K4's marks in the form of the field `hM` (`h₄` of `marksHead_hM`) is K4's authors'
    `K4.k4_markWideDebt_table` (Honest/K4/Law/MarkWideDebt.lean), under two hypotheses on the
    rounds' data. It is not imported or called here.
  * K4's authors have the first two shares as lemmas of their own (`K4.k4MarksWide_seat`,
    Honest/K4/Law/MarksWideSeat.lean; `K4.k4MarksWide_member`, Honest/K4/Law/MarksWideHead.lean).
    These two files stand over more of K4's authors' files and are not imported here. Their two
    short proofs are repeated inside the two lemmas. When these two files lie beneath this one (over
    a later seal), the two proofs give way to calls of K4's authors' lemmas.
  * The file imports a file of K4's authors that is no part of the sealed library
    (Honest/K4/Law/K4MarksTwelve.lean), which reaches modules under Johnson/Goal/ (its own head says
    so). So this file is a law: no file that defines a part of the description may import it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.MarksHead
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksTwelve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open P5J (TS)

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- The field `hseat` at `marksHead`, with K4's authors' share paid. -/
theorem marksHead_seat_k4 (h₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀, markSeat mk.place = true)
    (h₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, markSeat mk.place = true)
    (h₅ : ∀ mk ∈ K5.k5Marks Zp G₀, markSeat mk.place = true) :
    ∀ mk ∈ marksHead Zp G₀, markSeat mk.place = true :=
  marksHead_seat h₁ h₃ (fun mk hm => by
    unfold markSeat
    rw [K4.k4MarksWide_kind hm]
    rfl) h₅

/-- Every mark stands at the place of a sub-protocol of the proof file's first chain, with K4's
authors' share paid. -/
theorem marksHead_member_k4 {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (h₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place)
    (h₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place)
    (h₅ : ∀ mk ∈ K5.k5Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place)
    (h₆ : ∀ mk ∈ K6.part4Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place) :
    ∀ mk ∈ marksHead Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place :=
  marksHead_member h₁ h₃ (fun mk hm => by
    have h1 : mk.place ∈ (K4.k4MarksWide Zp G₀).map (·.place) := List.mem_map_of_mem hm
    rw [K4.k4MarksWide_places] at h1
    obtain ⟨mk', hm', e⟩ := List.mem_map.1 h1
    obtain ⟨b, hb, e'⟩ := K4.k4Marks_member h G₀ mk' hm'
    exact ⟨b, hb, e'.trans e⟩) h₅ h₆

/-- K4's authors' marks stand at places of the kind K4: neither K3 nor K6. -/
theorem k4_kinds : ∀ mk ∈ K4.k4MarksWide Zp G₀,
    mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6 := by
  intro mk hm
  rw [K4.k4MarksWide_kind hm]
  exact ⟨by decide, by decide⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.marksHead_seat_k4
#print axioms ProofFile.Honest.marksHead_member_k4
#print axioms ProofFile.Honest.k4_kinds
