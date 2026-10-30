-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverHeadFile.lean: what `falls_asks` (Honest/Law/CoverAsks.lean)
asks of the file's description holds of the proof file's description under the library's hypothesis
`P5J.AtMg` (Johnson/P5J/AtMg.lean). The description is
`P5J.F0T o Zp Np cF`. Its first chain is `cF`.

  1  `cut_exists`   general: a chain whose cut into sub-protocols is the library's written one has a
     last sub-protocol, and others before it (`hne`)
  2  `file_head`   under `P5J.AtMg`: the data of the file (`hdata`), the test on the places (`hpl`)
     and the written cut (`hcut`)

Limits.
  * `hdata` is a field of the hypothesis itself (`LaidAt.data`, Johnson/P5J/LaidOpens.lean). `hpl`
    is a clause of the description's test on its plan, which is another field
    (`FileDescription.planOk_ok`, Johnson/Desc/RunLaws.lean). `hcut` is the library's `cut_of_head`
    (Johnson/Road/K4/K4HeadWritten.lean).
  * `P5J.AtMg` is a hypothesis.
  * What `falls_asks` asks of the prover's lists of parts and of the other two chains (`hR`, `Sf`,
    `hf₂`, `hf₃`, `hmk₂`, `hmk₃`) is not treated here. `hf₂` and `hf₃` say that the other two chains
    have no falls: whoever supplies the lists of parts supplies these lists.
  * The statements are at the library's full-size parameter set alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverCutHead
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block Chain FileDescription)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open OnBytes.Maker (WholeD)
open P5J (TS)

/-- A chain with the written cut has a last sub-protocol, and others before it. -/
theorem cut_exists {S Cl : Type} {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull) :
    ∃ pre e₁, all = pre ++ [e₁] ∧ pre ≠ [] := by
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps_cut hcut, List.length_map]
  have h1 : 357 < all.length := by omega
  have a1 : all.drop 357 = [all[357]] := by
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_nil_of_le (by omega)]
  refine ⟨all.take 357, all[357], ?_, fun e => ?_⟩
  · rw [← a1]
    exact (List.take_append_drop 357 all).symm
  · have h2 := congrArg List.length e
    rw [List.length_take, hlen] at h2
    simp at h2

/-- Under `P5J.AtMg`: the file's data, the test on the places, and the written cut. -/
theorem file_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF) :
    (P5J.F0T o Zp Np cF).data "proof file" = .ok D ∧ (P5J.F0T o Zp Np cF).placesOk = true ∧
      cutOf (P5J.F0T o Zp Np cF).first.blocksInOrder = cutFirstFull :=
  ⟨h.laid.data, ((FileDescription.planOk_ok _).1 h.laid.planOk).places, OnBytes.Road.K4.cut_of_head h⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_exists
#print axioms ProofFile.Honest.file_head
