-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WrittenNonZero.lean: NO ROUND OF THE LIBRARY's WRITTEN DATA, OF THE KEY FILE OR OF THE PROOF
FILE, ASKS FOR MORE NON-ZERO ELEMENTS THAN ELEMENTS. By proof, from two closed statements of the
library; no evaluation is made here.

  `nz_of_chainAll`: every round of a plan that passes the public test on a chain's plan
    (`Desc.chainAll`, Johnson/Desc/MadeOk.lean) has `drawNZ ≤ drawE` in its entry: that test holds
    the side conditions of each round (`sideE`, OnBytes/Flat/HeldAll.lean). `nz_of_priced`: so has
    every round of a list of data that is held, place by place, against rounds of such a plan with
    the same entries (`PricedAt.entry`, Johnson/Desc/Ok/NumberPrices/AtData.lean).
  **`nz_writtenK`**, **`nz_writtenP`**: at all rounds of `writtenKFull` and of `writtenPFull`: from
    `keyPricesWritten` (Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean) and `proofPricesWritten`
    (…/ProofAtWritten.lean).
  `nz_proofData`: in scope, where the IOP's own test on the public files accepts, at all rounds of
    the proof file's data (`proof_written_of_live`, Johnson/Goal/Description/ProofWritten.lean).

Limits. The two closed statements rest on evaluations in Lean's kernel that are made in their own
files. That the written priced plans are the planner's is no theorem (these files' heads). Whether
any public files are in scope and pass the IOP's own test is not said here. The first plan's last
round is no round of the data: nothing is said of it here. The lists are not empty (18,948 and
48,390 rounds: `written_lengths`, `writtenP_lengths` in the two files that are called). A sentence
on entries of written lists: nothing on any drawn value. No property is had.


-/
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.Goal.Description.ProofWritten

set_option autoImplicit false

namespace AtPublicFiles.Written
open VerifiableInference VerifiableInference.Number VerifiableInference.Number.ByRuns
open OnBytes.Params OnBytes.Flat.Held OnBytes.Maker

/-- Every round of a plan that passes the public test on a chain's plan asks for no more non-zero
elements than elements. -/
theorem nz_of_chainAll {w : ℕ} {P : Planned} (h : Desc.chainAll w P = true) :
    ∀ r ∈ P.rounds, r.entry.drawNZ ≤ r.entry.drawE := by
  intro r hr
  unfold Desc.chainAll Desc.chainOk sideB at h
  simp only [Bool.and_eq_true] at h
  have hs := List.all_eq_true.1 h.1.1.1.1.2.2 r hr
  unfold sideR sideE at hs
  simp only [Bool.and_eq_true] at hs
  exact of_decide_eq_true hs.1.2

/-- A member of the left list of two lists that are related member by member has a partner. -/
theorem partnerL {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ d ∈ l₁, ∃ z ∈ l₂, R d z
  | _, _, .nil, _, h => absurd h (by simp)
  | _, _, .cons h t, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨z, hz, hr⟩ := partnerL t d hd
      exact ⟨z, List.mem_cons_of_mem _ hz, hr⟩

/-- Every round of data that is held, place by place, against rounds of a plan that passes that test
asks for no more non-zero elements than elements. -/
theorem nz_of_priced {w : ℕ} {P : Planned} (h : Desc.chainAll w P = true) {ds : List RDT}
    {rs : List PlanRound} (hsub : ∀ r ∈ rs, r ∈ P.rounds) (hp : List.Forall₂ PricedAt ds rs) :
    ∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE := by
  intro d hd
  obtain ⟨r, hr, hpr⟩ := partnerL hp d hd
  rw [hpr.entry]
  exact nz_of_chainAll h r (hsub r hr)

/-- A plan's rounds of the chain are rounds of the plan. -/
theorem mem_of_chainRounds {P : Planned} : ∀ r ∈ chainRounds P, r ∈ P.rounds :=
  fun _ h => (List.mem_filter.1 h).1

/-- Every round of a file's data that is priced against three plans which pass that test asks for no
more non-zero elements than elements. -/
theorem nz_of_rounds {D : WholeD} {P₁ P₂ P₃ : Planned} {w₁ w₂ w₃ : ℕ}
    (hp : PricedRounds D P₁ P₂ P₃) (h₁ : Desc.chainAll w₁ P₁ = true)
    (h₂ : Desc.chainAll w₂ P₂ = true) (h₃ : Desc.chainAll w₃ P₃ = true) :
    ∀ d ∈ D.ds₁ ++ D.ds₂ ++ D.ds₃, d.entry.drawNZ ≤ d.entry.drawE := by
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · rcases List.mem_append.1 hd with hd | hd
    · exact nz_of_priced h₁
        (fun r hr => mem_of_chainRounds r (List.mem_of_mem_dropLast hr)) hp.1 d hd
    · exact nz_of_priced h₂ mem_of_chainRounds hp.2.1 d hd
  · exact nz_of_priced h₃ mem_of_chainRounds hp.2.2 d hd

/-- **The key file's written data.** -/
theorem nz_writtenK : ∀ d ∈ Johnson.G.writtenKFull.ds₁ ++ Johnson.G.writtenKFull.ds₂ ++
    Johnson.G.writtenKFull.ds₃, d.entry.drawNZ ≤ d.entry.drawE :=
  nz_of_rounds keyPricesWritten.1 keyPricesWritten.2.1 keyPricesWritten.2.2.1
    keyPricesWritten.2.2.2

/-- **The proof file's written data.** -/
theorem nz_writtenP : ∀ d ∈ Johnson.G.writtenPFull.ds₁ ++ Johnson.G.writtenPFull.ds₂ ++
    Johnson.G.writtenPFull.ds₃, d.entry.drawNZ ≤ d.entry.drawE :=
  nz_of_rounds proofPricesWritten.1 proofPricesWritten.2.1 proofPricesWritten.2.2.1
    proofPricesWritten.2.2.2

/-- **The proof file's data, in scope, where the IOP's own test on the public files accepts.** -/
theorem nz_proofData (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∀ d ∈ (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles Z)).ds₁ ++
        (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles Z)).ds₂ ++
        (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles Z)).ds₃, d.entry.drawNZ ≤ d.entry.drawE := by
  rw [FlashProve.proof_written_of_live Z scope live]
  exact nz_writtenP

end AtPublicFiles.Written

#print axioms AtPublicFiles.Written.nz_of_chainAll
#print axioms AtPublicFiles.Written.partnerL
#print axioms AtPublicFiles.Written.nz_of_priced
#print axioms AtPublicFiles.Written.mem_of_chainRounds
#print axioms AtPublicFiles.Written.nz_of_rounds
#print axioms AtPublicFiles.Written.nz_writtenK
#print axioms AtPublicFiles.Written.nz_writtenP
#print axioms AtPublicFiles.Written.nz_proofData
