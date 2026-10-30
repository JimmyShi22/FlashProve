-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverDraws.lean: the field `hz` of `FirstAsks`
(Honest/Law/CoverAsks.lean) holds of the proof file's description under the library's hypothesis
`P5J.AtMg`. `hz` says of each gated round's entry that the elements that must not be 0 are among the
elements drawn: `drawNZ ≤ drawE`. The same is proved of the other two chains' rounds.

How. Under `P5J.AtMg` the file's data are the library's written data `writtenPFull`: one of the
tests that the hypothesis holds pins the declared rounds to the written lists (`LPFD.asks_written`,
Johnson/Desc/Laid/ProofAsksLaw.lean; `seat_in_scope`,
Johnson/Goal/Numbers/PlanWrittenDescScope.lean). The written data are equal to a form that Lean's
kernel can evaluate (`writtenPFull_eq`, Johnson/Flat/Dec/FitAtWritten.lean). On that form the
statement on the entries is closed, and `decide +kernel` decides it. Each datum has the entry of its
declared round (`KindFits`, Honest/Law/Due.lean; `kinds_of_data`, Honest/Law/DataKinds.lean).

  1  `draws_written_yes`, `draws_written_control`   the closed statement on the written data's three
     lists, and a control that rejects
  2  `entries_of_kinds`   general: what holds of every datum's entry holds of every declared round's
  3  `hz_of_data`   general: `hz` from the same statement on the data
  4  `data_head`   under `P5J.AtMg` the data are `writtenPFull`
  5  `hz_head`, `hz_shared_head`, `hz_second_head`   `hz` at the first chain's gated sub-protocols,
     and the same at all sub-protocols of the other two chains

Limits.
  * `P5J.AtMg` is a hypothesis.
  * The first chain's last round, the sealing round, is not among the gated rounds, and nothing is
    said of it here.
  * The closed statement is decided at one form of the written data. The statements are at the
    library's full-size parameter set alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverData
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription)
open OnBytes.Maker (WholeD RDT)
open P5J (TS)

/-! ## 1 The closed statement -/

set_option maxRecDepth 1000000 in
/-- At each datum of the written data's three lists: `drawNZ ≤ drawE`. -/
theorem draws_written_yes :
    (Johnson.G.dProofFull.ds₁.all fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)) = true ∧
      (Johnson.G.dProofFull.ds₂.all fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)) = true ∧
      (Johnson.G.dProofFull.ds₃.all fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with `<` in place of `≤` the first test rejects. -/
theorem draws_written_control :
    (Johnson.G.dProofFull.ds₁.all fun d => decide (d.entry.drawNZ < d.entry.drawE)) = false := by
  decide +kernel

/-! ## 2 From the data to the declared rounds -/

/-- What holds of every datum's entry holds of every declared round's entry. -/
theorem entries_of_kinds {p : Fmt.Entry → Prop} {ds : List RDT} {zs : List Fmt.DeclaredRound}
    (hk : List.Forall₂ KindFits ds zs) : (∀ d ∈ ds, p d.entry) → ∀ z ∈ zs, p z.entry := by
  induction hk with
  | nil =>
    intro _ z hz
    cases hz
  | cons h1 _ ih =>
    intro h z hz
    rcases List.mem_cons.1 hz with e | hz
    · rw [e, ← h1.1]
      exact h _ List.mem_cons_self
    · exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) z hz

variable {Xi : Type}

/-- The field `hz`, from the same statement on the first chain's data. -/
theorem hz_of_data {F : FileDescription Xi} {file : String} {D : WholeD} (hd : F.data file = .ok D)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    {z₁ : Fmt.DeclaredRound} (he : e₁.rounds = [z₁])
    (hD : ∀ d ∈ D.ds₁, d.entry.drawNZ ≤ d.entry.drawE) :
    ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE := fun b hb z hz =>
  entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) (kindFits_first hd cut he) hD z
    (List.mem_flatMap.2 ⟨b, hb, hz⟩)

/-! ## 3 Under the library's hypothesis -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under `P5J.AtMg` the file's data are the written data. -/
theorem data_head (h : P5J.AtMg o Z D r Zp Np cF) : D = Johnson.G.writtenPFull :=
  Except.ok.inj (h.laid.data.symm.trans
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
      (LPFD.asks_written h.laid.asks)).2.2)

/-- The field `hz` of `FirstAsks`, at the proof file's first chain. -/
theorem hz_head (h : P5J.AtMg o Z D r Zp Np cF)
    {pre₁ : List (Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl)}
    {e₁ : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl}
    (cut : (P5J.F0T o Zp Np cF).first.blocksInOrder = pre₁ ++ [e₁]) :
    ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE := by
  obtain ⟨z₁, he⟩ := (members_cut (file_head h).2.2 cut).2.2.2.2.2
  refine hz_of_data h.laid.data cut he ?_
  rw [data_head h, Johnson.G.writtenPFull_eq]
  exact fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.1 d hd)

/-- The same at the shared chain. -/
theorem hz_shared_head (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ b ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder, ∀ z ∈ b.rounds,
      z.entry.drawNZ ≤ z.entry.drawE := by
  intro b hb z hz
  refine entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) (kinds_of_data h.laid.data).2.1 ?_ z
    (List.mem_flatMap.2 ⟨b, hb, hz⟩)
  rw [data_head h, Johnson.G.writtenPFull_eq]
  exact fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.2.1 d hd)

/-- The same at the second chain. -/
theorem hz_second_head (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ b ∈ (P5J.F0T o Zp Np cF).second.blocksInOrder, ∀ z ∈ b.rounds,
      z.entry.drawNZ ≤ z.entry.drawE := by
  intro b hb z hz
  refine entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) (kinds_of_data h.laid.data).2.2.1 ?_ z
    (List.mem_flatMap.2 ⟨b, hb, hz⟩)
  rw [data_head h, Johnson.G.writtenPFull_eq]
  exact fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.2.2 d hd)

end ProofFile.Honest

#print axioms ProofFile.Honest.draws_written_yes
#print axioms ProofFile.Honest.draws_written_control
#print axioms ProofFile.Honest.entries_of_kinds
#print axioms ProofFile.Honest.hz_of_data
#print axioms ProofFile.Honest.data_head
#print axioms ProofFile.Honest.hz_head
#print axioms ProofFile.Honest.hz_shared_head
#print axioms ProofFile.Honest.hz_second_head
