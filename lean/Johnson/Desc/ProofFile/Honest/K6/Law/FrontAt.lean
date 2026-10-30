-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FrontAt.lean: THE PROMISE's PARTS AT BORDER 341, AT THE HONEST
LETTERS: from the first chain's thread (Honest/Thread/First.lean) to the structure `K6FrontItems`
(Johnson/Desc/K6/Honest/Law/FrontItems.lean). Statements with their proofs.

What it is not. It speaks of the full size alone. The hypothesis `P5J.AtMgA` is a premise: the
library shows that it has a member under the four premises of `P5J.head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean), which this file does not call. Nothing shows that the thread
holds at any run. Nothing on any property.

  `headFrontItems_of_formP`   CONDITIONAL on the thread's clause on the promise at 341, "no mark",
                              and four premises on the letters: `hMg`: the meaning of which the
                              promise's public fields are read is mgAll D mgBase; `hl`, `hps`, `hN`:
                              the segments' sorts, the places and the numbers are the full chain's
                              and the data's own
  `headFrontItems_of_thr`     CONDITIONAL on the thread at 341 and the same four
  `headFrontItems_at`         at the library's own letters (Honest/Thread/FirstAt.lean) the four are
                              paid by unfolding; CONDITIONAL on the hypothesis `P5J.AtMgA`
  `headLink_at`               CONDITIONAL on the same: the output head's segment is number 24. The
                              library proves this inside `paid_at_const`
                              (Johnson/Desc/Kinds/Law/K06AtConst.lean), which asks for the chain's
                              segment 24 besides: its four lines are typed anew

-/
import Johnson.Desc.K6.Honest.Law.FrontItems
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Place Strs Wit)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MgData mgAll mgBase MsgT CellsQ)
open VerifiableInference.Desc.Kinds.Head.Law (K6FrontItems)
open ProofFile.Honest.FirstThread (Letters Script WtF lettersAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Xd P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}

/-- **THE PROMISE's PARTS AT BORDER 341, AT THE HONEST LETTERS.** CONDITIONAL on four premises on
the letters: the meaning of which the promise's public fields are read is the composed one over the
empty base; the segments' sorts, the list of places and the table's numbers are the full chain's and
the data's own. -/
theorem headFrontItems_of_formP
    (L : Letters Bk Cl W₀ Rc Xi Tr X P (CellsQ rows cols) Tok MsgT)
    (D : MgData Xd P Tok rows cols nR Wp) (hMg : L.MgP = mgAll D mgBase)
    (hl : L.links = linksFull) (hps : L.ps = flatPlacesOf linksFull true) (hN : L.N = D.N)
    (a : P × S) (h : L.thread.formP 341 a) (hm : a.2.failed = none) :
    K6FrontItems D mgBase a := by
  have p := Small.partsAt_of_formP L 341 a h hm
  rw [hMg, hl, hps, hN] at p
  exact VerifiableInference.Desc.Kinds.Head.Law.frontItems_of_parts D mgBase rfl a p

/-- **The same wherever the thread holds at border 341.** CONDITIONAL on the same four. -/
theorem headFrontItems_of_thr
    (L : Letters Bk Cl W₀ Rc Xi Tr X P (CellsQ rows cols) Tok MsgT)
    (D : MgData Xd P Tok rows cols nR Wp) (hMg : L.MgP = mgAll D mgBase)
    (hl : L.links = linksFull) (hps : L.ps = flatPlacesOf linksFull true) (hN : L.N = D.N)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr L.thread 341 k s m E) :
    s.failed = none ∧ K6FrontItems D mgBase (L.pubOf m.st.input.x, s) := by
  obtain ⟨hm, p⟩ := Small.partsAt_of_thr L hT
  rw [hMg, hl, hps, hN] at p
  exact ⟨hm, VerifiableInference.Desc.Kinds.Head.Law.frontItems_of_parts D mgBase rfl _ p⟩
end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The same at the library's own letters**: the four premises are paid. CONDITIONAL on the one
hypothesis that ties the table's letters to the proof file's description. -/
theorem headFrontItems_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (a : ProofFile.InstPub × TS)
    (hf : (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.formP 341 a)
    (hm : a.2.failed = none) : K6FrontItems h.𝔇 mgBase a :=
  headFrontItems_of_formP (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) h.𝔇
    rfl rfl rfl rfl a hf hm

/-- The output head's segment is number 24, at these letters. CONDITIONAL on the same hypothesis. -/
theorem headLink_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  unfold VerifiableInference.OnPublicFiles.headLink
  rw [p4, ng]
  rfl
end

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headFrontItems_of_formP
#print axioms ProofFile.Honest.K6.headFrontItems_of_thr
#print axioms ProofFile.Honest.K6.headFrontItems_at
#print axioms ProofFile.Honest.K6.headLink_at
