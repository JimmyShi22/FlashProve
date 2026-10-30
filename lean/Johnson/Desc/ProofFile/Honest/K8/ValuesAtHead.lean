-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ValuesAtHead.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE, AT
THE STANDS OF THE HONEST THREAD: THE NAMED PREMISE `ValuesAtStand`
(Johnson/Desc/ProofFile/Honest/K8/LeftFront.lean) AT ALL 25 SEGMENTS IN ONE SENTENCE: AT A GENERAL
THREAD FROM `ChainThread`; AND AT THE FRAME's OWN THREAD, THAT OF THE FIRST CHAIN's LETTERS AT THE
LIBRARY's HEAD, UNDER THE HEAD, AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN.
Implications; none of the library's goals.

  **`valuesAtStand_of_chain_all`** the scope · the files read · an opening of the description · its
                   test on its plan · l < 25 · c.links[l]? = some Lk · the built segment Xl ·
                   ChainThread T b c Z l ⊢ ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b
  **`valuesAtStand_at_head_all`** the library's head h · the thread's letters, all free · an opening
                   of the description at cF · its test on its plan · l < 25 · cF.links[l]? = some Lk
                   · the built segment Xl ⊢ ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) (lettersHead
                   …).thread (batchAt P5J.At.links P5J.At.ps l), at every p, φ and Ok
By: `valuesAtStand_layers_of_chain`, `_att_of_chain`, `_head_of_chain` (ValuesOfChain.lean), by the
segment's number: 24, even, odd · `chainThread_at_head` (ChainThreadAtHead.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
two lines, on numbers of segments alone.
Limits. NO MEMBER: THAT THE THREAD HOLDS AT ANY RUN, OR THAT A STAND EXISTS, IS NOT SHOWN: where
there is no stand all is idle. THE LIBRARY's HEAD IS A PREMISE OF THE SECOND. p, φ and Ok are free:
at numbers p at which no stand exists the sentence is idle; Lk is the chain's own link at l. THE
FULL SIZE ALONE, and the format's second hash function alone. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ValuesOfChain
import Johnson.Desc.ProofFile.Honest.K8.ChainThreadAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.K9L (Pub9)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE NAMED PREMISE ValuesAtStand, AT THE CHAIN's OWN LINK AND THE LOT's OWN LENGTHS, AT ALL 25
SEGMENTS, FROM THE ONE NAMED PREMISE.** -/
theorem valuesAtStand_of_chain_all (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) (hLk : c.links[l]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl) (C : ChainThread T b c Z l) :
    ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  by_cases h24 : l = 24
  · subst h24
    exact valuesAtStand_head_of_chain hS hR O hOk hLk e3 C
  · obtain ⟨g, rfl | rfl⟩ := Nat.even_or_odd' l
    · exact valuesAtStand_layers_of_chain hS hR O hOk (by omega) hLk e3 C
    · exact valuesAtStand_att_of_chain hS hR O hOk (by omega) hLk e3 C

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **ValuesAtStand AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, AT ALL 25 SEGMENTS.** -/
theorem valuesAtStand_at_head_all {α : Type} {φ : S → α} {Ok : α × Option Pub9 → Prop}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) (hLk : cF.links[l]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl) :
    ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) :=
  valuesAtStand_of_chain_all h.scope h.reads O hOk hl hLk e3
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.valuesAtStand_of_chain_all
#print axioms ProofFile.Honest.K8.valuesAtStand_at_head_all
