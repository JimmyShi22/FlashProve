-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FormsInAtHead.lean: AT THE FIRST CHAIN's THREAD AT THE HEAD: THE
THREAD's FORM AT A BORDER GIVES THE PUBLIC TEST THAT THE TABLE TIES TO AN OPEN RUN OF FORMS. One
theorem; no definition; none of the library's goals. No kind is named in it.

  **`formsInA_of_form`**   under the library's head (h : `P5J.AtMgA`): the thread's clause `Form` at
                   a border b, a state s and a stand of the prover's run · the item forms l kk r is
                   in the table's open set at b · p is one of that item's runs, read ahead ⊢
                   `K9.formsInA` at the run p says yes at s
HOW. `Form` is "no mark" and the library's promise `onAt` (Johnson/Desc/First/Borders.lean) at the
honest letters; its fifth Bool `pubHeld` holds every public item that is tied to an open item
(`pubOfItems`); the honest letters leave the field `pub` as it is; `mgAll_formsInA_at`
(Johnson/Desc/Sound/MgAt/K3RidesDigFull.lean). WRITTEN A FURTHER TIME, AT ANOTHER FORM OF THE
PROMISE: the library's `formsInA_of_promise` (Johnson/LPFE1R/In8OfFacts.lean) has this end from
`onQ` at the composed meaning itself; here it stands at the thread's `Form`, at the honest letters.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `simp only [Bool.and_eq_true]` on one line, on a conjunction of six Bools.
Limits. An implication: that the form holds at any state, and that the item is open at any border,
are premises. THE FULL SIZE ALONE. THAT THE THREAD STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS
NOT SAID HERE: where it stands at none, all is idle.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.Sound.MgAt.K3RidesDigFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgAll_formsInA_at)
open VerifiableInference.Desc.First (S Item Pub onAt pubHeld pubOfItems openSets start)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The form at a border gives the test that is tied to an open run of forms.** -/
theorem formsInA_of_form {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m)
    {l kk : ℕ} {rn : String}
    (hO : Item.forms l kk rn ∈
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [])
    {p : ℕ × String} (hp : p ∈ h.𝔇.runs l kk rn) (hah : h.𝔇.ah p.1 p.2 = true) :
    VerifiableInference.Desc.K9.formsInA (h.𝔇.Rd l) (h.𝔇.N.sent l) (h.𝔇.N.group l) p.1 p.2 s =
      true := by
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  obtain ⟨-, hor⟩ := hF.2
  rcases hor with hb | ⟨hB, -⟩
  · exact absurd h0 hb
  · simp only [Bool.and_eq_true] at hB
    have hq := List.all_eq_true.1 hB.1.2 (Pub.formsIn l kk rn)
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hO, List.mem_singleton.2 rfl⟩))
    exact mgAll_formsInA_at h.𝔇 mgBase hq hp hah

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.formsInA_of_form
