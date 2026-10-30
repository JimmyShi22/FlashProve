-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/SmallAtHead.lean: THE SMALLNESS TEST, AT THE FIRST CHAIN's THREAD
AT THE HEAD: BEHIND EACH OF THE 25 DRAWS THE ITEM forms l (5 + shift) "small" MEANS NO MORE THAN THE
LIBRARY's `SmallAt` AT ITS TABLE `cellsAhead`, WHERE THE THREAD's FORM HOLDS BEHIND THE DRAW. Three
theorems; no definition; none of the library's goals.

  `small8_behind_draw`   BY THE KERNEL: at each of the 25 segments the library's test `small8B`
                   (Johnson/LPFE1R/In8OfFacts.lean) says yes at the border behind the draw: the item
                   is open there, and (4 + shift, "K8.equations") is one of its runs
  `small8_at_draw_no`    a control: at the draw's own border, in front of it, it says no at every
                   segment
  **`small_means_at_head`**   under the library's head (h : `P5J.AtMgA`): l < 25 · the thread's
                   `Form` at the border 14 * l + (if l = 24 then 5 else 4) + 3, at a state s · s has
                   a record tl of the test · the caller's list of tables is tl's own · SmallAt at
                   cellsAhead … l (z, s) ⊢ the thread's `means` at that item, at the seat (z, s), at
                   every input, every strings and every z
HOW. `formsInA_of_form` (Johnson/Desc/ProofFile/Honest/K8/FormsInAtHead.lean) ·
`forms_small_of_smallAt` (Johnson/Desc/K8/Honest/SmallBackAt9.lean) · the library's `lk_there`
(Johnson/P5J/AllFormsThereAt.lean), `fullLinks_sub` (Johnson/LPFK9R/SitsAtConstant.lean),
`mem_runsAt` (Johnson/Desc/Sound/MgAt/Runs.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
ONE OPTION IS RAISED, AT THE TWO CLOSED TESTS (maxRecDepth). `decide +kernel` twice; `decide` at
three written sorts.
Limits. THE FORM BEHIND THE DRAW AND THE TWO FACTS ON THE STATE ARE PREMISES. Nothing on the digits.
THE FULL SIZE ALONE. THAT THE THREAD STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS NOT SAID
HERE: where it stands at none, all is idle.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.FormsInAtHead
import Johnson.Desc.K8.Honest.SmallBackAt9
import Johnson.LPFE1R.In8OfFacts
import Johnson.P5J.AllFormsThereAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mem_runsAt)
open VerifiableInference.Desc.First (S Item ModelPart shift runsOf)
open VerifiableInference.Desc.First.K8 (SmallAt cellsAhead)
open VerifiableInference.Desc.First.K8.Honest (forms_small_of_smallAt)
open VerifiableInference.Desc.LinkJoin (small8B)
open IM (subAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

set_option maxRecDepth 1000000 in
/-- Behind each draw the item is open, and the single equations are one of its runs. -/
theorem small8_behind_draw : ((List.range 25).all fun m =>
    small8B (14 * m + (if m = 24 then 5 else 4) + 3) m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: in front of the draw, which opens the item, the test says no at every segment. -/
theorem small8_at_draw_no : ((List.range 25).any fun m =>
    small8B (14 * m + (if m = 24 then 5 else 4) + 2) m) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **BEHIND A DRAW THE ITEM ON THE RUN "small" MEANS NO MORE THAN THE LAW's SENTENCE.** -/
theorem small_means_at_head {l : ℕ} (hl : l < 25) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (14 * l + (if l = 24 then 5 else 4) + 3) k s m)
    {tl : HTailF2} (ht : s.tl? = some tl) (hf : s.funs? = some tl.funs)
    (w₀ : Local W₀ Rc ProofFile.Inst Tr) (z : ProofFile.InstPub) (yy : Strs) (v : WtF)
    (hS : SmallAt (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s)) s v) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means w₀
      (Item.forms l (5 + shift (subAt l)) "small") (z, s) yy v := by
  have h1 := List.all_eq_true.1 small8_behind_draw l (List.mem_range.2 hl)
  unfold small8B at h1
  rw [Bool.and_eq_true] at h1
  have hO := List.contains_iff_mem.1 h1.1
  have hsub : P5J.fullLinks[l]? = some (subAt l) := LPFK9.fullLinks_sub l hl
  have hr : ∀ sub : ModelPart,
      runsOf sub (5 + shift sub) "small" = [(4 + shift sub, "K8.equations")] := by
    intro sub
    cases sub <;> decide
  obtain ⟨Lk, hlk⟩ := P5J.lk_there h hl
  have hin := formsInA_of_form h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF hO
    (p := (4 + shift (subAt l), "K8.equations"))
    (mem_runsAt P5J.fullLinks l (subAt l) hsub _ _ _ (List.contains_iff_mem.1 h1.2)) rfl
  exact forms_small_of_smallAt
    { h.𝔇 with decT := fun _ _ => some (Q.cells w₀), cr1 := carryX } mgBase l (shift (subAt l))
    (subAt l) hsub (hr _) Lk hlk z s yy v ht hf hin hS

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.small8_behind_draw
#print axioms ProofFile.Honest.K8.small8_at_draw_no
#print axioms ProofFile.Honest.K8.small_means_at_head
