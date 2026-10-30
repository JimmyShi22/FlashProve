-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/WorthTwoOfOpen.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE:
AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD, IN FRONT OF EACH OF THE 25 BATCHINGS: IF EVERY
ITEM THAT IS OPEN THERE SAYS ITS SENTENCE, THE LIBRARY's TWO SENTENCES "WORTH" OF THE LOOKUP ON THE
DIGITS (`WorthTwo`, Johnson/Desc/First/Link/Law/WorthAtFront.lean) HOLD. IT PAYS NOTHING: IT TAKES
TWO OF THE OPEN ITEMS' SENTENCES AND WRITES THEM IN THE LIBRARY's OTHER WORDS. Three theorems; no
definition; none of the library's goals.

  `worth_open_full`   A CLOSED TEST ON THE TWO WRITTEN LISTS: at each l < 25 the items worth l
                   (7 + shift) "planes" and "keys" stand in the thread's forward open set at the
                   batching's border
  `worth_open_no`   a control: at each segment's first border the same test says no
  **`worthTwo_of_open`**   the head · the thread's letters, all free · l < 25 · what `digAt` returns
                   at l ⊢ at every input wI, seat a, strings st and witness v: (every item open at
                   the batching's border says its sentence of them) → WorthTwo at the data's list of
                   what is sent, radii, seats and arrays, at a.2 and v
HOW. The thread's sentence at an item worth is the composed meaning's field, by unfolding · the
piece's number: `hpc_at` (Johnson/LPFK9R/FactsAtConstant.lean) · from the item to each half:
`fPl_at`, `fKe_at` (Johnson/Desc/First/Look/K3At.lean) at `k3At_mgAll`
(Johnson/Desc/Sound/MgAt/K3At.lean). In the proof the meaning is written out at the thread's data,
in which the Script's field cells stands at the input (Q.cells wI): the two sealed lemmas read the
list of what is sent and the lookups' letters alone.
KIN, NOT CALLED (files that the library may not hold): the like at the lookup on the calls, at the
feed-forward layers' own member: `item_of_thr`, `open_k4`, `planes_item_head`, `planes_lay_head`
(Johnson/Desc/ProofFile/Honest/K4/Law/W/OpenAtHead.lean, NuHead.lean).
DEVICES: attribute [-instance] Inst.Model.Scl.ref, as the files beneath have it · the two closed
tests are one evaluation each by Lean's kernel (`decide +kernel`). TACTICS THAT SEARCH: `simp`, on
three lines, at Boolean "and" and at membership in a list.
Limits. AN IMPLICATION: WHO MAKES THE TWO ITEMS' SENTENCES TRUE IS NOT SAID. The witness v stands
under "for all". THE LIBRARY's HEAD IS A PREMISE. The full size and the format's second hash function alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.First.Link.Law.WorthAtFront
import Johnson.Desc.First.Link.Law.KxAtFront
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.LPFK9R.FactsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (fPl_at fKe_at k3At_mgAll)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase)
open VerifiableInference.Desc.LinkJoin (batchAt WorthTwo heardDig)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- **The two items are open in front of each batching.** -/
theorem worth_open_full : ((List.range 25).all fun l =>
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps l)).contains
        (Item.worth l (7 + shift (IM.subAt l)) "planes") &&
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps l)).contains
        (Item.worth l (7 + shift (IM.subAt l)) "keys")) = true := by
  decide +kernel

/-- A control: at each segment's first border the test says no. -/
theorem worth_open_no : ((List.range 25).any fun l =>
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l)).contains
        (Item.worth l (7 + shift (IM.subAt l)) "planes") ||
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l)).contains
        (Item.worth l (7 + shift (IM.subAt l)) "keys")) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **FROM THE OPEN ITEMS' SENTENCES TO THE TWO SENTENCES "WORTH".** -/
theorem worthTwo_of_open {l : ℕ} (hl : l < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD)) :
    ∀ wI a st v,
      (∀ j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
          (batchAt P5J.At.links P5J.At.ps l),
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means wI j a st v) →
      WorthTwo S.fork? heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad
        (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr a.2 v := by
  intro wI a st v hAll
  have hb := List.all_eq_true.1 worth_open_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at hb
  have m1 : Item.worth l (7 + shift (IM.subAt l)) "planes" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
        (batchAt P5J.At.links P5J.At.ps l) := by simpa using hb.1
  have m2 : Item.worth l (7 + shift (IM.subAt l)) "keys" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
        (batchAt P5J.At.links P5J.At.ps l) := by simpa using hb.2
  have q1 : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells wI), cr1 := carryX } mgBase).worth l
      (7 + shift (IM.subAt l)) "planes" (a.1, a.2) st v := hAll _ m1
  have q2 : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells wI), cr1 := carryX } mgBase).worth l
      (7 + shift (IM.subAt l)) "keys" (a.1, a.2) st v := hAll _ m2
  rw [LPFK9.hpc_at h l] at q1 q2
  exact ⟨fun g F' hf hg =>
      fPl_at (k3At_mgAll _ mgBase) (fun _ => ()) l hd a.1 a.2 st v q1 g F' hf hg,
    fun g F' hf hg =>
      fKe_at (k3At_mgAll _ mgBase) (fun _ => ()) l hd a.1 a.2 st v q2 g F' hf hg⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.worth_open_full
#print axioms ProofFile.Honest.K8.worth_open_no
#print axioms ProofFile.Honest.K8.worthTwo_of_open
