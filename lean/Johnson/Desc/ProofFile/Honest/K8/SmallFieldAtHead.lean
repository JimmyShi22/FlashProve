-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/SmallFieldAtHead.lean: THE SMALLNESS TEST, AT THE FIRST CHAIN's
THREAD AT THE HEAD: THE FIELD small OF THE RECORD `K8ItemsAt`
(Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean) IS MET AT ALL 25 DRAWS, AT THE LIBRARY's TABLE
`cellsAhead`, WHEREVER THE KIND's MEMBER IS SEATED. Two theorems; no definition; none of the
library's goals.

  **`small_field_at_head`**   under the library's head (h : `P5J.AtMgA`): l < 25 · `K8Seated` at the
                   border b := 14 * l + (if l = 24 then 5 else 4) + 2, at whatever member, reader
                   and parameters ⊢ the field's sentence, to the letter, at A a := cellsAhead … l a
                   and iS := forms l (5 + shift (subAt l)) "small": from a stand of the thread at
                   b, a step of the member and THE THREAD's FORM BEHIND THE STEP: SmallAt at the
                   seat behind gives the item's meaning there
  `itemsAt_small_paid`   so a record at that table and whatever first item is a record at the true
                   item: five fields are left
HOW. The stand holds the fold of the chain's blocks up to b from the first state (the clause `Made`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean); there the caller's list of tables is the record's
own, by a call of the library's `k8FunsAre` (Johnson/P1K8R/FunsAtSeat.lean); the step is a yes of
the draw's decision, which keeps that (`funs_behind_keeps`, Johnson/Desc/K8/Honest/FunsBehind.lean);
the form behind gives the public test, and with SmallAt the item (`small_means_at_head`,
Johnson/Desc/ProofFile/Honest/K8/SmallAtHead.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
NO TACTIC THAT SEARCHES.
Limits. ONE FIELD OF SIX. `K8Seated` and the form behind the step are premises. Nothing on digits,
tie, zz or fine. No witness's content is read: v is a letter. THE FULL SIZE ALONE. THAT THE THREAD
STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS NOT SAID HERE: where it stands at none, all is
idle.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallAtHead
import Johnson.Desc.ProofFile.Honest.K8.SeatedItemsAt
import Johnson.Desc.K8.Honest.FunsBehind
import Johnson.P1K8R.FunsAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S Item shift)
open VerifiableInference.Desc.First.K8 (Par SmallAt cellsAhead step_seats_iff)
open VerifiableInference.Desc.First.K8.Honest
open IM (subAt)
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

/-- **THE FIELD small, AT ALL 25 DRAWS.** Behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem small_field_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {P : Par × List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P) :
    ∀ k s m E ds y cols s' w₀ z yy v,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      SmallAt (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')) s' v →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means w₀
        (Item.forms l (5 + shift (subAt l)) "small") (z, s') yy v := by
  intro k s m E ds y cols s' w₀ z yy v hA hd hS hFb hSm
  have hT := hA.1
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hT.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  have h1 := P1K8S.k8FunsAre h.scope h.reads O (x := (l, if l = 24 then 5 else 4))
    (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩) _ _ _ _ hfold
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨d, rfl, -, rfl, rfl, -⟩ := seated_moved hK hd hM
  obtain ⟨rv, -, -, hm, -, -⟩ := (step_seats_iff P.1 blk hK.seats _ s s' _ _ _).1 hstep
  obtain ⟨tl, ht, hf⟩ := funs_behind_keeps (keeps_of_means hm) h1
  exact small_means_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hFb ht hf w₀ z yy v hSm

/-- **A record at whatever first item is a record at the true one**: the field small is paid. -/
theorem itemsAt_small_paid (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {P : Par × List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P) {i₀ iD : Item}
    (hI : K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) i₀ iD) :
    K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a)
      (Item.forms l (5 + shift (subAt l)) "small") iD :=
  { hI with
    small := small_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hK }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.small_field_at_head
#print axioms ProofFile.Honest.K8.itemsAt_small_paid
