-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/PlaysAtHead.lean: THE SMALLNESS TEST: THE DEBT "IT PLAYS"
(`PlaysS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT THE FIRST CHAIN's THREAD AT THE HEAD
(`lettersHead`), AT EACH OF THE KIND's 25 DRAWS: the output head's (border 343), the 12 layers'
segments' (28 g + 6), the 12 attention segments' (14 (2 g + 1) + 6): AT WHATEVER IS SAID, UNDER TWO
NAMED PREMISES. And the record `K8Seated` (Johnson/Desc/ProofFile/Honest/K8/Seated.lean) at these
letters, as theorems of their own. Six theorems; no definition; none of the library's goals.

  **`k8Seated_at_head.outHead`**, **`.layers`**, **`.att`**   THERE ARE the ground, the planned link
                   and the thread's member, each tied, with: at every reader of cells and every list
                   of matrices: HalfAt → the list is as long as the place's → K8Seated ‹the thread›
                   ‹the border› ‹the member› cells ‹the place's numbers, the list›
  **`playsS_at_head.outHead`**, **`.layers`**, **`.att`**   the same, ending at PlaysS ‹the thread›
                   Said ‹the border›, whatever is said
HOW. `small_plays` (Honest/K8/SeatedPlays.lean: the debt's law, general in the thread) at the
record; `playsS_of` (Honest/Thread/PaysS.lean). WRITTEN A FURTHER TIME: the three proofs of the
record are the first lines of `acceptedS_at_head.outHead`, `.layers`, `.att`
(Honest/K8/AcceptedAtHead.lean), which build it inside their proofs and do not state it.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `omega` on two lines of each of the three first proofs, on numbers of segments
and borders alone.
Limits. DEBTS UNDER PREMISES: `HalfAt`: the half at the member's place in the thread's list is the
kind's own: a sentence on the prover · the list's length. None of the facts on the plan's data that
"it is accepted" asks is asked. The thread's letters are all free. THE FULL SIZE ALONE, under the
library's head (h : `P5J.AtMgA`). It stands over the honest side's frame
(Johnson/Desc/ProofFile/Honest/), this kind's files there, and, at attention, laws of the attention
segments' own rounds (kind K5: Johnson/Desc/K5/Honest/Law/): files that the library may not hold.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AcceptedAtHead
import Johnson.Desc.ProofFile.Honest.K8.SeatedPlays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
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

/-! ## 1 The record -/

/-- **The record at the output head's draw.** -/
theorem k8Seated_at_head.outHead :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (24), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (24)).ks.length →
        K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (343) blk cells (ProofFile.k8Par Zp G₀ Xl (24), mats) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, -⟩ :=
    reached_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have ho : blk.oracles = [[]] := by
    obtain ⟨Lk, b, Xb, e1, e2, -, la, -⟩ := IM.k8_of_head h.scope h.reads O
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 24) (by omega) 5] at h0
    have hb' : cF.blocksInOrder[14 * (24) + 5 + 2]? = some blk := by
      have e : 14 * (24) + 5 + 2 = 343 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    exact oracles_of_alone la
  exact ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _) fun _ => rfl⟩

/-- **The record at a layers' segment's draw.** -/
theorem k8Seated_at_head.layers {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g)).ks.length →
        K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (28 * g + 6) blk cells (ProofFile.k8Par Zp G₀ Xl (2 * g), mats) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, -⟩ :=
    reached_layers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have ho : blk.oracles = [[]] := by
    obtain ⟨Lk, b, Xb, hp, e1, e2, -, la, -⟩ := IM.k8_of_layers h.scope h.reads O g hg
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g) (by omega) 4] at h0
    have hb' : cF.blocksInOrder[14 * (2 * g) + 4 + 2]? = some blk := by
      have e : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    exact oracles_of_alone la
  exact ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _) fun _ => rfl⟩

/-- **The record at an attention segment's draw.** -/
theorem k8Seated_at_head.att {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g + 1)).ks.length →
        K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (14 * (2 * g + 1) + 6) blk cells (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, -⟩ :=
    reached_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have ho : blk.oracles = [[]] := by
    obtain ⟨Lk, b, Xb, a, e1, e2, -, la, -⟩ := IM.k8_of_attention h.scope h.reads O g hg
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 4] at h0
    have hb' : cF.blocksInOrder[14 * (2 * g + 1) + 4 + 2]? = some blk := by
      have e : 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    exact oracles_of_alone la
  exact ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _) fun _ => rfl⟩

/-! ## 2 It plays -/

/-- **It plays, at the output head's draw.** -/
theorem playsS_at_head.outHead
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (24), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (24)).ks.length →
        PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (343) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hK⟩ :=
    k8Seated_at_head.outHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact ⟨G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    playsS_of _ Said (small_plays _ _ _ _ _ _ _ _ _ blk cells _ (hK cells mats hH hm))⟩

/-- **It plays, at a layers' segment's draw.** -/
theorem playsS_at_head.layers
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g)).ks.length →
        PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (28 * g + 6) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hK⟩ :=
    k8Seated_at_head.layers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  exact ⟨G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    playsS_of _ Said (small_plays _ _ _ _ _ _ _ _ _ blk cells _ (hK cells mats hH hm))⟩

/-- **It plays, at an attention segment's draw.** -/
theorem playsS_at_head.att
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g + 1)).ks.length →
        PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (14 * (2 * g + 1) + 6) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hK⟩ :=
    k8Seated_at_head.att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  exact ⟨G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm =>
    playsS_of _ Said (small_plays _ _ _ _ _ _ _ _ _ blk cells _ (hK cells mats hH hm))⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Seated_at_head.outHead
#print axioms ProofFile.Honest.K8.k8Seated_at_head.layers
#print axioms ProofFile.Honest.K8.k8Seated_at_head.att
#print axioms ProofFile.Honest.K8.playsS_at_head.outHead
#print axioms ProofFile.Honest.K8.playsS_at_head.layers
#print axioms ProofFile.Honest.K8.playsS_at_head.att
