-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ReadyAtHead.lean: THE SMALLNESS TEST: THE PAYER OF THE PREMISE "THE
STATE IN FRONT OF THE DRAW IS READY" (`K8ReadyS`, Johnson/Desc/ProofFile/Honest/K8/SeatedReady.lean)
AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`,
Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), AT ALL ITS ARGUMENTS: at the output head's
draw (border 343) and at each layers' segment's (border 28 g + 6). This file alone of the kind's
stands over these letters. Lemmas; none of the library's goals.

  `PlanFacts tl`   THREE FACTS ON A PLANNED LINK's DATA OF THE TEST, ON PUBLIC NUMBERS ALONE: NM is
                   the size of the list of matrices · no matrix is drawn in them · no draw is
                   counted in them
  `WaitsAt T b start`   "NO COUNT WAITS" AT THE BORDER, BY EITHER OF TWO ROADS (the field `waits` of
                   `K8Reached`)
  **`reached_head`**   THERE ARE: THE GROUND G₀ THAT THE LIBRARY's OWN MAKER YIELDS AT Zp
                   (ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀: a function: so G₀ is fixed) · the
                   planned link Xl at 24, of kind 2 · THE THREAD's MEMBER NUMBER 343, SEATED OVER
                   THE DRAW's BLOCK AT THE PLACE ProofFile.k8Par Zp G₀ Xl 24 (the fields `here` and
                   `seats` of `K8Seated`) · with: PlanFacts Xl.tl → WaitsAt … 343 … → K8Reached ‹the
                   thread› 343 (ProofFile.k8Par Zp G₀ Xl 24) Xl.tl …
  **`K8ReadyS_at_head.outHead`**   so: … → K8ReadyS ‹the thread› Said 343 (ProofFile.k8Par Zp G₀ Xl 24),
                   whatever is said
  **`reached_layers`**, **`K8ReadyS_at_head.layers`**   the like at g < 12, at the link Xl at 2 g,
                   of kind 0, border 28 g + 6: OF THE THREE FACTS THE FIRST IS THE LIBRARY's OWN
                   THERE (`IM.k8_of_layers`): the two others stay; UNDER ONE PREMISE MORE: `tabs`:
                   at every state reached there the closed list has the place's shapes
WHICH ROADS: the thread gives the library's "reached" over the members' own steps; the member right
in front lays the plan's data, closed, by its own yes (Johnson/Desc/K8/Honest/ReadsReach.lean); the
place's columns, rows and number of combinations are the link's by the lot's own text
(ParFacts.lean).
Limits. PAYERS UNDER PREMISES. WHAT STAYS A PREMISE: at the head `PlanFacts`; at a layers' segment
its second and third fact, and `tabs`; at both `WaitsAt`. OF `K8Seated` THE FIELDS here AND seats
ARE PAID; ITS OTHER FOUR (oracles · half · named · sees) ARE OWED AT THESE LETTERS before the law on
acceptance can be called. The attention segments: not here. THE FULL SIZE ALONE, under the library's
head, which has no member.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedReady
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K8.Honest.ReadsReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par tabs Seats approximateRangeProofDrawKind atS)
open VerifiableInference.Desc.First.K8.Honest (front_head front_layers draw_head draw_layers
  k8Par_nm k8Par_ks k8Par_ms k8Par_tau)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- Three facts on a planned link's data of the test. Spent whole at the output head alone: at a
layers' segment the first is the library's own. -/
structure PlanFacts (tl : HTailF2) : Prop where
  nm : tl.NM = tl.mats.size
  undrawn : tl.cfF.size = 0
  fold0 : tl.foldDrawn = 0

/-- "No count waits" at a border, by either of two roads. -/
def WaitsAt {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Q : Type}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (start : Q → S) : Prop :=
  (∀ a s, T.formP b (a, s) → s.noneWaits = true) ∨
    ∀ z s, Reach T.ft T.bs start b (z, s) → s.noneWaits = true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At the output head's draw.** -/
theorem reached_head :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧ Xl.kind = 2 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl 24)) ∧
      (PlanFacts Xl.tl →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 343
          (ProofFile.startS Zp) →
        K8Reached (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 343
          (ProofFile.k8Par Zp G₀ Xl 24) Xl.tl (ProofFile.startS Zp) fun v => v.x.pub) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Xl, hX, hk, hlen, hF⟩ := front_head h.scope h.reads O
  obtain ⟨blk, Xl', hX', hb, hs⟩ := draw_head h.scope h.reads O
  obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
  refine ⟨Bs.G₀, Xl', blk, O.blank, hX, hk, hb, hs, fun hP hW => ?_⟩
  exact
    { len := hlen
      begun := fun _ _ _ _ h0 => h0
      keep := fun z s hr => (hF (ProofFile.startS Zp) z s hr).1
      closed := fun z s hr => (hF (ProofFile.startS Zp) z s hr).2.1
      waits := hW
      undrawn := hP.undrawn
      fold0 := hP.fold0
      nm := k8Par_nm Zp Bs.G₀ Xl' 24 hP.nm
      ks := k8Par_ks Zp Bs.G₀ Xl' 24
      ms := k8Par_ms Zp Bs.G₀ Xl' 24
      tau := k8Par_tau Zp Bs.G₀ Xl' 24
      tabs := fun z s tl hr ht => (hF (ProofFile.startS Zp) z s hr).2.2 tl ht
      mark := fun _ s hf => Option.isNone_iff_eq_none.1 hf }

/-- So "ready" from the pair, whatever is said. -/
theorem K8ReadyS_at_head.outHead
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧ Xl.kind = 2 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl 24)) ∧
      (PlanFacts Xl.tl →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 343
          (ProofFile.startS Zp) →
        K8ReadyS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 343
          (ProofFile.k8Par Zp G₀ Xl 24)) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hk, hb, hs, hR⟩ :=
    reached_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact ⟨G₀, Xl, blk, hG, hX, hk, hb, hs,
    fun hP hW _ _ _ _ hA => ready_of_reached (hR hP hW) hA.1⟩

/-- **At a layers' segment's draw.** -/
theorem reached_layers {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧ Xl.kind = 0 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl (2 * g))) ∧
      (Xl.tl.cfF.size = 0 → Xl.tl.foldDrawn = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (28 * g + 6)
          (ProofFile.startS Zp) →
        (∀ z s tl, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (28 * g + 6) (z, s) → s.tl? = some tl →
          tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
            tabs (ProofFile.k8Par Zp G₀ Xl (2 * g))) →
        K8Reached (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (28 * g + 6)
          (ProofFile.k8Par Zp G₀ Xl (2 * g)) Xl.tl (ProofFile.startS Zp) fun v => v.x.pub) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Xl, hX, hk, hlen, hF⟩ := front_layers h.scope h.reads O hg
  obtain ⟨blk, Xl', hX', hb, hs, hnm⟩ := draw_layers h.scope h.reads O hg
  obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
  refine ⟨Bs.G₀, Xl', blk, O.blank, hX, hk, hb, hs, fun hU hD hW hT => ?_⟩
  exact
    { len := hlen
      begun := fun _ _ _ _ h0 => h0
      keep := fun z s hr => (hF (ProofFile.startS Zp) z s hr).1
      closed := fun z s hr => (hF (ProofFile.startS Zp) z s hr).2
      waits := hW
      undrawn := hU
      fold0 := hD
      nm := hnm
      ks := k8Par_ks Zp Bs.G₀ Xl' (2 * g)
      ms := k8Par_ms Zp Bs.G₀ Xl' (2 * g)
      tau := k8Par_tau Zp Bs.G₀ Xl' (2 * g)
      tabs := hT
      mark := fun _ s hf => Option.isNone_iff_eq_none.1 hf }

theorem K8ReadyS_at_head.layers
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧ Xl.kind = 0 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl (2 * g))) ∧
      (Xl.tl.cfF.size = 0 → Xl.tl.foldDrawn = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (28 * g + 6)
          (ProofFile.startS Zp) →
        (∀ z s tl, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (28 * g + 6) (z, s) → s.tl? = some tl →
          tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
            tabs (ProofFile.k8Par Zp G₀ Xl (2 * g))) →
        K8ReadyS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (28 * g + 6) (ProofFile.k8Par Zp G₀ Xl (2 * g))) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hk, hb, hs, hR⟩ :=
    reached_layers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  exact ⟨G₀, Xl, blk, hG, hX, hk, hb, hs,
    fun hU hD hW hT _ _ _ _ hA => ready_of_reached (hR hU hD hW hT) hA.1⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.reached_head
#print axioms ProofFile.Honest.K8.K8ReadyS_at_head.outHead
#print axioms ProofFile.Honest.K8.reached_layers
#print axioms ProofFile.Honest.K8.K8ReadyS_at_head.layers
