-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ReadyAtHeadAtt.lean: THE SMALLNESS TEST: THE PAYER OF THE PREMISE
"THE STATE IN FRONT OF THE DRAW IS READY" (`K8ReadyS`,
Johnson/Desc/ProofFile/Honest/K8/SeatedReady.lean) AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD
(`lettersHead`), AT EACH ATTENTION SEGMENT's DRAW (border 14 (2 g + 1) + 6): the third sort, beside
Johnson/Desc/ProofFile/Honest/K8/ReadyAtHead.lean. A JOINING OF TWO HOUSES' LAWS: what every state
reached there holds is another house's (Johnson/Desc/K5/Honest/Law/: `keep_at_draw`,
`tabs_at_reach`, `tabs_at_reach_all`, `member_at_head`). Lemmas; none of the library's goals.

  `draw_att`   THE DRAW's OWN MEMBER STANDS AT NUMBER 14 (2 g + 1) + 6, seated over the draw's block
                   at the place of the kind's own lot (the library's `IM.k8_of_attention`)
  **`reached_att`**   g < 12: THERE ARE: the ground G₀ that the library's own maker yields at Zp ·
                   the planned link Xl at 2 g + 1, of kind 1 · the thread's member at that border,
                   seated · with: Xl.tl.NM = Xl.tl.mats.size → Xl.tl.cfF.size = 0 → WaitsAt … →
                   K8Reached ‹the thread› ‹the border› (ProofFile.k8Par Zp G₀ Xl (2 g + 1)) { Xl.tl with
                   funClosed := false, foldDrawn := 0 } …
  **`K8ReadyS_at_head.att`**   so: … → K8ReadyS ‹the thread› Said ‹the border› (ProofFile.k8Par Zp G₀ Xl
                   (2 g + 1))
WHY THESE DATA: at an attention segment the frame lays the count of draws anew as 0, whatever the
plan's own: so "no draw is counted" is no premise here.
Limits. A PAYER UNDER PREMISES: the number of matrices · no matrix is drawn in the plan's data ·
`WaitsAt`. OF `K8Seated` THE FIELDS here AND seats ARE PAID; ITS OTHER FOUR ARE OWED AT THESE
LETTERS. THE FULL SIZE ALONE, under the library's head, which has a member under four premises on
the public files (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean). ONE LINE TAKES AN
INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the other house's files do: it can make
nothing provable that was not.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ReadyAtHead
import Johnson.Desc.K5.Honest.Law.DrawAt
import Johnson.Desc.K5.Honest.Law.TabsAtReachAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block FileDescription)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par tabs Seats approximateRangeProofDrawKind atS)
open VerifiableInference.Desc.First.K8.Ready (closedAt)
open VerifiableInference.Desc.First.K8.Honest (seats_of_alone k8Par_upd)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open H2K5.Honest (ReadsMember member_at_head keep_at_draw tabs_at_reach tabs_at_reach_all)

/-- **The draw's own member at an attention segment.** -/
theorem draw_att {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : Nat} (hg : g < 12) :
    ∃ (b : Block S ProofFile.Cl) (Xl : LinkH) (a : Attention.Plan),
      Bs.G₀.built[2 * g + 1]? = some Xl ∧ Bs.G₀.W.A[g]? = some a ∧ Xl.tl = a.seam.tl ∧
      c.blocksInOrder[14 * (2 * g + 1) + 6]? = some b ∧
      Seats b (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Z Bs.G₀ Xl (2 * g + 1))) := by
  obtain ⟨Lk, b, Xl, a, e1, e2, hX, la, eA, -⟩ := IM.k8_of_attention hS hR O g hg
  obtain ⟨hp, a', l, l', -, eA', -, -, -, -, -, -, el', etl, -⟩ :=
    (IM.ground_tails hS hR O.pub O.blank).1 g hg
  obtain rfl : l' = Xl := Option.some.inj (el'.symm.trans hX)
  obtain rfl : a' = a := Option.some.inj (eA'.symm.trans eA)
  refine ⟨b, l', a', hX, eA, etl, ?_, seats_of_alone la⟩
  have h0 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) 4,
    show 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 by omega] at h0
  exact h0

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

/-- **At an attention segment's draw.** -/
theorem reached_att {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      Xl.kind = 1 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl (2 * g + 1))) ∧
      (Xl.tl.NM = Xl.tl.mats.size → Xl.tl.cfF.size = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (14 * (2 * g + 1) + 6) (ProofFile.startS Zp) →
        K8Reached (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (14 * (2 * g + 1) + 6) (ProofFile.k8Par Zp G₀ Xl (2 * g + 1))
          { Xl.tl with funClosed := false, foldDrawn := 0 } (ProofFile.startS Zp) fun v => v.x.pub) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans M.blank)
  obtain ⟨blk, Xl', a, hX', eA, etl, hb, hs⟩ := draw_att h.scope h.reads O hg
  obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans M.built)
  have ea : (P5J.At.X Zp).A[g]? = some a := by
    rw [← M.pubW]
    exact eA
  refine ⟨Bs.G₀, Xl', blk, M.blank, M.built, M.kind, hb, hs, fun hN hU hW => ?_⟩
  obtain ⟨u1, u2, u3, u4⟩ := k8Par_upd Zp Bs.G₀ Xl' (2 * g + 1) false 0 hN
  exact
    { len := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1
      begun := fun _ _ _ _ h0 => h0
      keep := fun z s hr => by
        rw [keep_at_draw h hg ea hr, ← etl]
      closed := fun z s hr => by
        obtain ⟨tl, e, hc, -⟩ := tabs_at_reach h hg M hr
        unfold closedAt
        rw [e]
        exact congrArg some hc
      waits := hW
      undrawn := hU
      fold0 := rfl
      nm := u1
      ks := u2
      ms := u3
      tau := u4
      tabs := fun z s tl hr ht => tabs_at_reach_all h hg M hr tl ht
      mark := fun _ s hf => Option.isNone_iff_eq_none.1 hf }

/-- So "ready" from the pair, whatever is said. -/
theorem K8ReadyS_at_head.att
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      Xl.kind = 1 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl (2 * g + 1))) ∧
      (Xl.tl.NM = Xl.tl.mats.size → Xl.tl.cfF.size = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (14 * (2 * g + 1) + 6) (ProofFile.startS Zp) →
        K8ReadyS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (14 * (2 * g + 1) + 6) (ProofFile.k8Par Zp G₀ Xl (2 * g + 1))) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hk, hb, hs, hR⟩ :=
    reached_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  exact ⟨G₀, Xl, blk, hG, hX, hk, hb, hs,
    fun hN hU hW _ _ _ _ hA => ready_of_reached (hR hN hU hW) hA.1⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.draw_att
#print axioms ProofFile.Honest.K8.reached_att
#print axioms ProofFile.Honest.K8.K8ReadyS_at_head.att
