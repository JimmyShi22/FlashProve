-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/AcceptedAtHead.lean: THE SMALLNESS TEST: THE DEBT "IT IS ACCEPTED"
(`AcceptedS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's HEAD (`lettersHead`), AT EACH OF THE KIND's 25 DRAWS: the output head's (border 343), the
12 layers' segments' (28 g + 6), the 12 attention segments' (14 (2 g + 1) + 6): UNDER NAMED
PREMISES. It lays the record `K8Seated` (Johnson/Desc/ProofFile/Honest/K8/Seated.lean) at these
letters out of what is paid, and calls `small_acceptedS_reached`. NOT THE DEBT's LAW (that is
`small_acceptedS`, Honest/K8/SeatedReady.lean: general in the thread and in what is said): ITS
INSTANCE AT THESE LETTERS, with the records' premises paid as far as they are:
it shows that the pieces join at one place's numbers. Lemmas; none of the library's goals.

  `oracles_of_alone`   a block that the description lays alone over the kind's block, whole, states
                   one round without an oracle message
  `k8Par_lens`   the place's lists of rows and of columns are of one length
  `HalfAt T blk cells P`   A NAMED PREMISE ON THE THREAD's LETTER hs: the half at the member's place
                   is the kind's own at P (the field `half` of `K8Seated`)
  `seated_of`   `K8Seated` out of its parts
  **`acceptedS_at_head.outHead`**, **`.layers`**, **`.att`**   THERE ARE the ground, the planned
                   link and the thread's member, each tied, with: at every reader of cells and every
                   list of matrices: HalfAt → the list is as long as the place's → ‹the facts on the
                   plan's data› → WaitsAt → AcceptedS ‹the thread› Said fall ‹the border›, whatever
                   is said and whatever the fall
OF `K8Seated`'s SIX FIELDS: here · seats: Honest/K8/ReadyAtHead.lean, ReadyAtHeadAtt.lean · oracles
· sees · the second clause of named: PAID HERE · half · the first clause of named: PREMISES.
Limits. DEBTS UNDER PREMISES: `HalfAt` (whoever lays the prover's halves out of the lots of
rows: the kind's own lot is `smallSLot`, Honest/K8/SmallSLot.lean) · the list's length · the facts
on the plan's data (at the head three; at a layers' segment two; at attention two) · `WaitsAt` · at
a layers' segment `tabs`. THE FULL SIZE ALONE, under the library's head, which has a member under
four premises on the public files (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean). It
stands over another house's laws at attention. ONE LINE TAKES AN INSTANCE AWAY (attribute
[-instance] Inst.Model.Scl.ref), as the file beneath does: it can make nothing provable that was
not.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ReadyAtHeadAtt

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
open VerifiableInference.Desc.First.K8 (Par ParW tabs Seats approximateRangeProofDrawKind atS)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- Laid alone over the kind's block, whole: one round without an oracle message. -/
theorem oracles_of_alone {b : Block S ProofFile.Cl} {p : ParW} {name : String} {a : Place}
    (h : IM.LaidAlone ProofFile.sameReply b (VerifiableInference.Desc.First.K8.whole p) name a) :
    b.oracles = [[]] := (congrArg (·.oracles) h).trans rfl

/-- The place's lists of rows and of columns are of one length. -/
theorem k8Par_lens (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : Nat) :
    (ProofFile.k8Par Z G X l).ms.length = (ProofFile.k8Par Z G X l).ks.length := by
  show (X.tl.mats.toList.map (·.m)).length = (X.tl.mats.toList.map (·.k)).length
  rw [List.length_map, List.length_map]

/-- The half at the member's place is the kind's own. -/
def HalfAt {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (blk : Block S Claim)
    (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) : Prop :=
  (T.hs.find? fun g => g.place == blk.place) = some (smallHalf cells P)

/-- The record out of its parts. -/
theorem seated_of {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
    {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (here : T.bs[b]? = some blk) (seats : Seats blk (approximateRangeProofDrawKind (Cl := Claim) atS P.1))
    (oracles : blk.oracles = [[]]) (half : HalfAt T blk cells P)
    (hm : P.2.length = P.1.ks.length) (hl : P.1.ms.length = P.1.ks.length)
    (sees : ∀ w, T.φ.sees w = some w) : K8Seated T b blk cells P :=
  ⟨here, seats, oracles, half, by simp [smallFits, hm, hl], sees⟩

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
theorem acceptedS_at_head.outHead
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (24), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (24)).ks.length →
        PlanFacts Xl.tl →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (343)
          (ProofFile.startS Zp) →
        AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
          (343) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, hR⟩ :=
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
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm hP hW => ?_⟩
  exact small_acceptedS_reached fall (seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _)
    fun _ => rfl) (hR hP hW)

/-- **At a layers' segment's draw.** -/
theorem acceptedS_at_head.layers
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g)).ks.length →
        Xl.tl.cfF.size = 0 → Xl.tl.foldDrawn = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (28 * g + 6)
          (ProofFile.startS Zp) →
        (∀ z s tl, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (28 * g + 6) (z, s) → s.tl? = some tl →
          tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
            tabs (ProofFile.k8Par Zp G₀ Xl (2 * g))) →
        AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
          (28 * g + 6) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, hR⟩ :=
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
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm hU hD hW hT => ?_⟩
  exact small_acceptedS_reached fall (seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _)
    fun _ => rfl) (hR hU hD hW hT)

/-- **At an attention segment's draw.** -/
theorem acceptedS_at_head.att
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      ∀ (cells : Tr → Cells) (mats : List (Nat × String × Nat)),
        HalfAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
          (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats) →
        mats.length = (ProofFile.k8Par Zp G₀ Xl (2 * g + 1)).ks.length →
        Xl.tl.NM = Xl.tl.mats.size → Xl.tl.cfF.size = 0 →
        WaitsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
          (14 * (2 * g + 1) + 6) (ProofFile.startS Zp) →
        AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
          (14 * (2 * g + 1) + 6) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, hs, hR⟩ :=
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
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, fun cells mats hH hm hN hU hW => ?_⟩
  exact small_acceptedS_reached fall (seated_of hb hs ho hH hm (k8Par_lens Zp Bs.G₀ Xl _)
    fun _ => rfl) (hR hN hU hW)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.oracles_of_alone
#print axioms ProofFile.Honest.K8.k8Par_lens
#print axioms ProofFile.Honest.K8.seated_of
#print axioms ProofFile.Honest.K8.acceptedS_at_head.outHead
#print axioms ProofFile.Honest.K8.acceptedS_at_head.layers
#print axioms ProofFile.Honest.K8.acceptedS_at_head.att
