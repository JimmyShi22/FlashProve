-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PlainAtSeat.lean: AT THE SEATED LINK OF EACH SORT OF SEGMENT THE ORDER IS CUT AT "K8.equations", AND EACH RUN IN
FRONT OF THAT ENTRY AND BEHIND IT STANDS UNDER A RUN THAT LEAVES THE SMALLNESS TEST's RECORD AND THE LEDGER's SUMS: the structure
`PlainTies` (Honest/K9/PlainFree.lean), as a statement of its own. The library makes these terms inside the proofs of
`free_at_seat_layers`, `free_at_seat_att`, `free_at_seat_head` (Honest/K9/AtSeatAll.lean) and does not hand them out.

  `plainTies_seat_layers`, `plainTies_seat_att`, `plainTies_seat_head`   where the description is opened, in the goals' scope
  **`plainTies_lay_at_head`**, **`plainTies_att_at_head`**, **`plainTies_head_at_head`**   under the library's hypothesis `AtMgA`, at the seated link

The ties on the runs are taken as in Honest/K9/RunCores.lean.

Limits. Nothing here says that a run returns. The full size and the hash function `secondHashFunction` alone, as in the hypothesis. This
file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (attPre att_pre post_nil headPre headPost head_pre head_post)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open P5J (AtMgA)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim}

/-- The ties at a feed-forward segment. -/
theorem plainTies_seat_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) (e1 : c.links[l]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l)) :
    PlainTies Lk 4 [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")] := by
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', p4, X, e1', -, -, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  exact plainTies_layers Lk p4 _ ties tC tD hord

/-- The ties at an attention segment. -/
theorem plainTies_seat_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) (e1 : c.links[l]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l)) :
    PlainTies Lk 4 attPre [] := by
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (Desc.K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  exact ⟨by rw [hord]; rfl, att_pre Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ties tC tD tJ tP, post_nil Lk, ties.tEq⟩

/-- The ties at the head's segment. -/
theorem plainTies_seat_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (e1 : c.links[24]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt 24)) :
    PlainTies Lk 5 headPre headPost := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord
  have hU3 := P1K8.head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  exact ⟨by rw [hord]; rfl, head_pre Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties tC tD tP,
    head_post Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties, ties.tEq⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {k : ℕ} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **At the feed-forward segment 2 g.** -/
theorem plainTies_lay_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g) k Lk p w) :
    PlainTies Lk 4 [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hsub : IM.subAt (2 * g) = .layers := by
    unfold IM.subAt
    rw [if_neg (by omega), if_pos (Nat.mul_mod_right 2 g)]
  exact plainTies_seat_layers h.scope h.reads O (2 * g) (by omega) hsub Sd.link Sd.order

/-- **At the attention segment 2 g + 1.** -/
theorem plainTies_att_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) : PlainTies Lk 4 attPre [] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hsub : IM.subAt (2 * g + 1) = .attention := by
    unfold IM.subAt
    rw [if_neg (by omega), if_neg (by omega)]
  exact plainTies_seat_att h.scope h.reads O (2 * g + 1) (by omega) hsub Sd.link Sd.order

/-- **At the head's segment.** -/
theorem plainTies_head_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Sd : SeatedFree cF Zp 24 k Lk p w) : PlainTies Lk 5 headPre headPost := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact plainTies_seat_head h.scope h.reads O Sd.link Sd.order

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.plainTies_seat_layers
#print axioms ProofFile.Honest.K9.plainTies_seat_att
#print axioms ProofFile.Honest.K9.plainTies_seat_head
#print axioms ProofFile.Honest.K9.plainTies_lay_at_head
#print axioms ProofFile.Honest.K9.plainTies_att_at_head
#print axioms ProofFile.Honest.K9.plainTies_head_at_head
