-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/CopyRunAtHead.lean: the kind "the code switch" (K2): THE TIE AT A KEPT COPY FROM THE
TIE AT THE SENDER IN FRONT (`ownMsgs_copy_at_book`, AtFullSide/K2/OwnMsgsCopyAtBook.lean), WITH ITS
PREMISE ON EVERY RUN (hrun) PAID, UNDER THE LIBRARY's HEAD AND THE OPENING, AT THE BOOK, AT A
WRITTEN PAIR. IN hrun's STEAD STAND SEVEN PREMISES, OF WHICH NONE SPEAKS OF A RUN's COINS: two
public tests at the switch in front (its closing's test; its test on the instance, at every input
that is meant) · two on the filling D: how many challenges it reads at an address · one on the
written segments' numbers of challenges · two orders between three numbers. One step back. One
closed fact by evaluation in Lean's kernel; lemmas: calls.

  `copyPair_mem`    a written pair's two switches are written places, one link apart; the segment
                    is the written one between them
  `copyNoW`         BY LEAN's KERNEL (no control): the message that a kept copy copies is not the
                    last of the sending in front
  `ownMsgs_copy_at_head`   THE END. LEFT: hm₀ (the tie at the sender) · hNN · the seven

hrun's FIVE LIMBS AND THEIR PAYERS: the frame hands the switch in front its coins:
`own_hands_at_book` (AtFullSide/K2/OwnHandsAtTheBook.lean) · its rows return: `rows_isSome`
(Honest/K2/Law/LotsAnswer.lean), at four public tests · the own data in front of it read alike at
both switches: `lotOwn_of_prefix` · so do the challenges: `heard_of_prefix`
(Honest/K2/Law/HeardPrefix.lean) · the later switch's closing reads the sender's own messages as the
sender laid them: `hd_at_head` (Honest/K2/Law/OwnAtSender.lean).

Limits. hm₀ IS A PREMISE: the tie at the message that is copied: where that is itself a kept copy
the law must be called again. THE SEVEN ARE PREMISES: hcl₀ · hpub₀ · hD1 · hD0 · hgam · hf · hN₀. AT
CHAIN 0 ALONE. Link 1's kept copies have no switch in front: not spoken of. What
`ownMsgs_copy_at_book` says of itself holds here. The full size and the format's second hash function alone.
The head, the opening and the book's return are premises. Nothing on any property.
-/
import AtFullSide.K2.OwnMsgsCopyAtBook
import AtFullSide.K2.OwnHandsAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.HeardPrefix
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnAtSender
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left Sizes mainRows keptNo)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- A written pair's two switches are written places, one link apart; the segment is the written one
between them. -/
theorem copyPair_mem {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) :
    p₀ ∈ placesW ∧ p ∈ placesW ∧ p₀.link + 1 = p.link ∧ segsW[p.link - 1]? = some S := by
  unfold copyPairs at hx
  obtain ⟨q, hq, e⟩ := List.mem_filterMap.1 hx
  cases h1 : placesW.find? (fun a => a.link + 1 == q.link) with
  | none =>
    simp only [h1] at e
    cases e
  | some a =>
    cases h2 : segsW[q.link - 1]? with
    | none =>
      simp only [h1, h2] at e
      cases e
    | some T =>
      simp only [h1, h2] at e
      obtain ⟨rfl, rfl, rfl⟩ : a = p₀ ∧ q = p ∧ T = S := by
        have e' := Option.some.inj e
        exact ⟨congrArg (·.1) e', congrArg (·.2.1) e', congrArg (·.2.2) e'⟩
      have hb : (a.link + 1 == q.link) = true :=
        List.find?_some (p := fun b : SwitchPlace => b.link + 1 == q.link) h1
      exact ⟨List.mem_of_find?_eq_some h1, hq, beq_iff_eq.1 hb, h2⟩

set_option maxRecDepth 1000000 in
/-- The message that a kept copy copies is not the last of the sending in front. -/
theorem copyNoW : (copyPairs.all fun x => (List.range x.2.1.sizes.kept.length).all fun i =>
    decide (keptNo (membersOfSeg x.2.2 true) i <
      (switchSent x.1.sizes x.1.others).size - 1)) = true := by
  decide +kernel

variable {W₀ Rc Xi Tr Cells Tok : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **THE TIE AT A KEPT COPY FROM THE TIE AT THE SENDER IN FRONT, WITH THE PREMISE ON EVERY RUN
PAID.** hcl₀, hpub₀: two public tests at the switch in front. hD1, hD0: how many challenges the
filling reads at an address. hgam: the written segments' numbers of challenges lie below fx₀. -/
theorem ownMsgs_copy_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (Q : Script B (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N₀ N num fx₀ fx : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) {i n : Nat}
    (hi : i < p.sizes.kept.length)
    (hnn : n = keptNo (membersOfSeg S true) i)
    (hm₀ : OwnMsgs Q Vd N₀ num fx₀ (switchMsgOff 0 D readers (lotClosingAt lay segsW) p₀ n))
    (hNN : N₀ ≤ N)
    (hcl₀ : closingOk freshTable (segsW.take p₀.link) p₀ = true)
    (hpub₀ : ∀ w, Vd w → publicOk D lay p₀ (segsW.take p₀.link) w.x = true)
    (hD1 : ∀ w, Vd w → ∀ s m a, s < p₀.link → p.addrs s m = some a → (D w.x).heardAt a ≤ fx₀)
    (hD0 : ∀ w, Vd w → ∀ m, m < p₀.others.size - 1 → (D w.x).heardAt (p₀.ownAddr m) = 0)
    (hgam : ∀ Sg ∈ segsW.take p₀.link, ∀ g ∈ Sg.gamma, g < fx₀)
    (hf : fx₀ ≤ fx) (hN₀ : fx₀ ≤ N) :
    OwnMsgs Q Vd N num fx (switchMsgOff 0 D readers (lotClosingAt lay segsW) p (1 + i)) := by
  obtain ⟨m₀, m₁, hlk, hseg⟩ := copyPair_mem hx
  have hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact m₀
  have hp : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact m₁
  have hnlt : n < (switchSent p₀.sizes p₀.others).size - 1 := by
    rw [hnn]
    exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 copyNoW _ hx) i
      (List.mem_range.2 hi))
  have hlen : (segsW.take p₀.link).length = p₀.link := by
    have hlt : p.link - 1 < segsW.length := (List.getElem?_eq_some_iff.1 hseg).1
    rw [List.length_take]
    omega
  refine ownMsgs_copy_at_book h hB Q Vd N₀ N num fx₀ fx 0 D readers hx hi hnn hm₀ hNN ?_
  intro k w hd hV hNl c V hc hVr
  obtain ⟨get, put, -, hh, -⟩ := own_hands_at_book h O hB hp₀
  obtain ⟨c₀, hc₀, -⟩ := hh k
  have hl₀ : (hd.take fx₀).length = fx₀ := by
    rw [List.length_take]
    omega
  have hpre : hd.take fx₀ <+: hd.take fx := by
    have e : hd.take fx₀ = (hd.take fx).take fx₀ := by
      rw [List.take_take, Nat.min_eq_left hf]
    rw [e]
    exact List.take_prefix _ _
  have hrows := rows_isSome D readers lay segsW p₀ hcl₀ c₀ w (hd.take fx₀)
  rw [serves_at_head h.toAtMg O p₀ hp₀, roomy_at_head h.toAtMg O p₀ hp₀, hpub₀ w hV,
    fits_at_head h.toAtMg O p₀ hp₀] at hrows
  cases hV₀ : switchRowsLaid D readers (lotClosingAt lay segsW) p₀ c₀ w (hd.take fx₀) with
  | error e =>
    rw [hV₀] at hrows
    cases hrows
  | ok V₀ =>
    refine ⟨c₀, V₀, hc₀, hV₀, ?_, ?_, ?_⟩
    · simp only [Nat.sub_zero, List.take_length]
      exact lotOwn_of_prefix hp₀ hp segsW (D w.x) (readers w) hpre
        (fun s m a hs ha => by rw [hl₀]; exact hD1 w hV s m a hs ha)
    · simp only [Nat.sub_zero, List.take_length]
      exact heard_of_prefix hpre (fun Sg hSg g hg => by rw [hl₀]; exact hgam Sg hSg g hg)
    · intro Wl
      simp only [Nat.sub_zero, List.take_length]
      rw [hlen, Nat.zero_add]
      have e := hd_at_head h.toAtMg O hp₀ hp (by omega) (D w.x) (readers w) (hd.take fx)
        (hD0 w hV) Wl n hnlt
      rw [segments_at_head h.toAtMg O] at e
      exact e

end AtFullSide.K2

#print axioms AtFullSide.K2.copyPair_mem
#print axioms AtFullSide.K2.copyNoW
#print axioms AtFullSide.K2.ownMsgs_copy_at_head
