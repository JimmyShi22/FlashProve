-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceK14Roots.lean: THE FENCE AT K14's TWO SENDINGS: PREMISE (T) OF `bookKept_at_send` | `bookKept_at_send_desc`
(Johnson/Desc/Sound/FenceK14Sends.lean, FenceK14AtDesc.lean): "the piece's stretch lists as many trees as the planner's layout has shapes":
THE BLOCK's HALF, AND (T) ITSELF FROM ONE FACT ON THE DATA; AND THE RIDER AT A LAYOUT THAT IS A VALUE OF THE PLAN ALONE. Nine theorems.

WHERE (T) CAN COME FROM. Not from a yes of the verifier: the roots are in no view (`roundsFit`, Johnson/Desc/Block.lean: "but for the
roots"). Not from the tiling's premises as they stand (ChainFit, Johnson/Desc/Sound/Tiles.lean: a declared round is held against its data in
what is stored and what is opened, not in the trees sent). It is a fact on the maker of the data: ROUND BY ROUND THE DATA
LIST AS MANY TREES AS THE DECLARED ROUND's ENTRY HAS ROOTS (typed at a description's data:
RoundAsG, DataRounds.lean: d.trees.length = r.entry.roots). Here is what stands between it and (T):
  `decideSend_codes`: a yes of the sending's decision: the record's codes are the place's (its own second test).
  `sendAt_rounds`: a sending at this chain declares K1's two rounds. `sendAt_roots`: their entries' roots sum to the number
    of the place's trees. `trees_length`: that is the layout's number of shapes.
  `sendAt_codes`: the first, at a sending at this chain's state.
  `sendAt_shapes`: SO at a yes: the layout of `Received` has as many shapes as the block's declared rounds have roots.
  `hT_of_data`: (T) AS bookKept_at_send ASKS IT, for a block b := a sending at this chain, from (D): the number of trees that
    the piece's stretch lists is the sum of the declared rounds' roots.
  `sendAt_received_plan`: at a yes the layout of `Received` IS layTrees Q.codes Q.sent: A VALUE OF THE PLACE ALONE.
  `seatedNew_named`: THE RIDER, NAMED, at a piece of the description's form: b the second or the fifth of blocks P: there are the
    sending's own n, Q, … with b = sendAt P n Q …, Q.codes = P.codes, such that FOR THE LAYOUT lay := layTrees P.codes Q.sent (where
    it is there), at every yes under the fence: the i-th of Q.sent is seated at q.base + lay.tree i, at part lay.part i: SO
    THE PLAN's HALF AND THE SENDING KIND's LEMMA ("the trees and tenants that the block declares are the layout") MEET IT AT ONE lay.

Every "there is", walked: none new.
Limits. (D) is a premise. Book-keeping. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceK14AtDesc
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Grows Block named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend layRows sendOwn Owing)
open VerifiableInference.Desc.Sound (Frame Piece below Received FenceAt SeatedAt bookedOf seated_of_received)
open _root_.Run.PQ (CK)

/-- A yes of the sending's decision: the record's codes are the place's. -/
theorem decideSend_codes {L : Type} (Q : VerifiableInference.Desc.K1.Par) (owed : Option Nat)
    (d : DState L) (rs : List Fmt.RoundView) (ids : Array Nat) (d' : DState L)
    (h : decideSend Q owed d rs = .ok (ids, d')) : d.st.codes = Q.codes := by
  unfold decideSend at h
  split at h
  · obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, h2, h⟩ := dbind_ok h
    have h2' := (VerifiableInference.Desc.K1.need_ok _ _ _).1 h2
    simpa using h2'
  · cases h

/-- A sending at this chain declares K1's two rounds. -/
theorem sendAt_rounds (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St) :
    (sendAt P n Q inFront groups behind).rounds = VerifiableInference.Desc.K1.rounds Q := rfl

/-- Their entries' roots sum to the number of the place's trees. -/
theorem sendAt_roots (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St) :
    ((sendAt P n Q inFront groups behind).rounds.map (·.entry.roots)).sum = Q.trees.length := by
  rw [sendAt_rounds]
  simp [VerifiableInference.Desc.K1.rounds, VerifiableInference.Desc.K1.seedEntry,
    VerifiableInference.Desc.K1.answerEntry]

/-- The place's trees are the layout's shapes. -/
theorem trees_length (Q : VerifiableInference.Desc.K1.Par) (lay : TreeLay)
    (h : layTrees Q.codes Q.sent = some lay) : Q.trees.length = lay.shapes.size := by
  unfold VerifiableInference.Desc.K1.Par.trees
  -- one text for two grounds, as at oraclesOf_length (FenceK14Sends.lean)
  first
    | rw [h]
    | rw [VerifiableInference.Desc.Own.treesMade_eq, h]
  simp

/-- A yes of a sending at this chain's state: the record's codes are the place's. -/
theorem sendAt_codes (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') : d.st.codes = Q.codes := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  have e := decideSend_codes Q none _ rs ids x2 hx
  exact e

/-- **At a yes: a layout of the place's messages at the record's codes has as many shapes as the block's declared
rounds have roots.** -/
theorem sendAt_shapes (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') (lay : TreeLay)
    (hl : layTrees d.st.codes Q.sent = some lay) :
    lay.shapes.size = ((sendAt P n Q inFront groups behind).rounds.map (·.entry.roots)).sum := by
  rw [sendAt_roots, trees_length Q lay (by rw [← sendAt_codes P n Q inFront groups behind d d' rs gs h]; exact hl)]

/-- **(T), as `bookKept_at_send` asks it, from one fact on the data**: (D): the number T of trees that the piece's stretch
lists is the sum of the declared rounds' roots. (Whatever ft, sent, lay `Received` is said with: the number of
the layout's shapes is the growth of the roots.) -/
theorem hT_of_data (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (T : ℕ) (hD : T = ((sendAt P n Q inFront groups behind).rounds.map (·.entry.roots)).sum) :
    ∀ (d d' : St) ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') →
      lay.shapes.size = T := by
  rintro d d' ft sent lay hR ⟨rs, gs, h⟩
  obtain ⟨lay₀, r1, _, _, _, r5⟩ := sendAt_received P n Q inFront groups behind hb d d' rs gs h
  have e := sendAt_shapes P n Q inFront groups behind d d' rs gs h lay₀ r1
  have r5' := hR.2.2.2.2
  rw [hD, ← e]
  omega

/-- At a yes the layout is the place's own: a value of the plan alone. -/
theorem sendAt_received_plan (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (lay : TreeLay) (hl : layTrees Q.codes Q.sent = some lay)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    Received Q.gp.firstTree Q.sent lay d.st d.book d.roots d'.st d'.book d'.roots := by
  obtain ⟨lay₀, hR⟩ := sendAt_received P n Q inFront groups behind hb d d' rs gs h
  have e := hR.1
  rw [sendAt_codes P n Q inFront groups behind d d' rs gs h, hl] at e
  obtain rfl := Option.some.inj e
  exact hR

/-- **THE RIDER, NAMED, at a piece of the description's form.** -/
theorem seatedNew_named {W P₁ : Type} {F : Frame} {C : CK} (lo : ℕ) (low : Tree → Option ℕ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b = b2 ∨ b = b5) :
    ∃ n Q inFront groups behind, b = sendAt P n Q inFront groups behind ∧ Q.codes = P.codes ∧
      ∀ lay, layTrees P.codes Q.sent = some lay →
      ∀ (q : Piece C F (P₁ × St) Unit W),
        q.b = (below b).lift Prod.snd (fun (t : P₁ × St) s => (t.1, s)) →
        ∀ a τ c,
          FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
            (fun t => t.2.roots)) q.base a →
          q.ior.red.out a τ = some c →
          ∀ i, i < Q.sent.size → SeatedAt lo low c.1.2.book (a.1.2.st.oracles.size + i)
            (q.base + lay.tree.getD i 0) (lay.part.getD i 0) := by
  obtain ⟨n, Q, inFront, groups, behind, rfl, hc, hbk⟩ := sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  refine ⟨n, Q, inFront, groups, behind, rfl, hc, fun lay hl q hq a τ c hf hout => ?_⟩
  obtain ⟨_, gs, hd⟩ := piece_yes q a τ c hout
  rw [hq] at hd
  obtain ⟨hd', _⟩ := decide_below_lift _ a.1 c.1 _ gs hd
  have hR := sendAt_received_plan P n Q inFront groups behind hbk lay (by rw [hc]; exact hl) _ _ _ gs hd'
  exact seated_of_received lo low q.base _ _ lay _ _ _ _ _ _ hR hf.1

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.sendAt_received_plan
#print axioms Desc.K14.Law.Fence.seatedNew_named
#print axioms Desc.K14.Law.Fence.hT_of_data
#print axioms Desc.K14.Law.Fence.decideSend_codes
#print axioms Desc.K14.Law.Fence.sendAt_roots
#print axioms Desc.K14.Law.Fence.trees_length
#print axioms Desc.K14.Law.Fence.sendAt_shapes
