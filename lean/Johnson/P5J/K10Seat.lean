-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Seat.lean: OF K10's NAMED CONDITION AT THE CLOSED CONSTANT (`AtMgA.K10Owes`,
Johnson/P5J/K10Owes.lean) WHAT SPEAKS OF THE SEAT AND OF THE TABLE's TWO COUNTS IS PAID, AT THE
CONCRETE SECOND HASH FUNCTION: the fields step, trees, msgs. Statements and proofs. After
Johnson/P5J/K09Seat.lean, which does the like for the batching kind.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `k10_block_at`: at a number k whose place in `At.ps` is of the kind K10 the first chain's flat
    list holds a sub-protocol B at that place, and B is the closing of a link, seated alone
    (`LaidAlone`): by `At.places_paid` and `k10_sits_every` (Johnson/LPFK10R/SitsEvery.lean).
  `k10_counts_at`: the fields trees and msgs: the constant's numbers' two counts stay across such a
    place: B declares no oracle (`told_k10`), and the numbers are closed over the sub-protocols
    (`At.N_at`; `told_succ_ps`, Johnson/Desc/First/ToldSucc.lean).
  `k10_step_at`: the field step: under the three flat lists' heads (q1, q2, q3: premises, as in the
    tower's own rows): where the piece at number k of the seated term's first row puts out b from a:
    the public part stays; `K10Step a.1.2 b.1.2`; the strings behind are what the library's stage
    leaves at the piece's own base (`Behind F q.base`).
Limits. AT OnBytes.secondHashFunction ALONE (the theorems on the seat that are called stand in scope at that
hash). q1, q2, q3 are premises. Nothing on the laws. Nothing on soundness.

-/
import Johnson.P5J.K10Owes
import Johnson.P5J.PlacesPaid
import Johnson.LPFK10R.CloseShareScope
import Johnson.Desc.First.ToldSucc
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Link.Law.OracleRides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start blockPlaces told_succ_ps)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (K10Step Behind Par)
open VerifiableInference.Desc.LinkJoin (out_strs)
open Johnson.Desc.First.Walk.Tied (block_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a place of the kind K10 there sits the closing of a link, alone.** -/
theorem k10_block_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : ℕ) (p : Place)
    (hp : At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∃ (B : Block TS ProofFile.Cl) (Q : Par) (a : Place), cF.blocksInOrder[k]? = some B ∧ B.place = p ∧
      a.kind = KindName.K10 ∧ B.oracles.flatten = [] ∧
      IM.LaidAlone ProofFile.sameReply B
        (VerifiableInference.Desc.K9.closing Q : Block TS Unit).retype B.name a := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hk2 := IM.head_is_two h.scope h.reads O
  have hpl := At.places_paid h.scope h.reads h.laid
  have e : (blockPlaces cF.blocksInOrder)[k]? = some p := by rw [hpl]; exact hp
  unfold blockPlaces at e
  rw [List.getElem?_map] at e
  obtain ⟨B, hB, hBp⟩ := Option.map_eq_some_iff.1 e
  have hBK : B.place.kind = KindName.K10 := by rw [hBp]; exact hK
  obtain ⟨l, sub, Lk, pw, Q, -, -, -, -, -, h5⟩ :=
    LPFK10.k10_sits_every O hk2 B (List.mem_of_getElem? hB) hBK
  have ht := LPFK10.told_k10 O hk2 hB hBK
  unfold LPFK10.toldC at ht
  rw [List.getElem?_map, hB] at ht
  exact ⟨B, Q, _, hB, hBp, rfl, Option.some.inj ht, h5⟩

/-- **The table's two counts stay across K10's places.** -/
theorem k10_counts_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : ℕ) (p : Place)
    (hp : At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    (At.N Zp cF).treesAt At.ps[k + 1]? = (At.N Zp cF).treesAt At.ps[k]? ∧
      (At.N Zp cF).msgsAt At.ps[k + 1]? = (At.N Zp cF).msgsAt At.ps[k]? := by
  obtain ⟨B, Q, a, hB, -, -, h0, -⟩ := k10_block_at h k p hp hK
  have hpl := At.places_paid h.scope h.reads h.laid
  rw [At.N_at h.scope h.reads h.laid]
  have e := told_succ_ps (N := P5T.numbersOf (At.pseats Zp)) (s := At.shape Zp) (links := At.links)
    (bs := cF.blocksInOrder) At.ps hpl (ProofFile.Law.flatPlaces_nodup fullLinks true) k B hB
  rw [h0] at e
  simpa using e

/-- **What the seated term's piece at K10's number puts out.** -/
theorem k10_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (k : ℕ) (p : Place)
    (hp : At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∀ q, (h.toAtMg.row L)[k]? = some q → ∀ a τ b, q.ior.red.out a τ = some b →
      b.1.1 = a.1.1 ∧ K10Step a.1.2 b.1.2 ∧
        Behind (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) q.base
          (strsOf _ a.2) (strsOf _ b.2) := by
  intro q hq a τ b hb
  obtain ⟨B, Q, pa, hB, -, hpa, -, h5⟩ := k10_block_at h k p hp hK
  have hT := h.toAtMg.ofDesc L q1 q2 q3
  have eb := OfDesc.pieceAt hT hq hB
  obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := Piece.out_decide _ a b τ hb
  rw [eb] at hd
  obtain ⟨s', hs', he⟩ := held_decide B a.1 b.1 _ gs hd
  obtain ⟨⟨y, hy, hw⟩, -, -⟩ := LPFK10.seated_yes h5 (by rw [hpa]; decide) _ _ _ _ hs'
  exact ⟨by rw [he], ⟨_, _, y, hy, by rw [he]; exact hw⟩,
    ⟨q.ds, a.2, τ, rfl, congrArg (strsOf _) (out_strs hb)⟩⟩

end P5J

#print axioms P5J.k10_block_at
#print axioms P5J.k10_counts_at
#print axioms P5J.k10_step_at
