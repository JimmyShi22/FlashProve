-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSeam.lean: THE CHAIN OF PAYERS OF "BEHIND A SENDING THE NEW MESSAGES HAVE
THEIR PROMISE", JOINED IN ONE TERM. The ledger's clauses at the shared chain's two sendings
(two_core, five_core, Johnson/Desc/K14/Law/LedgerSends.lean) ask one premise with a price (hD). HERE
ITS PAYER IS TYPED, general in the place: from K1's law of a sending (send_gives_smpAt,
Johnson/Desc/K1/Law/GoodSendForms.lean) through the seam (sendGivesSmp_of_send, smp_of_number,
Johnson/Desc/Sound/SendSeam.lean; sendCf_of_smp, Johnson/Desc/Sound/SendLaw.lean), with the seam's
"word" paid by word_paid (Johnson/Desc/Sound/WordOfFirst.lean), at the reading smpSt
(Johnson/Desc/Sound/SmpShared.lean; smpByNumber is the same term after unfolding).

  send_cf         **the law of a sending (SendGivesCf) at a piece that holds a sending**, at
                  smpSt. Called at the two places by d2_seamed | d5_seamed
                  (Johnson/Desc/K14/Law/LedgerSeamRow.lean).
WHAT STAYS, ALL ON THE PLAN AND THE DATA: hC, he₁, hk₁, he (K1's law's own: the condition on the
plan and the radii; the first written round is the seeds' round; the count) · entry (the k-th
message's member bears the plan's shape and the law's radius) · all (each new member is a sampled
message's) · hnum (at a yes inside On the plan's letter oNo gives a SAMPLED message's member its
number in the record) · htree (its tree is base + n, n below the number of the FIRST written round's
trees) · hSh (the piece shows what it sends: Piece.ShownAll, Johnson/Desc/Sound/ShownOfData.lean: it
reads the piece's base and written rounds alone, so it is the row's own piece's; cutShown pays it at
a cut row).
TO KNOW. memK ranges over ALL messages of the place, an unsampled one too (the first mask at "send
o_u"): the other files' forms ask entry and htree at every k. There is no member of the meant kind
for such a message: memK k is there a dummy, OUTSIDE ms and outside the sendings of new; its radius
is read by nothing.
What is not claimed. NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerPays
import Johnson.Desc.Sound.WordOfFirst
import Johnson.Desc.Sound.SendSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.K1 (sendPiece IsSend sampledAt shapeAt shapesOf condPort errPort
  seedEntry seedMaps)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Xi W : Type} {Fr : Frame} (G : FileDescription Xi)

/-- **Part 5's law of a sending at a piece that holds a sending**, at the reading by fixed numbers.
    -/
theorem send_cf (P : VerifiableInference.Desc.K1.Par) (rad : ℕ → ℕ) (hC : condPort P rad = true)
    (blk : Block (P₁ × St) Cl) (hS : IsSend P (fun t : P₁ × St => t.2.st) blk) (base : ℕ)
    (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : ℕ)
    (he : errPort P rad ≤ e) (oNo : Mem → ℕ) (memK : Fin (shapesOf P).length → Mem)
    (new : List Mem) (On : (P₁ × St) × Fr.E.Str → Prop)
    (entry : ∀ k, (memK k).1.l.get (memK k).2 = (shapeAt P k, rad k.val))
    (all : ∀ x ∈ new, ∃ k, sampledAt P k ∧ memK k = x)
    (hnum : ∀ a τ x, On a →
      (sendPiece (W := W) (F := Fr) blk base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      ∀ k, sampledAt P k →
        oNo (memK k) = x.1.2.st.oracles.size - (shapesOf P).length + k.val)
    (htree : ∀ k, ∃ n, ((memK k).1.seat (memK k).2).1 = base + n ∧ n < d₁.trees.length)
    (hSh : ∀ x ∈ new, (sendPiece (W := W) (F := Fr) blk base d₁ d₂ P.coordinates e).ShownAll G
      P.codes x.1.l x.1.seat) :
    SendGivesCf P.codes G (fun t : P₁ × St => smpSt P.codes oNo stSh t.2)
      (sendPiece (W := W) (F := Fr) blk base d₁ d₂ P.coordinates e) new On fun _ => True := by
  refine sendCf_of_smp P.codes G _ _ new On _ ?_ hSh ?_
  · intro x hx
    obtain ⟨k, _, rfl⟩ := all x hx
    obtain ⟨n, hj, hn⟩ := htree k
    refine ⟨n, d₁.trees[n], hj, ?_⟩
    show treeShT [d₁, d₂] n = _
    rw [treeShT_cons, if_pos hn]
    exact List.getElem?_eq_getElem hn
  · exact sendGivesSmp_of_send G P rad _ hC blk (fun t : P₁ × St => t.2.st) hS base d₁ d₂ he₁ hk₁ e
      he memK new On (fun _ => True)
      ⟨entry, all, fun _ _ _ _ _ => trivial,
        smp_of_number P rad (fun t : P₁ × St => t.2.st) oNo _ memK On entry hnum⟩
      (fun y μ k => fInOf G P.codes (memK k) base d₁ d₂ y μ)
      (fun y τ k => by
        obtain ⟨n, hj, hn⟩ := htree k
        exact word_paid G P.codes blk base d₁ d₂ P.coordinates e (memK k) n hj hn y τ)

end Desc.K14.Law

#print axioms Desc.K14.Law.send_cf
