-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HpubOf.lean: THE CALL hpub_of, THE ARM "TIED,
AT THE READS": the binder hpub of k01_law at the tied public items that come at
a link's reads' place: behind an accepting run of the sending's piece each of them holds. A
statement with its proof: a call of pub_formsIn_new_later (R1).

OBJECT. sendPiece c base d₁ d₂ cc e at any sub-protocol c under the lot's own B (c.UnderR B.retype),
B with LaterSend P B and two declared rounds (meant: IM.k1Reads).
USER. hpub at N := D.N, links := linksFull, ps := flatPlacesOf linksFull true, k := noL l false,
P := parL Z G l false, B := blkL Z G l false X arrs, t := 1, T := tiedAt linksFull ps (noR l): the
first half of tiedL Mg.more l false. HpubAtFull.lean lays hT in by the kernel's fact.
Main names:
  yes_of_piece   behind the piece's accepting run B has accepted, on two rounds
  hpub_of        **the call**
PAID INSIDE: formsInT l j r in front (off the promise: inAt_pub) · the clause on the book
(inAt_book) · the new messages' seats (hP: the row's laterSeatsB).
PREMISES THAT STAY, BY NAME.
  hMg     Mg.pub = pubAll D base0.
  hT      ON THE TABLE: each item of T is a formsIn l j r whose formsInT l j r is tied to an item
          that is open in front.
  hRd     ON THE LETTER D.Rd: what a reader gave in front it gives behind (ReadersStay).
  hfound  SecondFound: each array of the segment's second sending is found behind under a new
          number: it wants that the frame's list own is numbered as the shape's messages.
NOT HERE: the items that the door's filling makes at the place (the second half of tiedL).
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.K1.Law.PubAtLaterCall
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers PubData pubAll)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.Sound (Frame strsOf)

variable {Pp W Cl : Type} {F : Frame}

/-- **Behind an accepting run of the piece of a sending, at a sub-protocol c under the lot's own B:
B has accepted, on two rounds, from the piece's state in front to its state behind.** -/
theorem yes_of_piece (B : Block S Unit) (h2 : B.rounds.length = 2) (c : Block S Cl)
    (hu : c.UnderR (B.retype : Block S Cl)) (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ)
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])) (x : S × F.E.Str)
    (hx : (sendPiece (W := W) (F := F) c base d₁ d₂ cc e).ior.red.out a τ = some x) :
    ∃ rs gs, rs.length = 2 ∧ B.decide a.1 rs gs = .ok x.1 := by
  obtain ⟨rs, cols, n, hst⟩ := K13.Law.piece_step _ hx
  obtain ⟨hfit, gs, hd⟩ := step_ok F.ft c _ _ rs cols n hst
  refine ⟨rs.map noDigest, gs, ?_, hu.2 _ _ _ _ hd⟩
  rw [List.length_map, Keeps.fit_length _ _ hfit, hu.1]
  exact h2

/-- **THE CALL hpub_of, THE ARM "TIED, AT THE READS"**: the binder hpub of k01_law at the tied
public items that come at a link's reads' place. T: these items. -/
theorem hpub_of (D : PubData) (base0 : Pub → Pp × S → Bool) (Mg : Meaning Pp W)
    (hMg : Mg.pub = pubAll D base0) (links : List ModelPart) (ps : List Place) (k : ℕ) (P : Par)
    (B : Block S Unit) (hS : LaterSend P B) (h2 : B.rounds.length = 2) (c : Block S Cl)
    (hu : c.UnderR (B.retype : Block S Cl)) (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ) (z : Pp)
    (l t : ℕ) (ht : t < 3) (hP : laterSeatsB D.N P l t (D.N.treesAt ps[k]?) = true)
    (T : List Pub)
    (hT : ∀ q ∈ T, ∃ j r, q = .formsIn l j r ∧
      Pub.formsInT l j r ∈ First.pubOfItems (openAt links ps k))
    (hRd : ∀ (s s' : S) rs gs j r, rs.length = 2 → B.decide s rs gs = .ok s' →
      Pub.formsInT l j r ∈ First.pubOfItems (openAt links ps k) → ReadersStay D l j r s s')
    (hfound : ∀ (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
      SecondFound (idsOf P s.st.oracles.size).toList s s') :
    ∀ (a : S × F.E.Str) τ x, Sound.onQ D.N Mg links ps (fun s : S => (z, s)) k a →
      a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ cc e).ior.red.out a τ = some x →
      ∀ q ∈ T, Mg.pub q (z, x.1) = true := by
  intro a τ x ha hm hx q hq
  obtain ⟨j, r, rfl, ho⟩ := hT q hq
  obtain ⟨rs, gs, hlen, hd⟩ := yes_of_piece B h2 c hu base d₁ d₂ cc e a τ x hx
  have hIn : InAt D.N Mg links ps k (z, a.1) (strsOf F a.2) := ⟨ha, hm⟩
  have h0 := inAt_pub hIn _ (List.mem_append_right _ ho)
  obtain ⟨hb, hTr⟩ := inAt_book hIn
  rw [hMg] at h0 ⊢
  exact pub_formsIn_new_later hS D base0 (z, a.1) (z, x.1) rs gs hlen hd hb l j r
    (hRd _ _ rs gs j r hlen hd ho) t _ ht hTr hP (hfound _ _ rs gs hlen hd) h0

end VerifiableInference.Desc.K1
