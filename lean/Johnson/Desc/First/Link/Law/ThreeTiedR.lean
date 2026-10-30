-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ThreeTiedR.lean: A LINK's THREE PIECES (the batching; the frame's
sub-protocol behind it; the one equation) TIED IN THE SECOND FORM OF THE CHAIN OF PROMISES
(`TiedAtR`) AT THE OWN PIECES OF THE IOP AS WRITTEN IN LEAN, FROM THE THREE PIECES' LAWS AS THEY
COME, AT WHATEVER RELATIONS THEY COME: general in the five relations, each of which may hang on the
public part. And so the batching kind's share (`KindTiedR … .K9`). Definitions and theorems. IT
OVERTAKES LinkTiedPubR.lean's `TiedAsksR` | `link_tied_pubR`, LinkTiedEachR.lean's `LinkAsksR` and
K9KindTiedR.lean's `k9_kindTiedR` AS THE FORM TO COUNT.

Why. `TiedAsksR` fixed the relation in front of the batching as «the listed runs' forms are worth 0»
(`relForms`). The table's row of the batching closes, beside the forms, two sentences on worths; the
tie's fourth clause is asked at EVERY transcript and must give all that the row closes: from the
forms alone the two sentences cannot be had (by reading):
that list could be paid by nobody. The law that has the two sentences in its front relation lies
(`link_table_worth`, WorthAtFront.lean). Here no relation is fixed: whichever law is
laid in, its own relations stand in the ties.

What is said.
  `ThreeAsksR … R0 R1 R1' R2 R3 z`: at the public part z: the three pieces' laws (`GoodIn`) between
    the conditions `onTR` at the four borders, and five debts a piece (`TieRestR`) at these very
    relations. `three_tied_pubR`: **`TiedAtR … (fun a => a) Rch k | k + 1 | k + 2` at the three own
    pieces.** `ThreeAsks`: the letters under «there are». `k9_kindTiedR'`: **`KindTiedR Nm Mg links
    pl Rch E pcs .K9` from `ThreeAsks` and `ShutAsksR` at every link.**

Limits. BOOK-KEEPING: AN IMPLICATION. `ThreeAsks` and `ShutAsksR` at every link ARE THE DEBTS:
nothing is paid here; that they can be met is shown nowhere here. Rch is a letter. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open _root_.Run (ckP)

variable {P W : Type} {F : Frame}

/-- **THE THREE LAWS AND FIVE DEBTS A PIECE, AT THE PUBLIC PART z.** -/
structure ThreeAsksR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (pb pq pe : Piece (ckP .two) F S Claim W)
    (R0 R1 R1' R2 R3 : S × F.E.Str → W → Prop) (z : P) : Prop where
  gb : pb.GoodIn (onTR Nm Mg links pl (fun s : S => (z, s)) Rz k)
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1)) R0 R1
  gq : pq.GoodIn (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1)) R1' R2
  ge : pe.GoodIn (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1 + 1)) R2 R3
  Tb : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz k pb R0 R1
  Tq : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) pq R1' R2
  Te : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1) pe R2 R3

/-- **THE THREE PIECES, TIED AT THE OWN PIECES OF THE IOP.** -/
theorem three_tied_pubR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop) (k : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (hqb : qb.b = (below b₁).lift Prod.snd fun t s => (t.1, s))
    (hqq : qq.b = (below b₂).lift Prod.snd fun t s => (t.1, s))
    (hqe : qe.b = (below b₃).lift Prod.snd fun t s => (t.1, s))
    (Eb Eq Ee : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEb : ∀ a b w, Eb a b w = w)
    (hEq : ∀ a b w, Eq a b w = w) (hEe : ∀ a b w, Ee a b w = w)
    (R0 R1 R1' R2 R3 : P → S × F.E.Str → W → Prop)
    (H : ∀ z, ThreeAsksR Nm Mg links pl (RchAt Rch z) k (atRec qb (below b₁))
      (atRec qq (below b₂)) (atRec qe (below b₃)) (R0 z) (R1 z) (R1' z) (R2 z) (R3 z) z) :
    TiedAtR Nm Mg links pl (fun a => a) Rch k (qb.withMap Eb) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1) (qq.withMap Eq) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1 + 1) (qe.withMap Ee) :=
  ⟨(tiedByR_of_part Nm Mg links pl Rch k qb (below b₁) hqb Eb hEb _ _ R0 R1 fun z =>
      tiedByR_of (H z).gb (tieOwesR_of_rest (H z).Tb)).tiedAtR,
    (tiedByR_of_part Nm Mg links pl Rch (k + 1) qq (below b₂) hqq Eq hEq _ _ R1' R2 fun z =>
      tiedByR_of (H z).gq (tieOwesR_of_rest (H z).Tq)).tiedAtR,
    (tiedByR_of_part Nm Mg links pl Rch (k + 1 + 1) qe (below b₃) hqe Ee hEe _ _ R2 R3 fun z =>
      tiedByR_of (H z).ge (tieOwesR_of_rest (H z).Te)).tiedAtR⟩

/-- **ALL THAT THE THREE TIES TAKE AT ONE LINK, THE LETTERS UNDER «THERE ARE».** -/
def ThreeAsks (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop) (k : ℕ)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (Eb Eq Ee : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) : Prop :=
  ∃ (b₁ b₂ b₃ : Block S Claim) (R0 R1 R1' R2 R3 : P → S × F.E.Str → W → Prop),
    qb.b = (below b₁).lift Prod.snd (fun t s => (t.1, s)) ∧
    qq.b = (below b₂).lift Prod.snd (fun t s => (t.1, s)) ∧
    qe.b = (below b₃).lift Prod.snd (fun t s => (t.1, s)) ∧
    (∀ a b w, Eb a b w = w) ∧ (∀ a b w, Eq a b w = w) ∧ (∀ a b w, Ee a b w = w) ∧
    ∀ z, ThreeAsksR Nm Mg links pl (RchAt Rch z) k (atRec qb (below b₁)) (atRec qq (below b₂))
      (atRec qe (below b₃)) (R0 z) (R1 z) (R1' z) (R2 z) (R3 z) z

/-- **THE BATCHING KIND's SHARE OF THE CHAIN OF PROMISES, SECOND FORM: THE FORM TO COUNT.** -/
theorem k9_kindTiedR' (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W)
    (pcs : List (Piece (ckP .two) F (P × S) Claim W)) (hfit : k9Fit links pl = true)
    (hlen : pl.length ≤ pcs.length)
    (HL : ∀ m < links.length, ∀ qb qq qe, pcs[batchAt links pl m]? = some qb →
      pcs[batchAt links pl m + 1]? = some qq → pcs[batchAt links pl m + 1 + 1]? = some qe →
      ThreeAsks Nm Mg links pl Rch (batchAt links pl m) qb qq qe (E (batchAt links pl m))
        (E (batchAt links pl m + 1)) (E (batchAt links pl m + 1 + 1)))
    (HS : ∀ m < links.length, ∀ qs, pcs[batchAt links pl m + 4]? = some qs →
      ShutAsksR Nm Mg links pl Rch (batchAt links pl m + 4) qs (E (batchAt links pl m + 4))) :
    KindTiedR Nm Mg links pl Rch E pcs .K9 := by
  intro i q a hq ha hk
  obtain ⟨m, hm, hb, hi⟩ := k9_at links pl hfit i a ha hk
  have g : TiedAtR Nm Mg links pl (fun a => a) Rch (batchAt links pl m)
        (pcs[batchAt links pl m].withMap (E (batchAt links pl m))) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (batchAt links pl m + 1)
        (pcs[batchAt links pl m + 1].withMap (E (batchAt links pl m + 1))) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (batchAt links pl m + 1 + 1)
        (pcs[batchAt links pl m + 1 + 1].withMap (E (batchAt links pl m + 1 + 1))) := by
    obtain ⟨b₁, b₂, b₃, R0, R1, R1', R2, R3, hqb, hqq, hqe, hEb, hEq, hEe, H⟩ :=
      HL m hm pcs[batchAt links pl m] pcs[batchAt links pl m + 1]
        pcs[batchAt links pl m + 1 + 1] (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    exact three_tied_pubR Nm Mg links pl Rch _ b₁ b₂ b₃ _ _ _ hqb hqq hqe _ _ _ hEb hEq hEe R0 R1
      R1' R2 R3 H
  rcases hi with rfl | rfl | rfl
  · obtain rfl : pcs[batchAt links pl m] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.1
  · obtain rfl : pcs[batchAt links pl m + 1 + 1] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.2.2
  · obtain ⟨pw, piece, b₅, hqs, hEs, H⟩ := HS m hm q hq
    exact shut_tied_pubR Nm Mg links pl Rch _ pw piece b₅ q hqs _ hEs H

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.three_tied_pubR
#print axioms VerifiableInference.Desc.LinkJoin.k9_kindTiedR'
