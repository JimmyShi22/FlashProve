-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTiedEachR.lean: THE LINK's THREE PIECES TIED, IN THE SECOND FORM OF
THE CHAIN OF PROMISES (`TiedAtR`), AT EVERY LINK OF A LIST OF PIECES: the form in which a kind's
share of the chain of promises is joined (`KindTiedR`, Johnson/Desc/Sound/TiedR.lean): «for every
link l below n and every piece q that stands at the link's number in the list: q, with the table's
extractor at that number, is tied there». A definition and three theorems: LinkTiedEach.lean's, in
the second form; book-keeping over LinkTiedPubR.lean.

What is said.
  `LinkAsksR … Rch k qb qq qe Eb Eq Ee`: there are letters at which all that `link_tied_pubR` takes
    holds. `tiedR_of_asks`: it gives the three ties at k, k + 1, k + 2. `link_tied_eachR`: **if at
    every link below n the three pieces that stand at k l, k l + 1, k l + 2 meet `LinkAsksR`: each
    of the three is tied at its number.** `behind_tied_eachR`: the second alone.

Limits. BOOK-KEEPING: AN IMPLICATION: shown of no IOP. One list a link pays all three places. Rch,
the table's letters, the list of pieces and the numbers are free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedPubR

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

/-- **ALL THAT THE THREE TIES TAKE AT ONE LINK, THE LETTERS UNDER «THERE ARE».** -/
def LinkAsksR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop) (k : ℕ)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (Eb Eq Ee : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) : Prop :=
  ∃ (α : Type) (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (l : ℕ) (sub : First.ModelPart)
    (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (ctx : P → S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String)),
    SegAt l sub L ∧
    qb.b = (below b₁).lift Prod.snd (fun t s => (t.1, s)) ∧
    qq.b = (below b₂).lift Prod.snd (fun t s => (t.1, s)) ∧
    qe.b = (below b₃).lift Prod.snd (fun t s => (t.1, s)) ∧
    (∀ a b w, Eb a b w = w) ∧ (∀ a b w, Eq a b w = w) ∧ (∀ a b w, Ee a b w = w) ∧
    ∀ z, TiedAsksR Nm Mg links pl (RchAt Rch z) k C Rw sub L φ Ok Fu p pw tmOf lenOf d N b₃
      (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) (ctx z) Rd own rdW items z

/-- It gives the three ties. -/
theorem tiedR_of_asks {Nm : Numbers} {Mg : Meaning P W} {links : List ModelPart} {pl : List Place}
    {Rch : ℕ → (P × S) × F.E.Str → Prop} {k : ℕ} {qb qq qe : Piece (ckP .two) F (P × S) Claim W}
    {Eb Eq Ee : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W}
    (H : LinkAsksR Nm Mg links pl Rch k qb qq qe Eb Eq Ee) :
    TiedAtR Nm Mg links pl (fun a => a) Rch k (qb.withMap Eb) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1) (qq.withMap Eq) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1 + 1) (qe.withMap Ee) := by
  obtain ⟨α, C, Rw, l, sub, L, φ, Ok, Fu, p, pw, tmOf, lenOf, d, N, b₁, b₂, b₃, ctx, Rd, own, rdW,
    items, h, hqb, hqq, hqe, hEb, hEq, hEe, Hz⟩ := H
  exact link_tied_pubR Nm Mg links pl Rch k C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₁ b₂ b₃ qb
    qq qe hqb hqq hqe Eb Eq Ee hEb hEq hEe ctx Rd own rdW items Hz

/-- **THE THREE PIECES, TIED AT EVERY LINK OF A ROW OF PIECES.** -/
theorem link_tied_eachR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (pcs : List (Piece (ckP .two) F (P × S) Claim W))
    (E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (kOf : ℕ → ℕ) (n : ℕ)
    (H : ∀ l < n, ∀ qb qq qe, pcs[kOf l]? = some qb → pcs[kOf l + 1]? = some qq →
      pcs[kOf l + 1 + 1]? = some qe →
      LinkAsksR Nm Mg links pl Rch (kOf l) qb qq qe (E (kOf l)) (E (kOf l + 1))
        (E (kOf l + 1 + 1)))
    (hlen : ∀ l < n, kOf l + 1 + 1 < pcs.length) :
    ∀ l < n, ∀ i < 3, ∀ q, pcs[kOf l + i]? = some q →
      TiedAtR Nm Mg links pl (fun a => a) Rch (kOf l + i) (q.withMap (E (kOf l + i))) := by
  intro l hl i hi q hq
  have h2 := hlen l hl
  have g := tiedR_of_asks (H l hl pcs[kOf l] pcs[kOf l + 1] pcs[kOf l + 1 + 1]
    (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    (List.getElem?_eq_getElem h2))
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · obtain rfl : pcs[kOf l] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.1
  · obtain rfl : pcs[kOf l + 1] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.2.1
  · obtain rfl : pcs[kOf l + 1 + 1] = q :=
      Option.some.inj ((List.getElem?_eq_getElem h2).symm.trans hq)
    exact g.2.2

/-- **THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING, AT EVERY LINK.** -/
theorem behind_tied_eachR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (pcs : List (Piece (ckP .two) F (P × S) Claim W))
    (E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (kOf : ℕ → ℕ) (n : ℕ)
    (H : ∀ l < n, ∀ qb qq qe, pcs[kOf l]? = some qb → pcs[kOf l + 1]? = some qq →
      pcs[kOf l + 1 + 1]? = some qe →
      LinkAsksR Nm Mg links pl Rch (kOf l) qb qq qe (E (kOf l)) (E (kOf l + 1))
        (E (kOf l + 1 + 1)))
    (hlen : ∀ l < n, kOf l + 1 + 1 < pcs.length) :
    ∀ l < n, ∀ q, pcs[kOf l + 1]? = some q →
      TiedAtR Nm Mg links pl (fun a => a) Rch (kOf l + 1) (q.withMap (E (kOf l + 1))) :=
  fun l hl q hq => link_tied_eachR Nm Mg links pl Rch pcs E kOf n H hlen l hl 1 (by omega) q hq

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tiedR_of_asks
#print axioms VerifiableInference.Desc.LinkJoin.link_tied_eachR
#print axioms VerifiableInference.Desc.LinkJoin.behind_tied_eachR
