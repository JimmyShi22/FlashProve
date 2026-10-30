-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SentShown.lean: THE TWO PREMISES OF `shown_new`
(Johnson/Desc/K1/Law/ShownNew.lean) AT THE PIECE OF A SENDING's LAW (`sendPiece`,
Johnson/Desc/K1/Law/GoodSend3.lean): "each new member's tree is one that the piece's own stretch
sends" (`SentBy`, Johnson/Desc/Sound/WordsLaw.lean) and "the piece shows what it sends"
(`Piece.ShownAll`, Johnson/Desc/Sound/ShownOfData.lean). Statements as definitions of a Prop, and
their proofs. General in the block, the base, the two written rounds and the price.
WHY NOT BY `cutShown` | `shownOfData`: these speak of the pieces that the maker cuts out of a row;
the law's own piece is no member of such a row by its text. So the second goes by the lemma beneath
them (`shownBehind`, Johnson/Desc/Sound/ShownBehind.lean), which is general in base and stretch.
Main names:
  `OwedSentBySend`, `sentBy_send`: each member of new sits in a tree base + n with n below the
    number of trees that the FIRST written round sends: `SentBy (sendPiece b base d₁ d₂ c e) new`.
  `OwedShownAllAt`, `shownAll_at`: AT ANY PIECE p: the seats fit (`SeatFits`); each tree that p's
    stretch sends is listed (`ListedAt`); what is told of such a tree has the data's depth and
    words: `p.ShownAll G cs m seat`. `shownAll_send`: so at `sendPiece`.
  `shown_send`: **the two, laid into `shown_new`**: behind a yes of `sendPiece`:
    `shownJT cs G ms j t (strsOf F x.2)`.
What is not claimed. `SeatFits`, `ListedAt`, "what is told of the tree has the data's shape", that a
member sits at the seat, or the bound on n: tests on the plan. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.ShownNew
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Sound (Frame Piece Mem SitsAt shownJT SentBy strsOf SeatFits ListedAt
  shownBehind)

/-- **OWED.** The new members' trees are sent by the law's piece's first round. -/
def OwedSentBySend : Prop :=
  ∀ {T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT) (c e : ℕ)
    (new : List Mem),
    (∀ x ∈ new, ∃ n, (x.1.seat x.2).1 = base + n ∧ n < d₁.trees.length) →
    SentBy (sendPiece (W := W) (F := F) b base d₁ d₂ c e) new

theorem sentBy_send : OwedSentBySend := by
  intro T Cl W F b base d₁ d₂ c e new h x hx
  obtain ⟨n, hj, hn⟩ := h x hx
  refine ⟨n, d₁.trees[n], hj, ?_⟩
  show treeShT [d₁, d₂] n = some d₁.trees[n]
  rw [treeShT_cons, if_pos hn]
  exact List.getElem?_eq_getElem hn

/-- **OWED.** At any piece: seats that fit, trees that are listed and told as the data has them:
the piece shows what it sends. -/
def OwedShownAllAt : Prop :=
  ∀ {Xi T Cl W : Type} {C : CK} {F : Frame} (p : Piece C F T Cl W) (G : FileDescription Xi) (cs : Codes)
    (m : List (OracleShape × ℕ)) (seat : Fin m.length → ℕ × ℕ), SeatFits G cs m seat →
    ListedAt F p.base p.ds →
    (∀ n sh, treeShT p.ds n = some sh → ∀ o, G.oracleAt (p.base + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) →
    p.ShownAll G cs m seat

theorem shownAll_at : OwedShownAllAt := by
  intro Xi T Cl W C F p G cs m seat hS hL hO y τ k n sh hj hs
  exact shownBehind Xi G cs m seat hS C F p.base p.ds hL y τ k n sh hj hs (hO n sh hs)

/-- So at the law's piece. -/
theorem shownAll_send {Xi T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT)
    (c e : ℕ) (G : FileDescription Xi) (cs : Codes) (m : List (OracleShape × ℕ))
    (seat : Fin m.length → ℕ × ℕ) (hS : SeatFits G cs m seat) (hL : ListedAt F base [d₁, d₂])
    (hO : ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (base + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ c e).ShownAll G cs m seat :=
  shownAll_at (sendPiece (W := W) (F := F) b base d₁ d₂ c e) G cs m seat hS hL hO

/-- **The two, laid into `shown_new`.** -/
theorem shown_send {Xi T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT)
    (c e : ℕ) (G : FileDescription Xi) (cs : Codes) (ms new : List Mem)
    (hn : ∀ x ∈ new, ∃ n, (x.1.seat x.2).1 = base + n ∧ n < d₁.trees.length)
    (hS : ∀ x ∈ new, SeatFits G cs x.1.l x.1.seat) (hL : ListedAt F base [d₁, d₂])
    (hO : ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (base + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W)
    (j t : ℕ) (hex : ∃ x ∈ ms, SitsAt x j t) (hin : ∀ x ∈ ms, SitsAt x j t → x ∈ new) :
    ∀ a τ x, (sendPiece (W := W) (F := F) b base d₁ d₂ c e).ior.red.out a τ = some x →
      shownJT cs G ms j t (strsOf F x.2) :=
  shown_new cs G ms new _ (sentBy_send b base d₁ d₂ c e new hn)
    (fun x hx => shownAll_send b base d₁ d₂ c e G cs x.1.l x.1.seat (hS x hx) hL hO) j t hex hin

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sentBy_send
#print axioms VerifiableInference.Desc.K1.shownAll_at
#print axioms VerifiableInference.Desc.K1.shown_send
