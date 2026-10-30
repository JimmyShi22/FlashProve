-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PieceFacts.lean: two of the three facts on the piece that holds the approximate
range proof's sub-protocol (our files: the smallness test's block), at any IOP as written in Lean (our
files: a description): no round is laid behind the piece, and its written rounds are the draw's one
round `rdt p` ITSELF, all six fields. Statements and proofs: counting; no new mathematics.

  `rdt_of_roundIs`: a round's data that are those of the kind's declared round (`RoundIs`,
    Johnson/Desc/Sound/Stretch.lean) are `rdt p` (Johnson/Desc/First/K8/LawView.lean): the declared
    round sends no root, opens nothing and reads no stored part, and its name's kind is "entries".
  `ds_of_along`: so a list of one.
  `k08_facts_of_fits`: at rows of pieces that hold the written IOP's sub-protocols and tile its first
    chain: at a number k, not the last, whose sub-protocol has the kind's rounds: q.back = [] and
    q.ds = [rdt p]. By `fits_piece` (Johnson/Road/K4/PieceAtFits.lean).
  `k08_facts_at_maker`: ALL THREE FACTS AT THE MAKER's OWN ROWS (`piecesAt`): where the maker's letter
    for the first row lays the cap (`AtCap`, Johnson/Desc/Sound/BoundsAtCap.lean): the piece at number
    k holds the sub-protocol, no round is laid behind it, its written rounds are [rdt p], AND ITS
    ERRORS ARE THE CAP. By `piece_at_desc` (Johnson/Road/K4/PieceAtDesc.lean).
Limits. That the sub-protocol at a number has the kind's rounds is a premise: at the proof file's 25
places it is left to a file that is not in this library. The
errors are had at the maker's rows alone, not at any rows that tile. No soundness is claimed.

-/
import Johnson.Desc.First.K8.LawView
import Johnson.Desc.First.K8.Whole
import Johnson.Road.K4.PieceAtFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription numAt)
open VerifiableInference.Desc.Sound

/-- **The declared round's data are `rdt p`.** -/
theorem rdt_of_roundIs (p : Par) (num : Fmt.TreeSource → ℕ) (d : RDT)
    (h : RoundIs num (round p) d) : d = rdt p := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨⟨e, k, i, t, o⟩, s⟩ := d
  have hk : k = Fmt.Kind.entries := (Option.some.inj h2).symm
  have ht : t = [] := List.length_eq_zero_iff.1 h6
  have ho : o = [] := h5
  have hs : s = [] := h4
  have he : e = (round p).entry := h1
  have hi : i = (round p).items := h3
  subst hk ht ho hs he hi
  rfl

/-- A list of one. -/
theorem ds_of_along (p : Par) (num : Fmt.TreeSource → ℕ) (ds : List RDT) (hl : ds.length = 1)
    (hA : Along (RoundIs num) [round p] ds) : ds = [rdt p] := by
  match ds, hl, hA with
  | [d], _, hA => rw [rdt_of_roundIs p num d hA.1]

/-- **Two facts on the piece, at any written IOP.** -/
theorem k08_facts_of_fits {Xi : Type} {C : CK} {W : Type} (G : FileDescription Xi) (file : String)
    (D : WholeD) (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type}
    (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁)
    (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : Par) (hr : b.rounds = [round p]) :
    q.back = [] ∧ q.ds = [rdt p] := by
  obtain ⟨_, hb, hl, hA⟩ := OnBytes.Road.K4.fits_piece G file D hD R hO ht hd hq hk hk1
  rw [hr] at hl hA
  exact ⟨hb, ds_of_along p _ q.ds hl hA⟩

/-- **The three facts at the maker's own rows.** -/
theorem k08_facts_at_maker {Xi : Type} {C : CK} {W : Type} (G : FileDescription Xi) (file : String)
    (D : WholeD) (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃ (d wEnd : W)
    (hc : AtCap rest₁) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : Par) (hr : b.rounds = [round p]) :
    ∃ q, ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? = some q ∧
      q.b = held b ∧ q.back = [] ∧ q.ds = [rdt p] ∧ q.err = Iop.Err.cap 128 (uLT C q.ds) := by
  obtain ⟨base, ds, hq, hl, hA⟩ := OnBytes.Road.K4.piece_at_desc G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃
    h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd k b hk hk1
  rw [hr] at hl hA
  exact ⟨_, hq, rfl, rfl, ds_of_along p _ ds hl hA, hc k ds⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_facts_at_maker
#print axioms VerifiableInference.Desc.First.K8.rdt_of_roundIs
#print axioms VerifiableInference.Desc.First.K8.ds_of_along
#print axioms VerifiableInference.Desc.First.K8.k08_facts_of_fits
