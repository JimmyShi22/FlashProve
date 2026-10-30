-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PieceFacts.lean: the kind «the code switch»: THE FACTS ON A PIECE THAT THE
KIND's LAW ASKS OF THE WRITTEN ROUNDS, at any three rows of pieces that hold a description's
blocks and tile its first chain. NO BLOCK IMPORTS THIS FILE. Why. The law of the code switch takes
two written rounds d₁ d₂ under two premises: their entries are the block's own (K2.rounds p), and
each has the kind of its name. The rule for a file cuts the file's written rounds into stretches
and shows of each that it goes along its block's declared rounds (Along (RoundIs num),
Johnson/Desc/Sound/Stretch.lean). Here the one is carried to the other.
  entries_along   where written rounds go along declared rounds, one for one: their entries are
                  the declared rounds' entries, and each has the kind that its name has. (General
                  in the declared rounds. For rounds that are bare entries the like stands in
                  Johnson/Top/H0/MergeLaw/PieceFacts.lean: entries_of_along; the switch's second
                  round names the trees that it opens, so it is no bare entry.)
  k2_stretch      at any block that declares the switch's rounds at p: the stretch is [d₁, d₂]
                  with the two premises
  k2_piece        so at the piece at a number k, not the last, of the first row: it holds «held
                  b»; no round behind; its written rounds are [d₁, d₂] with the two premises. By
                  fits_piece (Johnson/Road/K4/PieceAtFits.lean).
LIMITS. Of the piece's errors and its base nothing is said. That k is not the last number is a
premise. No soundness is claimed.
-/
import Johnson.Road.K4.PieceAtFits
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

theorem entries_along {num : Fmt.TreeSource → ℕ} : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    ds.length = rs.length → Along (RoundIs num) rs ds →
    ds.map (·.entry) = rs.map (·.entry) ∧ ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind
  | [], [], _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl
  | r :: rs, d :: ds, hl, h => by
    have h' : RoundIs num r d ∧ Along (RoundIs num) rs ds := h
    obtain ⟨k1, k2⟩ := entries_along rs ds (Nat.succ.inj hl) h'.2
    have e1 : d.entry = r.entry := h'.1.1
    have e2 : Fmt.kindOf r.entry.name = some d.kind := h'.1.2.1
    refine ⟨by rw [List.map_cons, List.map_cons, e1, k1], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [e1]
      exact e2
    · exact k2 x hx

theorem k2_stretch {T Cl : Type} {num : Fmt.TreeSource → ℕ} (p : P2) (b : Block T Cl)
    (hb : b.rounds = rounds p) (ds : List RDT) (hl : ds.length = b.rounds.length)
    (h : Along (RoundIs num) b.rounds ds) :
    ∃ d₁ d₂, ds = [d₁, d₂] ∧ [d₁, d₂].map (·.entry) = (rounds p).map (·.entry) ∧
      ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind := by
  rw [hb] at hl h
  obtain ⟨k1, k2⟩ := entries_along _ ds hl h
  match ds, hl, k1, k2 with
  | [d₁, d₂], _, k1, k2 => exact ⟨d₁, d₂, rfl, k1, k2⟩

theorem k2_piece {Xi W : Type} {C : CK} (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
    (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : P2) (hb : b.rounds = rounds p) :
    q.b = held b ∧ q.back = [] ∧ ∃ d₁ d₂, q.ds = [d₁, d₂] ∧
      [d₁, d₂].map (·.entry) = (rounds p).map (·.entry) ∧
      ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind := by
  obtain ⟨h1, h2, hl, hA⟩ := OnBytes.Road.K4.fits_piece G file D hD R hO ht hd hq hk hk1
  exact ⟨h1, h2, k2_stretch p b hb q.ds hl hA⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.entries_along
#print axioms VerifiableInference.Desc.First.K2.k2_stretch
#print axioms VerifiableInference.Desc.First.K2.k2_piece
