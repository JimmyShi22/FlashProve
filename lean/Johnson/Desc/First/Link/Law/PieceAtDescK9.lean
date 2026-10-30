-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PieceAtDescK9.lean: THE MAKER's PIECE AT THE NUMBER OF A SUB-PROTOCOL
THAT DECLARES THE BATCHING's ONE ROUND, WRITTEN OUT, AT EVERY IOP AS WRITTEN IN LEAN WHOSE DATA
RETURN (in the Lean names a «block» is a sub-protocol and a «description» the IOP as written in
Lean). So two debts of the link's law on its first piece (`OwesPieces`, LinkOwes.lean: hds: the
piece's one round; hbk: nothing is put back) have their payer at the maker's own piece. After the
pattern of Johnson/Desc/First/Close/Law/PieceAtDescK10.lean.

What is said.
  `k9_of_is`: data that are the declared round «BAT-sigma»'s are `k9Round p`. `ds_of_along9`: so the
    data of a sub-protocol that declares that one round are `[k9Round p]`. `k9_piece_at_desc`:
    **under `piece_at_desc`'s own premises and b.rounds = [{ entry := K9.entry p }]:
    there is a number base with: the first list's piece number k IS `pieceOf (held b) base [k9Round
    p] [] (rest₁ k [k9Round p])`.** `hds_hbk_of`: **hds and hbk at a piece of that form, and at the
    piece over the verifier's state that is cut from it (`atRec`).**

Limits. Which sub-protocol stands at which number of the first chain is a premise; so are: the data
return; the first chain's last sub-protocol has a round; each of the three flat lists has a first
member; k is not the last number. rest₁ (the piece's error) is a letter: hcap («its error is the cap
at 128») is the caller's choice of it: not here. base stands under «there is». Nothing on soundness.

-/
import Johnson.Road.K4.PieceAtDesc
import Johnson.Desc.First.Batch.Law.AtCap
import Johnson.Desc.First.Link.Law.LinkTiedPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9L (k9Round)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Run.PQ (CK)

/-- Data that are the declared round's are k9Round p. -/
theorem k9_of_is (num : Fmt.TreeSource → ℕ) (p : K9.Where) (d : RDT)
    (h : RoundIs num { entry := K9.entry p } d) : d = k9Round p := by
  rcases d with ⟨⟨en, kd, it, tr, op⟩, st⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  have hk : Fmt.kindOf (K9.entry p).name = some .elems := by
    show Fmt.kindOf "BAT-sigma" = some .elems
    decide
  rw [hk] at h2
  obtain rfl := Option.some.inj h2
  obtain rfl : tr = [] := List.length_eq_zero_iff.1 h6
  subst h1 h3 h4 h5
  simp [k9Round, Fmt.DeclaredRound.items, Fmt.Entry.cut, K9.entry]

/-- The data of a sub-protocol that declares that one round. -/
theorem ds_of_along9 (num : Fmt.TreeSource → ℕ) (p : K9.Where) (ds : List RDT)
    (h : Along (RoundIs num) [{ entry := K9.entry p }] ds) (hl : ds.length = 1) :
    ds = [k9Round p] := by
  match ds, h, hl with
  | [d], h, _ => rw [k9_of_is num p d h.1]

/-- **THE MAKER's PIECE AT THE BATCHING's NUMBER, WRITTEN OUT.** -/
theorem k9_piece_at_desc {Xi W : Type} {C : CK} (G : FileDescription Xi) (file : String)
    (D : WholeD) (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃
    (d wEnd : W) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : K9.Where)
    (hr : b.rounds = [{ entry := K9.entry p }]) :
    ∃ base : ℕ,
      ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? =
          some (pieceOf (held b) base [k9Round p] [] (rest₁ k [k9Round p])) := by
  obtain ⟨base, ds, e1, e2, e3⟩ := OnBytes.Road.K4.piece_at_desc G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃
    h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd k b hk hk1
  rw [hr] at e3
  obtain rfl := ds_of_along9 _ p ds e3 (by rw [e2, hr]; rfl)
  exact ⟨base, e1⟩

/-- **hds AND hbk** at a piece of that form, and at the piece over the verifier's state that is cut
from it. -/
theorem hds_hbk_of {P Cl W : Type} {C : CK} {F : Frame} (b : Block (P × S) Cl) (base : ℕ)
    (p : K9.Where) (x : Rest C F (P × S) W [k9Round p]) (b₀ : Block S Cl) :
    (pieceOf b base [k9Round p] [] x).ds = [k9Round p] ∧
      (pieceOf b base [k9Round p] [] x).back = [] ∧
      (atRec (pieceOf b base [k9Round p] [] x) b₀).ds = [k9Round p] ∧
      (atRec (pieceOf b base [k9Round p] [] x) b₀).back = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k9_of_is
#print axioms VerifiableInference.Desc.LinkJoin.ds_of_along9
#print axioms VerifiableInference.Desc.LinkJoin.k9_piece_at_desc
#print axioms VerifiableInference.Desc.LinkJoin.hds_hbk_of
