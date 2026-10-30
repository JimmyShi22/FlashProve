-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceAtDesc.lean: THE PIECE NUMBER k OF A DESCRIPTION's FIRST ROW, WRITTEN OUT; AND
AT A BLOCK THAT DECLARES K4's ROUNDS ITS STRETCH IS K4's WRITTEN ROUNDS. At every description F
whose data are made (`F.data file = .ok D`) and whose first chain's last block has a round
(`F.sealLast`), at the pieces that the maker cuts (`piecesAt`, Johnson/Desc/Sound/PaidAtDesc.lean).
Book-keeping on lists: theorems put together (`cutBlocks`, `paidAtDesc`, `stretchOfData`); no
round is evaluated.

  `cutRow_at`: the maker's piece number k is `pieceOf` of the row's block number k at `rest`'s value
    at the number i + k; it has no round behind where a block number k + 1 stands.
  `tiled_owed`: every piece of a tiled row is owed just its stretch.
  `piece_at_desc`: where block number k of F's first chain is b and a block number k + 1 stands: the
    first row's piece number k is `pieceOf (held b) base ds [] (rest₁ k ds)` for a number base and a
    stretch ds that has as many rounds as b declares, along which `RoundIs` holds.
  `k4_piece_at_desc`: where b declares K4's rounds at par (`Declares`): k4Ds par = some ds.
    (In a group that is not the first: `k4_piece_later`, Johnson/Road/K4/PieceLater.lean.)

Limits. Which block stands at which number of a description's first chain is a premise; so is that
each of the three chains' flat lists has a first block (h₁, h₂, h₃). rest₁ is a letter. base is not
said in closed form (`tiled_base`, Johnson/Road/K4/PieceAtFits.lean, has it as a sum). Nothing on
soundness.
-/
import Johnson.Road.K4.PieceAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Desc.First.K4 (Par k4Ds)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription numAt)
open VerifiableInference.Desc.Sound

variable {T Cl W : Type} {C : CK} {F : Frame}

/-- **The maker's piece number k.** -/
theorem cutRow_at (rest : (i : ℕ) → (ds : List RDT) → Rest C F T W ds) (putBack : List Fmt.RoundView) :
    ∀ (l : List (Block T Cl)) (b : Block T Cl) (i base : ℕ) (ds : List RDT) (k : ℕ)
      (p : Piece C F T Cl W),
      ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[k]? =
        some p →
      ∃ b', (b :: l)[k]? = some b' ∧ ∃ (base' : ℕ) (ds' : List RDT) (back' : List Fmt.RoundView),
        p = pieceOf b' base' ds' back' (rest (i + k) ds') ∧ (k < l.length → back' = [])
  | [], b, i, base, ds, 0, p, hp => by
    rw [cutRow_nil, List.getElem?_cons_zero] at hp
    exact ⟨b, rfl, base, ds, putBack, (Option.some.inj hp).symm,
      fun h => absurd h (Nat.lt_irrefl 0)⟩
  | [], b, i, base, ds, k + 1, p, hp => by
    rw [cutRow_nil, List.getElem?_cons_succ] at hp
    cases hp
  | b' :: l, b, i, base, ds, 0, p, hp => by
    rw [cutRow_cons, List.getElem?_cons_zero] at hp
    exact ⟨b, rfl, base, _, [], (Option.some.inj hp).symm, fun _ => rfl⟩
  | b' :: l, b, i, base, ds, k + 1, p, hp => by
    rw [cutRow_cons, List.getElem?_cons_succ] at hp
    obtain ⟨c, hc, base', ds', back', e, hb⟩ := cutRow_at rest putBack l b' (i + 1) _ _ k p hp
    refine ⟨c, by rw [List.getElem?_cons_succ]; exact hc, base', ds', back', ?_,
      fun h => hb (Nat.lt_of_succ_lt_succ h)⟩
    rw [e, Nat.add_right_comm, Nat.add_assoc]

/-- Every piece of a tiled row is owed just its stretch. -/
theorem tiled_owed : ∀ (l : List (Piece C F T Cl W)) (p : Piece C F T Cl W), Tiled p l →
    ∀ q ∈ p :: l, q.Owed
  | [], p, h, q, hq => by
    obtain rfl : q = p := by simpa using hq
    exact h.1
  | p' :: l, p, h, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact tiled_owed l p' h.2.2.2.2 q hq

variable {Xi : Type}

/-- **The first row's piece number k at a description** whose data are made and whose first chain's
last block has a round, where block number k is b and a block number k + 1 stands. -/
theorem piece_at_desc (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl) (l₁ : List (Block G.S₁ G.Cl))
    (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl)) (b₃ : Block G.S₃ G.Cl)
    (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁) (h₂ : G.shared.blocksInOrder = b₂ :: l₂)
    (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃ (d wEnd : W) (k : ℕ) (b : Block G.S₁ G.Cl)
    (hk : G.first.blocksInOrder[k]? = some b) (hk1 : k + 1 < G.first.blocksInOrder.length) :
    ∃ (base : ℕ) (ds : List RDT),
      ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? =
          some (pieceOf (held b) base ds [] (rest₁ k ds)) ∧
      ds.length = b.rounds.length ∧ Along (RoundIs (numAt D.t₁ D.t₂ 0)) b.rounds ds := by
  obtain ⟨hO, hF, -⟩ := paidAtDesc Xi W G file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂
    rest₃ d wEnd
  have hA := (stretchOfData Xi G file D hD C _ _ _ _ _ _ _ _
    (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd) (held b₁) (l₁.map held) (held b₂)
    (l₂.map held) (held b₃) (l₃.map held) rest₁ rest₂ rest₃ sealRound
    (by rw [h₁]; exact held_map_rounds (b₁ :: l₁)) (by rw [h₂]; exact held_map_rounds (b₂ :: l₂))
    (by rw [h₃]; exact held_map_rounds (b₃ :: l₃)) ⟨rfl, rfl, rfl⟩).1
  have hB := cutBlocks C _ _ _ W rest₁ [sealRound] (l₁.map held) (held b₁) 0 0 D.ds₁
  generalize hrow : ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
    (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁) = row at hA ⊢
  have hrow' : (cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).1 ::
      (cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).2 = row := hrow
  rw [hrow'] at hB
  have hlen : row.length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hB
    simp only [List.length_map, List.length_cons] at h5
    rw [h₁, List.length_cons]
    exact h5
  have hkl : k < row.length := by
    rw [hlen]
    exact Nat.lt_of_succ_lt hk1
  obtain ⟨p, hp⟩ : ∃ p, row[k]? = some p := ⟨row[k], List.getElem?_eq_getElem hkl⟩
  have hp' : ((cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).1 ::
      (cutRow rest₁ [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held)).2)[k]? = some p := by
    rw [hrow']
    exact hp
  obtain ⟨c, hc, base, ds, back, e, hb⟩ := cutRow_at rest₁ [sealRound] (l₁.map held) (held b₁) 0 0
    D.ds₁ k p hp'
  have hc' : c = held b := by
    have e1 : (held b₁ :: l₁.map held : List (Block (G.XiPub × G.S₁) G.Cl)) =
        (b₁ :: l₁).map held := rfl
    rw [e1, ← h₁, List.getElem?_map, hk] at hc
    exact (Option.some.inj hc).symm
  have hb0 : back = [] := hb (by
    have : k + 1 < (b₁ :: l₁).length := by rw [← h₁]; exact hk1
    simpa using this)
  subst hc' hb0
  rw [Nat.zero_add] at e
  have hm : p ∈ row := List.mem_of_getElem? hp
  have hOw : p.Owed := by
    have ht : Tiled (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁ := hF.tiled₁
    exact tiled_owed _ _ ht _ (by rw [hrow]; exact hm)
  have hAl := hA _ hm
  subst e
  refine ⟨base, ds, hp, ?_, hAl⟩
  have h6 := hOw.1
  simpa [pieceOf] using h6

/-- **At a block that declares K4's rounds the stretch is K4's written rounds.** -/
theorem k4_piece_at_desc (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃
    (d wEnd : W) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) {par : Par} (hd : Declares b par) :
    ∃ (base : ℕ) (ds : List RDT),
      ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? =
          some (pieceOf (held b) base ds [] (rest₁ k ds)) ∧ k4Ds par = some ds := by
  obtain ⟨base, ds, e, hl, hA⟩ := piece_at_desc (C := C) G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃
    rest₁ rest₂ rest₃ d wEnd k b hk hk1
  exact ⟨base, ds, e, k4Ds_of_along (pieceOf (held b) base ds [] (rest₁ k ds)) hd hl hA⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cutRow_at
#print axioms OnBytes.Road.K4.tiled_owed
#print axioms OnBytes.Road.K4.piece_at_desc
#print axioms OnBytes.Road.K4.k4_piece_at_desc
