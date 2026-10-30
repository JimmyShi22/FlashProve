-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceAtFits.lean: THREE FACTS ON A PIECE THAT A KIND's LAW ASKS (its block, no round
behind, its stretch), AT ANY THREE ROWS OF PIECES THAT HOLD A DESCRIPTION's BLOCKS AND TILE ITS
FIRST CHAIN: not at the maker's own cut alone (Johnson/Road/K4/PieceAtDesc.lean). WITHOUT THE KIND:
for a description G whose data are made (`G.data file = .ok D`), rows T with `OfDesc G T`
(Johnson/Desc/Sound/DescThree.lean), `Tiled T.p₁ T.l₁` and `rowData T.p₁ T.l₁ = D.ds₁` (two fields
of `Three.Fits`, Johnson/Desc/Sound/FileRule.lean): whatever piece q stands at a number k of the
first row that is not the last. Book-keeping on lists; theorems put together; no round is
evaluated.

  `tiled_back`: in a tiled row all but the last have no round behind.
  `tiled_base`: piece number k's first tree has the first piece's number plus the trees of the
    pieces in front.
  `along_of_tiled`: what holds along a chain's declared rounds and data holds along every piece of a
    row that tiles it (`cutAlong`, Johnson/Desc/Sound/Stretch.lean, without the maker).
  `along_first`: at every description: `RoundIs` holds along the first chain (the first third of
    `stretchOfOk`, at `FileDescription.data`).
  `fits_piece`: q holds `held b`, b the chain's block number k; q.back = []; q's stretch has as many
    rounds as b declares; `RoundIs` holds along it.
  `k04_piece`: where b declares K4's rounds at par (`Declares`): k4Ds par = some q.ds. (As a list:
    `k04_piece_later`, Johnson/Road/K4/PieceLater.lean; in the first group `k4Ds_first`,
    Johnson/Road/K4/DsTailR.lean, writes it out.)

Limits. OF q.err AND q.ext NOTHING IS SAID: at rows that are not the maker's they are tied to
nothing; at the maker's they are the letter rest's: the errors: `cutRow_err`
(Johnson/Road/K4/PieceAtCut.lean), under `AtCap`. That a seat's tree lies below q.base is a test on
the plan: `tiled_base` gives the number alone. That k is not the last number is a premise. Nothing
on soundness.
-/
import Johnson.Road.K4.PieceAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Desc.First.K4 (Par k4Ds)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription numAt)
open VerifiableInference.Desc.Sound

variable {T Cl W : Type} {C : CK} {F : Frame}

/-- In a tiled row all but the last have no round behind. -/
theorem tiled_back : ∀ (l : List (Piece C F T Cl W)) (p : Piece C F T Cl W), Tiled p l →
    ∀ (k : ℕ) (q : Piece C F T Cl W), k < l.length → (p :: l)[k]? = some q → q.back = []
  | [], _, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | p' :: l, p, h, 0, q, _, hq => by
    rw [List.getElem?_cons_zero] at hq
    obtain rfl := Option.some.inj hq
    exact h.2.2.1
  | p' :: l, p, h, k + 1, q, hk, hq => by
    rw [List.getElem?_cons_succ] at hq
    exact tiled_back l p' h.2.2.2.2 k q (Nat.lt_of_succ_lt_succ hk) hq

/-- The first tree of piece number k. -/
theorem tiled_base : ∀ (l : List (Piece C F T Cl W)) (p : Piece C F T Cl W), Tiled p l →
    ∀ (k : ℕ) (q : Piece C F T Cl W), (p :: l)[k]? = some q →
      q.base = p.base + (((p :: l).take k).map (·.trees)).sum
  | _, p, _, 0, q, hq => by
    rw [List.getElem?_cons_zero] at hq
    obtain rfl := Option.some.inj hq
    simp
  | [], p, _, k + 1, q, hq => by
    rw [List.getElem?_cons_succ] at hq
    cases hq
  | p' :: l, p, h, k + 1, q, hq => by
    rw [List.getElem?_cons_succ] at hq
    rw [tiled_base l p' h.2.2.2.2 k q hq, h.2.2.2.1, List.take_succ_cons, List.map_cons,
      List.sum_cons, Nat.add_assoc]

/-- **What holds along a chain holds along every piece of a row that tiles it.** -/
theorem along_of_tiled (P : Fmt.DeclaredRound → RDT → Prop) :
    ∀ (l : List (Piece C F T Cl W)) (p : Piece C F T Cl W) (ds : List RDT), Tiled p l →
      rowData p l = ds → Along P ((p :: l).flatMap (·.b.rounds)) ds →
      ∀ q ∈ p :: l, Along P q.b.rounds q.ds
  | [], p, ds, _, hd, hA, q, hq => by
    obtain rfl : q = p := by simpa using hq
    have e : q.ds = ds := by
      rw [← hd]
      simp [rowData]
    rw [e]
    simpa using hA
  | p' :: l, p, ds, h, hd, hA, q, hq => by
    have e : ds = p.ds ++ rowData p' l := by
      rw [← hd]
      simp [rowData]
    have len : p.ds.length = p.b.rounds.length := by
      have h6 := h.1.1
      rw [h.2.2.1] at h6
      simpa using h6
    have sp := along_split P p.b.rounds ((p' :: l).flatMap (·.b.rounds)) ds
      (by rwa [List.flatMap_cons] at hA)
    rw [e, List.take_left' len, List.drop_left' len] at sp
    rcases List.mem_cons.1 hq with rfl | hq
    · exact sp.1
    · exact along_of_tiled P l p' _ h.2.2.2.2 rfl sp.2 q hq

variable {Xi : Type}

/-- **At every description `RoundIs` holds along the first chain.** -/
theorem along_first (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D) :
    Along (RoundIs (numAt D.t₁ D.t₂ 0)) (G.first.blocksInOrder.flatMap (·.rounds)) D.ds₁ := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok G file D hD
  obtain ⟨w₁, w₂, w₃⟩ := written_as file G.roundsDeclaredByBlocks _ hR
  exact (stretchOfOk _ R₁ R₂ R₃ _ _ _ _ (Or.inr ⟨_, _, rfl⟩) w₁ w₂ w₃ hok).1

/-- **The facts on the piece at a number that is not the last**, at any rows that hold the
description's blocks and tile its first chain. -/
theorem fits_piece (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) :
    q.b = held b ∧ q.back = [] ∧ q.ds.length = b.rounds.length ∧
      Along (RoundIs (numAt D.t₁ D.t₂ 0)) b.rounds q.ds := by
  have hqb : q.b = held b := by
    have e := congrArg (·[k]?) hO.b₁
    simp only [List.getElem?_map, hq, hk, Option.map_some] at e
    exact Option.some.inj e
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  have hkl : k < R.l₁.length := by
    rw [List.length_cons] at hlen
    omega
  have hb := tiled_back R.l₁ R.p₁ ht k q hkl hq
  have hm : q ∈ R.p₁ :: R.l₁ := List.mem_of_getElem? hq
  have hfl : (R.p₁ :: R.l₁).flatMap (·.b.rounds) = G.first.blocksInOrder.flatMap (·.rounds) := by
    have e1 : (R.p₁ :: R.l₁).flatMap (·.b.rounds) =
        ((R.p₁ :: R.l₁).map (·.b)).flatMap (·.rounds) := by
      rw [List.flatMap_map]
    rw [e1, hO.b₁]
    refine flat_of_map _ _ ?_
    rw [List.map_map, List.map_map]
    rfl
  have hA := along_of_tiled (RoundIs (numAt D.t₁ D.t₂ 0)) R.l₁ R.p₁ D.ds₁ ht hd
    (by rw [hfl]; exact along_first G file D hD) q hm
  have hOw := (tiled_owed R.l₁ R.p₁ ht q hm).1
  rw [hb, hqb] at hOw
  rw [hqb] at hA
  exact ⟨hqb, hb, by simpa using hOw, hA⟩

/-- **K4's piece**: at a block that declares K4's rounds. -/
theorem k04_piece (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) {par : Par} (hdc : Declares b par) :
    q.b = held b ∧ q.back = [] ∧ k4Ds par = some q.ds := by
  obtain ⟨hqb, hb, hl, hA⟩ := fits_piece G file D hD R hO ht hd hq hk hk1
  have hK : k4Ds par = some q.ds :=
    k4Ds_of_along q (by rw [hqb]; exact hdc) (by rw [hqb]; exact hl) (by rw [hqb]; exact hA)
  exact ⟨hqb, hb, hK⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tiled_back
#print axioms OnBytes.Road.K4.tiled_base
#print axioms OnBytes.Road.K4.along_of_tiled
#print axioms OnBytes.Road.K4.along_first
#print axioms OnBytes.Road.K4.fits_piece
#print axioms OnBytes.Road.K4.k04_piece
