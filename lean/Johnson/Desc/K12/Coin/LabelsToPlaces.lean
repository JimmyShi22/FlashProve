-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LabelsToPlaces.lean: **THE SEAM AT THE NUMBERING BY LABELS: UNDER "THE BOOK IS
IN ORDER" IT IS THE SEAM AT THE NUMBERING BY PLACES.** Statements and proofs.

GameLabels.lean's game promises nothing, and concludes "one tuple for all rows" at the oracles that
`nuOf π nl t` names: the book's place z by the label of the tree that stands there. The word's seam
(FramesTie.lean, ToldAtFile.lean) stands at a numbering by the place: z ↦ lo + z: because what a
description tells of its trees is told in the order of sending. The two meet where the tree at the
place z bears the label firstTree + z: `BookOrd` (Johnson/Desc/Sound/BookInOrder.lean).
  `ntuple_congr`: "one tuple for all rows" reads a numbering at the members' places and at the
    mask's alone.
  `nuOf_at`: at a place of the data's book whose tree is there, under `BookOrd`: `nuOf π (nlAt π lo)
    t` is lo + z.
  `qn_places_of_labels`: **the game's conclusion at the labels gives the conclusion at the places**,
    where the data's book is in order.
  `seams_of_places`: so `SeatSeams` at z ↦ lo + z (GameCand.lean) and "inside the row's promise the
    data's book is in order" give `SeatSeamsV` (GameLabelsAt.lean).
SO THE INVARIANT IS SPENT IN THE SEAM, NOT IN THE GAME: the row's end by the labels
(`k12_cand_atV`) wants of the promise "the book is in order"; it does not want "the mask has
come", nor the two facts on the numbering below base.
Limits: those of GameLabels.lean. NO SOUNDNESS IS CLAIMED. First arm in its use; the two lemmas on
the numbering hold at both.

-/
import Johnson.Desc.K12.Coin.GameLabelsAt
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pin (NTuple)
open H2K.JointK (WO)
open H2K.First (Plain made_of)
open Johnson.Pack (sigOf)

/-- "One tuple for all rows" reads a numbering at the members' places and at the mask's alone. -/
theorem ntuple_congr (F : Frame) (π : P12) (no no' : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (h1 : ∀ i, no (D.mems.get i).t = no' (D.mems.get i).t)
    (h2 : no D.fresh.t = no' D.fresh.t) (h : NTuple F π no rad rd x a rest G0 Ly D) :
    NTuple F π no' rad rd x a rest G0 Ly D := by
  have e1 : ∀ i, W0 F no D.book x.2 (D.mems.get i).t = W0 F no' D.book x.2 (D.mems.get i).t := by
    intro i
    unfold W0
    rw [h1 i]
  have e2 : W0 F no D.book x.2 D.fresh.t = W0 F no' D.book x.2 D.fresh.t := by
    unfold W0
    rw [h2]
  obtain ⟨row₀, hok, hT⟩ := h
  refine ⟨row₀, hok, ?_⟩
  have key : ∀ (wM wM' : Fin D.mems.length → WO) (wF wF' : WO), wM = wM' → wF = wF' →
      H2K.Pin.TupleAt (H2K.First.good_of_ok π a row₀ D hok)
        { x.1 with st := begun x.1.st x.1.g G0, pass := .claim row₀ Ly } Ly x.1.st G0 rd
        (fun i => (wM i).1) wF.1 (fun i => (wM i).2) (rad (H2K.Pub.sgOf a)) →
      H2K.Pin.TupleAt (H2K.First.good_of_ok π a row₀ D hok)
        { x.1 with st := begun x.1.st x.1.g G0, pass := .claim row₀ Ly } Ly x.1.st G0 rd
        (fun i => (wM' i).1) wF'.1 (fun i => (wM' i).2) (rad (H2K.Pub.sgOf a)) := by
    rintro _ _ _ _ rfl rfl h'
    exact h'
  exact key (fun i => W0 F no D.book x.2 (D.mems.get i).t)
    (fun i => W0 F no' D.book x.2 (D.mems.get i).t) (W0 F no D.book x.2 D.fresh.t)
    (W0 F no' D.book x.2 D.fresh.t) (funext e1) e2 hT

/-- At a place whose tree is there, under "the book is in order". -/
theorem nuOf_at {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D)
    (hO : BookOrd π.nums.firstTree D.book) (lo z : ℕ) (T : Tree) (hT : D.book.trees[z]? = some T) :
    nuOf π (nlAt π lo) t z = lo + z := by
  rw [nuOf_of_fixes hf]
  unfold H2K.First.numAt nlAt
  rw [hT]
  show lo + (T.number - π.nums.firstTree) = lo + z
  rw [hO z T hT]
  omega

/-- **The conclusion at the labels gives the conclusion at the places.** -/
theorem qn_places_of_labels (F : Frame) (π : P12) (lo : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str)
    (hO : ∀ a rest G0 Ly D, Fixes π x.1 a rest G0 Ly D → BookOrd π.nums.firstTree D.book)
    (h : QN π (NTuple F π (nuOf π (nlAt π lo) x.1) rad rd) x) :
    QN π (NTuple F π (fun z => lo + z) rad rd) x := by
  obtain ⟨a, rest, G0, Ly, D, hf, hN⟩ := h
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  refine ⟨a, rest, G0, Ly, D, hf, ntuple_congr F π _ _ rad rd x a rest G0 Ly D (fun i => ?_) ?_ hN⟩
  · obtain ⟨_, _, _, T, hT, _⟩ := hm.mem i
    exact nuOf_at hf (hO a rest G0 Ly D hf) lo _ T hT
  · obtain ⟨_, _, T, hT, _⟩ := hm.fresh
    exact nuOf_at hf (hO a rest G0 Ly D hf) lo _ T hT

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The seams at the places, and the book in order inside the promise, give the seams at the
labels.** -/
theorem seams_of_places (enter : A → Except String T12) (F : Frame) (π : P12) (lo : ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (mine : List Mem) (on : A × F.E.Str → Prop)
    (ins outs : A × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hO : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf F a.2) → enter a.1 = .ok t →
      ∀ st rest G0 Ly D, Fixes π t st rest G0 Ly D → BookOrd π.nums.firstTree D.book)
    (h : SeatSeams cs G arr smp enter F π (fun z => lo + z) rad rd base mine on ins outs) :
    SeatSeamsV cs G arr smp enter F π (nlAt π lo) rad rd base mine on ins outs := by
  intro hS hF a ha hp hq
  obtain ⟨t, ht, q⟩ := hq
  exact h hS hF a ha hp
    ⟨t, ht, qn_places_of_labels F π lo rad rd (t, a.2) (hO a t ha hp ht) q⟩

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.ntuple_congr
#print axioms VerifiableInference.Desc.K12.Coin.nuOf_at
#print axioms VerifiableInference.Desc.K12.Coin.qn_places_of_labels
#print axioms VerifiableInference.Desc.K12.Coin.seams_of_places
