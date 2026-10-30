-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceBase.lean: THE PIECE's BASE IS THE TABLE's OWN NUMBER AT THE PLACE: at rows
that hold a description's blocks and tile its first chain from 0, the first tree's number of the
piece at number k is `N.treesAt` at the k-th place, for every table of numbers N that passes the
table's test `bookFit` against what the description's blocks tell. Then at K4's twelve numbers.
Four theorems.
Why. K04_law's statement speaks of a piece q of the rows T and of the table's numbers N; the table
reads its numbers at the piece's base, AND NOTHING TIED THE TWO. The two count one thing: the
trees that the data in front send = the roots that the blocks in front declare = the oracles that
they tell. That chain lies: `along_first` and `along_of_tiled`
(Johnson/Road/K4/PieceAtFits.lean) give, at EVERY piece of the row, that its stretch is its
block's declared rounds' data; `row_more` (Johnson/Desc/Sound/PieceMore.lean) sums them;
`base_treesAt` (Johnson/Desc/Sound/PieceFence.lean) carries the sum to `treesTold` and, by
`bookFit_at`, to `N.treesAt`. HERE THEY ARE JOINED; nothing new is counted.
  `base_at_rows`: general in the description and the number k (not the row's last).
  `k04_more`: in the goals' scope, at an opening of the proof file's description, number 28 g + 4
  is not the first chain's last (K8's block stands at 28 g + 6).
  `k04_base_at_makers`: **at K4's twelve numbers**: N.treesAt (some (k4PlaceAt g)) = q.base.
  `k04_cap_at_cut`: the cap at K4's twelve numbers, at the maker's cut: `cap_at_cut`.
Limits. h0 (the first piece's base is 0), ht, hd are lines on the rows: at the maker's own rows
`rows_of_cut` (Johnson/Road/K4/PieceMakers.lean) pays them, AT THE LIST OF ALL TREES `allOf D`
ALONE: these statements stand at a general list, which is wider than their payer: at another list
nobody pays the three. `k04_more` and `k04_base_at_makers`: IN THE GOALS' SCOPE, AT THE FORMAT's
SECOND HASH FUNCTION `OnBytes.secondHashFunction`, at an opening of the proof file's description. hok and hbook
are Bools on the plan and the table: asked, not shown. WHAT THE BLOCKS TELL is `toldOf`
(PieceFence.lean): bs.map fun b => b.oracles.flatMap id. That the table's list of places and the
chain's flat list run in step is used at the twelve numbers alone (`atK4_full`). Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.K04Tied
import Johnson.Road.K4.PieceMakers
import Johnson.Desc.Sound.PieceSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Flat OnBytes.Maker
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription Place numAt blocksOk)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf bookFit)
open VerifiableInference.Desc.Sound

/-- **The piece's base is the table's own number at the place**, at any number but the last. -/
theorem base_at_rows {Xi W : Type} {C : CK} (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
    (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁)
    (h0 : R.p₁.base = 0) (N : Numbers) (ps : List Place) (hok : blocksOk G.first.blocksInOrder = true)
    (hbook : bookFit N ps (toldOf G.first.blocksInOrder) = true) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk1 : k + 1 < G.first.blocksInOrder.length)
    (hkp : k ≤ ps.length) : N.treesAt ps[k]? = q.base := by
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  have hkl : k < R.l₁.length := by
    rw [List.length_cons] at hlen
    omega
  have hfl : (R.p₁ :: R.l₁).flatMap (·.b.rounds) = G.first.blocksInOrder.flatMap (·.rounds) := by
    have e1 : (R.p₁ :: R.l₁).flatMap (·.b.rounds) =
        ((R.p₁ :: R.l₁).map (·.b)).flatMap (·.rounds) := by
      rw [List.flatMap_map]
    rw [e1, hO.b₁]
    refine flat_of_map _ _ ?_
    rw [List.map_map, List.map_map]
    rfl
  have hA := along_of_tiled (RoundIs (numAt D.t₁ D.t₂ 0)) R.l₁ R.p₁ D.ds₁ ht hd
    (by rw [hfl]; exact along_first G file D hD)
  have hM := row_more (numAt D.t₁ D.t₂ 0) R.p₁ R.l₁ ht hA k q hq (Or.inl hkl)
  have hb : (R.p₁ :: R.l₁).map (·.b) = G.first.blocksInOrder.map held := by
    rw [hO.b₁, List.map_map]
    rfl
  rw [hb, h0] at hM
  exact (base_treesAt hM (by rw [blocksOk_held]; exact hok) N ps
    (by rw [toldOf_held]; exact hbook) hkp).symm

section AtK4
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Number 28 g + 4 is not the first chain's last: K8's block stands at 28 g + 6. -/
theorem k04_more (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) :
    28 * g + 4 + 1 < c.blocksInOrder.length := by
  obtain ⟨Lk', b8, _, _, f1, f2, _⟩ := IM.k8_of_layers hS hR O g hg
  have hi8 : IM.flatIx c (2 * g) 4 = 28 * g + 6 := by
    rw [IM.flatIx_scope hS hR O (by omega) 4]
    omega
  have hf8 : c.blocksInOrder[28 * g + 6]? = some b8 := by
    rw [← hi8]
    exact IM.hear_at_flat f1 f2
  have hl : 28 * g + 6 < c.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hf8).1
  omega

/-- **At K4's twelve numbers the table's number at K4's place is the piece's base.** -/
theorem k04_base_at_makers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W} (hT : OfDesc _ T) (file : String)
    (hD : (descAt Z A B c).data file = .ok D) (ht : Tiled T.p₁ T.l₁)
    (hd : rowData T.p₁ T.l₁ = D.ds₁) (h0 : T.p₁.base = 0) (N : Numbers)
    (hok : blocksOk c.blocksInOrder = true)
    (hbook : bookFit N (flatPlacesOf linksFull true)
      (c.blocksInOrder.map fun b => b.oracles.flatMap id) = true) (g : ℕ) (hg : g < 12)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) ProofFile.Cl W}
    (hq : (T.p₁ :: T.l₁)[28 * g + 4]? = some q) : N.treesAt (some (k4PlaceAt g)) = q.base := by
  have hp : (flatPlacesOf linksFull true)[28 * g + 4]? = some (k4PlaceAt g) := (atK4_full g hg).1
  have hkp : 28 * g + 4 ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1
  have h := base_at_rows (descAt Z A B c) file D hD T hT ht hd h0 N (flatPlacesOf linksFull true)
    hok hbook hq (k04_more hS hR O g hg) hkp
  rw [hp] at h
  exact h

/-- **The cap at K4's twelve numbers, at the maker's cut.** -/
theorem k04_cap_at_cut {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all (descAt Z A B c) X₁ X₂ W}
    {b₁ : Block (ProofFile.InstPub × S) ProofFile.Cl} {l₁ : List (Block (ProofFile.InstPub × S) ProofFile.Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) W ds} {r : Fmt.RoundView}
    (hc₁ : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 D.ds₁ b₁ l₁) (hcap : AtCap rest₁) (g : ℕ)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) ProofFile.Cl W}
    (hq : (T.p₁ :: T.l₁)[28 * g + 4]? = some q) :
    q.err = Iop.Err.cap 128 (uLT (ckP .two) q.ds) :=
  cap_at_cut hc₁ hcap hq

end AtK4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.base_at_rows
#print axioms OnBytes.Road.K4.k04_more
#print axioms OnBytes.Road.K4.k04_base_at_makers
#print axioms OnBytes.Road.K4.k04_cap_at_cut
