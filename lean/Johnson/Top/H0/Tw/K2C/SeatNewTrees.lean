-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SeatNewTrees.lean: code switching: AT seatN := seatNew N m r EACH NEW MEMBER's
TREE IS ONE THAT THE FIRST WRITTEN ROUND OF THE CODE SWITCH's STRETCH SENDS: the premise hseat of
the law at a place (k02_place | k02_place2, K2Caller/PlaceLaw.lean | PlaceLaw2.lean) and the premise
hsent of hshN_of (Johnson/P1K2R/TieTwoPays.lean: for the second tie's hshN). Theorems
with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hseat_seatNew   hseat at seat := seatNew N m r, at a letter base with base = N.treesAt pIn:
                  seatNew_is_layout (Tw/K2C/SentByPlace.lean), then hseat_of_lay
                  (Johnson/Desc/Book/SeatOfLay.lean): seatNew IS its seatOfLay (N.treesAt pIn) lay₀
  hsent_of_hseat  hsent follows from hseat, where the stretch's written rounds begin with d₁ (typed
                  after a text of this project)
  hsent_seatNew   hsent at seatN := seatNew N m r, at q.base := base and q.ds := d₁ :: ds: the
                  caller rewrites by q.ds = d₁ :: ds. At seatNew it makes the test sentInB
                  (Johnson/P1K2R/TieTwoPays.lean) needless
FROM: sentPlaceB N (m + 1) pIn codes sent (Tw/K2C/SentByPlace.lean) · hlay · hl (both closed; hl
follows from the test on the members: ThreeTogether.lean's len_of_tests) · hb : base = N.treesAt pIn
· hd : d₁.trees.length = lay₀.shapes.size.
WHO CAN PAY THE LAST TWO. hb, «tb = base», at base := the sub-protocol's piece's q.base and
pIn := ps[k]?: base_treesAt (Johnson/Desc/Sound/PieceFence.lean: from PieceMore num
0 bs k q · blocksOk · bookFit · k ≤ ps.length): closed, no state. hd: k2_piece_trees with
numsAt_roots (Tw/K2C/PieceTrees.lean, as hseat_at_place (not in this library) calls them): it
wants also p.roots = n.roots · q.ds = [d₁, d₂] · codes | sent := P1K2.numsAt's n.codes | n.sent, and
takes q under ThreeAt · OfDesc · Tiled · (R.p₁ :: R.l₁)[k]? = some q. THAT ONE q MEETS BOTH PAYERS'
PREMISES IS SAID BY NOTHING NAMED HERE. Neither file is imported here. SeatOfLay.lean is.
hsent's sentence has the name
Sound.SentBy (Johnson/Desc/Sound/WordsLaw.lean: spenders, no payer seen there).
LIMITS. The test's value, hb and hd are premises. No soundness is claimed. On hiding nothing.

-/
import Johnson.Top.H0.Tw.K2C.SentByPlace
import Johnson.Desc.Book.SeatOfLay
import Johnson.G.TestsFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.First (Numbers)

variable {N : Numbers} {m : ℕ} {pIn : Option VerifiableInference.Desc.Place} {codes : Codes}
  {sent : Array OracleNotice} {lay₀ : TreeLay}

/-- **hseat at seatNew.** -/
theorem hseat_seatNew (h : sentPlaceB N (m + 1) pIn codes sent = true)
    (hlay : layTrees codes sent = some lay₀) (r : SwRow) (hl : r.l.length ≤ sent.size - 1)
    {base : ℕ} (hb : base = N.treesAt pIn) {d₁ : RDT} (hd : d₁.trees.length = lay₀.shapes.size) :
    ∀ i, base ≤ (seatNew N m r i).1 ∧ (seatNew N m r i).1 - base < d₁.trees.length := by
  intro i
  rw [seatNew_is_layout h hlay r hl i, hb]
  exact VerifiableInference.Desc.Book.hseat_of_lay hlay (N.treesAt pIn) r.l.length
    (Nat.le_trans hl (Nat.sub_le _ _)) d₁ hd i

/-- **hsent from hseat.** -/
theorem hsent_of_hseat {len base : ℕ} {d₁ : RDT} {ds : List RDT} {seat : Fin len → ℕ × ℕ}
    (h : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length) :
    ∀ i, ∃ n sh, (seat i).1 = base + n ∧ treeShT (d₁ :: ds) n = some sh := by
  intro i
  obtain ⟨h1, h2⟩ := h i
  refine ⟨(seat i).1 - base, d₁.trees[(seat i).1 - base], by omega, ?_⟩
  rw [Johnson.G.treeSh_flat, List.flatMap_cons, List.getElem?_append_left h2]
  exact List.getElem?_eq_getElem h2

/-- **hsent at seatNew.** -/
theorem hsent_seatNew (h : sentPlaceB N (m + 1) pIn codes sent = true)
    (hlay : layTrees codes sent = some lay₀) (r : SwRow) (hl : r.l.length ≤ sent.size - 1)
    {base : ℕ} (hb : base = N.treesAt pIn) {d₁ : RDT} (ds : List RDT)
    (hd : d₁.trees.length = lay₀.shapes.size) :
    ∀ i, ∃ n sh, (seatNew N m r i).1 = base + n ∧ treeShT (d₁ :: ds) n = some sh :=
  hsent_of_hseat (hseat_seatNew h hlay r hl hb hd)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hseat_seatNew
#print axioms VerifiableInference.Desc.First.K2Caller.hsent_of_hseat
#print axioms VerifiableInference.Desc.First.K2Caller.hsent_seatNew
