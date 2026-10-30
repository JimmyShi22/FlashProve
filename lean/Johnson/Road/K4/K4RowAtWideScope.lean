-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowAtWideScope.lean: THE ASSEMBLY's STRUCTURE FOR K4's ROW, K4RowAt
(Johnson/Road/K4/K04LawOf.lean), HAS A MEMBER AT THE WIDER MEANING OVER THE CLOSED BASE, IN THE
GOALS' SCOPE AT AN OPENING OF THE IOP AS WRITTEN IN LEAN: rowAt_wide
(Johnson/Road/K4/K4RowAtAtWide.lean) called with the payers of k4Row_wide_scope
(Johnson/Road/K4/K4RowWideScope.lean). One statement: a call.

  **`rowAt_wide_scope`**: Nonempty (K4RowAt x linksFull … (28 * g + 4) (2 * g) (k4PlaceAt g) q
    (k4DataWide Dm E mgBase) (mgWide Dm E mgBase) told z). PREMISES: the scope (hS, hR) · an
    opening O · hX : Bs.G₀.W = X (the public parameters are a letter: IM.Open.W pays it at Z.p.X) ·
    g < 12 · hx, hl: x is the member of K4's lot's list that bears the number 2 g ·
    Fl : K4Fill Dm E Z c (twelve lines "this parameter is this term") · Sn : the nine named tests
    K4NamedW.
  PAID INSIDE: H (atK4_full, Johnson/Road/K4/K04Tied.lean) · K4OnX's nine · K4OnD's eight · hhead ·
    hH · Dm.lk (2 g) = some Lk and the five ties on Lk's sub-protocols.
Limits. THE WIDER MEANING IS A BRIDGE's SIDE, NOT THE MEANING THAT COUNTS. K4Fill IS SHOWN AT NO Dm;
the nine tests stand as premises; THEY ARE SHOWN TOGETHER NOWHERE. That there is an opening is shown
by no theorem. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4RowAtAtWide
import Johnson.Road.K4.K4RowWideScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Riders (k4OnX_of_scope seats_at_open)
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit Block FileDescription)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (Frame Piece MsgT mgWide MgData WideData mgBase linksFull)

variable {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ} {x : Bool × Par} {told : List (List VerifiableInference.Desc.Oracle)}

/-- **UNDER THE SCOPE, AN OPENING, THE TWELVE LINES AND THE NINE TESTS (ALL PREMISES): the
assembly's structure for K4's row has a member at the wider meaning over the closed base.** -/
theorem rowAt_wide_scope (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X)
    (E : WideData ProofFile.InstPub) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hX : Bs.G₀.W = X)
    (hg : g < 12) (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) (Fl : K4Fill Dm E Z c)
    (Sn : K4NamedW Dm E (28 * g + 4) (2 * g) (parOf x) told (Forest.elems X.y.fo))
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK rows cols) Tok MsgT))
    (z : ProofFile.InstPub) :
    Nonempty (K4RowAt x linksFull (flatPlacesOf linksFull true) (28 * g + 4) (2 * g)
      (k4PlaceAt g) q
      (k4DataWide Dm E (mgBase (P := ProofFile.InstPub) (W := Wit (CellsK rows cols) Tok MsgT)))
      (mgWide Dm E (mgBase (P := ProofFile.InstPub) (W := Wit (CellsK rows cols) Tok MsgT))) told
      z) := by
  subst hX
  obtain ⟨k4, kN, _⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨Lk, x', e1, e3, e5, st, runO, runG, fO, oRun, fG, gRun⟩ := seats_at_open hS hR O hg
  obtain rfl : x = x' := k04_sits_one hx e3 hl e5
  have hH : isLay Dm.links (headLink Bs.G₀.W) = false := by
    rw [Fl.links]
    unfold headLink
    rw [k4, kN, if_pos rfl]
    decide +kernel
  have hlk : Dm.lk (2 * g) = some Lk := by
    rw [Fl.lk]
    exact e1
  exact rowAt_wide Dm E hH (atK4_full g hg) (k4OnX_of_scope hS hR O hg hx hl)
    (k4OnD_of_fill Dm hS hR O rfl hg hx hl Fl) Sn (hhead_of_fill Fl z q.base) hlk st fO oRun fG gRun

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rowAt_wide_scope
