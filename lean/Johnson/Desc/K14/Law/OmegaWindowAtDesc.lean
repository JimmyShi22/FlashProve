-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OmegaWindowAtDesc.lean: o_omega's TREE LIES IN THE WINDOW OF THE SHARED CHAIN's
OWN TREES, AT ANY IOP AS WRITTEN IN LEAN WHOSE SHARED CHAIN TELLS WHAT K14's chainOf TELLS: the two
comparisons of numbers that omegaForward | omegaBack (Johnson/Desc/Sound/OmegaCrosses.lean) ask, and
with them the fields POf | POb of TablesFitR (Johnson/P5J/TopTablesR.lean). NO PIECE OF THE ROW IS
NAMED: the upper bound is the row's END, not the base of its piece number 6.

  hiAt_end               behind the last piece of a tiled row hiAt is the row's first base and the trees
                         that the row's written rounds send.
  withOmega_pos          CALLED, NOT DECLARED HERE: another file's lemma
                         (Johnson/Desc/K14/Law/OmegaHasMsg.lean): o_omega's sending has a message, at
                         every shape.
  omega_window_at_desc   N.lo ≤ (N.tenant .oOmega).1 ∧ (N.tenant .oOmega).1 < hiAt (1 + T.l₂.length)
                         T.p₂ T.l₂ at N := tiedNumbers N₁ Ns, whatever N₁.
  window_from_zero       A NEGATIVE TEST OF THE PREMISE hN: at tenants counted from 0 in the place of the
                         first chain's number of trees the lower comparison FAILS as soon as that number
                         is above o_omega's place in the chain's own count.
FROM   F.planOk = true · F.data file = .ok D · of the row: its first base is D.t₁, its written rounds are
       D.ds₂, it is tiled (three fields of Three.Fits) · hG: F's shared chain tells what chainOf c P tests
       last tells · the two sendings' layouts of trees (hU · hlU · hlO) · hN · hNlo: the numbers' first tree is the number of trees that F's first chain
       tells, and the tenants are tenantSh at that number.
HOW    counts_of_planOk (Johnson/Desc/Sound/SeamDesc.lean: the first chain tells D.t₁ trees, the shared
       chain D.t₂) · told_of_chain | told_length (Johnson/Desc/K12/Coin/ToldAtFile.lean: the shared chain
       tells the two layouts' trees first) · hlo_sh (Johnson/Desc/Sound/SeamTreesSh.lean) · lay_lt
       (OnBytes/Tie/Pv/Keeps/LayOne.lean: a message's tree is one of its layout's).
BESIDE omega_window (Johnson/Desc/K14/Law/OmegaWindow.lean): the same conclusion from the base of the
row's piece number 6, which is asked there as a premise.
AT THE SHARED TABLE's CONSTANT (Sh.nums A O = tiedNumbers O.N₁ (numbersSh (Sh.t₁ A) (Sh.layU A)
(Sh.layO A) (0, 0) (0, 0)) with A.G := F): hN and hNlo are rfl. This file does not import the constant.
What is not claimed. ReadsTree, the third premise of omegaForward | omegaBack. That the premises are met
anywhere: no member is shown here. No law. Nothing on soundness.

-/
import Johnson.Desc.Sound.SeamDesc
import Johnson.Desc.Sound.SeamTreesSh
import Johnson.Desc.Sound.SentBeforeTiled
import Johnson.Desc.K12.Coin.ToldAtFile
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.K14.Law.OmegaHasMsg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open _root_.Run.PQ (CK)
open Desc.K14.Law.Fence (tenantSh hlo_sh counts_of_planOk)
open VerifiableInference.Desc.K12.Coin (told_of_chain told_length)

/-- Behind the last piece of a tiled row: the row's first base and all the trees that the row sends. -/
theorem hiAt_end {S Cl W : Type} {C : CK} {F : Frame} :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W), Tiled p l →
      hiAt (1 + l.length) p l = p.base + ((rowData p l).map (·.trees.length)).sum
  | [], p, _ => by
    show p.base + p.trees = _
    simp [rowData, Piece.trees]
  | q :: l, p, h => by
    have ih := hiAt_end l q h.2.2.2.2
    have e : hiAt (1 + (q :: l).length) p (q :: l) = hiAt (1 + l.length) q l := by
      show hiAt (1 + (l.length + 1)) p (q :: l) = _
      rw [← Nat.add_assoc]
      rfl
    rw [e, ih, h.2.2.2.1]
    simp [rowData, Piece.trees, Nat.add_assoc]

/-- **The window on o_omega's tree, with no piece of the row named.** -/
theorem omega_window_at_desc {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hp : F.planOk = true) (hD : F.data file = .ok D)
    {C : CK} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (hb : T.p₂.base = D.t₁)
    (hd : rowData T.p₂ T.l₂ = D.ds₂) (ht : Tiled T.p₂ T.l₂)
    (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hG : VerifiableInference.Desc.oraclesOf F.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf c P tests last).blocksInOrder)
    (sU : Array OracleNotice) (hU : withU P.S = some sU) (layU layO : TreeLay)
    (hlU : layTrees P.codes sU = some layU) (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (N₁ : Numbers) (Ns : NumbersS)
    (hN : Ns.tenant = tenantSh (VerifiableInference.Desc.oraclesOf F.first.blocksInOrder).length layU layO)
    (hNlo : Ns.lo = (VerifiableInference.Desc.oraclesOf F.first.blocksInOrder).length) :
    (tiedNumbers N₁ Ns).lo ≤ ((tiedNumbers N₁ Ns).tenant .oOmega).1 ∧
      ((tiedNumbers N₁ Ns).tenant .oOmega).1 < hiAt (1 + T.l₂.length) T.p₂ T.l₂ := by
  obtain ⟨c1, c2⟩ := counts_of_planOk F file D hp hD
  have e1 : (tiedNumbers N₁ Ns).lo = (VerifiableInference.Desc.oraclesOf F.first.blocksInOrder).length := hNlo
  have e2 : (tiedNumbers N₁ Ns).tenant =
      tenantSh (VerifiableInference.Desc.oraclesOf F.first.blocksInOrder).length layU layO := hN
  rw [e1, e2]
  refine ⟨hlo_sh _ layU layO .oOmega, ?_⟩
  have h : layO.tree.getD 0 0 < layO.shapes.size := OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (withOmega_pos P.S)
  have hE : hiAt (1 + T.l₂.length) T.p₂ T.l₂ = D.t₁ + D.t₂ := by
    rw [hiAt_end _ _ ht, hb, hd]
    rfl
  have hL : layU.shapes.size + layO.shapes.size ≤ D.t₂ := by
    rw [← c2, hG, told_of_chain c P tests last sU hU, List.length_append, List.length_append,
      told_length P.codes sU _ layU (by rw [VerifiableInference.Desc.Own.treesMade_eq]; exact hlU),
      told_length P.codes _ _ layO (by rw [VerifiableInference.Desc.Own.treesMade_eq]; exact hlO)]
    omega
  rw [hE, ← c1]
  simp only [tenantSh]
  omega

/-- A negative test of hN: tenants counted from 0 fall out of the window from below. -/
theorem window_from_zero (lo : ℕ) (layU layO : TreeLay)
    (h : layU.shapes.size + layO.tree.getD 0 0 < lo) : ¬ lo ≤ (tenantSh 0 layU layO .oOmega).1 := by
  simp only [tenantSh]
  omega

end Desc.K14.Law

#print axioms Desc.K14.Law.hiAt_end
#print axioms Desc.K14.Law.omega_window_at_desc
#print axioms Desc.K14.Law.window_from_zero
