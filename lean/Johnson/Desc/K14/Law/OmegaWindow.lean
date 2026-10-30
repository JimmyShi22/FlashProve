-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OmegaWindow.lean: o_omega's TREE, NUMBERED THROUGH THE FILE, IS ONE OF THE
SHARED CHAIN's OWN: the window that "Omega's promise crosses" asks (omegaForward | omegaBack,
Johnson/Desc/Sound/OmegaCrosses.lean; TablesFit's fields POf | POb), AT THE TENANTS tenantSh
(Johnson/Desc/Sound/SharedMembers.lean). One theorem: a joining: no brick is typed here.


OBJECT   the numbers tiedNumbers N₁ Ns with Ns.tenant = tenantSh lo layU layO and Ns.lo = lo; a row
         f :: l of pieces.
USER     the two premises on N of omegaForward | omegaBack; pOf_at_sig | pOb_at_sig's (W). Nobody
         calls it.
FIELD    TablesFit's POf | POb (beneath g₂).

  omega_window   N.lo ≤ (N.tenant .oOmega).1 ∧ (N.tenant .oOmega).1 < hiAt (1 + l.length) f l.
                 THE LOWER HALF: hlo_sh. THE UPPER: tO_sh (o_omega's tree lies below lo + the two
                 sendings' numbers of trees) · hiAt_get at the row's piece number 6, whose base is
                 that sum · hiAt_le along a tiled row.
LEFT: sb_sh's own premises (Johnson/Desc/Sound/SeamTreesSh.lean): the layout of o_omega's sending
(hlO · hO) · Tiled f l · the piece number 6 and its base (b6) · and 5 ≤ l.length.
What is not claimed. b6 and Tiled at the seated row: the data's. That Ns is laid so at the seat. AT
A TENANT LAID BY THE CHAIN's OWN COUNT FROM 0 THE LOWER HALF WOULD FAIL WHEREVER lo IS ABOVE THAT
COUNT: tenantSh adds lo: that is what makes the number one through the file. Nothing on soundness.

-/
import Johnson.Desc.Sound.SeamTreesSh
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open Desc.K14.Law.Fence (tenantSh hlo_sh tO_sh)

/-- **The window on o_omega's tree.** -/
theorem omega_window {P₁ S₂ Cl Cells Tok : Type} {C : CK} {Fr : Frame} (lo : ℕ)
    (layU layO : TreeLay) (codes : Codes) (sentO : Array OracleNotice)
    (hlO : layTrees codes sentO = some layO) (hO : 1 < sentO.size) (N₁ : Numbers) (Ns : NumbersS)
    (hN : Ns.tenant = tenantSh lo layU layO) (hNlo : Ns.lo = lo)
    (f : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))) (hT : Tiled f l)
    (x6 : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (h6 : (f :: l)[6]? = some x6)
    (b6 : x6.base = lo + layU.shapes.size + layO.shapes.size) (hl : 5 ≤ l.length) :
    (tiedNumbers N₁ Ns).lo ≤ ((tiedNumbers N₁ Ns).tenant .oOmega).1 ∧
      ((tiedNumbers N₁ Ns).tenant .oOmega).1 < hiAt (1 + l.length) f l := by
  have e1 : (tiedNumbers N₁ Ns).lo = lo := hNlo
  have e2 : (tiedNumbers N₁ Ns).tenant = tenantSh lo layU layO := hN
  rw [e1, e2]
  refine ⟨hlo_sh lo layU layO .oOmega, ?_⟩
  have h := tO_sh lo layU layO codes sentO hlO hO
  rw [← b6, ← hiAt_get 6 f l x6 h6] at h
  exact Nat.lt_of_lt_of_le h (hiAt_le f l hT 6 _ (by omega))

end Desc.K14.Law
