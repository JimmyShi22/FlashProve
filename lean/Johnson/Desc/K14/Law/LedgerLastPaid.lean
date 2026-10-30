-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerLastPaid.lean: "THE TWO READERS OF A WITNESS SAY THE SAME OF o_omega AT
THE SHARED CHAIN's LAST BORDER", WITH ITS PREMISE ON THE RANGE PAID BY NAME, AND FROM THE FILLING OF
RECORD. omega_at_last (Johnson/Desc/K14/Law/LedgerLast.lean) asks hin: every index that the layout
gives an entry of Omega has its place below the code's message length. It is refuted
under linOk alone and proved under Codes.lengthsOk (omegaInRange_of_lengths,
Johnson/Desc/K14/Law/InRange.lean). HERE IT IS CALLED.

  omega_at_last_paid   omega_at_last at S := the plan's shape, without hin: from linOk and lengthsOk
                  of the plan's codes.
  omega_of_XK     the same from XK at border 12 (sharedX, codX, omY are in it).
WHAT STAYS. hlin, hl (two tests on the plan) · hm, hent, hten (the member at o_omega's number: its
entry and seat by the plan) · hO, h0 (by PlanShapes).
What is not claimed. No soundness; no level. NO MEMBER IS SHOWN.

-/
import Johnson.Desc.K14.Law.LedgerLast
import Johnson.Desc.K14.Law.LedgerNineTen
import Johnson.Desc.K14.Law.InRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K1 (shapesOf shapeAt)
open VerifiableInference.Desc.Sound
open Desc.K14.Law.Fence (sharedX sharedX_twelve)

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem)

/-- **The tie at the last border, its premise on the range paid.** -/
theorem omega_at_last_paid (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 0 < (withOmega Q.S).size) (h0 : 0 < (shapesOf (parO Q)).length) (nO : ℕ)
    (hnO : nO = sentU.size) (hX : sharedX Q sentU layU layO 12 d = true)
    (hY : codY Q 12 d = true) (hZ : omY (shapeAt (parO Q) ⟨0, h0⟩) nO 12 d = true) (t₁ : ℕ)
    (w : Wit Cells Tok MsgT) (x : Mem) (hm : mem nO = some x)
    (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hlin : linOk Q.codes Q.par.S = true) (hl : Q.codes.lengthsOk = true) :
    ∀ y < Q.par.S.matrixRows,
      wordsSh arr t₁ d.st d.book w d.loc.oOmega .main ((linLayOmega d.st.codes Q.par.S).index y) =
        rgOf Q.codes arr mem (rdK Q.codes) w d.loc.oOmega .main
          ((linLayOmega d.st.codes Q.par.S).index y) := by
  have hc : d.st.codes = Q.codes := ((codY_iff Q 12 d).1 hY).resolve_left (by omega)
  refine omega_at_last arr mem Q sentU layU layO d hO h0 nO hnO hX hY hZ t₁ Q.par.S w x hm hent hten
    fun y hy => ?_
  rw [hc, hent, shape_omega Q h0]
  exact omegaInRange_of_lengths Q.codes Q.par.S hl hlin y hy

/-- **The same from the filling of record at border 12.** -/
theorem omega_of_XK (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 0 < (withOmega Q.S).size) (h0 : 0 < (shapesOf (parO Q)).length)
    (sU sS : OracleShape) (Y : ℕ → St → Bool)
    (hX : XK Q sentU layU layO (sU, shapeAt (parO Q) ⟨0, h0⟩, sS, Y) sentU.size 12 d = true)
    (t₁ : ℕ) (w : Wit Cells Tok MsgT) (x : Mem) (hm : mem sentU.size = some x)
    (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hlin : linOk Q.codes Q.par.S = true) (hl : Q.codes.lengthsOk = true) :
    ∀ y < Q.par.S.matrixRows,
      wordsSh arr t₁ d.st d.book w d.loc.oOmega .main ((linLayOmega d.st.codes Q.par.S).index y) =
        rgOf Q.codes arr mem (rdK Q.codes) w d.loc.oOmega .main
          ((linLayOmega d.st.codes Q.par.S).index y) := by
  obtain ⟨g1, g2, g3, _⟩ := (XK_iff Q sentU.size _ sentU layU layO 12 d).1 hX
  exact omega_at_last_paid arr mem Q sentU layU layO d hO h0 sentU.size rfl g1
    (codY_of_codX Q 12 12 d g2) g3 t₁ w x hm hent hten hlin hl

end Desc.K14.Law

#print axioms Desc.K14.Law.omega_at_last_paid
#print axioms Desc.K14.Law.omega_of_XK
