-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedAt.lean: the four clauses of the two product layers of the gated products in what
the chain of a layers' sub-proof's own rounds owes at its end, at the chain's value, from the
pull-back of the ledger of the verifier's claims on the gated products.

Cb/Pv/Lay/At/Own.lean has the chain of the own rounds of a layers' sub-proof that is not the first,
at the library's description (P.layV W). Cb/Pv/Lay/End/Last.lean writes what a chain owes at its end
as a record, LayTail.Bill. This file reads the letters of the claims on the gated products off a
last statement e of that chain and pays the record's fields o5, o6 (c5 and c6 are True at this
chain).

Main theorem: gated_share.

Limits: as Cb/Pv/Lay/End/GatedShare.lean. The other fourteen fields of the record are not paid here.


-/
import Cb.Pv.Lay.At.Own
import Cb.Pv.Lay.End.Last
import Cb.Pv.Lay.End.GatedShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)

section Share

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The four fields of the chain's bill that belong to the two product layers of the gated
products, at the chain's value, with the letters read off a last statement e. -/
theorem gated_share (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (P.layV W).toTail.s7.Nx) (m : M) (s : ℕ) (h1 : 1 ≤ P.D.lL) (hs1 : s ≤ lF P.D)
    (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D)
    (hfm : ∀ x : GatedNm, x.InR P.D s → fm (ι x) = toAff (gatedFm P.rd P.D
      (gatedEAt P.fp ((P.layV W).toTail.b5 e).2 ((P.layV W).toTail.b6 e).2) s x))
    (hY : GoodNm Y ι P.D s)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (gatedLedOf P.fp Y ι ((P.layV W).toTail.b5 e).2 ((P.layV W).toTail.b6 e).2 s)) (P.msg m)) :
    (P.layV W).toTail.s5.Lc ((P.layV W).toTail.b5 e).1.1 ((P.layV W).toTail.b5 e).1.2 m ∧
      (P.layV W).toTail.ow5 ((P.layV W).toTail.b5 e) m ∧
      (P.layV W).toTail.s6.Lc ((P.layV W).toTail.b6 e).1.1 ((P.layV W).toTail.b6 e).1.2 m ∧
      (P.layV W).toTail.ow6 ((P.layV W).toTail.b6 e) m := by
  obtain ⟨a5, a6⟩ := gated_pull P.fp P.hrd Y ι fm ((P.layV W).toTail.b5 e).2
    ((P.layV W).toTail.b6 e).2 (P.msg m) s h1 hs1 hs2 hfe hfm hY h
  exact ⟨trivial, a5, trivial, a6⟩

end Share

end Cb.Pv.Lay.End.Gated
