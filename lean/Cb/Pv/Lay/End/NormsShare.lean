-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsShare.lean: the norms' share of the ledger of a layers' sub-proof, part by part,
and what it pays, at the chain's value.

Cb/Pv/Lay/End/LayEnd.lean takes the ledger of the verifier's claims in eleven parts. Four of them
are the claims on the norms: sq, bat, led, hot. This file gives these four parts off a last
statement of the chain of Cb/Pv/Lay/At/Own.lean and shows what LayEnd.lean's record Shares asks of
them.

Main definitions: sqAt, batAt, rowsAt, hotAt. Main theorems: ledAt_eq (the four parts, one after the
other, are the ledger of Cb/Pv/Lay/End/NormsBillAt.lean); norms_share (the premise Shares.norms at
these parts); hot_target (from the part hot alone: the extension of each defect d10 vanishes at
zt).

Limits: as Cb/Pv/Lay/End/NormsBillAt.lean. The part hot pays none of the six fields. hot_target is
used by no theorem. zt is tied to nothing.


-/
import Cb.Pv.Lay.End.LayEnd
import Cb.Pv.Lay.End.NormsBillAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd d10)
open Blocks (ext)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ι : NormsNm → Nm)

/-- The three claims behind the sums of squares. -/
noncomputable def sqAt (e : (tailAt P W).s7.Nx) (zt : ℕ → E) (b B : ℕ) :
    TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (clNorms (namesAt P.nr (readsAt Y ι)) (eAt P W e zt) (u1At P.nr ((tailAt P W).b1 e).2)
    (P.D.lL + 1) b B P.D.nNu)

/-- The batch of the row products. -/
noncomputable def batAt (e : (tailAt P W).s7.Nx) (zt : ℕ → E) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf [cBatch (namesAt P.nr (readsAt Y ι)) (eAt P W e zt) P.D.nNu]

/-- The norms' rows. -/
noncomputable def rowsAt (e : (tailAt P W).s7.Nx) (zt : ℕ → E) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (clLedger (namesAt P.nr (readsAt Y ι)) (eAt P W e zt) (u2At P.nr ((tailAt P W).b2 e).2)
    P.D)

/-- The selectors' sums. -/
noncomputable def hotAt : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (clHot (E := E) (namesAt P.nr (readsAt Y ι)) P.D)

omit [Fintype J₂] in
/-- The four parts, one after the other, are the ledger of the claims on the norms. -/
theorem ledAt_eq (e : (tailAt P W).s7.Nx) (zt : ℕ → E) (b B : ℕ) :
    ledAt P W Y ι e zt b B =
      sqAt P W Y ι e zt b B ++ (batAt P W Y ι e zt ++ (rowsAt P W Y ι e zt ++ hotAt P Y ι)) := by
  unfold ledAt normsLed normsCl sqAt batAt rowsAt hotAt ledOf
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

/-- What the record Shares asks of the norms' parts. -/
theorem norms_share (fm : Nm → TWhole.Aff E P.J) (e : (tailAt P W).s7.Nx) (zt : ℕ → E) (m : M)
    (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hst : ((tailAt P W).b1 e).2.st.1.2 = ((tailAt P W).b1 e).1.1.1.2)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ι x) = toAff (normsFm P.rd P.D (eAt P W e zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h1 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (sqAt P W Y ι e zt b B)) (P.msg m))
    (h2 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (batAt P W Y ι e zt)) (P.msg m))
    (h3 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (rowsAt P W Y ι e zt)) (P.msg m))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (hotAt P Y ι)) (P.msg m)) :
    (tailAt P W).lL ((tailAt P W).xL e) ((tailAt P W).b1 e).1.1.1.1.2 m ∧
      (tailAt P W).s1.Lc ((tailAt P W).b1 e).1.1 ((tailAt P W).b1 e).1.2 m ∧
      (tailAt P W).ow1 ((tailAt P W).b1 e) m ∧
      (tailAt P W).lP ((tailAt P W).xP e) ((tailAt P W).b2 e).1.1.1.2 m ∧
      (tailAt P W).s2.Lc ((tailAt P W).b2 e).1.1 ((tailAt P W).b2 e).1.2 m ∧
      (tailAt P W).ow2 ((tailAt P W).b2 e) m := by
  refine norms_bill P W Y ι fm e zt m b s B hl hd hB hst hfm gXi gP gR gS ?_
  rw [ledAt_eq, pull_append, pull_append, pull_append]
  exact ⟨h1, h2, h3, h4⟩

/-- From the part hot alone: the extension of each defect d10 vanishes at zt. -/
theorem hot_target (fm : Nm → TWhole.Aff E P.J) (en : NormsE E) (m : M) (lNI b s : ℕ)
    (hfm : ∀ l x, l < P.D.ne → x < P.D.nx →
      fm (ι (.sel l x)) = toAff (normsFm P.rd P.D en lNI b s (.sel l x)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (hotAt P Y ι)) (P.msg m)) :
    ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) en.zt = 0 := by
  refine hot_last (namesAt P.nr (readsAt Y ι)) en P.D (P.rd (P.msg m))
    (Sum.elim (P.msg m) fun j => (lateA Y fm j).val (P.msg m)) (fun l x h1 h2 => ?_)
    ((ledOf_holds _ _).1 ((Cb.Sub.pullL_holds _ _ _).1 h4))
  show (lateA Y fm (Y.at' (ι (.sel l x)))).val (P.msg m) = _
  unfold lateA
  rw [Y.ok _ (gS l x h1 h2), hfm l x h1 h2, toAff_val]
  show Blocks.Form.val (P.msg m) (extF P.rd P.D.lT _ en.zt) = _
  rw [val_extF P.rd P.hrd]
  simp only [sel_cell]

end Cb.Pv.Lay.End
