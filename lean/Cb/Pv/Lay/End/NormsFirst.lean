-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsFirst.lean: the norms' six clauses of what the chain of the FIRST layers'
sub-proof's own rounds owes at its end, at the chain's value.

Cb/Pv/Lay/End/NormsBillAt.lean, NormsShare.lean and NormsParts.lean speak of the chain of a layers'
sub-proof that is not the first (Cb/Pv/Lay/At/Own.lean). The first sub-proof has a chain of its own
(Cb/Pv/Lay/At/OwnFirst.lean: P.layVF W, P.layVOF W): its statements behind the token point hold two
points more. The norms' two stretches are the same. This file says the three files' statements at
that chain; the token point is read off a statement by P.fs.pvF.

Main definitions: tailFst, eAtF, ledAtF, sqAtF, batAtF, rowsAtF. The part hot is hotAt of
Cb/Pv/Lay/End/NormsShare.lean.
Main theorems: norms_bill_first, hst_run_first, ledAtF_eq, norms_share_first, eAtF_parts,
led_at_parts_first, norms_at_parts_first.

Limits: as the three files.


-/
import Cb.Pv.Lay.At.OwnFirst
import Cb.Pv.Lay.End.NormsParts
import Cb.Pv.Lay.End.NormsShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (d10 lDd)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

section Bill

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnFPar E M X)
  (W : P.WFPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The letters of the chain behind the token point. -/
noncomputable abbrev tailFst : LayTail E M P.fs.X3 := (P.layVF W).toTail

/-- The letters of the claims on the norms, off a last statement of the chain. -/
noncomputable def eAtF (e : (tailFst P W).s7.Nx) (zt : ℕ → E) : NormsE E :=
  normsEAt P.nr (P.fs.pvF ((tailFst P W).xL e)) ((tailFst P W).b1 e).1.1.1.1.2
    ((tailFst P W).b1 e).1.1.1.2
    ((tailFst P W).b1 e).2 ((tailFst P W).b2 e).1.1.1.2 ((tailFst P W).b2 e).1.1.2
    (@id (Fin 1 → E) ((tailFst P W).b2 e).1.2 0) ((tailFst P W).b2 e).2 zt

/-- The ledger of the claims on the norms, off a last statement of the chain. -/
noncomputable def ledAtF (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (e : (tailFst P W).s7.Nx)
    (zt : ℕ → E) (b B : ℕ) : TWhole.Ledger E (P.J ⊕ J₂) :=
  normsLed (namesAt P.nr (readsAt Y ι)) (eAtF P W e zt) (u1At P.nr ((tailFst P W).b1 e).2)
    (u2At P.nr ((tailFst P W).b2 e).2) P.D (P.D.lL + 1) b B

/-- The six fields of the chain's bill that belong to the norms; c1 is True at this chain. -/
theorem norms_bill_first (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (tailFst P W).s7.Nx) (zt : ℕ → E) (m : M) (b s B : ℕ) (hl : lDd P.D = b + s)
    (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hst : ((tailFst P W).b1 e).2.st.1.2 = ((tailFst P W).b1 e).1.1.1.2)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ι x) = toAff (normsFm P.rd P.D (eAtF P W e zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (ledAtF P W Y ι e zt b B)) (P.msg m)) :
    (tailFst P W).lL ((tailFst P W).xL e) ((tailFst P W).b1 e).1.1.1.1.2 m ∧
      (tailFst P W).s1.Lc ((tailFst P W).b1 e).1.1 ((tailFst P W).b1 e).1.2 m ∧
      (tailFst P W).ow1 ((tailFst P W).b1 e) m ∧
      (tailFst P W).lP ((tailFst P W).xP e) ((tailFst P W).b2 e).1.1.1.2 m ∧
      (tailFst P W).s2.Lc ((tailFst P W).b2 e).1.1 ((tailFst P W).b2 e).1.2 m ∧
      (tailFst P W).ow2 ((tailFst P W).b2 e) m := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := norms_pull P.nr P.hrd Y ι fm (P.fs.pvF ((tailFst P W).xL e))
    ((tailFst P W).b1 e).1.1.1.1.2 ((tailFst P W).b1 e).1.1.1.2 ((tailFst P W).b1 e).2
    ((tailFst P W).b2 e).1.1.1.2 ((tailFst P W).b2 e).1.1.2
    (@id (Fin 1 → E) ((tailFst P W).b2 e).1.2 0)
    ((tailFst P W).b2 e).2 zt (P.msg m) b s B hl hd hB hst hfm gXi gP gR gS h
  exact ⟨a1, trivial, a2, a3, a4, a5⟩

/-- In the last statement of a run the premise hst of norms_bill_first holds. -/
theorem hst_run_first (x : P.fs.X3) (ts : (tailFst P W).ch.Trs) :
    ((tailFst P W).b1 ((tailFst P W).ch.run x ts)).2.st.1.2 =
      ((tailFst P W).b1 ((tailFst P W).ch.run x ts)).1.1.1.2 := by
  rw [st1_run]
  rfl

end Bill

section Share

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnFPar E M X)
  (W : P.WFPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ι : NormsNm → Nm)

/-- The three claims behind the sums of squares. -/
noncomputable def sqAtF (e : (tailFst P W).s7.Nx) (zt : ℕ → E) (b B : ℕ) :
    TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (clNorms (namesAt P.nr (readsAt Y ι)) (eAtF P W e zt) (u1At P.nr ((tailFst P W).b1 e).2)
    (P.D.lL + 1) b B P.D.nNu)

/-- The batch of the row products. -/
noncomputable def batAtF (e : (tailFst P W).s7.Nx) (zt : ℕ → E) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf [cBatch (namesAt P.nr (readsAt Y ι)) (eAtF P W e zt) P.D.nNu]

/-- The norms' rows. -/
noncomputable def rowsAtF (e : (tailFst P W).s7.Nx) (zt : ℕ → E) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (clLedger (namesAt P.nr (readsAt Y ι)) (eAtF P W e zt) (u2At P.nr ((tailFst P W).b2 e).2)
    P.D)

omit [Fintype J₂] in
/-- The four parts, one after the other, are the ledger of the claims on the norms. -/
theorem ledAtF_eq (e : (tailFst P W).s7.Nx) (zt : ℕ → E) (b B : ℕ) :
    ledAtF P W Y ι e zt b B =
      sqAtF P W Y ι e zt b B ++
        (batAtF P W Y ι e zt ++ (rowsAtF P W Y ι e zt ++ hotAt P.toOwnPar Y ι)) := by
  unfold ledAtF normsLed normsCl sqAtF batAtF rowsAtF hotAt ledOf
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

/-- What the record Shares asks of the norms' parts. -/
theorem norms_share_first (fm : Nm → TWhole.Aff E P.J) (e : (tailFst P W).s7.Nx) (zt : ℕ → E)
    (m : M)
    (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hst : ((tailFst P W).b1 e).2.st.1.2 = ((tailFst P W).b1 e).1.1.1.2)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ι x) = toAff (normsFm P.rd P.D (eAtF P W e zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h1 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (sqAtF P W Y ι e zt b B)) (P.msg m))
    (h2 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (batAtF P W Y ι e zt)) (P.msg m))
    (h3 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (rowsAtF P W Y ι e zt)) (P.msg m))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (hotAt P.toOwnPar Y ι)) (P.msg m)) :
    (tailFst P W).lL ((tailFst P W).xL e) ((tailFst P W).b1 e).1.1.1.1.2 m ∧
      (tailFst P W).s1.Lc ((tailFst P W).b1 e).1.1 ((tailFst P W).b1 e).1.2 m ∧
      (tailFst P W).ow1 ((tailFst P W).b1 e) m ∧
      (tailFst P W).lP ((tailFst P W).xP e) ((tailFst P W).b2 e).1.1.1.2 m ∧
      (tailFst P W).s2.Lc ((tailFst P W).b2 e).1.1 ((tailFst P W).b2 e).1.2 m ∧
      (tailFst P W).ow2 ((tailFst P W).b2 e) m := by
  refine norms_bill_first P W Y ι fm e zt m b s B hl hd hB hst hfm gXi gP gR gS ?_
  rw [ledAtF_eq, pull_append, pull_append, pull_append]
  exact ⟨h1, h2, h3, h4⟩

end Share

section Parts

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnFPar E M X)
  (W : P.WFPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J) (q : (tailFst P W).Parts) (m : M)
  (p : Fin P.D.lT → E) (c σ dl e1 e2 : E) (ρj : Fin (P.D.lL + 1) → E)
  (pt1 : PPt P.nr.sq.R.L.toSum.T.par.fmt) (pt2 : PPt P.nr.rows.tok.toSum.T.par.fmt)
  (zt : ℕ → E)
  (hx : P.fs.pvF q.x = p) (hsL : q.sL = sWAt P.nr (P.msg m) p) (hcN : q.cN = c)
  (ho1 : q.o1 = o1At P.nr (P.msg m) p c ρj e1 pt1) (hsP : q.sP = sPAt P.nr (P.msg m) p dl)
  (hcP : q.cP = σ) (hr2 : q.r2 = fun _ => zAt P.nr (P.msg m) p dl σ)
  (ho2 : q.o2 = o2At P.nr (P.msg m) p dl σ e2 pt2)

include hx hsL hcN ho1 hsP hcP hr2 ho2 in
omit [Fintype J₂] [DecidableEq J₂] in
/-- The letters of the claims on the norms, off the record. -/
theorem eAtF_parts :
    eAtF P W q.e zt = normsEAt P.nr p (sWAt P.nr (P.msg m) p) c (o1At P.nr (P.msg m) p c ρj e1 pt1)
      (sPAt P.nr (P.msg m) p dl) σ (zAt P.nr (P.msg m) p dl σ)
      (o2At P.nr (P.msg m) p dl σ e2 pt2) zt := by
  show normsEAt P.nr (P.fs.pvF q.x) q.sL q.cN q.o1 q.sP q.cP (@id (Fin 1 → E) q.r2 0) q.o2 zt = _
  rw [hx, hsL, hcN, ho1, hsP, hcP, hr2, ho2]
  rfl

variable (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
  (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
    fm (ι x) = toAff (normsFm P.rd P.D (eAtF P W q.e zt) (P.D.lL + 1) b s x))
  (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
  (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
  (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
  (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
  (h12 : ∀ ν, ν < P.D.nNu → l1 (Dgs P.nr (P.msg m) p ν) + h1 (Dgs P.nr (P.msg m) p ν) -
    2 * sig (Dgs P.nr (P.msg m) p ν) = 0)
  (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P.nr (P.msg m) p ν) + rq (Dgs P.nr (P.msg m) p ν) -
    sig (Dgs P.nr (P.msg m) p ν) + 1 = 0)
  (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) zt = 0)

include hx hsL hcN ho1 hsP hcP hr2 ho2 hl hd hB hfm gXi gP gR gS h12 h16 hHot in
/-- The pull-back of the ledger of the claims on the norms holds. -/
theorem led_at_parts_first :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (ledAtF P W Y ι q.e zt b B)) (P.msg m) := by
  have hE := eAtF_parts P W q m p c σ dl e1 e2 ρj pt1 pt2 zt hx hsL hcN ho1 hsP hcP hr2 ho2
  rw [hE] at hfm
  show TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
    (normsLed (namesAt P.nr (readsAt Y ι)) (eAtF P W q.e zt) (u1At P.nr q.o1) (u2At P.nr q.o2) P.D
      (P.D.lL + 1) b B)) (P.msg m)
  rw [hE, ho1, ho2]
  exact (norms_pull_iff P.nr P.hrd Y ι fm p _ c _ _ σ _ _ zt (P.msg m) b s B hl hd hB hfm gXi gP gR
    gS).2 ⟨last_meets P.nr _ (P.msg m) _ p c σ dl e1 e2 ρj pt1 pt2 zt b s hl h12 h16 hHot,
      outU_holds _ _ _ _ _ _, outU_holds _ _ _ _ _ _⟩

include hx hsL hcN ho1 hsP hcP hr2 ho2 hl hd hB hfm gXi gP gR gS h12 h16 hHot in
/-- The norms' six clauses, in the record's parts: norms_bill_first applied, with every premise
shown. One of them (c1) is True at this chain. -/
theorem norms_at_parts_first :
    (tailFst P W).lL q.x q.sL m ∧ (tailFst P W).s1.Lc (((q.x, q.sL), q.cN), q.pN) q.r1 m ∧
      (tailFst P W).ow1 q.b1 m ∧ (tailFst P W).lP (q.b1, q.d1) q.sP m ∧
      (tailFst P W).s2.Lc (((q.b1, q.d1), q.sP), q.cP) q.r2 m ∧ (tailFst P W).ow2 q.b2 m := by
  have hst : ((tailFst P W).b1 q.e).2.st.1.2 = ((tailFst P W).b1 q.e).1.1.1.2 := by
    show q.o1.st.1.2 = q.cN
    rw [ho1, hcN]
    rfl
  exact norms_bill_first P W Y ι fm q.e zt m b s B hl hd hB hst hfm gXi gP gR gS
    (led_at_parts_first P W Y ι fm q m p c σ dl e1 e2 ρj pt1 pt2 zt hx hsL hcN ho1 hsP hcP hr2 ho2
      b s B hl hd hB hfm gXi gP gR gS h12 h16 hHot)

end Parts

end Cb.Pv.Lay.End
