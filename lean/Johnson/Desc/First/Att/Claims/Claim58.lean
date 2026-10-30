-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Claim58.lean: kind K5, the claims are the written lists: claims 5 to 8
(endValuesE and claim5 with the key forms keyWL, keyIX, keyWH, joinR16; valueProduct and claim6;
claim7; claim8).

Main names:
  `divOf`, `maxOf`: the records of the division and of the maximum as the kind's: the terms inside
    ptsOfOwn.
  `gv_claim5` … `gv_claim8`: wherever the kind's routine returns at K, at `inOld h`, it returns the
    written value (jP of Fo.claim5V) and has gathered just the written list (Fo.claim5T …
    Fo.claim8T).
A read that gives a default: pwW.getD b default. The two records' defaults need not have one weight;
the routines read of it the layer and the head alone, which are 0 in both (`getD_lam`, `getD_a`).
Used of OnBytes: plain records, pure functions and definitions alone; no routine in a context and no
theorem on a run: the records Attention.Heard, Divide, Attain, Sc3, Scd, PW, Joins, ACall, Shape,
Seg, Table, Model.TenAt; the pure functions Attention.atRh, atRhp, remForm, indexForm, keyWL, keyIX,
keyWH, joinR16, ACall.holds, sc3A, sc3B, Divide's and Attain's accessors, Shape.NP; the written
forms and lists Fo.endValuesET, claim5V, claim5T, valueProductT, claim6T, claim7T, bitsSumF, claim8T
and the readers' written forms.
Not claimed: that a routine returns; what a form is worth.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Claim4

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (TablesP ScoreT Fun1 geoOf ptsOfOwn w1Of callOf tabOf keysOf tenOf sum3Of sumDOf)

variable {K : ℕ}

/-- The record of OnBytes/Model of the division as the kind's: the term inside ptsOfOwn. -/
def divOf (d : Divide) : P.DivP :=
  { pwW := w1Of d.pwW, pwX := w1Of d.pwX, pwH := w1Of d.pwH, qWH := d.qWH, zsl := d.zsl, zgW := d.zgW, ziW := d.ziW, zcW := d.zcW, zgX := d.zgX, ziX := d.ziX, zgH := d.zgH, ziH := d.ziH, zcH := d.zcH
    s5 := d.s5, sIB := d.sIB, s5h := d.s5h, scE := sum3Of d.scE, gam := d.gam, sCl := d.sCl, vpm := sum3Of d.vpm, wJv := d.wJv, vpd := sum3Of d.vpd }

/-- The record of OnBytes/Model of the maximum as the kind's: the term inside ptsOfOwn. -/
def maxOf (x : Attain) : P.MaxP :=
  { tg := x.tg, ti := x.ti, sM6 := x.sM6, scF := sum3Of x.scF, scd := sumDOf x.scd, scH := sum3Of x.scH }

theorem d_inOld (h : Attention.Heard) : (inOld h).p.d = divOf h.d := rfl
theorem x_inOld (h : Attention.Heard) : (inOld h).p.x = maxOf h.x := rfl

theorem getD_lam (pw : Array PW) (b : ℕ) :
    ((w1Of pw).getD b default).lam = (pw.getD b default).lam := by
  unfold w1Of
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases pw[b]? <;> rfl

theorem getD_a (pw : Array PW) (b : ℕ) :
    ((w1Of pw).getD b default).a = (pw.getD b default).a := by
  unfold w1Of
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases pw[b]? <;> rfl

/-! ### the key forms of claim 5 -/

theorem keys_eq (a b : Attention.Seg) : (keysOf a == keysOf b) = (a == b) := by
  cases a <;> cases b <;> rfl

theorem holds_callOf (c : ACall) (s : Attention.Seg) : (callOf c).holds (keysOf s) = c.holds s := by
  unfold P.CallG.holds ACall.holds callOf
  dsimp only
  induction c.segs with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.contains_cons, List.contains_cons, ih, keys_eq]

theorem keyWL_divOf (d : Divide) : P.Runs.keyWL (divOf d) = keyWL d := by
  unfold P.Runs.keyWL keyWL divOf
  dsimp only
  rw [sumW_w1Of]
  rfl

theorem keyIX_divOf (S : Shape) (d : Divide) : P.Runs.keyIX (geoOf S) (divOf d) = keyIX S d := by
  unfold P.Runs.keyIX keyIX divOf
  dsimp only
  rw [sumW_w1Of]
  rfl

theorem keyWH_divOf (d : Divide) : P.Runs.keyWH (divOf d) = keyWH d := by
  unfold P.Runs.keyWH keyWH divOf
  dsimp only
  rw [sumW_w1Of]
  rfl

theorem foldl_state {α σ τ : Type} (φ : τ → σ) (f : σ → α → σ) (g : τ → α → τ)
    (hf : ∀ s a, f (φ s) a = φ (g s a)) : ∀ (xs : List α) (s : τ), xs.foldl f (φ s) = φ (xs.foldl g s)
  | [], _ => rfl
  | a :: xs, s => by rw [List.foldl_cons, List.foldl_cons, hf, foldl_state φ f g hf xs]

theorem joinR16_old (S : Shape) (d : Divide) (j : Joins) :
    P.Runs.joinR16 (geoOf S) (divOf d) (jP j) = jP (joinR16 S d j) := by
  unfold P.Runs.joinR16 joinR16
  dsimp only
  rw [calls_zip, List.foldl_map, keyWL_divOf, keyIX_divOf]
  refine foldl_state jP _ _ (fun s x => ?_) _ _
  show (if (tabOf x.1.kind == tabOf Table.r16) = true then
      (jP s).set x.2 (let v := Aff.ofConst zeroE
        let v := if (callOf x.1).holds (keysOf Attention.Seg.wl) = true then v + keyWL d else v
        if (callOf x.1).holds (keysOf Attention.Seg.ix) = true then v + keyIX S d else v)
    else jP s) = _
  rw [tab_eq, holds_callOf, holds_callOf]
  split <;> rfl

/-! ### claim 5 -/

theorem gv_endValuesE (h : Attention.Heard) (b : ℕ) (w' : P.W1) (w : PW) (hl : w'.lam = w.lam)
    (ha : w'.a = w.a) :
    GV K (P.Runs.endValuesE (inOld h) b w') () (Fo.endValuesET h K b w) := by
  unfold P.Runs.endValuesE Fo.endValuesET
  rw [hl, ha]
  exact GV.bind0 (gv_readDenominator h _ _ _ _) (GV.bind (GV.lin _)
    (GV.bind0 (gv_readHead h _ h.S.atO _ _ _ _) (GV.lin _)))

/-- **Claim 5 of the kind's own text: the written joins and the written list.** -/
theorem gv_claim5 (h : Attention.Heard) (j : Joins) :
    GV K (P.Runs.claim5 (inOld h) (jP j)) (jP (Fo.claim5V h j)) (Fo.claim5T h K) := by
  unfold P.Runs.claim5 Fo.claim5V Fo.claim5T
  refine GV.bind0 (gv_lessPieces _ h.d.pwW _
    (fun w => Fo.readDenominatorF h K h.t.hW h.d.zgW w.lam w.a)
    fun w => gv_readDenominator h _ _ _ _) ?_
  refine GV.bind0 (gv_lessPieces _ h.d.pwW _
    (fun w => Fo.readHeadT h K h.t.tO (atRh h.S) h.d.zgW h.d.zcW w.lam w.a)
    fun w => gv_readHead h _ (atRh h.S) _ _ _ _) ?_
  refine GV.bind0 (gv_lessPieces _ h.d.pwW _
    (fun w => Fo.readHeadT h K h.t.tO (atRhp h.S) h.d.zgW h.d.zcW w.lam w.a)
    fun w => gv_readHead h _ (atRhp h.S) _ _ _ _) ?_
  refine GV.bind0 (gv_lessPieces _ h.d.pwH _
    (fun w => Fo.readHeadT h K h.t.tO (atRh h.S) h.d.zgH h.d.zcH w.lam w.a)
    fun w => gv_readHead h _ (atRh h.S) _ _ _ _) ?_
  refine GV.bind0 (gv_lessPieces _ h.d.pwH _
    (fun w => Fo.readHeadT h K h.t.tO (atRhp h.S) h.d.zgH h.d.zcH w.lam w.a)
    fun w => gv_readHead h _ (atRhp h.S) _ _ _ _) ?_
  refine GV.bind (GV.lin _) (GV.bind (GV.lin _) (GV.bind (GV.lin _) ?_))
  refine GV.bind (GV.forInList _ _ ?_ _) ?_
  · intro k
    exact GV.bind0 (gv_lessPieces _ h.d.pwX _
      (fun w => Fo.readIndexBitF h K h.t.hX h.d.zgX w.lam w.a k)
      fun w => gv_readIndexBit h _ _ _ _ _) (GV.bind1 (GV.lin _) (GV.pure _))
  refine GV.bind (GV.lin _) (GV.bind (GV.lin _) (GV.bind (GV.lin _) ?_))
  refine GV.bind (GV.forInList _ _ ?_ _) ((GV.pure _).cast ?_ rfl)
  · intro b
    exact GV.bind1 (gv_endValuesE h b _ _ (getD_lam _ _) (getD_a _ _)) (GV.pure _)
  · show (P.Runs.joinR16 (geoOf h.S) (divOf h.d) (jP j)).set h.d.qWH (P.Runs.keyWH (divOf h.d)) = _
    rw [joinR16_old, keyWH_divOf]
    rfl

/-! ### claim 6 -/

/-- The kind's "a number in the field" is that of OnBytes/Model: one text. -/
theorem ofNat_old : P.ofNat = Model.ofNat := rfl

theorem pwW_inOld (h : Attention.Heard) : (inOld h).p.d.pwW = w1Of h.d.pwW := rfl
theorem sumA_old (sc : Sc3) (b : ℕ) : (sum3Of sc).a b = sc3A sc b := rfl
theorem sumB_old (sc : Sc3) (b : ℕ) : (sum3Of sc).b b = sc3B sc b := rfl

theorem gv_valueProduct (h : Attention.Heard) (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool)
    (tV : ℕ) : GV K (P.Runs.valueProduct (inOld h) (sum3Of sc) tS pt isD tV) ()
      (Fo.valueProductT h K sc tS pt isD tV) := by
  unfold P.Runs.valueProduct Fo.valueProductT
  refine GV.bind (GV.lin _) (GV.bind1 (GV.forInList _ _ ?_ _) (GV.pure _))
  intro b
  simp only [pwW_inOld, getD_lam, getD_a, ofNat_old, sumA_old, sumB_old]
  refine GV.bind0 (gv_plane h _ _ _ _ _ _) (GV.bind0 (gv_plane h _ _ _ _ _ _) ?_)
  refine GV.bind (GV.lin _) (GV.bind0 (gv_readGroup h _ h.S.atV _ _ _) ?_)
  exact GV.bind1 (GV.lin _) (GV.pure _)

/-- **Claim 6 of the kind's own text: the written list.** -/
theorem gv_claim6 (h : Attention.Heard) : GV K (P.Runs.claim6 (inOld h)) () (Fo.claim6T h K) := by
  unfold P.Runs.claim6 Fo.claim6T
  exact GV.bind (GV.lin _) (GV.bind (gv_valueProduct h h.d.vpm _ _ _ _)
    (gv_valueProduct h h.d.vpd _ _ _ _))

/-! ### claim 7 -/

/-- **Claim 7 of the kind's own text: the written list.** -/
theorem gv_claim7 (h : Attention.Heard) : GV K (P.Runs.claim7 (inOld h)) () (Fo.claim7T h K) := by
  unfold P.Runs.claim7 Fo.claim7T
  refine GV.bind (GV.forInList _ _ ?_ _) (GV.bind (GV.lin _) (GV.bind (GV.forInList _ _ ?_ _)
    (GV.bind (GV.lin _) (GV.bind (GV.forInList _ _ ?_ _)
      (GV.bind1 (GV.forInList _ _ ?_ _) (GV.pure _))))))
  · intro b
    exact GV.bind0 (gv_readMaximum h _ _ _ _) (GV.bind1 (GV.lin _) (GV.pure _))
  · intro b
    exact GV.bind0 (gv_readHead h _ h.S.atQ _ _ _ _) (GV.bind1 (GV.lin _) (GV.pure _))
  · intro lam
    exact GV.bind0 (gv_readGroup h _ h.S.atK _ _ _) (GV.bind1 (GV.lin _) (GV.pure _))
  · intro b
    refine GV.bind1 (GV.forInList _ _ ?_ _) (GV.bind0 (GV.pure _) (GV.pure _))
    intro k
    exact GV.bind0 (gv_readIndexBit h _ _ _ _ _) (GV.bind1 (GV.lin _) (GV.pure _))

/-! ### claim 8 -/

/-- **Claim 8 of the kind's own text: the written list.** -/
theorem gv_claim8 (h : Attention.Heard) : GV K (P.Runs.claim8 (inOld h)) () (Fo.claim8T h K) := by
  unfold P.Runs.claim8 Fo.claim8T Fo.bitsSumF
  refine GV.bind (GV.lin _) (GV.bind1 (GV.forInList _ _ ?_ _) (GV.pure _))
  intro b
  refine GV.bind (GV.lin _) (GV.bind0 (GV.foldlM0 _
    (fun s k => Aff.addMul s
      (Fo.readIndexBitF h K h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k)
      (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE)))
    (fun _ k => GV.bind0 (gv_readIndexBit h _ _ _ _ _) (GV.pure _)) _ _) ?_)
  exact GV.bind1 (GV.lin _) (GV.pure _)

end K5Law
