-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadersWritten.lean.
What the readers of the attention sub-proof's claims return, written out.

The claims of the attention sub-proof (OnBytes/Model/AttentionClaimsA.lean,
OnBytes/Model/AttentionClaimsB.lean) are made of forms on the slots and, many of them, of a form
that a reader makes of the array of tables. The readers: `u3at`, `plane`, `shV`, `xl`,
`readDenominator`, `readMaximum`, `readIndexBit`, `readHead`, `readGroup`. A reader asks the state
for one number alone: K, the number of columns of that array. Here each reader's form is a written
function of the heard record h, of K and of the reader's own arguments, and it is shown that this is
what the reader returns.

 * `shVF`, `overGF`, `readDenominatorF`, `readMaximumF`, `readIndexBitF` (and `planeF`,
   OnBytes/Tie/Pv/Lookup/Ends/FoClaim3Members.lean; `u3Form`,
   OnBytes/Tie/Pv/Lookup/Port/FoReads.lean, for `u3at`): written forms. The data of these readers
   have a value at all numbers of columns: also where the reader refuses (`u3at` tests its index
   against the table's length; the written form does not).
 * `xlF`, `readHeadF`, `readGroupF`: written forms under `Option`. `xl` refuses where `cutLast` or
   `headFeat` does; there `xlF` is `none`. `readHeadF` and `readGroupF` are `none` if `xlF` is at
   one of the heads of keys and values.
 * `u3at_returns` … `readIndexBit_returns`: if the reader returns y from a state F with `F.LS.size =
   F.ns` in which the array of tables has K columns (`colsOf F h.iU3 = K`), then y is the written
   form at K. `xl_returns`, `readHead_returns`, `readGroup_returns`: then the written form at K is
   `some y`.
 * `shV_vL`, `overG_vL`, `readDenominator_vL`, `readMaximum_vL`, `readIndexBit_vL`: the value of
   the reader's data (OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAttForms.lean) is the written form, at all
   numbers of columns, and the data add no claim.
 * `xlD`, `readHeadD`, `readGroupD`: data of `xl`, `readHead`, `readGroup` whose value is the
   written form: xlD's by definition, the two others' over xlD; `xl_vL`, `readHead_vL`,
   `readGroup_vL` say so. They are other terms than `fixedD_xl`, `fixedD_readHead`,
   `fixedD_readGroup` of OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAttForms.lean. That the two have one
   value at all numbers of columns is not shown here; where the reader returns, both have the value
   that it returns.
 * `foldlM_vO`, `weightedO`, `weighted_vO`, `overG_vO`: a loop of passes that add no claim and may
   have no value.

Nothing is said of whether a reader returns.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoClaim3Members

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

/-! ### a loop of passes that add no claim and may have no value -/

section
variable {α σ : Type} [HasGood α] [HasGood σ] {t0 : ℕ}

/-- A loop of passes each of which adds no claim and has the value `step s a`, which may be missing:
the loop's value is the loop of `step` in Option, and it adds no claim. -/
theorem foldlM_vO {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedD t0 (f s a)) (k : ℕ → ℕ)
    (step : σ → α → Option σ) :
    ∀ (l : List α) (s : σ) (hl : Good t0 l) (hs : Good t0 s),
      (∀ a ∈ l, ∀ (s : σ) (gs : Good t0 s) (ga : Good t0 a),
        (hf s a gs ga).v k = step s a ∧ (hf s a gs ga).L k = []) →
      (FixedD.foldlM hf l s hl hs).v k = l.foldlM step s ∧
      (FixedD.foldlM hf l s hl hs).L k = []
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | a :: l, s, hl, hs, H => by
    obtain ⟨e1, e2⟩ := H a List.mem_cons_self s hs ⟨hl.out a List.mem_cons_self⟩
    cases e : step s a with
    | none =>
      rw [e] at e1
      refine ⟨?_, ?_⟩
      · show ((hf s a hs _).bind _).v k = _
        rw [bind_v, bindV_none _ _ e1, List.foldlM_cons, e]
        rfl
      · show ((hf s a hs _).bind _).L k = _
        rw [bind_L, bindL_none _ _ e1, e2]
        rfl
    | some s' =>
      rw [e] at e1
      obtain ⟨b1, b2⟩ := bindD_some (hf s a hs ⟨hl.out a List.mem_cons_self⟩)
        (fun s' hs' => FixedD.foldlM hf l s'
          ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ hs') e1
      obtain ⟨i1, i2⟩ := foldlM_vO hf k step l s'
        ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
        ⟨(hf s a hs ⟨hl.out a List.mem_cons_self⟩).goodV k _ e1⟩
        fun b hb => H b (List.mem_cons_of_mem _ hb)
      refine ⟨?_, ?_⟩
      · show ((hf s a hs _).bind _).v k = _
        rw [b1, i1, List.foldlM_cons, e]
        rfl
      · show ((hf s a hs _).bind _).L k = _
        rw [b2, i2, e2]
        rfl

end

/-- The weighted sum of n forms, each of which may be missing. -/
def weightedO (n : ℕ) (w : Array E) (fv : ℕ → Option Aff) : Option Aff :=
  (List.range n).foldlM (fun s i => (fv i).map fun x => Aff.addMul s x (w.getD i zeroE))
    (Aff.ofConst zeroE)

/-- The data of a weighted sum over passes that add no claim and may have no value. -/
theorem weighted_vO {t0 : ℕ} (n : ℕ) (w : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ i, FixedD t0 (f i)) (k : ℕ → ℕ) (fv : ℕ → Option Aff)
    (H : ∀ i, (hf i).v k = fv i ∧ (hf i).L k = []) :
    (fixedD_weighted n w f hf).v k = weightedO n w fv ∧
    (fixedD_weighted n w f hf).L k = [] :=
  foldlM_vO (t0 := t0)
    (fun (s : Aff) (a : ℕ) _ _ => (hf a).bind fun a_3 _ =>
      FixedD.pure (s.addMul a_3 (w.getD a zeroE)))
    k (fun s i => (fv i).map fun x => Aff.addMul s x (w.getD i zeroE)) (List.range n)
    (Aff.ofConst zeroE) inferInstance inferInstance (fun a _ s gs _ => by
      obtain ⟨h1, h2⟩ := H a
      cases e : fv a with
      | none =>
        rw [e] at h1
        refine ⟨?_, by rw [bind_L, bindL_none _ _ h1, h2]; rfl⟩
        rw [bind_v, bindV_none _ _ h1]
        show none = Option.map _ (fv a)
        rw [e]
        rfl
      | some x =>
        rw [e] at h1
        obtain ⟨b1, b2⟩ := bindD_some (hf a)
          (fun a_3 (_ : Good t0 a_3) => FixedD.pure (t0 := t0) (s.addMul a_3 (w.getD a zeroE)))
          h1
        refine ⟨b1.trans ?_, by rw [b2, h2]; rfl⟩
        show _ = Option.map _ (fv a)
        rw [e]
        rfl)

/-! ### xl -/

/-- What xl returns, where its two tests pass. K: the number of columns of the array of tables. -/
def xlF (h : Attention.Heard) (K t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) : Option Aff :=
  match cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls with
  | .ok cut =>
    match headFeat X hd h.S.dh with
    | .ok j0 => some (weightedF (eqTab cut.1).size (eqTab cut.1) fun ch =>
        weightedF X.nl (limbWeights X.nl) fun l =>
          u3Form h.iU3 K (t + (tenCell X l lam j0 / 2 ^ h.S.ls + ch)))
    | _ => none
  | _ => none

/-- The data of xl, with its value written. -/
def xlD (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    FixedD h.iU3 (xl h t X lam hd zc) :=
  FixedD.ofQuiet (fun k => xlF h (k h.iU3) t X lam hd zc)
    (fun F c a G c' hr hs => by
      unfold xlF
      cases hc : cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls with
      | error e =>
        have hr' : (liftM (refuse "plan-tensor-layout" : Blk Aff) : SubM Aff) F c =
            .ok ((a, G), c') := by
          unfold xl at hr
          rw [hc] at hr
          exact hr
        exact absurd ((FixedD.refuse (t0 := h.iU3) (α := Aff) "plan-tensor-layout").run
          _ _ _ _ _ hr' hs).1 (by intro q; cases q)
      | ok cut =>
        cases hj : headFeat X hd h.S.dh with
        | error e =>
          have hr' : (liftM (refuse "plan-tensor-layout" : Blk Aff) : SubM Aff) F c =
              .ok ((a, G), c') := by
            unfold xl at hr
            rw [hc] at hr
            dsimp only at hr
            rw [hj] at hr
            exact hr
          exact absurd ((FixedD.refuse (t0 := h.iU3) (α := Aff) "plan-tensor-layout").run
            _ _ _ _ _ hr' hs).1 (by intro q; cases q)
        | ok j0 =>
          have hr' : (weighted (eqTab cut.1).size (eqTab cut.1) fun ch =>
              weighted X.nl (limbWeights X.nl) fun l =>
                u3at h t (tenCell X l lam j0 / 2 ^ h.S.ls + ch)) F c = .ok ((a, G), c') := by
            unfold xl at hr
            rw [hc] at hr
            dsimp only at hr
            rw [hj] at hr
            exact hr
          obtain ⟨e1, a1, k1, _⟩ := (fixedD_weighted (t0 := h.iU3) _ _ _ fun ch =>
            fixedD_weighted _ _ _ fun l =>
              fixedD_u3at h t (tenCell X l lam j0 / 2 ^ h.S.ls + ch)).run _ _ _ _ _ hr' hs
          obtain ⟨w1, w2⟩ := weighted_vL (t0 := h.iU3) (eqTab cut.1).size (eqTab cut.1) _
            (fun ch => fixedD_weighted _ _ _ fun l =>
              fixedD_u3at h t (tenCell X l lam j0 / 2 ^ h.S.ls + ch)) (colsOf F) _
            fun ch => weighted_vL _ _ _ _ (colsOf F) _ fun _ => u3at_vL h t _ (colsOf F)
          rw [w2] at a1
          exact ⟨w1.symm.trans e1, a1, k1⟩)
    (fun k a ha => by
      unfold xlF at ha
      split at ha
      · rename_i cut hc
        split at ha
        · rename_i j0 hj
          obtain ⟨w1, _⟩ := weighted_vL (t0 := h.iU3) (eqTab cut.1).size (eqTab cut.1) _
            (fun ch => fixedD_weighted _ _ _ fun l =>
              fixedD_u3at h t (tenCell X l lam j0 / 2 ^ h.S.ls + ch)) k _
            fun ch => weighted_vL _ _ _ _ k _ fun _ => u3at_vL h t _ k
          exact (fixedD_weighted (t0 := h.iU3) _ _ _ fun ch =>
            fixedD_weighted _ _ _ fun l =>
              fixedD_u3at h t (tenCell X l lam j0 / 2 ^ h.S.ls + ch)).goodV k a (w1.trans ha)
        · cases ha
      · cases ha)

theorem xl_vL (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) (k : ℕ → ℕ) :
    (xlD h t X lam hd zc).v k = xlF h (k h.iU3) t X lam hd zc ∧ (xlD h t X lam hd zc).L k = [] :=
  ⟨rfl, rfl⟩

/-! ### the readers whose value is there at every number of columns -/

/-- What shV returns. -/
def shVF (h : Attention.Heard) (K t off nl J lam j : ℕ) : Aff :=
  weightedF nl (limbWeights nl) fun l => u3Form h.iU3 K (t + (off + (l * h.S.Lam + lam) * J + j))

theorem shV_vL (h : Attention.Heard) (t off nl J lam j : ℕ) (k : ℕ → ℕ) :
    (fixedD_shV h t off nl J lam j).v k = some (shVF h (k h.iU3) t off nl J lam j) ∧
    (fixedD_shV h t off nl J lam j).L k = [] :=
  weighted_vL _ _ _ _ k _ fun _ => u3at_vL h t _ k

/-- The sum over the heads of keys and values. -/
def overGF (h : Attention.Heard) (zg : Array E) (fv : ℕ → Aff) : Aff :=
  weightedF h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) fv

theorem overG_vL {t0 : ℕ} (h : Attention.Heard) (zg : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ g, FixedD t0 (f g)) (k : ℕ → ℕ) (fv : ℕ → Aff)
    (H : ∀ g, (hf g).v k = some (fv g) ∧ (hf g).L k = []) :
    (fixedD_overG h zg f hf).v k = some (overGF h zg fv) ∧ (fixedD_overG h zg f hf).L k = [] :=
  weighted_vL _ _ _ _ k _ H

/-- What readDenominator returns. -/
def readDenominatorF (h : Attention.Heard) (K t : ℕ) (zg : Array E) (lam a : ℕ) : Aff :=
  overGF h zg fun g => shVF h K t h.S.oZr 4 h.S.cf.H lam (g * h.S.HA + a)

theorem readDenominator_vL (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ)
    (k : ℕ → ℕ) :
    (fixedD_readDenominator h t zg lam a).v k = some (readDenominatorF h (k h.iU3) t zg lam a) ∧
    (fixedD_readDenominator h t zg lam a).L k = [] :=
  overG_vL _ _ _ _ k _ fun _ => shV_vL h t _ _ _ _ _ k

/-- What readMaximum returns. -/
def readMaximumF (h : Attention.Heard) (K t : ℕ) (zg : Array E) (lam a : ℕ) : Aff :=
  overGF h zg fun g => shVF h K t h.S.oMr 4 h.S.cf.H lam (g * h.S.HA + a)

theorem readMaximum_vL (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) (k : ℕ → ℕ) :
    (fixedD_readMaximum h t zg lam a).v k = some (readMaximumF h (k h.iU3) t zg lam a) ∧
    (fixedD_readMaximum h t zg lam a).L k = [] :=
  overG_vL _ _ _ _ k _ fun _ => shV_vL h t _ _ _ _ _ k

/-- What readIndexBit returns. -/
def readIndexBitF (h : Attention.Heard) (K t : ℕ) (zg : Array E) (lam a b : ℕ) : Aff :=
  overGF h zg fun g =>
    shVF h K t h.S.oIb 1 (h.S.cf.lt * h.S.cf.H) lam (b * h.S.cf.H + g * h.S.HA + a)

theorem readIndexBit_vL (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a b : ℕ)
    (k : ℕ → ℕ) :
    (fixedD_readIndexBit h t zg lam a b).v k = some (readIndexBitF h (k h.iU3) t zg lam a b) ∧
    (fixedD_readIndexBit h t zg lam a b).L k = [] :=
  overG_vL _ _ _ _ k _ fun _ => shV_vL h t _ _ _ _ _ k

/-! ### the two readers over xl -/

theorem overG_vO {t0 : ℕ} (h : Attention.Heard) (zg : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ g, FixedD t0 (f g)) (k : ℕ → ℕ) (fv : ℕ → Option Aff)
    (H : ∀ g, (hf g).v k = fv g ∧ (hf g).L k = []) :
    (fixedD_overG h zg f hf).v k = weightedO h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) fv ∧
    (fixedD_overG h zg f hf).L k = [] :=
  weighted_vO _ _ _ _ k _ H

/-- What readHead returns, where xl's tests pass at every head of keys and values. -/
def readHeadF (h : Attention.Heard) (K t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    Option Aff :=
  weightedO h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) fun g => xlF h K t X lam (g * h.S.HA + a) zc

/-- The data of readHead over xlD. -/
def readHeadD (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    FixedD h.iU3 (readHead h t X zg zc lam a) :=
  fixedD_overG h zg _ fun g => xlD h t X lam (g * h.S.HA + a) zc

theorem readHead_vL (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ)
    (k : ℕ → ℕ) :
    (readHeadD h t X zg zc lam a).v k = readHeadF h (k h.iU3) t X zg zc lam a ∧
    (readHeadD h t X zg zc lam a).L k = [] :=
  overG_vO _ _ _ _ k _ fun _ => xl_vL h t X lam _ zc k

/-- What readGroup returns, where xl's tests pass at every head of keys and values. -/
def readGroupF (h : Attention.Heard) (K t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    Option Aff :=
  weightedO h.S.G (eqTab (zg.extract 0 h.S.cf.lgk)) fun g => xlF h K t X lam g zc

/-- The data of readGroup over xlD. -/
def readGroupD (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    FixedD h.iU3 (readGroup h t X zg zc lam) :=
  fixedD_overG h zg _ fun g => xlD h t X lam g zc

theorem readGroup_vL (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ)
    (k : ℕ → ℕ) :
    (readGroupD h t X zg zc lam).v k = readGroupF h (k h.iU3) t X zg zc lam ∧
    (readGroupD h t X zg zc lam).L k = [] :=
  overG_vO _ _ _ _ k _ fun _ => xl_vL h t X lam _ zc k

/-! ### where a reader returns, it returns the written form -/

/-- Here and in the five that follow: what the reader returns, from a state with `F.LS.size = F.ns`
in which the array of tables has K columns, is the written form at K. -/
theorem u3at_returns (h : Attention.Heard) (t i : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : u3at h t i F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = u3Form h.iU3 K (t + i) := by
  have e := ((fixedD_u3at h t i).run _ _ _ _ _ hr hs).1
  rw [(u3at_vL h t i (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

theorem plane_returns (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : plane h t x lam a z isD F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = planeF h K t x lam a z isD := by
  have e := ((fixedD_plane h t x lam a z isD).run _ _ _ _ _ hr hs).1
  rw [(plane_vL h t x lam a z isD (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

theorem shV_returns (h : Attention.Heard) (t off nl J lam j : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : shV h t off nl J lam j F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = shVF h K t off nl J lam j := by
  have e := ((fixedD_shV h t off nl J lam j).run _ _ _ _ _ hr hs).1
  rw [(shV_vL h t off nl J lam j (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

theorem readDenominator_returns (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : readDenominator h t zg lam a F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = readDenominatorF h K t zg lam a := by
  have e := ((fixedD_readDenominator h t zg lam a).run _ _ _ _ _ hr hs).1
  rw [(readDenominator_vL h t zg lam a (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

theorem readMaximum_returns (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : readMaximum h t zg lam a F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = readMaximumF h K t zg lam a := by
  have e := ((fixedD_readMaximum h t zg lam a).run _ _ _ _ _ hr hs).1
  rw [(readMaximum_vL h t zg lam a (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

theorem readIndexBit_returns (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a b : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : readIndexBit h t zg lam a b F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : y = readIndexBitF h K t zg lam a b := by
  have e := ((fixedD_readIndexBit h t zg lam a b).run _ _ _ _ _ hr hs).1
  rw [(readIndexBit_vL h t zg lam a b (colsOf F)).1, hK] at e
  exact (Option.some.inj e).symm

/-- Here and in the two that follow: where the reader returns y, from such a state, the written form
at K is `some y`. -/
theorem xl_returns (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : xl h t X lam hd zc F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : xlF h K t X lam hd zc = some y := by
  have e := ((xlD h t X lam hd zc).run _ _ _ _ _ hr hs).1
  rw [(xl_vL h t X lam hd zc (colsOf F)).1, hK] at e
  exact e

theorem readHead_returns (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : readHead h t X zg zc lam a F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : readHeadF h K t X zg zc lam a = some y := by
  have e := ((readHeadD h t X zg zc lam a).run _ _ _ _ _ hr hs).1
  rw [(readHead_vL h t X zg zc lam a (colsOf F)).1, hK] at e
  exact e

theorem readGroup_returns (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ)
    {F G : Fork} {c c' : Ctx} {y : Aff} {K : ℕ}
    (hr : readGroup h t X zg zc lam F c = .ok ((y, G), c')) (hs : F.LS.size = F.ns)
    (hK : colsOf F h.iU3 = K) : readGroupF h K t X zg zc lam = some y := by
  have e := ((readGroupD h t X zg zc lam).run _ _ _ _ _ hr hs).1
  rw [(readGroup_vL h t X zg zc lam (colsOf F)).1, hK] at e
  exact e

end Fo
