-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartTie0Of.lean: the ties at the first sending, proved for the concrete readings under the
hypotheses of `Spec.ldPartTie0Of`.

Definitions, one statement (`Spec.ldPartTie0Of`) and its proof, with six lemmas.
The ties are `LdPartTie0` (Cb/Part/LdPartHead.lean): seven clauses between the reading of the
messages behind the first sending and the overwriting of the further witness. The concrete readings
are `T.O'`, the reading of cells by a naming (`LdPartNm.out`, Cb/Part/LdPartCellsOut.lean), and
`T.vld`, the front lookup's own clause on its bits (`LdPartLk.ValidU`, Cb/Part/LdPartLkp.lean).
The analogue of Cb/Part/LdPartTieOf.lean and Cb/Part/LdPartTieOfProofs.lean for segment 0: nothing
was kept; `T.OK` requires that the rectangle of layer 0 alone covers the first body's matrix.

Main names:
  `T : LdPartTie0L P K S' St' J`, `T.OK pp`: a record of parameters and the fourteen conditions on
    it; see their docstrings.
  `Spec.ldPartTie0Of`: for P : `LdPartD Cf` (Cb/Part/LdPartDef.lean), K : `LdPartPk`
    (Cb/Part/LdPartRide.lean), and `LdPartD.bitsV` of Cb/Part/LdPartLkpBits.lean: `P.Props p`,
    `T.OK pp`, E of characteristic pp (an instance argument) ⇒
    `LdPartTie0 P K T.O' T.ov T.x' P.bitsV.ok T.vld`.

Limits: The parameters are variables: nothing here is stated of the model or at the model's numbers,
and nothing here shows that any parameters meet the hypotheses. This file gives no instance of
`T.OK`. This file does not say where the conditions on entries come from (the first sending's places
and lens). Nothing on masks.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartHead
import Cb.Part.LdPartCellsOut
import Cb.Part.LdPartTieNmProofs
import Cb.Part.LdPartLkpBitsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Finset Cb.Rng Cb.RngPk IOR

/-- A record of parameters for the ties at the first sending. `p₁`, `nm₁`, `at₁`: parameters, naming
and places of the first body's matrix among the messages S' behind the first sending. `ov`: the
overwriting of the further witness. `oR`, `oC`: where the packed rows of layer 0 and the Cw columns
are. `x'`, `msg`, `R`, `e`: the first front's readings and the places of its lookup's names. -/
structure LdPartTie0L {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} (P : LdPartD Cf) (K : LdPartPk) (S' : Sig E) (St' J : Type) [Fintype J] where
  p₁   : RngPar
  nm₁  : LdPartNm p₁
  at₁  : p₁.Rp → p₁.C → S'.Ent
  ov   : S'.Msg → LdPartW E → LdPartW E
  oR   : Fin (P.rp K 0) → p₁.Rp
  oC   : Fin K.Cw → p₁.C
  x'   : St' → Cf.Xm
  msg  : Cf.conf.Msg × S'.Msg → J → E
  R    : LdPartRd E J
  e    : ((P.keysOf 0).lk P.fmt.h (P.fmt.hi + P.fmt.lo) R x').Nm E → J

namespace LdPartTie0L
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {Cf : LdCf F E} {P : LdPartD Cf} {K : LdPartPk} {S' : Sig E} {St' J : Type}
  [Fintype J] (T : LdPartTie0L P K S' St' J)

def O' : LdPartOut E S' := T.nm₁.out S' T.at₁
def L : LdPartLk E St' J := (P.keysOf 0).lk P.fmt.h (P.fmt.hi + P.fmt.lo) T.R T.x'
def vld : St' → Cf.conf.Msg × S'.Msg → Prop := fun st um => T.L.ValidU T.e st (T.msg um)
def mpk (m : S'.Msg) : T.p₁.Rp → T.p₁.C → E := fun i κ => S'.ents m (T.at₁ i κ)

/-- The conditions. `nP` to `D₁`: packing factor, radix, bound and window of `p₁` are those of K and
P. `uniq`: unique packing at pp. `ok₁`: `nm₁.OK`. `own`: segment 0's matrix is on oR, oC in the
standard order. `cover`: the rectangle oR × oC covers the first body's matrix. `ovPk`, `ovBit`: ov
touches layer 0 alone. `ovOwn`, `ovB`: layer 0 of the overwritten witness is what is at the
rectangle's places, its bits what is at the places of the lookup's bit names. `rdA`, `rdW`: the
readings R are nm₁'s reading of the messages and the image of the matrix read off the index's
message. -/
structure OK (pp : ℕ) : Prop where
  nP    : K.P = T.p₁.P
  rdx₁  : T.p₁.rdx = K.rdx
  B₁    : T.p₁.B = P.B
  D₁    : T.p₁.D = P.D
  uniq  : Uniq (2 * P.D) K.rdx K.P pp
  ok₁   : T.nm₁.OK
  own   : T.nm₁.OwnAt K.P 0 (2 ^ (P.seg 0).rowsLog) (P.seg 0).cols T.oR T.oC
  cover : ∀ i c, ∃ i' c', T.oR i' = i ∧ T.oC c' = c
  ovPk  : ∀ m w j, j ≠ 0 → (T.ov m w).pk j = w.pk j
  ovBit : ∀ m w j, j ≠ 0 → (T.ov m w).bit j = w.bit j
  ovOwn : ∀ m w i c, P.layW K (T.ov m w) 0 i c = S'.ents m (T.at₁ (T.oR i) (T.oC c))
  ovB   : ∀ U m w (Y : Fin (2 ^ (P.keysOf 0).sz.dd)) (i : Fin (2 ^ (P.keysOf 0).sz.w)),
    T.msg (U, m) (T.e (.inl (Y, i))) = (T.ov m w).bit 0 ((P.keysOf 0).sz.bitNo Y i)
  rdA   : ∀ U m, T.R.A (T.msg (U, m)) = T.O'.A m
  rdW   : ∀ U m, T.R.W (T.msg (U, m)) = fun y c => algebraMap F E (P.matU U y c)

end LdPartTie0L

def Spec.ldPartTie0Of : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (K : LdPartPk) (p pp : ℕ) [CharP E pp] (S' : Sig E) (St' J : Type)
      [Fintype J] (T : LdPartTie0L P K S' St' J),
    P.Props p → T.OK pp → LdPartTie0 P K T.O' T.ov T.x' P.bitsV.ok T.vld

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  {P : LdPartD Cf} {K : LdPartPk} {S' : Sig E} {St' J : Type} [Fintype J]
  (T : LdPartTie0L P K S' St' J) {pp : ℕ}

theorem ldPartTie0Of_own (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) :
    P.layW K (T.ov m w) 0 = resM T.oR T.oC (T.mpk m) :=
  funext fun i => funext fun c => h.ovOwn m w i c

theorem ldPartTie0Of_uniq (h : T.OK pp) : Uniq (2 * T.p₁.D) T.p₁.rdx T.p₁.P pp := by
  rw [h.D₁, h.rdx₁, ← h.nP]
  exact h.uniq

theorem ldPartTie0Of_pkX (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (g : LdPartGh)
    (h2 : PackBy P.B K.rdx (P.layX K g 0) (P.layW K (T.ov m w) 0)) : T.O'.pkX m g := by
  rw [ldPartTie0Of_own T h m w] at h2
  show PackBy T.p₁.B T.p₁.rdx (T.nm₁.lay g) (T.mpk m)
  rw [h.B₁, h.rdx₁]
  exact ldPartTieNm_packOwn E T.p₁ T.nm₁ K.P 0 _ _ _ _ T.oR T.oC g P.B K.rdx (T.mpk m)
    h.nP h.ok₁ h.own h.cover h2

theorem ldPartTie0Of_rdX [CharP E pp] {p : ℕ} (hP : P.Props p) (h : T.OK pp) (m : S'.Msg)
    (g : LdPartGh) (hx : T.O'.pkX m g) (q : Place) (hq : q ∈ (P.seg 0).places) :
    T.O'.A m q.1 q.2.1 q.2.2 = ((g q.1 q.2.1 q.2.2 : ℤ) : E) := by
  obtain ⟨hle, _, hr, hc⟩ := hP.reads 0 hP.pos q hq
  have hs : q.1 = 0 := Nat.le_zero.1 hle
  have s1 : q.2.1 < T.nm₁.R q.1 := by
    rw [hs, h.own.R]
    rw [hs] at hr
    exact hr
  have s2 : q.2.2 < T.nm₁.C q.1 := by
    rw [hs, h.own.C]
    rw [hs] at hc
    exact hc
  refine (ldPartCells_out T.p₁ T.nm₁ E S' T.at₁).2.1
    pp (ldPartTie0Of_uniq T h) h.ok₁ ?_ m g hx q.1 q.2.1 q.2.2 s1 s2
  rw [h.B₁, h.D₁]
  have := hP.le_D
  have := hP.one_le
  omega

theorem ldPartTie0Of_pkR (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (hr : T.O'.pkR m) :
    Packed K.P (2 * P.D) K.rdx (P.layW K (T.ov m w) 0) := by
  have hr' : Packed T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m) := hr
  rw [ldPartTie0Of_own T h m w, h.nP, ← h.D₁, ← h.rdx₁]
  obtain ⟨Y, hY⟩ := hr'
  exact ⟨_, ldPartRes_by E _ _ _ _ T.p₁.P _ _ T.oR T.oC Y (T.mpk m) hY⟩

theorem ldPartTie0Of_rdOwn [CharP E pp] (h : T.OK pp) (m : S'.Msg) (w : LdPartW E) (hr : T.O'.pkR m)
    (r c : ℕ) (h1 : r < 2 ^ (P.seg 0).rowsLog) (h2 : c < (P.seg 0).cols) :
    T.O'.A m 0 r c = P.cellsW K (T.ov m w) 0 r c := by
  have hr' : Packed T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m) := hr
  obtain ⟨i, ei, _, e2⟩ := h.own.row r h1
  obtain ⟨c', ec, _⟩ := h.own.col c h2
  have hl : r % K.P < K.P := by
    rw [← e2]
    exact lt_of_lt_of_eq (T.nm₁.rowAt 0 r).2.2 h.nP.symm
  have hc : (r / K.P < P.rp K 0 ∧ r % K.P < K.P) ∧ c < K.Cw := ⟨⟨ei ▸ i.2, hl⟩, ec ▸ c'.2⟩
  unfold LdPartD.cellsW
  rw [dif_pos hc, if_pos ⟨h1, h2⟩, ldPartTie0Of_own T h m w]
  show ((T.nm₁.mats (cells T.p₁.P (2 * T.p₁.D) T.p₁.rdx (T.mpk m)) 0 r c : ℤ) : E) = _
  have hU := ldPartTie0Of_uniq T h
  rw [ldPartTieNm_readOwn E pp T.p₁ T.nm₁ K.P 0 _ _ _ _ T.oR T.oC (2 * T.p₁.D) T.p₁.rdx (T.mpk m)
        h.nP h.own hU hr' r c ⟨r / K.P, hc.1.1⟩ ⟨r % K.P, hc.1.2⟩ ⟨c, hc.2⟩ h1 h2 rfl rfl rfl,
    h.D₁, h.rdx₁]

end

theorem ldPartTie0Of : Spec.ldPartTie0Of := by
  intro F E _ _ _ _ _ Cf P K p pp _ S' St' J _ T hP h
  exact
    { ovPk := h.ovPk
      ovBit := h.ovBit
      pkX := ldPartTie0Of_pkX T h
      rdX := ldPartTie0Of_rdX T hP h
      bits := fun st U m w g hx hb =>
        ldPartBits_tie F E Cf P 0 St' J T.R T.x' T.e st (T.msg (U, m)) (P.matU U) g
          ((T.ov m w).bit 0) (hP.wf 0 hP.pos) (h.rdW U m)
          (fun q hq => by rw [h.rdA U m]; exact ldPartTie0Of_rdX T hP h m g hx q hq)
          (fun Y i => h.ovB U m w Y i) hb
      pkR := ldPartTie0Of_pkR T h
      rdOwn := ldPartTie0Of_rdOwn T h }

end Cb
