-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartReq.lean: for toys: the fourth part of the object (`PReq`,
Cb/Obj/LdObjectParts.lean): a request with one segment, and what it leaves as the data of the
standard test over a family; its bundle of hypotheses from the premises of `rqPart_hyp`: conditions
on codes, on the arrangement, on the layout and on numbers, and that the model's relaxed relation is
trivial.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. The object is one record with a configuration and, over it,
the sub-protocols of the proof system, as five terms. A request's preamble is the fourth; the test
for linear constraints at N instances, the fifth, takes up what it leaves.
Definitions, statements as theorems, proofs. Generic: any configuration, an abstract field, variable
codes.

The seam: the test at N instances runs over what the request leaves: one `on : LdOLd Cf` for both.
Here "on" is `(rqD2 ..).on` for a standard test `D : StdLn2 Cf Pn` (Cb/Obj/LdObjectLinStd2.lean)
that is made from the request:
  Sa := the oracle messages after the request's segment, literally; the tensor row is trivial,
    "rest" has the coefficients 0 on the carried message (`GNew.oc`, Cb/Ld/LdGroupPlace.lean).
  The filed rows := what is claimed after the locations, as rows on all entries (`RowN`, `rowsOf`,
    `ldLoc_after_rows`, Cb/Req1/LdSegAfterRows.lean), with the places of Cb/Ld/LdGroupPlace.lean
    (`rqPJ`, `rqPQ`; `rq_lin`: for non-empty P, if the folded complex has its laws (`hC`), by
    definition of the cut).
  Asked of the shape: every oracle message that is kept at the bridge is held (`IsEmpty S₂.O`), so
    that all that is left is read at the positions Pn; finitely many rows.

Main names:
  `LdOLe.of`: the fields of an `LdOLd` but S; `(of D).on` = D by definition.
  `rqD2`, `rqEn2`, `rqEn2_laws`: for non-empty P and the shape asked above, if the folded complex
    has its laws (`hC`), a claim holds if and only if what is claimed after the locations does.
  `rqPart : PReq Cf`, `rqPart_hyp`: for non-empty P and the shape asked above: `RqHyp`
    (Cb/Obj/LdObjectReqStd.lean), the laws of the folded complex, the layout of `B0 : StdLn Cf Pn`
    lies on the configuration's, and ba (.inr a) ≤ t₂ ⇒ `(rqPart ..).Hyp (Sa.qFam True ba)`: `lay`,
    `r.Hyp`, `r.ZkS`, `r.Fmt` at the bound of the test that follows (the `qaB` of `partB`,
    Cb/Obj/LdObjectPartBat.lean, by definition).

Limits: this request has g = 0, τ = 0: no pending tensor row, no mask message for it, no final
batching: it claims nothing about the encoded index. This file does not say that the conditions can
be met. It says nothing on the fifth part over this "on" (`D.HypB` for D := `rqD2 ..`). It says
nothing on the other way to the seam: an end of the request with a batching of pending rows
(Cb/Obj/LdObjectReqEnd*.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqStd
import Cb.Obj.LdObjectPartBat
import Cb.Req1.LdSegAfterRows
import Cb.Obj.LdObjectLinStd
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- The fields of an `LdOLd` but S. -/
@[reducible] def LdOLe.of {F E : Type} [Field F] [Field E] [Algebra F E]
    {Cf : LdCf F E} (D : LdOLd Cf) : LdOLe Cf D.S :=
  { Cl := D.Cl, Y := D.Y, finY := D.finY, klo := D.klo, l := D.l, lay := D.lay, py := D.py,
    g := D.g, ψ := D.ψ, τ := D.τ, restM := D.restM, more := D.more, e' := D.e', t := D.t,
    NW := D.NW, SdW := D.SdW, iW := D.iW, lW := D.lW, NU := D.NU, SdU := D.SdU, iU := D.iU,
    lU := D.lU, NO := D.NO, SdO := D.SdO, iO := D.iO, lO := D.lO }

theorem LdOLe.of_on {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (D : LdOLd Cf) :
    (LdOLe.of D).on = D := rfl

section
variable {F E P Pn : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype P]
  [Nonempty P] [Fintype Pn] [Nonempty Pn] (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (R : StdGM E P)
  (T : StdArr R.D) (kp : R.A → Prop) [DecidablePred kp] (Hh : StdHeld T kp) (V : StdNew Hh.hd Pn)
  (w1 : (rqFold Cf.conf R T kp Hh).tgt.S.Wit × (rqFold Cf.conf R T kp Hh).tgt.Wp) (L₂ t₂ tl : ℕ)

/-- Where the entries of the folded complex are among the entries of the oracle messages that are
left. -/
def rqPJ (j : T.sh.Cf.J) : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.Ent :=
  ⟨.inr (V.N.place (.inl (.inl j))).1, (V.N.place (.inl (.inl j))).2⟩
def rqPQ (q : T.sh.Cf.Q) : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.Ent :=
  ⟨.inr (V.N.place (.inl (.inr q))).1, (V.N.place (.inl (.inr q))).2⟩

omit [Nonempty Pn] [Nonempty (Fin Cf.C₀.n)] in
theorem rq_lin (hC : T.sh.Cf.Laws) :
    (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.Lin (rqPJ Cf R T kp Hh V w1 L₂ t₂ tl)
      (rqPQ Cf R T kp Hh V w1 L₂ t₂ tl) (rqFold Cf.conf R T kp Hh).slf id where
  cutJ := fun _ _ => rfl
  cutQ := fun _ _ => rfl
  form := fun _ _ => Iff.rfl
  laws := hC

variable (B0 : StdLn Cf Pn) (tb₃ : ℕ) [IsEmpty (rqFold Cf.conf R T kp Hh).S₂.O]
  [Fintype (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.RowN]

/-- The oracle messages that are left are read at the positions Pn, as they are. -/
def rqPosA :
    ∀ a : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.O,
      Pn → ((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.om a).P
  | .inl a => isEmptyElim a
  | .inr none => id
  | .inr (some _) => id

/-- The standard test over what the request leaves: layout, the test's three messages and numbers,
but tb₃, are those of B0; a claim is (what the locations leave, the instance); the tensor row is
trivial; the filed rows are those of what is claimed after the locations. -/
@[reducible] def rqD2 : StdLn2 Cf Pn where
  Cl := (((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.Xc ×
        (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.hd.Smp) ×
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.Lc) × Cf.conf.X
  Y := B0.Y
  klo := B0.klo
  l := B0.l
  lay := B0.lay
  py := B0.py
  g := fun _ _ => 0
  ψ := fun _ => (fun _ => 0, fun _ => 0)
  τ := fun _ => 0
  e' := B0.e'
  t := B0.t
  MW := B0.MW
  MU := B0.MU
  MO := B0.MO
  dW := B0.dW
  dU := B0.dU
  dO := B0.dO
  Sa := (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S
  posA := rqPosA Cf R T kp Hh V w1 L₂ t₂ tl
  iM := .inr none
  cM := fun _ _ => 0
  BM := (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.RowN
  SbM := fun _ => (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.Ent → E
  slM := fun _ => Slf.idf
  xM := fun cl =>
    (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.rowsOf (rqPJ Cf R T kp Hh V w1 L₂ t₂ tl)
      (rqPQ Cf R T kp Hh V w1 L₂ t₂ tl) (rqFold Cf.conf R T kp Hh).slf id cl.1
  er := B0.er
  tb₁ := B0.tb₁
  tb₂ := B0.tb₂
  tb₃ := tb₃
  d := B0.d
  bad := B0.bad
  L2 := B0.L2
  Lc := B0.Lc

/-- The end of the request: what it leaves is the data of that test. -/
@[reducible] def rqEn2 : RqEnd Cf (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc where
  e := LdOLe.of (rqD2 Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃).on
  cl := id

omit [Nonempty Pn] [Nonempty (Fin Cf.C₀.n)] in
theorem rqEn2_laws (hC : T.sh.Cf.Laws) : (rqEn2 Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃).Laws where
  fwd := fun x _ _ _ m h => ⟨by
    show ∑ y, ∑ c, (0 : E) * _ * _ + ∑ j, (0 : E) * _ = 0
    rw [Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by rw [zero_mul, zero_mul],
      Finset.sum_eq_zero fun _ _ => zero_mul _, add_zero],
    (ldLoc_after_rows E Unit _ _ _ _ _ _ (rq_lin Cf R T kp Hh V w1 L₂ t₂ tl hC) x m).1 h⟩
  bwd := fun x _ _ _ m h =>
    (ldLoc_after_rows E Unit _ _ _ _ _ _ (rq_lin Cf R T kp Hh V w1 L₂ t₂ tl hC) x m).2 h.2

variable (t : ℕ) (dw : R.D.S.Wit × (Cf.conf.PIdx × Cf.conf.Cells)) (d : ℕ)
  (Lst mC mS mW : ℕ → ℕ) (L : ℕ) (w0 : (rqA (E := E) Cf.conf).W) (L₁ t₁ : ℕ)
  (c0 : Cf.conf.Cells) (w₀ : Cf.conf.PIdx × Cf.conf.Cells)

/-- The fourth part of the object: the request, and what it leaves. -/
@[reducible] def rqPart : PReq Cf where
  on := (rqD2 Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃).on
  Kr := Unit
  cr := fun _ => ()
  cr' := fun _ => ()
  r := rqReq Cf R T kp Hh V w1 L₂ t₂ tl (rqEn2 Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃) w0 L₁ t₁
    (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0
  w₀ := w₀
  qφ := fun _ => True

omit [Nonempty Pn] [Nonempty (Fin Cf.C₀.n)] in
open Classical in
/-- Its bundle of hypotheses, at the bound "at most ba a long positions of the oracle message a" of
the test that follows. -/
theorem rqPart_hyp (ba : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.O → ℕ)
    (hba : ∀ a, ba (.inr a) ≤ t₂) (hlay : ∀ a, ∃ l, B0.lay a = Cf.lay l) (hC : T.sh.Cf.Laws)
    (h : RqHyp Cf R T kp Hh V L₂ t₂ tl t d Lst mC mS mW L L₁ t₁) :
    (rqPart Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃ t dw d Lst mC mS mW L w0 L₁ t₁ c0 w₀).Hyp
      ((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.S.qFam (E₀ := extNone) (fun _ => True) ba) where
  lay := hlay
  rHyp := rqReq_hyp Cf R T kp Hh V w1 L₂ t₂ tl _ w0 L₁ t₁ _ c0 h.first (rqL_hyp dw h) h.new
    (rqEn2_laws Cf R T kp Hh V w1 L₂ t₂ tl B0 tb₃ hC) h.rno
  rZk := ldReqS_of_zk _ _ _ _ _ (rqReq_zk Cf R T kp Hh V w1 L₂ t₂ tl _ w0 L₁ t₁ _ c0)
  rFmt := rqReq_fmt Cf R T kp Hh V w1 L₂ t₂ tl _ t dw d Lst mC mS mW L w0 L₁ t₁ c0 _
    (fun _ hU =>
      ⟨fun _ _ => Finset.eq_empty_of_forall_notMem fun s _ => isEmptyElim s.1,
        fun a =>
          le_trans (le_trans
              (cnt_mono fun x hx => Finset.mem_map.2 ⟨⟨.inr a, x⟩, Finset.mem_toRight.2 hx, rfl⟩)
              (hU.2.2 (.inr a))) (hba a)⟩)
    h.first h.new h.shape h.fold h.list h.loc h.pos

end
end Cb
