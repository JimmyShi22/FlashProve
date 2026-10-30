-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LinZc.lean: the claim that ties the scalar ZC of an attention
sub-proof to the table on the committed denominators, said on cells, for the written form of the
claim.

Statements and proofs. `linZc` (Johnson/Road/Rows/AttLin.lean) proves the same of a run of the
routine `lessPieces` in a context. Here the written form `Fo.lessF` stands in the run's place: the
first line of claim 5, as `Say5.zc` has it (Johnson/Desc/First/Att/Claims/Say58.lean). The proofs
follow those of `less_rule` and `linZc`, with `lessF_value`
(Johnson/Desc/First/Att/Claims/Worth.lean) and `readDenominatorF_rd2`
(Johnson/Desc/First/Att/Claims/MeanRd.lean) where these have `lessPieces_value` and
`readDenominator_rd2`.
Main names:
  `lessF_rule`: a written form "slot s less the pieces' weighted forms" that is worth 0 makes the
    slot's hidden value the sum over the pairs of the pair's weight times the value of its form.
  `linZcF`: the line worth 0 gives W.slot h.d.sZC = rv (L5.dimOf h.S) C p (cellsK h.S M) .zc.
  `linZcF_say`: the same from `Say5`.
Premises, as those of `linZc`: the setting `AttAt`, in which every table is true of the matrices in
the world W; piece b is pair b; the pieces' weights and the verifier's two points are the library's;
the table on the denominators lies in the list with its weights. One more: the indices read lie in
the table (the proof of `linZc` takes it from the run's own test).
Used of OnBytes, Johnson/Road and Inst: plain records, pure functions and lemmas on
them alone; no routine in a context and no theorem on a run: `AttAt`, `TabAt`, `PiecesAll`,
`cellsK`, `L5.dimOf`, `pt`, `sum_pieces`, `piece_at`, `rd2_pts`, `rv`, `wp`, `yg`, `yi`, `eqT`,
`rd2`, `denV`, `Fo.lessF`, `Fo.readDenominatorF`.
Limits: that a table is true is a premise. That W.slot h.d.sZC is what was sent less a mask entry,
and that cellsK h.S M are the cells of a tuple of committed messages, is not stated here. Nothing on
probabilities, on an honest prover or on hiding.

-/
import Johnson.Road.Rows.AttLin
import Johnson.Desc.First.Att.Claims.MeanRd
import Johnson.Desc.First.Att.Claims.Say58

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub rd2 eqT denV rv wp)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub Kf}

/-- **`less_rule` (Johnson/Road/Rows/AttLin.lean) for the written form.** -/
theorem lessF_rule {S : Attention.Shape} (s : ℕ) {pw : Array PW} (P : PiecesAll S pw) (fv : PW → Aff) (om V : ℕ → Kf)
    (hw : ∀ b < S.NP, ρ.val (pw.getD b default).wp = om b)
    (hf : ∀ b < S.NP, (fv (pw.getD b default)).value ρ W = V b)
    (h0 : (Fo.lessF (Aff.slot s) pw fv).value ρ W = 0) : W.slot s = ∑ b ∈ range S.NP, om b * V b := by
  rw [lessF_value, Aff.value_slot, sum_pieces P, sub_eq_zero] at h0
  rw [h0]
  exact sum_congr rfl fun b hb => by rw [hw b (mem_range.mp hb), hf b (mem_range.mp hb)]

/-- **The scalar ZC is its rule value**, from the written form of claim 5's first line. -/
theorem linZcF (A : AttAt ρ W tl K3 M h lid cf fs) (P : PiecesAll h.S h.d.pwW)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) C p.z .w3 b)
    (hzg : h.d.zgW.size = h.S.cf.lgk) (hzi : h.d.ziW.size = h.S.cf.lt)
    (hg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ h.d.ziW j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.hW h.S.cf.NAs h.S.T (eqTab h.d.ziW))
    (hin : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oZr + (l * h.S.Lam + (h.d.pwW.getD b default).lam) * h.S.cf.H +
        (g * h.S.HA + (h.d.pwW.getD b default).a) < (h.t.tabLen.lookup h.t.hW).getD 0)
    (h0 : (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Fo.readDenominatorF h K3 h.t.hW h.d.zgW w.lam w.a).value ρ W = 0) :
    W.slot h.d.sZC = rv (L5.dimOf h.S) C p (cellsK h.S M) .zc := by
  refine lessF_rule h.d.sZC P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z))
      (denV (cellsK h.S M) b)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readDenominatorF_rd2 A Tb (Nat.le_of_eq hzg.symm) ha (hin b hb), e]
  exact rd2_pts A hzi hg hi _

/-- The same from what claim 5's list says. -/
theorem linZcF_say (A : AttAt ρ W tl K3 M h lid cf fs) (P : PiecesAll h.S h.d.pwW)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) C p.z .w3 b)
    (hzg : h.d.zgW.size = h.S.cf.lgk) (hzi : h.d.ziW.size = h.S.cf.lt)
    (hg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ h.d.ziW j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.hW h.S.cf.NAs h.S.T (eqTab h.d.ziW))
    (hin : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oZr + (l * h.S.Lam + (h.d.pwW.getD b default).lam) * h.S.cf.H +
        (g * h.S.HA + (h.d.pwW.getD b default).a) < (h.t.tabLen.lookup h.t.hW).getD 0)
    (S5 : Say5 ρ W h K3) :
    W.slot h.d.sZC = rv (L5.dimOf h.S) C p (cellsK h.S M) .zc :=
  linZcF A P hw hzg hzi hg hi Tb hin S5.zc

end K5Law

#print axioms K5Law.lessF_rule
#print axioms K5Law.linZcF
#print axioms K5Law.linZcF_say
