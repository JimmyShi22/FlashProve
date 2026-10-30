-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/All.lean

The 25 segments of the integer model whose head carries the cost ledger
(Policy/Rel/LedgerHead.lean), over p = 2^64 - 2^32 + 1: the model's conditions modulo p hold if and
only if every segment's conditions hold.

Definitions, and statements with their proofs. `segPol s pol k` is `segHeadPolY s pol`
(Policy/Seg/Head.lean) at k = 24, else the library's `TS.segM s k` (Cm/TargetSegModel.lean). The
library states the assemblies of the first 24 segments for every number h : `Hd` of the head's
cells, at a trace's matrices for those with `h.OK` (Cm/TargetSegFFAll.lean, Cm/TargetSegAtt.lean);
they are taken at `Hd.main`.
`SegsOKPol`: what is asked of 25 segments, after `TS.SegsOK` (Cm/TargetSegAll.lean). The conditions
are `LedgerRel.Cond Gl.p` (Policy/Rel/LedgerRel.lean). The statements stand in `Spec`, each under
its docstring: `condPol_iff`, `equivPol_of`, `equivPol_to`, `segsPol_ok`, `segPol_equiv`,
`segPol_admit`, `segPol_force`, `segPol_noReply`.

Limits: nothing on protocols. That matrices below the relaxed bound with all segments' conditions
exist exactly if the request is true under the policy is not stated here. What the heads of
Cm/TargetSegAll.lean and Cm/TargetSegModel.lean list as not said is not said here either, but for
two things: 25 segments that meet what is asked exist (`segsPol_ok`), and no coefficient table
before the last segment reads the reply (`segPol_noReply`).
-/
import Policy.Seg.HeadY
import Cm.TargetSegModelProofs
import Cm.TargetSegNoReplyProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Inst.Model.All Cm.Seg

/-- Segment k of the model with the ledger's head. -/
def segPol (s : Cm.Scales) (pol : AcceptancePolicy) (k : ℕ) :
    SegSpec (Instance ppref) Gl.F Gl.E :=
  if k = 24 then segHeadPolY s pol else TS.segM s k

theorem segPol_head (s : Cm.Scales) (pol : AcceptancePolicy) : segPol s pol 24 = segHeadPolY s pol := if_pos rfl

theorem segPol_ne (s : Cm.Scales) (pol : AcceptancePolicy) {k : ℕ} (hk : k ≠ 24) :
    segPol s pol k = TS.segM s k := if_neg hk

theorem segPol_ff (s : Cm.Scales) (pol : AcceptancePolicy) {g : ℕ} (hg : g < nGr) :
    segPol s pol (2 * g) = TS.ffSeg s.kap s.nf g tokX := by
  have hg' : g < 12 := hg
  rw [segPol_ne s pol (by omega)]
  exact TS.seg_ff s (TS.attM s) hg

theorem segPol_att (s : Cm.Scales) (pol : AcceptancePolicy) {g : ℕ} (hg : g < nGr) :
    segPol s pol (2 * g + 1) = TS.attM s g := by
  rw [segPol_ne s pol (by omega)]
  exact TS.seg_att s (TS.attM s) hg

/-- The clauses of the last segment: the keys and identities of the head with the ledger
(`HeadCl`, Policy/Seg/Head.lean) at the trace's cells, and the identity on y. -/
def HeadAtPol (s : Cm.Scales) (pol : AcceptancePolicy) (W : Mat) (x : Instance ppref) (T : Trace) : Prop :=
  HeadCl s.nf pol W x T.vHead ∧ (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Gl.p) = 0)

/-- What is asked of the 25 segments. -/
structure SegsOKPol (s : Cm.Scales) (pol : AcceptancePolicy) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E) :
    Prop where
  rows   : ∀ k < nSeg, (seg k).rowsLog = Cm.Seg.rowsLog k
  cols   : ∀ k < nSeg, (seg k).cols = Cm.Seg.cols k
  wf     : ∀ k < nSeg, (seg k).WF TS.fmtRef
  places : ∀ k < nSeg, ∀ q ∈ (seg k).places, q ∈ reads Hd.main k
  ffTo   : ∀ g < nGr, ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg (2 * g)).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM (toMat Hd.main T)) ↔
      TS.FFAt s g W x T
  ffOf   : ∀ g < nGr, ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg (2 * g)).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM M) ↔
      TS.FFAt s g W x (ofMat Hd.main M)
  attTo  : ∀ g < nGr, ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg (2 * g + 1)).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM (toMat Hd.main T)) ↔
      TS.AttAt s g T
  attOf  : ∀ g < nGr, ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg (2 * g + 1)).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM M) ↔
      TS.AttAt s g (ofMat Hd.main M)
  headTo : ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg 24).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM (toMat Hd.main T)) ↔
      HeadAtPol s pol W x T
  headOf : ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg 24).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM M) ↔
      HeadAtPol s pol W x (ofMat Hd.main M)

namespace Spec

/-- States: the conditions `LedgerRel.Cond Gl.p` hold if and only if the clauses of all 25 segments
hold. -/
def condPol_iff : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (W : Mat) (x : Instance ppref) (T : Trace),
    LedgerRel.Cond Gl.p (ppOf s pol) W x T ↔
      (∀ g < nGr, TS.FFAt s g W x T) ∧ (∀ g < nGr, TS.AttAt s g T) ∧ HeadAtPol s pol W x T

/-- States: for all segments with `SegsOKPol s pol seg` and all integer matrices M, the conditions
hold at the trace of M if and only if every segment's conditions hold at M. -/
def equivPol_of : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E),
    SegsOKPol s pol seg →
    ∀ (W : Mat) (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ),
      LedgerRel.Cond Gl.p (ppOf s pol) W x (ofMat Hd.main M) ↔
      ∀ k < nSeg, (seg k).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM M)

/-- States the same at a trace T and its matrices. -/
def equivPol_to : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E),
    SegsOKPol s pol seg →
    ∀ (W : Mat) (x : Instance ppref) (T : Trace),
      LedgerRel.Cond Gl.p (ppOf s pol) W x T ↔
      ∀ k < nSeg, (seg k).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM (toMat Hd.main T))

/-- States: the 25 segments `segPol s pol` meet `SegsOKPol`. -/
def segsPol_ok : Prop := ∀ (s : Cm.Scales) (pol : AcceptancePolicy), SegsOKPol s pol (segPol s pol)

/-- States the two equivalences at `segPol s pol`. -/
def segPol_equiv : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (W : Mat) (x : Instance ppref),
    (∀ M : ℕ → ℕ → ℕ → ℤ,
      LedgerRel.Cond Gl.p (ppOf s pol) W x (ofMat Hd.main M) ↔
      ∀ k < nSeg, (segPol s pol k).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM M)) ∧
    (∀ T : Trace,
      LedgerRel.Cond Gl.p (ppOf s pol) W x T ↔
      ∀ k < nSeg,
        (segPol s pol k).Holds TS.fmtRef x (Cm.TP.castW Gl.p W) (TS.cM (toMat Hd.main T)))

/-- States: at a witness T of the relation, r < e, the matrices of T are below 129 in absolute value
at all places of the shapes, and they meet all segments' conditions at the index's matrix. -/
def segPol_admit : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) (T : Trace),
    LedgerRel.Ryes Gl.p (ppOf s pol) i x T →
    x.r < x.e ∧
    (∀ q : Cb.Place, InShape q → |toMat Hd.main T q.1 q.2.1 q.2.2| < 129) ∧
    ∀ k < nSeg,
      (segPol s pol k).Holds TS.fmtRef x (Cm.TP.castW Gl.p i.mat) (TS.cM (toMat Hd.main T))

/-- States: if r < e, matrices that are below 2^18 in absolute value at all places of the shapes and
meet all segments' conditions at the index's matrix give a witness of the relaxed relation. -/
def segPol_force : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ),
    x.r < x.e →
    (∀ q : Cb.Place, InShape q → |M q.1 q.2.1 q.2.2| < 2 ^ 18) →
    (∀ k < nSeg, (segPol s pol k).Holds TS.fmtRef x (Cm.TP.castW Gl.p i.mat) (TS.cM M)) →
    LedgerRel.Rno Gl.p (ppOf s pol) i x (ofMat Hd.main M)

/-- States: at two requests with the same prompt every coefficient table of a segment before the
last is the same. -/
def segPol_noReply : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (k : ℕ),
    k < 24 → ∀ x x' : Instance ppref, x.prompt = x'.prompt → TS.sameS (segPol s pol k) x x'

end Spec

theorem condPol_iff : Spec.condPol_iff := by
  intro s pol W x T
  constructor
  · intro h
    exact ⟨fun g hg => ⟨h.ffKey g hg, h.ffIdn g hg⟩, fun g hg => ⟨h.attKey g hg, h.attIdn g hg⟩,
      ⟨h.headKey, h.headIdn, h.headJc, h.headSums⟩, h.yZero⟩
  · rintro ⟨h1, h2, ⟨h3, h4, h5, h6⟩, h7⟩
    exact ⟨⟨fun g hg => (h1 g hg).1, fun g hg => (h1 g hg).2,
        fun g hg => (h2 g hg).1, fun g hg => (h2 g hg).2⟩,
      h3, h4, h5, h6, h7⟩

theorem equivPol_of : Spec.equivPol_of := by
  intro s pol seg hS W x M
  rw [condPol_iff s pol W x (ofMat Hd.main M)]
  constructor
  · rintro ⟨h1, h2, h3⟩ k hk
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · exact (hS.ffOf g hg x M W).2 (h1 g hg)
    · exact (hS.attOf g hg x M W).2 (h2 g hg)
    · exact (hS.headOf x M W).2 h3
  · intro h
    exact ⟨fun g hg => (hS.ffOf g hg x M W).1 (h _ (TS.two_lt hg).1),
      fun g hg => (hS.attOf g hg x M W).1 (h _ (TS.two_lt hg).2),
      (hS.headOf x M W).1 (h 24 (by show 24 < 25; norm_num))⟩

theorem equivPol_to : Spec.equivPol_to := by
  intro s pol seg hS W x T
  rw [condPol_iff s pol W x T]
  constructor
  · rintro ⟨h1, h2, h3⟩ k hk
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · exact (hS.ffTo g hg x T W).2 (h1 g hg)
    · exact (hS.attTo g hg x T W).2 (h2 g hg)
    · exact (hS.headTo x T W).2 h3
  · intro h
    exact ⟨fun g hg => (hS.ffTo g hg x T W).1 (h _ (TS.two_lt hg).1),
      fun g hg => (hS.attTo g hg x T W).1 (h _ (TS.two_lt hg).2),
      (hS.headTo x T W).1 (h 24 (by show 24 < 25; norm_num))⟩

theorem segsPol_ok : Spec.segsPol_ok := fun s pol =>
  { rows := fun k hk => by
      by_cases h : k = 24
      · subst h
        rw [segPol_head]
        rfl
      · rw [segPol_ne s pol h]
        exact (TS.segs_ok s).rows k hk
    cols := fun k hk => by
      by_cases h : k = 24
      · subst h
        rw [segPol_head]
        rfl
      · rw [segPol_ne s pol h]
        exact (TS.segs_ok s).cols k hk
    wf := fun k hk => by
      by_cases h : k = 24
      · subst h
        rw [segPol_head]
        exact headPolY_wf s pol
      · rw [segPol_ne s pol h]
        exact (TS.segs_ok s).wf k hk
    places := fun k hk q hq => by
      by_cases h : k = 24
      · subst h
        rw [segPol_head] at hq
        exact headPolY_places s pol q hq
      · rw [segPol_ne s pol h] at hq
        exact reads_plain_sub k ((TS.segs_ok s).places k hk q hq)
    ffTo := fun g hg x T W => by
      rw [segPol_ff s pol hg]
      exact TS.ffSeg_toMat XI s.kap s.nf Hd.main g tokX mainOK hg x T W
    ffOf := fun g hg x M W => by
      rw [segPol_ff s pol hg]
      exact TS.ffSeg_ofMat XI s.kap s.nf Hd.main g tokX hg x M W
    attTo := fun g hg x T W => by
      rw [segPol_att s pol hg]
      exact TS.attSpec_iff_toMat TS.fmtRef keyVec_agree_spec idnVal_agree_spec s.kap s.nf Hd.main
        mainOK hg x T (Cm.TP.castW Gl.p W)
    attOf := fun g hg x M W => by
      rw [segPol_att s pol hg]
      exact TS.attSpec_iff_ofMat TS.fmtRef keyVec_agree_spec idnVal_agree_spec s.kap s.nf Hd.main
        hg x M (Cm.TP.castW Gl.p W)
    headTo := fun x T W => by
      rw [segPol_head]
      exact headPolY_holds_int s pol x W (toMat Hd.main T) T.vHead (readsAtMain_toMat T)
    headOf := fun x M W => by
      rw [segPol_head]
      exact headPolY_holds_int s pol x W M (ofMat Hd.main M).vHead (readsAtMain_ofMat M) }

theorem segPol_equiv : Spec.segPol_equiv := fun s pol W x =>
  ⟨fun M => equivPol_of s pol (segPol s pol) (segsPol_ok s pol) W x M,
    fun T => equivPol_to s pol (segPol s pol) (segsPol_ok s pol) W x T⟩

theorem segPol_admit : Spec.segPol_admit := by
  intro s pol i x T h
  obtain ⟨hr, hb, hc⟩ :
    x.r < x.e ∧ Cm.Below 129 T ∧ LedgerRel.Cond Gl.p (ppOf s pol) i.mat x T := h
  exact ⟨hr,
    fun q hq =>
      (Cm.lay_below Hd.main mainOK 129 T (by norm_num)).1 ((lay_below_main 129 T).1 hb) q hq,
    ((segPol_equiv s pol i.mat x).2 T).1 hc⟩

theorem segPol_force : Spec.segPol_force := by
  intro s pol i x M hr hb hc
  refine ⟨hr, (lay_below_main (2 ^ 18) _).2 fun n hn => ?_,
    ((segPol_equiv s pol i.mat x).1 M).2 hc⟩
  show |Cm.Seg.get (ofMat Hd.main M) n| < 2 ^ 18
  rw [Cm.lay_ofMat_get]
  unfold Cm.Seg.rd
  rw [if_pos hn]
  exact hb n.place (Cm.lay_inShape Hd.main mainOK n hn)

theorem segPol_noReply : Spec.segPol_noReply := fun s pol k hk x x' h => by
  rw [segPol_ne s pol (by omega)]
  exact TS.no_reply s k hk x x' h

end Policy
