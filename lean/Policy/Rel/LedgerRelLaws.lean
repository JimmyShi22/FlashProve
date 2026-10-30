-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerRelLaws.lean

The laws of the relation pair with the cost ledger (Policy/Rel/LedgerRel.lean), under the conditions
told below: nothing wraps around, and both languages are "true under the policy", with the honest
trace as a witness.

The statements are in `Policy.Spec`, each told in its docstring, in three layers.
1. The head alone, for every prime p with 2^61 - 1 ≤ p: `ledger_head_honest`, `ledger_head_noWrap`
   (from Policy/Rel/LedgerHeadHonest.lean and Policy/Rel/LedgerHeadNoWrap.lean).
2. The whole model, for every such prime and every table with `LedgerRel.TableOK`: `ledger_noWrap`
   and `ledger_honest`; then `ledger_forces`, `ledger_trace_iff`, `ledger_admits`, `ledger_lang`.
   `ledger_sub` is for every p and table.
3. At p = 2^64 - 2^32 + 1: `ledger_relation_at_protocol_prime`.

Limits:
* The statements are on a relation, not on a protocol.
* They use the constants of Inst/Model/Head/ (cost = gap + 2^8; the step table: `EX`,
  Inst/Model/Tables.lean).
* They do not say that some request is true under a policy, nor that the relation is not everything:
  Policy/Rel/LedgerGuards.lean and Policy/Rel/PosGuards.lean do, at the policies named there.
* What the heads of Policy/Rel/True.lean and Policy/Rel/LedgerRel.lean list as not said is not said
  here either.
-/
import Cm.RelProofs
import Cm.TargetPRelProofs
import Policy.Rel.LedgerRel
import Policy.Rel.LedgerHeadHonest
import Policy.Rel.LedgerHeadNoWrap

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.Spec

open Inst.Model Inst.Model.All

/-! ## 1. The head alone -/

/-- For a prime p with 2^61 - 1 ≤ p: under `Head.N.HonIn` the honest cells meet the field relation
of the head modulo p. -/
def ledger_head_honest : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ (np : NormPar) (X : ℕ → Vec) (H : Mat) (y : Head.Req), Head.N.HonIn np X H y →
      LedgerHead.RF (F := ZMod p) np (fun j v => ((H j v : ℤ) : ZMod p)) y
        (Head.N.honCells np X H y)

/-- For a prime p with 2^61 - 1 ≤ p, a valid final normalisation, an output matrix with entries at
most 2^12 in absolute value and a policy with `AcceptancePolicy.OK`: if cells t meet the field relation of the
head modulo p, the stream that they hold is below 2^39 in absolute value; and for every stream X
that they hold, the final normalisation of X runs at every position, and the policy's clauses hold
of the logits of X. -/
def ledger_head_noWrap : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ np : NormPar, np.OK → ∀ H : Mat, (∀ j v, |H j v| ≤ 2 ^ 12) → ∀ pol : AcceptancePolicy, pol.OK →
      ∀ (x : Instance ppref) (t : Head.Cells ℤ),
        LedgerHead.RF (F := ZMod p) np (fun j v => ((H j v : ℤ) : ZMod p)) (Head.Req.of pol x) t →
        (∀ i < Head.nT, ∀ j < Head.nD, |Head.xAt t i j| < 2 ^ 39) ∧
        ∀ X : ℕ → Vec, (∀ i < Head.nT, ∀ j < Head.nD, Head.xv t j i = X i j) →
          (∀ pos < Head.nT, NORM.OK np Head.nD (X pos)) ∧
          PolOK (fun i v => dot Head.nD (NORM.out np Head.nD (X i)) fun j => H j v) pol x

/-! ## 2. The whole model, at a variable prime

But for `ledger_sub`, each statement is for a prime p with 2^61 - 1 ≤ p and a
table pp with `LedgerRel.TableOK`. -/

/-- Nothing wraps around: if the cells are below 2^18 and meet the conditions modulo p, the integer
program at the table runs and the table's policy holds of its logits. -/
def ledger_noWrap : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref) (T : Trace),
        Cm.Below (2 ^ 18) T → LedgerRel.Cond p pp i.mat x T →
        ModelR ppref pp.kap pp.nf (fun _ => tbRef) pp.pol i.weights x

/-- If the integer program at the table runs and the table's policy holds (and y = 0 if
e < `ppref.T`), the honest trace has cells below 129 and meets the conditions modulo p; r < e is not
asked here. -/
def ledger_honest : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref), (x.e < ppref.T → x.y.val = 0) →
        ModelR ppref pp.kap pp.nf (fun _ => tbRef) pp.pol i.weights x →
        Cm.Below 129 (Cm.trace pp i x) ∧ LedgerRel.Cond p pp i.mat x (Cm.trace pp i x)

/-- Ryes ⊆ Rno, at every p and every table -/
def ledger_sub : Prop :=
  ∀ (p : ℕ) (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) (T : Trace),
    LedgerRel.Ryes p pp i x T → LedgerRel.Rno p pp i x T

/-- every witness of the relaxation shows `RinfPP pp` at the index that the matrix holds -/
def ledger_forces : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref) (T : Trace),
        LedgerRel.Rno p pp i x T → RinfPP pp i.index x

/-- the honest trace is a witness of the relation exactly where `RinfPP pp` holds -/
def ledger_trace_iff : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref),
        LedgerRel.Ryes p pp i x (Cm.trace pp i x) ↔ RinfPP pp i.index x

/-- if there is a witness, the honest trace is one -/
def ledger_admits : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref) (T : Trace),
        LedgerRel.Ryes p pp i x T → LedgerRel.Ryes p pp i x (Cm.trace pp i x)

/-- both languages are `RinfPP pp` -/
def ledger_lang : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ pp : ScalesAndPolicy, LedgerRel.TableOK pp →
      ∀ (i : Cm.Idx) (x : Instance ppref),
        ((∃ T, LedgerRel.Ryes p pp i x T) ↔ RinfPP pp i.index x) ∧
        ((∃ T, LedgerRel.Rno p pp i x T) ↔ RinfPP pp i.index x)

/-! ## 3. At the protocol's prime -/

/-- The relation at the protocol's prime. At every lawful table s of scales and every policy with C,
θ < 2^40 and cap < 2^16, with the conditions formed modulo 2^64 - 2^32 + 1: every relaxed witness of
the pair with the cost ledger shows that the request is true under the policy (the integer program
runs, the request has its form, the policy's three clauses hold of its logits, at the cost
gap + 2^8); and at every such request the honest trace is a strict witness. On a relation, not on a
protocol. -/
def ledger_relation_at_protocol_prime : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ (i : Cm.Idx) (x : Instance ppref),
      (∀ T : Trace, LedgerRel.Rno (2 ^ 64 - 2 ^ 32 + 1) (ppOf s pol) i x T →
        IsTrueUnder s pol i x) ∧
      (IsTrueUnder s pol i x →
        LedgerRel.Ryes (2 ^ 64 - 2 ^ 32 + 1) (ppOf s pol) i x (Cm.trace (ppOf s pol) i x))

end Policy.Spec

namespace Policy

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef)

/-! ## 1. The head alone -/

theorem ledger_head_honest : Spec.ledger_head_honest := fun p _ _ _ _ _ _ h =>
  LedgerHead.hon_rf p h

theorem ledger_head_noWrap : Spec.ledger_head_noWrap := fun p _ hB _ hn _ hH _ hpol _ _ h =>
  haveI : Cm.TI.Big p := ⟨hB⟩
  LedgerHead.noWrap_pol (LedgerHead.rfz_of_rf h) hn hH hpol

/-! ## 2. The whole model, from the head and the library's theorems on the layers -/

/-- a lawful `ScalesAndPolicy` meets `TableOK` -/
theorem tableOK_of_lawful {pp : ScalesAndPolicy} (h : Lawful pp) : LedgerRel.TableOK pp :=
  ⟨⟨h.ff, h.sh, h.one, h.nf, h.km⟩, h.polOK⟩

theorem tableOK_ppOf {s : Cm.Scales} (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : PolCond pol) :
    LedgerRel.TableOK (ppOf s pol) :=
  ⟨hs, hpol⟩

theorem ledger_lawfulK {pp : ScalesAndPolicy} (h : LedgerRel.TableOK pp) :
    LawfulK pp.kap pp.nf fun _ => tbRef :=
  h.scales.lawfulK

/-- `RinfPP` at the index that a matrix holds: the request's form, and `ModelR` -/
theorem rinfPP_idx (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref) :
    RinfPP pp i.index x ↔
      Head3 x ∧ ModelR ppref pp.kap pp.nf (fun _ => tbRef) pp.pol i.weights x :=
  RinfPP_iff pp i.index x

/-- bound and conditions give the field relation of the head -/
theorem ledger_headRF {p : ℕ} {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} {T : Trace}
    (b : Cm.Below (2 ^ 18) T) (c : LedgerRel.Cond p pp i.mat x T) :
    LedgerHead.RF (F := ZMod p) pp.nf (Cm.TP.castH p i.mat) (Head.Req.of pp.pol x) T.vHead :=
  ⟨fun j hj => ⟨b.hf j hj, b.hd j hj, b.hr j hj, fun _ hφ => b.toBelowL.headX hφ hj⟩,
    c.headKey, c.headIdn, c.headJc, c.headSums⟩

theorem ledger_noWrap : Spec.ledger_noWrap := by
  intro p hp hB pp hpp i x T b c
  haveI : Cm.TI.Big p := ⟨hB⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hL := ledger_lawfulK hpp
  obtain ⟨hlast, hpol⟩ := ledger_head_noWrap p hp hB pp.nf hL.nf i.weights.H (abs_H i.wf) pp.pol
    hpp.pol x T.vHead (ledger_headRF b c)
  have hR : Cm.Lay.RFL p pp.kap pp.nf (fun _ => tbRef) i.mat (tokOf x.prompt) T :=
    ⟨fun g hg => ⟨fun a => b.ff g hg a.val a.property, c.ffKey g hg, c.ffIdn g hg⟩,
      fun g hg => ⟨fun a ha => b.att g hg a ha, c.attKey g hg, c.attIdn g hg⟩, hlast⟩
  have hS := Cm.TP.Lay.stream_eqK (p := p) hL i.wf hR
  have hx : ∀ a < Head.nT, ∀ j < Head.nD, Head.xv T.vHead j a =
      XK ppref pp.kap (tbsOf fun _ => tbRef) (Layout.weightsOf ppref kRef i.mat) x.prompt
        (2 * ppref.layers) a j := fun a ha j hj => by
    rw [T.x_head hj ha]
    exact hS 11 (by decide) 8 le_rfl a ha j hj
  have h12 := hpol _ hx
  have hrun : RunsK ppref pp.kap pp.nf (tbsOf fun _ => tbRef)
      (Layout.weightsOf ppref kRef i.mat) x.prompt :=
    Cm.TP.Lay.runsK_of (p := p) (T := T) hL i.wf hR h12.1
  exact ⟨hrun, h12.2⟩

theorem ledger_honest : Spec.ledger_honest := by
  intro p hp hB pp hpp i x hy hm
  haveI : Cm.TI.Big p := ⟨hB⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hL := ledger_lawfulK hpp
  have hff := fun g (hg : g < nGr) => ffK_honest (p := p) hL i.wf hm.1 hg
  have hatt := fun g (hg : g < nGr) => attK (W := i.mat) (prompt := x.prompt) hL hg
  have hin : Head.N.HonIn pp.nf (xsK pp.kap (fun _ => tbRef) i.mat x.prompt 11 8)
      (Layout.weightsOf ppref kRef i.mat).H (Head.Req.of pp.pol x) :=
    Head.N.honIn_stream hL.nf (abs_H i.wf) hm.1.2 (Head.Req.of_ok pp.pol x)
      (Head.Policy.polOK_inst hm.2) hpp.pol.C hpp.pol.theta hpp.pol.cap
  have hv : (Cm.trace pp i x).vHead =
      Head.N.honCells pp.nf (xsK pp.kap (fun _ => tbRef) i.mat x.prompt 11 8)
        (Layout.weightsOf ppref kRef i.mat).H (Head.Req.of pp.pol x) :=
    vHead_honTK _ _ _ _ _ _
  have hF : ∀ g (hg : g < nGr), (Cm.TP.segFF p pp.kap pp.nf g).RF (tokOf x.prompt)
      (Cm.TP.castW p i.mat) fun c => (Cm.trace pp i x).vFF g c.val := fun g hg => by
    unfold Cm.trace
    rw [vFF_honTK]
    exact (hff g hg).1
  have hA : ∀ g (hg : g < nGr),
      AttSeg.RFraw (scl := SFK pp.kap pp.nf g) (DAK pp.kap g) tbRef (ZMod p)
        ((Cm.trace pp i x).vAtt g) := fun g hg => by
    unfold Cm.trace
    rw [vAtt_honTK]
    exact AttSeg.rfraw_of_int (scl := SFK pp.kap pp.nf g) (DAK pp.kap g) tbRef _ (ZMod p)
      (hatt g hg).1
  have hH : LedgerHead.RF (F := ZMod p) pp.nf (Cm.TP.castH p i.mat) (Head.Req.of pp.pol x)
      (Cm.trace pp i x).vHead := by
    rw [hv]
    exact ledger_head_honest p hp hB _ _ _ _ hin
  refine ⟨⟨⟨fun g hg c hc => ?_, fun g hg c hc => ?_⟩,
      fun a ha φ hφ => ?_, fun a ha φ hφ => ?_,
      fun a ha φ hφ => ?_⟩,
    ⟨⟨fun g hg => (hF g hg).2.1, fun g hg => (hF g hg).2.2,
        fun g hg => (hA g hg).2.1, fun g hg => (hA g hg).2.2⟩,
      hH.keys, hH.idns, hH.jc, hH.sums,
      fun he => (Cm.TP.y_zero_iff (p := p) x).2 (hy he)⟩⟩
  · unfold Cm.trace
    rw [vFF_honTK]
    exact Int.lt_add_one_iff.2 ((hff g hg).2 c hc)
  · unfold Cm.trace
    rw [vAtt_honTK]
    exact Int.lt_add_one_iff.2 ((hatt g hg).2 c hc)
  · exact Int.lt_add_one_iff.2 ((Head.N.hon_cells_le hin ha).1 φ hφ)
  · exact Int.lt_add_one_iff.2 ((Head.N.hon_cells_le hin ha).2.1 φ hφ)
  · exact Int.lt_add_one_iff.2 ((Head.N.hon_cells_le hin ha).2.2.1 φ hφ)

theorem ledger_sub : Spec.ledger_sub := fun _ _ _ _ _ h =>
  ⟨h.1, h.2.1.mono (by norm_num), h.2.2⟩

theorem ledger_forces : Spec.ledger_forces := fun p hp hB pp hpp i x T hR =>
  haveI : Cm.TI.Big p := ⟨hB⟩
  haveI : Fact p.Prime := ⟨hp⟩
  (rinfPP_idx pp i x).2
    ⟨(Cm.TP.form_iff (p := p) x).1 ⟨hR.1, hR.2.2.yZero⟩,
      ledger_noWrap p hp hB pp hpp i x T hR.2.1 hR.2.2⟩

theorem ledger_trace_iff : Spec.ledger_trace_iff := fun p hp hB pp hpp i x =>
  ⟨fun hR => ledger_forces p hp hB pp hpp i x _ (ledger_sub p pp i x _ hR),
    fun ht =>
      ⟨((rinfPP_idx pp i x).1 ht).1.1,
        ledger_honest p hp hB pp hpp i x ((rinfPP_idx pp i x).1 ht).1.2.2
          ((rinfPP_idx pp i x).1 ht).2⟩⟩

theorem ledger_admits : Spec.ledger_admits := fun p hp hB pp hpp i x T hR =>
  (ledger_trace_iff p hp hB pp hpp i x).2
    (ledger_forces p hp hB pp hpp i x T (ledger_sub p pp i x T hR))

theorem ledger_lang : Spec.ledger_lang := fun p hp hB pp hpp i x =>
  ⟨⟨fun ⟨T, hR⟩ => ledger_forces p hp hB pp hpp i x T (ledger_sub p pp i x T hR),
      fun ht => ⟨_, (ledger_trace_iff p hp hB pp hpp i x).2 ht⟩⟩,
    ⟨fun ⟨T, hR⟩ => ledger_forces p hp hB pp hpp i x T hR,
      fun ht => ⟨_, ledger_sub p pp i x _ ((ledger_trace_iff p hp hB pp hpp i x).2 ht)⟩⟩⟩

/-! ## 3. At the protocol's prime -/

theorem ledger_gl_big : 2 ^ 61 - 1 ≤ Code.pGold := by decide +kernel

theorem ledger_relation_at_protocol_prime : Spec.ledger_relation_at_protocol_prime :=
  fun _ hs _ hpol i x =>
    ⟨fun T h =>
        ledger_forces Code.pGold Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x T h,
      fun h =>
        (ledger_trace_iff Code.pGold Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol)
          i x).2 h⟩

end Policy
