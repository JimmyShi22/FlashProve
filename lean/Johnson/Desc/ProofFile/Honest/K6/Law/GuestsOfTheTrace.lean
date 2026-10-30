--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/GuestsOfTheTrace.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE PREMISE hw OF `k6_guests_of_input` (Honest/K6/Law/GuestsOfInput.lean) EXCHANGED FOR A FINER ONE,
hβ. hβ STAYS A PREMISE, BEARS THE WEIGHT: that the input's trace, read by cells, is cellOf at
theTrace at a served instance read off the input's own bytes: owed at the filling that is run. AN
EXCHANGE, NOT A PAYMENT. No definition; six theorems.

What hβ says. Under Vd w there are an index i and an instance xI with: the library's reader of an
instance off the two files' bytes (`ProofFile.instOf`, Johnson/Desc/ProofFile/InstOf.lean) reads xI off
the input's own w.x; i serves xI (`ServesAt`); what the cells' reader makes of the input's trace is
the library's reader by labels (`cellOf`) at the library's full-size trace with its planes
(`theTrace`, Johnson/HonestTrace/FullPlanes.lean) at i and xI; the head's weights off w.w₀ are i's.
GENERAL in the types W₀, Rc, Tr and in the two readers: so it can be held against a filling whose
trace is of the library's type (cells: cellOf) and against one whose trace is a reader of cells
already (cells: the identity).

  `k6_request_ext`          two requests with the same three fields are one
  `k6_request_of_instOf`    THE INSTANCE's TWO SPELLINGS, under h: where instOf reads xI off ξ, the
                            request that the head's seat reads off the first state is reqX xI, and
                            the token of the reply that is asked about is xI's. It names nothing of
                            K6: a corollary of `instOf_agrees`: its authors' if they want it
  `k6_seg_at_head`          under h, hG: the segment that the honest side's numbers name is 24
  `k6_hw_of_theTrace`       h, hG, hβ ⊢ hw
  `k6_guests_of_theTrace`   h, hG, the thread, hβ ⊢ the field guests of `K6HeadBelow`
  `k6_beta_of_hinge`        A COROLLARY FROM A FORM: the library's `TraceHinge`
                            (Johnson/HonestTrace/TraceHinge.lean) at a letter trace, and the like
                            ties at that function's answer ⊢ hβ

What it is not.
  * hβ IS PAID BY NOBODY AT A FILLING THAT IS RUN. It is a premise on the prover's input (w.trace,
    w.w₀, w.x). No law may take it unseen.
  * hβ ASKS THE WHOLE READER (an equation of two readers, at all numbers, labels, rows and columns);
    hw needs the head's four ranges of list 24 alone: whoever cannot pay hβ can still pay hw.
  * `TraceHinge` BY ITSELF IS A FORM AND NO DEBT: in `k6_beta_of_hinge` the letter trace is tied to
    no prover and no filling; a function that never answers meets the form, and then the second
    premise cannot be met where Vd w holds.
  * The weights' tie stays a clause of hβ here.
  * THAT THE THREAD STANDS AT ANY RUN: by nothing that we hold.
  * h: the full size and the format's second hash function alone.
  * InstOf.lean is not in the library yet: by its authors' own mark: compiled, not yet attacked.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure; it imports
    Johnson/Goal/Meaning/HeadStartScope.lean by name and calls `T_in_scope`, `V_public` and
    `numbers_in_scope`, which are declared in that folder.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.GuestsOfInput
import Johnson.Desc.ProofFile.Honest.K6.Law.ReaderAtTheTrace
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsScope
import Johnson.Desc.ProofFile.InstOf
import Johnson.Goal.Meaning.HeadStartScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (trFull theTrace cellOf ServesAt TraceHinge)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headWit' headWhereOf headTensorOf ReaderMeets headTable_at_blank
  planes_served_reader_at_theTrace)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}

/-- Two requests with the same three fields are one. -/
theorem k6_request_ext : ∀ (a b : Request), a.tok = b.tok → a.r = b.r → a.e = b.e → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- CONDITIONAL: the hypothesis h. **THE INSTANCE's TWO SPELLINGS.** It names nothing of K6 but the
head's own requestOf and reqX: a corollary of instOf_agrees: its authors' if they want it. -/
theorem k6_request_of_instOf (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {ξ : ProofFile.Inst}
    {xI : Instance ppref} (hi : ProofFile.instOf ξ = some xI) :
    requestOf (ProofFile.startS Zp ξ.pub) = reqX xI ∧
      OnBytes.Desc.Reply.tokOf ξ.asked = xI.y.val := by
  have N := InScope.numbers_in_scope h.scope h.reads h.pubOne
  have hT : Zp.p.X.T = ppref.T := by
    show (At.X Zp).T = ppref.T
    rw [InScope.T_in_scope h.scope h.reads h.pubOne, N.lt]
    rfl
  have hV : Zp.p.X.P.h.V = ppref.V := by
    show (At.X Zp).P.h.V = ppref.V
    rw [InScope.V_public h.pubOne, N.V]
    rfl
  obtain ⟨-, r1, r2, r3, r4, r5, -, -⟩ := ProofFile.instOf_agrees hT hV hi
  refine ⟨k6_request_ext _ _ (funext fun t => ?_) r1 r2, r5⟩
  show (requestOf (ProofFile.startS Zp ξ.pub)).tok t = if t < ppref.T then xI.tok t else 0
  by_cases ht : t < ppref.T
  · rw [if_pos ht, show xI.tok t = (xI.prompt ⟨t, ht⟩).val from dif_pos ht]
    exact r3 ⟨t, ht⟩
  · rw [if_neg ht]
    exact r4 t (Nat.le_of_not_lt ht)

/-- CONDITIONAL: h; hG. The segment that the honest side's numbers name is number 24. -/
theorem k6_seg_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : (headWhereOf Zp G).seg = 24 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have Tb := headTable_at_blank h.scope h.reads O (congrArg Prod.fst h.toAtMg.plans_written)
  show Bs.G₀.built.size - 1 = 24
  rw [Tb.size]

/-- hβ STAYS A PREMISE, BEARS THE WEIGHT: that the input's trace, read by cells, is cellOf at
theTrace at a served instance read off the input's own bytes: owed at the filling that is run.
CONDITIONAL: the hypothesis h; hG; hβ. **hw OF k6_guests_of_input FROM hβ**, general in the types W₀
Rc Tr and in the two readers. -/
theorem k6_hw_of_theTrace (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr : Type}
    (cells : Tr → ProofFile.Honest.Cells) (weights : W₀ → ProofFile.Honest.Weights) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hβ : Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ProofFile.instOf w.x = some xI ∧
      ServesAt (At.X Zp) i xI ∧ cells w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ ∧
      (letI := sizesOf (At.X Zp).hS
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v)) :
    Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref) (pl : ℕ → ℕ → ℕ → ℤ),
      (∀ k r c, pl k r c = 0 ∨ pl k r c = 1) ∧ ServesAt (At.X Zp) i xI ∧
      (letI := sizesOf (At.X Zp).hS
       ReaderMeets (At.X Zp) (headWhereOf Zp G) (cells w.trace) (trFull (At.X Zp) pl i xI) ∧
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v) ∧
      requestOf (ProofFile.startS Zp w.x.pub) = reqX xI ∧
      OnBytes.Desc.Reply.tokOf w.x.asked = xI.y.val := by
  intro hVd
  obtain ⟨i, xI, hi, Sv, hcell, hc⟩ := hβ hVd
  letI : Sizes := sizesOf (At.X Zp).hS
  have eW : G.W = (At.X Zp) := ground_of_blank hG
  obtain ⟨pl, h01, -, hM⟩ := planes_served_reader_at_theTrace h.scope h.reads h.pubOne Sv
    (headWhereOf Zp G) (k6_seg_at_head h hG) (by show G.W.hS = _; rw [eW]) rfl
  obtain ⟨q1, q2⟩ := k6_request_of_instOf h hi
  refine ⟨i, xI, pl, h01, Sv, ⟨?_, hc⟩, q1, q2⟩
  rw [hcell]
  exact hM

/-- hβ, THIS THEOREM's END, STAYS A PREMISE, BEARS THE WEIGHT: that the input's trace, read by
cells, is cellOf at theTrace at a served instance read off the input's own bytes: owed at the
filling that is run. A COROLLARY FROM A FORM.
In it the letter trace is tied to no prover and no filling. -/
theorem k6_beta_of_hinge {W₀ Rc Tr : Type} (cells : Tr → ProofFile.Honest.Cells)
    (weights : W₀ → ProofFile.Honest.Weights) (G : ProofFile.Ground) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    {trace : Cm.Idx → ProofFile.Inst → Option OnBytes.HonestTrace.Tr}
    (Hg : TraceHinge (At.X Zp) trace ProofFile.instOf)
    (hα : Vd w → ∃ (i : Cm.Idx) (ω : OnBytes.HonestTrace.Tr), trace i w.x = some ω ∧
      cells w.trace = ⟨cellOf (At.X Zp) ω⟩ ∧
      (letI := sizesOf (At.X Zp).hS
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v)) :
    Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ProofFile.instOf w.x = some xI ∧
      ServesAt (At.X Zp) i xI ∧ cells w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ ∧
      (letI := sizesOf (At.X Zp).hS
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v) := by
  intro hVd
  obtain ⟨i, ω, ht, hcell, hc⟩ := hα hVd
  obtain ⟨xI, hx, Sv, hω⟩ := Hg i w.x ω ht
  exact ⟨i, xI, hx, Sv, by rw [hcell, hω], hc⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- hβ STAYS A PREMISE, BEARS THE WEIGHT: that the input's trace, read by cells, is cellOf at
theTrace at a served instance read off the input's own bytes: owed at the filling that is run.
CONDITIONAL: the hypothesis h; hG; the thread; hβ. **THE FIELD guests OF `K6HeadBelow` FROM hβ.** -/
theorem k6_guests_of_theTrace (cells : Tr → ProofFile.Honest.Cells) (weights : W₀ → ProofFile.Honest.Weights)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hβ : Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ProofFile.instOf w.x = some xI ∧
      ServesAt (At.X Zp) i xI ∧ cells w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ ∧
      (letI := sizesOf (At.X Zp).hS
       ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
         (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v)) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    letI : Given := (headWit' cells weights Zp G m.st.input).given
      (parOf (At.X Zp).hS (workOf (At.X Zp))) m.st.heard
    CornerGuests (headWit' cells weights Zp G m.st.input).cells.toCells :=
  k6_guests_of_input h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights hG
    (k6_hw_of_theTrace h cells weights hG w Vd hβ)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_request_ext
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_request_of_instOf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_seg_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_hw_of_theTrace
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_beta_of_hinge
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_guests_of_theTrace
