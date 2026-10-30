-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TraceFull.lean: CONDITIONAL: ONE NAMED PREMISE ON THE TRACE,
AND WHAT FOLLOWS FROM IT. TraceIsFull gives two premises of attention's joined law on K5's member at
a Script laid from lots: hqa and hSm; nothing goes back. IT PAYS NOTHING: what is won is a name that
a payer can aim at: one sentence on the trace in the library's own terms. Under the library's head
on the public input (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). No filling is named, and no thread. One
definition, a premise's form; seven statements with their proofs.

  TraceIsFull         THE FORM, TraceIsFull X Vd cells: at each input v that meets Vd there are pl,
                      an index i and a request x that is served (ServesAt,
                      Johnson/HonestTrace/Full.lean) such that the trace's reader has, at each
                      segment of a proof with 12 groups and each matrix's label OFF THE PLANES, the
                      image in the field of the entry of the library's own full-size trace trFull X
                      pl i x
  hqa_of_traceIsFull · hSm_of_traceIsFull   the two premises from the form
  traceIsFull_of_hinge   THE FORM FOLLOWS FROM TraceHinge (Johnson/HonestTrace/TraceHinge.lean) AND
                      hV
  traceIsFull_of_cellOf   a reader that is the library's reader by labels (cellOf) of such a trace
                      meets the form
  noAt_ff_bNo_iff · noAt_att_bNo_iff · noAt_head_bNo_iff   THE FENCE a ≠ bNo X (σ.no 12) SHUTS OUT
                      JUST THE PLANES' NAME (b, bA, bH), at every X

The premises. h: the head · hg: g is below 12 · hT: the form · hC: the reader is cellOf of such a
trace · H: TraceHinge · hV: at a valid input the hinge's function answers at the input's own
instance, and the input's reader is cellOf of what it answers · ha: a is the plan of group g · hS,
hL: the seat has the plan's shape and the attention sub-proof's number.

HOW TraceHinge AND THE FORM PART: TraceHinge is on an integer trace as a function of an index and an
input; it reads the request off the input; the index is the function's own first argument, which
nothing ties to the input; it has the planes; it goes one way: where the trace is there. TraceIsFull
is on a valid input's reader of cells; untied; off the planes. BETWEEN THEM STANDS hV.

How. Sealed, in Johnson/Goal/HonestTrace/FullInScope.lean: cellOf_label_in_scope; borrowed_in_scope:
an attention sub-proof's qa is its group's, served or not; small_off_planes_in_scope: at a served
request every entry off the planes' number is below 129 in absolute value. The fence: bNo_even,
bNo_odd, bNo_head (Full.lean) and MatName.no?_inj (Johnson/HonestTrace/Names.lean).
hSm_of_traceIsFull has the steps of cellsSmallQ_of_int (CellsSmallOfInt.lean in this folder),
unfolded, with labelOf_label (PackedAtSeg.lean) and val_eOfF (PackedVals.lean).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. hT, hC, H AND hV ARE PREMISES HERE: THIS FILE PAYS NONE. pl, i and x stand
under "there is", behind "for all v": NOTHING TIES i TO THE INPUT's INDEX OR x TO ITS REQUEST: the
form is no word on the committed weights. It speaks of all 25 segments' matrices off the planes,
where K5 at group g spends two segments'. NOTHING AT A PLANE's NUMBER. hqa_of_traceIsFull does not
spend the serving. At a Vd that holds of no input the form asks nothing; that an input's trace is
such a trace is not proved here. In traceIsFull_of_hinge trace and instOf are letters that nothing
ties to a filling; the function that never answers meets the hinge, and then hV fails at every valid
input. The docstring of TraceHinge names a function that meets it (fullTrace, in two files of the
frame's folder): these two files are not imported. All is at the library's full size: 12 groups, and
the numbers of parts of parts_in_scope. At the earlier hash OnBytes.secondHashFunction, a fixed function.
Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under
ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. No property of a prover or a protocol is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQRaw
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedAtSeg
import Johnson.HonestTrace.TraceHinge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

section
open OnBytes.Maker (WholeD)
open OnBytes.Model.Layer (matIx)
open OnBytes.HonestTrace (Sz MatName noAt bNo bNo_even bNo_odd bNo_head nameNo_isSome
  nameNo_eq_some_iff parts_in_scope trFull cellOf_label_in_scope borrowed_in_scope
  small_off_planes_in_scope)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (szOf)
open P5J (AtMgA TS)

/-- **In a group's list the planes' number is the number of the name b, and of no other name.** -/
theorem noAt_ff_bNo_iff (X : OnBytes.Model.Verify.Public) {g : ℕ} (hg : g < 12) {μ : MatName}
    {a : ℕ} (ha : noAt X (.ff g) μ = some a) : a = bNo X (2 * g) ↔ μ = .b := by
  have hb : noAt X (.ff g) .b = some (bNo X (2 * g)) := by
    rw [bNo_even X hg]
    rfl
  constructor
  · intro e
    rw [e] at ha
    exact MatName.no?_inj ha hb
  · intro e
    rw [e, hb] at ha
    exact (Option.some.inj ha).symm

/-- **The like in an attention sub-proof's list: bA.** -/
theorem noAt_att_bNo_iff (X : OnBytes.Model.Verify.Public) (g : ℕ) {μ : MatName} {a : ℕ}
    (ha : noAt X (.att g) μ = some a) : a = bNo X (2 * g + 1) ↔ μ = .bA := by
  have hb : noAt X (.att g) .bA = some (bNo X (2 * g + 1)) := by
    rw [bNo_odd]
    show some ((OnBytes.Road.Hd.shapeA X ((2 * g + 1) / 2)).cf.NAs + 2) = _
    rw [show (2 * g + 1) / 2 = g by omega]
  constructor
  · intro e
    rw [e] at ha
    exact MatName.no?_inj ha hb
  · intro e
    rw [e, hb] at ha
    exact (Option.some.inj ha).symm

/-- **The like in the head's list: bH.** -/
theorem noAt_head_bNo_iff (X : OnBytes.Model.Verify.Public) {μ : MatName} {a : ℕ}
    (ha : noAt X .head μ = some a) : a = bNo X 24 ↔ μ = .bH := by
  have hb : noAt X .head .bH = some (bNo X 24) := by
    rw [bNo_head]
    rfl
  constructor
  · intro e
    rw [e] at ha
    exact MatName.no?_inj ha hb
  · intro e
    rw [e, hb] at ha
    exact (Option.some.inj ha).symm

section
open Inst.Model Inst.Model.All

/-- PAID BY NOBODY. **THE TRACE IS, OFF THE PLANES, THE LIBRARY's OWN FULL-SIZE TRACE AT SOME SERVED
REQUEST.** It is meant as a corollary of the thread's test on inputs, once that has a text, and of
`TraceHinge` (Johnson/HonestTrace/TraceHinge.lean) at the filling that is run: see
`traceIsFull_of_hinge`. pl, i and x stand under "there is": nothing ties them to the input. The
fence a ≠ bNo X (σ.no 12) shuts out just the planes' name (the three theorems above). It is a
definition: a premise's form, on the trace alone. Nothing is claimed of it, and nothing proves that
it can be met. -/
def TraceIsFull (X : OnBytes.Model.Verify.Public) {W₀ Rc Tr : Type}
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (cells : Tr → Cells) : Prop :=
  ∀ v, Vd v → ∃ (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref),
    OnBytes.HonestTrace.ServesAt X i x ∧
      ∀ (σ : OnBytes.HonestTrace.Seg) (μ : OnBytes.HonestTrace.MatName) (a : ℕ), σ.Below 12 →
        OnBytes.HonestTrace.noAt X σ μ = some a →
        a ≠ OnBytes.HonestTrace.bNo X (σ.no 12) → ∀ r c,
        (cells v.trace).cell (σ.no 12) μ.label r c =
          ((OnBytes.HonestTrace.trFull X pl i x (σ.no 12) a r c : ℤ) : Cb.Gl.F)

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

section
open Inst.Model Inst.Model.All

include h in
/-- hC IS PAID BY NOBODY. **A reader that is the library's reader by labels of such a trace meets
the form.** CONDITIONAL: under the hypothesis h; hC. -/
theorem traceIsFull_of_cellOf {W₀ Rc Tr : Type} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {cells : Tr → Cells}
    (hC : ∀ v, Vd v → ∃ (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx) (x : Instance ppref),
      OnBytes.HonestTrace.ServesAt (P5J.At.X Zp) i x ∧ ∀ l s r c, (cells v.trace).cell l s r c =
        OnBytes.HonestTrace.cellOf (P5J.At.X Zp)
          (OnBytes.HonestTrace.trFull (P5J.At.X Zp) pl i x) l s r c) :
    TraceIsFull (P5J.At.X Zp) Vd cells := by
  intro v hv
  obtain ⟨pl, i, x, hs, e⟩ := hC v hv
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  refine ⟨pl, i, x, hs, fun σ μ a hσ ha _ r c => ?_⟩
  rw [e]
  exact cellOf_label_in_scope h.scope h.reads hX _ hσ ha r c

include h in
/-- H AND hV ARE PAID BY NOBODY. **THE FORM FOLLOWS FROM THE LIBRARY's `TraceHinge`**, where at each
valid input the hinge's function answers, at some index and the input's own instance, a trace of
which the input's reader is the reader by labels. CONDITIONAL: under the hypothesis h; H; hV. trace
and instOf are letters: nothing ties them to a filling. -/
theorem traceIsFull_of_hinge {W₀ Rc Tr : Type} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {cells : Tr → Cells} {trace : Cm.Idx → ProofFile.Inst → Option OnBytes.HonestTrace.Tr}
    {instOf : ProofFile.Inst → Option (Instance ppref)}
    (H : OnBytes.HonestTrace.TraceHinge (P5J.At.X Zp) trace instOf)
    (hV : ∀ v, Vd v → ∃ i ω, trace i v.x = some ω ∧
      ∀ l s r c, (cells v.trace).cell l s r c =
        OnBytes.HonestTrace.cellOf (P5J.At.X Zp) ω l s r c) :
    TraceIsFull (P5J.At.X Zp) Vd cells := by
  intro v hv
  obtain ⟨i, ω, hω, e⟩ := hV v hv
  obtain ⟨x, -, hs, rfl⟩ := H i v.x ω hω
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  refine ⟨OnBytes.HonestTrace.plOf (P5J.At.X Zp) i x, i, x, hs, fun σ μ a hσ ha _ r c => ?_⟩
  rw [e]
  exact cellOf_label_in_scope h.scope h.reads hX _ hσ ha r c

end

include h in
/-- hT IS PAID BY NOBODY. **ONE MATRIX READ ALIKE UNDER TWO SEGMENTS' NUMBERS**: qa, at the group's
segment and at its attention sub-proof's. CONDITIONAL: under the hypothesis h; hT; hg. The serving
is not spent. -/
theorem hqa_of_traceIsFull {W₀ Rc Tr : Type} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {cells : Tr → Cells} (hT : TraceIsFull (P5J.At.X Zp) Vd cells) {g : ℕ} (hg : g < 12) :
    ∀ v, Vd v → ∀ r c, (cells v.trace).cell (2 * g) "qa" r c =
      (cells v.trace).cell (2 * g + 1) "qa" r c := by
  intro v hv r c
  obtain ⟨pl, i, x, -, e⟩ := hT v hv
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  have n0 : noAt (P5J.At.X Zp) (.ff g) .qa = some (matIx (P5J.At.X Zp).y).iQA := rfl
  have n1 : noAt (P5J.At.X Zp) (.att g) .qa =
      some ((OnBytes.Road.Hd.shapeA (P5J.At.X Zp) g).cf.NAs + 3) := by
    show some ((OnBytes.Road.Hd.shapeA (P5J.At.X Zp) ((2 * g + 1) / 2)).cf.NAs + 3) = _
    rw [show (2 * g + 1) / 2 = g by omega]
  have e0 : (cells v.trace).cell (2 * g) "qa" r c =
      ((trFull (P5J.At.X Zp) pl i x (2 * g) (matIx (P5J.At.X Zp).y).iQA r c : ℤ) : Cb.Gl.F) :=
    e (.ff g) .qa _ hg n0 (fun t => by cases (noAt_ff_bNo_iff _ hg n0).1 t) r c
  have e1 : (cells v.trace).cell (2 * g + 1) "qa" r c =
      ((trFull (P5J.At.X Zp) pl i x (2 * g + 1)
        ((OnBytes.Road.Hd.shapeA (P5J.At.X Zp) g).cf.NAs + 3) r c : ℤ) : Cb.Gl.F) :=
    e (.att g) .qa _ hg n1 (fun t => by cases (noAt_att_bNo_iff _ g n1).1 t) r c
  have b : trFull (P5J.At.X Zp) pl i x (2 * g + 1)
      ((OnBytes.Road.Hd.shapeA (P5J.At.X Zp) g).cf.NAs + 3) r c =
      trFull (P5J.At.X Zp) pl i x (2 * g) (matIx (P5J.At.X Zp).y).iQA r c :=
    (borrowed_in_scope h.scope h.reads hX pl i x).2.1 g hg r c
  rw [e0, e1, b]

include h in
/-- hT IS PAID BY NOBODY. **THE TRACE's CELLS ARE SMALL.** CONDITIONAL: under the hypothesis h; hT;
hg; a is the group's plan; the seat has the plan's shape and the attention sub-proof's number. -/
theorem hSm_of_traceIsFull {W₀ Rc Tr : Type} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {cells : Tr → Cells} (hT : TraceIsFull (P5J.At.X Zp) Vd cells) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {Z5 : Seat5}
    (hS : Z5.P.S = a.S) (hL : Z5.link = 2 * g + 1) :
    CellsSmallQ Vd a cells Z5 := by
  intro v hv i c hi hc
  obtain ⟨pl, ix, x, hs, e⟩ := hT v hv
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hX
  have h5 : a.seam.tl.mats.size = 5 := by
    have e5 : (_root_.Meaning.tlAt (P5J.At.X Zp) (2 * g + 1)).mats.size = 5 :=
      _root_.Meaning.size_odd hX C hg
    rw [H2K5.Door.tlAt_att hg ha] at e5
    exact e5
  have hsz : i < 5 := by
    by_contra hn
    have e0 : a.seam.tl.mats.getD i {} = {} := by
      simp [Array.getD, show ¬ i < a.seam.tl.mats.size by omega]
    rw [e0] at hc
    exact absurd hc (Nat.not_lt_zero _)
  obtain ⟨μ, hμ⟩ := nameNo_isSome Sz.ref (σ := .att g) (mu := i) hsz
  have P : (P5J.At.X Zp).y.parts.getD 0 0 = 3 ∧ (P5J.At.X Zp).y.parts.getD 1 0 = 1 ∧
      (∀ g < 12, (OnBytes.Road.Hd.shapeA (P5J.At.X Zp) g).cf.NAs = 1) ∧ (P5J.At.X Zp).hS.NHf = 4 :=
    parts_in_scope h.scope h.reads hX
  obtain ⟨p0, p1, pA, pH⟩ := P
  have eN : a.S.cf.NAs = Sz.ref.NAs := by
    rw [← H2K5.Door.shapeA_at ha]
    exact pA g hg
  have hno : noAt (P5J.At.X Zp) (.att g) μ = some i := by
    have t := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
    show MatName.no? _ _ (OnBytes.Road.Hd.shapeA (P5J.At.X Zp) ((2 * g + 1) / 2)).cf.NAs _ _ _ = _
    rw [p0, p1, pH, show (2 * g + 1) / 2 = g by omega, pA g hg]
    exact t
  have hf : i ≠ bNo (P5J.At.X Zp) (2 * g + 1) := by
    rw [bNo_odd, H2K5.Door.shapeA_at ha, ← hS]
    exact hi
  refine ⟨fun r => trFull (P5J.At.X Zp) pl ix x (2 * g + 1) i r.val c, fun r => ?_, fun r => ?_⟩
  · exact lt_of_lt_of_le
      (small_off_planes_in_scope h.scope h.reads hX pl hs (2 * g + 1) i r.val c hf) (by
        have eb : (szOf a.seam.tl).beta = 2 ^ 17 := rfl
        rw [eb]
        norm_num)
  · have e1 : (cells v.trace).cell (2 * g + 1) μ.label r.val c =
        ((trFull (P5J.At.X Zp) pl ix x (2 * g + 1) i r.val c : ℤ) : Cb.Gl.F) :=
      e (.att g) μ i hg hno hf r.val c
    unfold cellAt
    rw [val_eOfF, hS, hL, labelOf_label eN hμ, e1]
    exact (map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) _).symm

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.noAt_ff_bNo_iff
#print axioms ProofFile.Honest.K5.noAt_att_bNo_iff
#print axioms ProofFile.Honest.K5.noAt_head_bNo_iff
#print axioms ProofFile.Honest.K5.TraceIsFull
#print axioms ProofFile.Honest.K5.traceIsFull_of_cellOf
#print axioms ProofFile.Honest.K5.traceIsFull_of_hinge
#print axioms ProofFile.Honest.K5.hqa_of_traceIsFull
#print axioms ProofFile.Honest.K5.hSm_of_traceIsFull
