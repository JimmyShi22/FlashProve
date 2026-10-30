--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyNumbers.lean: THE STATEMENTS ON PUBLIC NUMBERS that E2E/KeyFirstHalf.lean takes as premises,
gathered in one structure, with a test with code; what they give; and THAT THEY HOLD at the
library's written sizes of a key of the full size (`Lk6.AtPlan.keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean). Definitions, statements and proofs, and tests.

What is defined.
  **`KeyNumbers im x codes lin V a b`**: of the four public values that the premises read (the
    index-mask message's notice, the ranges' item, the codes, the shape of the test on the table):
    both messages have an OOD sample and mask rows, the own one main rows · V ≤ 63 and V is the own
    message's main table's number of bits · the own message's free mask entries are what the lookups
    take and a more; the index-mask message's likewise, b more · every part of every lookup has a
    level · every block's term has V variables.
  `keyNumbersB`: the same as a test with code.
What is shown.
  `numbers_of_B`: where the test is true the structure holds.
  `idxTake_eq`: what the lookups take off the index-mask message's ledger, as E2E/KeyFirstHalf.lean
    counts it, is the library's `Wf.indexMasks`.
  **`KeyNumbers.pile`**: b and `Wf.indexMasks` add up to the index-mask message's free entries: the
    equation of numbers that E2E/KeyLedgers.lean's `pile_count` asks.
  `Hearings`, `linksHeard_of`, **`first_half_at`**: E2E/KeyFirstHalf.lean's `first_half_chain` under
    `KeyNumbers`: what is left as premises: the statement's codes at the start are the plan's · the
    fold over the two sendings accepts · no lookup has written anything · `Hearings`: for each
    lookup the planner's entries, the rounds' fit, the hearing's accept, `Left`, `Off`.
  `layout_at_full`, `terms_full`, **`numbers_full`**: AT THE FULL SIZE `KeyNumbers` HOLDS, at V =
    19, a = 1,978, b = 207: by Lean's kernel, field by field, over the library's `layout_full` for
    the planes' layout (which the kernel does not evaluate by itself).
Tests, by Lean's evaluator, at the full size: the test with code is true at these three numbers.
Negative tests: it is false at V = 18, at a = 1,979 and at b = 206. The numbers one by one: 36,863
free entries and 34,885 taken; 255 and 48; two lookups.

Limits.
- `Hearings` IS A PREMISE: the hearing's accept, `roundsFit`, `Left` and `Off` are shown of no run,
  and no member of `Hearings` with a lookup is typed. That the two sendings accept is a premise too.
- That a key file's parameter bytes read back to these four values is not treated.
- That the statement's codes at the chain's start are the plan's is a premise wherever this is used.
- Nothing on any property.


-/
import E2E.KeyFirstHalf
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLookup
open OnBytes
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key

/-- **The statements on public numbers.** -/
structure KeyNumbers (im : OracleNotice) (x : Params.WfPublic) (codes : Codes)
    (lin : Params.LinShape) (V a b : ℕ) : Prop where
  idxSample : im.shape.answers ≠ 0
  idxMask : 0 < im.shape.maskRows
  ownSample : x.message.shape.answers ≠ 0
  ownMask : 0 < x.message.shape.maskRows
  ownMain : 0 < x.message.shape.mainRows
  small : V ≤ 63
  bits : ceilLog2 x.message.shape.mainRows +
    (codes.base.getD x.message.shape.code default).logEll = V
  own : freeOf codes x.message.shape = ownTake (Wf.lookupsOf x (Wf.matrixOf lin)) + a
  idx : freeOf codes im.shape = idxTake (Wf.lookupsOf x (Wf.matrixOf lin)) + b
  levels : ∀ y ∈ Wf.lookupsOf x (Wf.matrixOf lin), ∀ v ∈ (faceOfLkp y).parts, 1 ≤ v
  terms : ∀ y ∈ (Wf.lookupsOf x (Wf.matrixOf lin)).zipIdx, ∀ bl ∈ blocksOf x codes y.2,
    (termOf x codes y.2 (canon ((faceOfLkp y.1).mu + (faceOfLkp y.1).d)) bl).pairs.length = V

/-- The same as a test with code. -/
def keyNumbersB (im : OracleNotice) (x : Params.WfPublic) (codes : Codes) (lin : Params.LinShape)
    (V a b : ℕ) : Bool :=
  im.shape.answers != 0 && decide (0 < im.shape.maskRows) && x.message.shape.answers != 0 &&
    decide (0 < x.message.shape.maskRows) && decide (0 < x.message.shape.mainRows) &&
    decide (V ≤ 63) &&
    (ceilLog2 x.message.shape.mainRows +
      (codes.base.getD x.message.shape.code default).logEll == V) &&
    (freeOf codes x.message.shape == ownTake (Wf.lookupsOf x (Wf.matrixOf lin)) + a) &&
    (freeOf codes im.shape == idxTake (Wf.lookupsOf x (Wf.matrixOf lin)) + b) &&
    ((Wf.lookupsOf x (Wf.matrixOf lin)).all fun y =>
      (faceOfLkp y).parts.all fun v => decide (1 ≤ v)) &&
    ((Wf.lookupsOf x (Wf.matrixOf lin)).zipIdx.all fun y => (blocksOf x codes y.2).all fun bl =>
      (termOf x codes y.2 (canon ((faceOfLkp y.1).mu + (faceOfLkp y.1).d)) bl).pairs.length == V)

theorem numbers_of_B {im : OracleNotice} {x : Params.WfPublic} {codes : Codes}
    {lin : Params.LinShape} {V a b : ℕ} (h : keyNumbersB im x codes lin V a b = true) :
    KeyNumbers im x codes lin V a b := by
  unfold keyNumbersB at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem idxTake_sum : ∀ xs : List Lookup, idxTake xs = (xs.map Lkp.keyMasks).sum
  | [] => rfl
  | x :: xs => by
    show 2 * (faceOfLkp x).parts.length + idxTake xs = Lkp.keyMasks x + (xs.map Lkp.keyMasks).sum
    rw [idxTake_sum xs]
    rfl

/-- What the lookups take off the index-mask message's ledger is the library's count. -/
theorem idxTake_eq (x : Params.WfPublic) (m : Wf.Matrix) :
    idxTake (Wf.lookupsOf x m) = Wf.indexMasks x m := by
  unfold Wf.indexMasks
  rw [sumT_eq, idxTake_sum]

/-- **The equation of numbers that the batching of the rows on the table asks.** -/
theorem KeyNumbers.pile {im : OracleNotice} {x : Params.WfPublic} {codes : Codes}
    {lin : Params.LinShape} {V a b : ℕ} (h : KeyNumbers im x codes lin V a b) :
    b + Wf.indexMasks x (Wf.matrixOf lin) = freeOf codes im.shape := by
  rw [h.idx, idxTake_eq]
  omega

/-! ## The front half under the numbers -/

open VerifiableInference.Desc (foldBlocks roundsFit noDigest OpenedColumn)
open OnBytes.Model (Fork)

/-- **What is left of `LinksHeard` beside the numbers**: link by link, along the chain's rounds: the
planner makes the lookup's entries; so many rounds are left and fit their entries; the hearing
accepts them from the fresh ledger; `Left`; `Off` of the rows and of the three claims' leads. -/
inductive Hearings (set : Params.Setting) : ℕ → List Lookup → List Fmt.RoundView → List Fmt.RoundView → Prop
  | nil (i : ℕ) (rs : List Fmt.RoundView) : Hearings set i [] rs rs
  | cons {i : ℕ} {x : Lookup} {xs : List Lookup} {rs rs' : List Fmt.RoundView} {es : List Fmt.Entry}
      {gV : HeardV} {G G₂ : Fork} {cl : List PlaneClaim}
      (hes : (lookupPlace set i x).entries = some es) (hlen : es.length ≤ rs.length)
      (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
      (hh : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots)
        ((rs.take es.length).map noDigest) = some (gV, G))
      (hL : Left (lookupPlace set i x) (toHeardG gV) G cl G₂)
      (hO : ∀ c ∈ (toHeardG gV).rows.toList, Off (faceOfLkp x) 0 c)
      (hO' : ∀ c ∈ cl, Off (faceOfLkp x) 0 c.lead)
      (tail : Hearings set (i + 1) xs (rs.drop es.length) rs') :
      Hearings set i (x :: xs) rs rs'

theorem linksHeard_of (one : Params.OneTime) {set : Params.Setting} {V : ℕ} :
    ∀ {i : ℕ} {xs : List Lookup} {rs rs' : List Fmt.RoundView}, Hearings set i xs rs rs' →
    (∀ y ∈ xs, ∀ v ∈ (faceOfLkp y).parts, 1 ≤ v) →
    (∀ y ∈ xs.zipIdx i, ∀ bl ∈ blocksOf one.ranges one.codes y.2, (termOf one.ranges one.codes y.2
      (canon ((faceOfLkp y.1).mu + (faceOfLkp y.1).d)) bl).pairs.length = V) →
    LinksHeard one set V i xs rs rs' := by
  intro i xs rs rs' h
  induction h with
  | nil i rs => exact fun _ _ => .nil i rs
  | @cons i x xs rs rs' es gV G G₂ cl hes hlen hfit hh hL hO hO' _ ih =>
    intro h1 h2
    rw [List.zipIdx_cons] at h2
    exact .cons (h1 x (List.mem_cons_self ..)) hes hlen hfit hh hL hO hO'
      (h2 (x, i) (List.mem_cons_self ..))
      (ih (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
        fun y hy => h2 y (List.mem_cons_of_mem _ hy))

/-- **The front half of the first chain, under the numbers**: E2E/KeyFirstHalf.lean's
`first_half_chain` with its statements on public numbers gathered in `KeyNumbers`; and the equation
of numbers for the batching behind. -/
theorem first_half_at (one : Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Params.Setting) (N : H2U.PlaceNums) (ft : ℕ)
    {s s₂ : FirstState} {rs rs₂ rs₃ : List Fmt.RoundView} {cols cols₂ : List OpenedColumn} {V a b : ℕ}
    (hN : KeyNumbers one.indexMasks one.ranges one.codes one.lin V a b)
    (hc : s.d.st.codes = one.codes)
    (hfront : foldBlocks ft ((firstChain one D told set N).first ::
      (firstChain one D told set N).front) s rs cols = .ok (s₂, rs₂, cols₂))
    (hf : s.base.fork = none) (hk : s.base.keys = []) (hr : s.base.rows = [])
    (hH : Hearings set 0 (lookupsOf one) rs₂ rs₃) :
    ∃ s₄, foldBlocks ft (firstChain one D told set N).blocksInOrder s rs cols =
        foldBlocks ft
          (((firstChain one D told set N).back.drop 1).map
              (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
            [{ (firstChain one D told set N).last with
                planOk := (firstChain one D told set N).last.planOk &&
                  (firstChain one D told set N).last.hasNoClaimsAndNothingAfter }]) s₄ rs₃ cols₂ ∧
      s₄.base.fork = none ∧ s₄.base.keys.length = (lookupsOf one).length ∧
      s₄.d.st.codes = one.codes ∧ LeftIs s₄.d s₄.idx b one.indexMasks.shape ∧
      b + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) =
        freeOf one.codes one.indexMasks.shape := by
  obtain ⟨s₄, h1, h2, h3, h4, h5⟩ := first_half_chain one D told set N ft hfront hN.idxSample
    hN.idxMask hN.ownSample hN.ownMask hf hk hr (linksHeard_of one hH hN.levels hN.terms) hN.small
    (hc ▸ hN.own) (hc ▸ hN.idx) hN.ownMain (hc ▸ hN.bits)
  exact ⟨s₄, h1, h2, h3, h4.trans hc, h5, hN.pile⟩

/-! ## At the library's written sizes of a key of the full size -/

section Full
open Lk6.AtPlan

theorem layout_at_full : Wf.layout keyFull.ranges.x.lookups
    (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).ell =
    Wf.layFrom (2 ^ 18) 0 0
      [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
        ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] := by
  have e2 : (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).ell =
      2 ^ keyRangesLines.group.logL := by decide +kernel
  have e1 : keyFull.ranges.x.lookups = keyRangesLines.lookups := rfl
  rw [e1, e2]
  exact layout_full

theorem terms_full : ((Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).zipIdx.all
    fun y => (blocksOf keyFull.ranges.x keyFull.codes y.2).all fun bl =>
      (termOf keyFull.ranges.x keyFull.codes y.2
        (canon ((faceOfLkp y.1).mu + (faceOfLkp y.1).d)) bl).pairs.length == 19) = true := by
  unfold blocksOf
  rw [layout_at_full]
  decide +kernel

/-- **At the library's written sizes of a key of the full size the statements on public numbers
hold.** -/
theorem numbers_full : KeyNumbers keyFull.once.input keyFull.ranges.x keyFull.codes
    keyFull.once.shape 19 1978 207 where
  idxSample := by decide +kernel
  idxMask := by decide +kernel
  ownSample := by decide +kernel
  ownMask := by decide +kernel
  ownMain := by decide +kernel
  small := by decide
  bits := by decide +kernel
  own := by decide +kernel
  idx := by decide +kernel
  levels := by decide +kernel
  terms := by
    have h := terms_full
    simp only [List.all_eq_true, beq_iff_eq] at h
    exact h

def fullB (V a b : ℕ) : Bool :=
  keyNumbersB keyFull.once.input keyFull.ranges.x keyFull.codes keyFull.once.shape V a b

#guard fullB 19 1978 207
-- negative tests
#guard !fullB 18 1978 207
#guard !fullB 19 1979 207
#guard !fullB 19 1978 206
-- the numbers one by one
#guard (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).length == 2
#guard freeOf keyFull.codes keyFull.ranges.x.message.shape == 36863
#guard ownTake (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)) == 34885
#guard freeOf keyFull.codes keyFull.once.input.shape == 255
#guard idxTake (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)) == 48

end Full

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.numbers_of_B
#print axioms AtPublicFiles.KeyLookup.idxTake_eq
#print axioms AtPublicFiles.KeyLookup.KeyNumbers.pile
#print axioms AtPublicFiles.KeyLookup.linksHeard_of
#print axioms AtPublicFiles.KeyLookup.first_half_at
#print axioms AtPublicFiles.KeyLookup.numbers_full
