-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanAtIndex.lean: THE FIELD planAt OF LLT25.PlanOk₃ (hP) AT THE INDEX MASKS' MEMBER:
ITS FIRST AND FIFTH CLAUSES: the mirror, at that member, of
Johnson/LLT25R/PlanAtW.lean (shape_at_W · tie_W · fits_W · planAt_field_w), over it.
  shape_at_I   whoever of mine sits at N₁.index has the shape (vAt Z N₁).indexShape: by mineI and
      oneSeat.
  tie_I   PlanAt's first clause at such a member, where the sized proof is the written one (hz): by
      Johnson/P2LawR/IndexAtHead.lean's closed fact.
  fits_I   its fifth clause there, BY ShapeFits' SECOND ARM (the first is false at the written
      shape, by Lean's kernel): two closed facts and A PREMISE THAT STAYS: hlg: the member's tree is
      told no deeper than the stage's Z.a.
  **planAt_field_i**   the field planAt, in its own text, as planAt_field_w has it, WITH hEI
      NARROWED TO THE RADIUS (hRI: our radB at the index masks' member) AND THAT COMPARISON (hDI).
THE COUNT, not checked by Lean: of the twelve clauses that the field seats does not give:
NINE ARE MET WHOLE; OF THE TENTH (the fit at the index masks' member) TWO PARTS OF THREE;
WHAT STAYS: THE TWO RADII (at W's member and at the index masks' member) AND hDI.
Limits. IT MAY NOT BE SAID THAT planAt IS MET: hRW, hRI and hDI stay; nobody has them as theorems.
Where this and lean/THEOREM.md differ, the page
holds. In this file they are premises. oneSeat, mineW and mineI are premises here (fields of
hP). Written, the named tests, the field seats and hz are premises; under the head hz is
P5J.AtMg.sized_at_head. Nothing on soundness.

-/
import Johnson.LLT25R.PlanAtW
import Johnson.P2LawR.IndexAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.PlanIndex
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K12.Coin (ShapeFits)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open LLT25 (vAt mineOf)
open LLT25.PlanB (elder3B planAt_field_w)
open ToldDesc (p14At tieB)

/-- **Whoever of mine sits at the index masks' seat has their shape.** -/
theorem shape_at_I (Z : ProofFile.Pub) (N₁ : Numbers) (mine : List Mem)
    (h1 : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y)
    (hI : ∃ x ∈ mine, seatOf x = (vAt Z N₁).index ∧ (x.1.l.get x.2).1 = (vAt Z N₁).indexShape)
    (y : Mem) (hy : y ∈ mine) (hs : y.1.seat y.2 = N₁.index) :
    (y.1.l.get y.2).1 = (vAt Z N₁).indexShape := by
  obtain ⟨x, hx, e1, e2⟩ := hI
  obtain rfl : y = x := h1 y hy x hx (hs.trans e1.symm)
  exact e2

/-- **The first clause at a member with that shape.** -/
theorem tie_I (Z : ProofFile.Pub) (hz : Z.p.chains.made.sized.proof = proofSizedFull) (N₁ : Numbers)
    (y : Mem) (hy : (y.1.l.get y.2).1 = (vAt Z N₁).indexShape) :
    tieB (p14At Z).codes (y.1.l.get y.2).1 = true := by
  rw [hy]
  show tieB Z.p.chains.made.sized.proof.codes
    ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) = true
  rw [hz]
  exact P5J.tie_index_written

/-- **The fifth clause at a member with that shape, where its tree is told no deeper than the
stage's Z.a.** -/
theorem fits_I {Xi' : Type} (G' : FileDescription Xi') (Z : ProofFile.Pub)
    (hz : Z.p.chains.made.sized.proof = proofSizedFull) (N₁ : Numbers) (st : Fmt.M1.Stage)
    (y : Mem) (hy : (y.1.l.get y.2).1 = (vAt Z N₁).indexShape)
    (hlg : ∀ o, G'.oracleAt (seatOf y).1 = some o → o.logLength ≤ st.Z.a) :
    fitsAtB G' (p14At Z).codes st y = true := by
  refine (fitsAtB_iff G' _ st y).2 fun o ho => ?_
  rw [hy]
  show ShapeFits Z.p.chains.made.sized.proof.codes st
    ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) o.logLength
  rw [hz]
  exact Or.inr ⟨P5J.fits_index_written.1, P5J.fits_index_written.2, hlg o ho⟩

/-- **The field planAt: what stays: the two radii, and one comparison of two numbers.** -/
theorem planAt_field_i {Xi Xi' : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)
    (G' : FileDescription Xi') {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x)
    (hz : Z.p.chains.made.sized.proof = proofSizedFull)
    (hN : H2U.placesOfMade Z.made = .ok N) (hT : Sh.Tests (Sh.planAt Z N G)) (file : String)
    (D : WholeD) (hp : G'.planOk = true) (hd : G'.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ)
    (ms₁ : List Mem) (N₁ : Numbers) (a b : ℕ × ℕ) (stages : List Fmt.M1.Stage)
    (hS : SeatsFit (p14At Z).codes G' (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)))
    (h1 : ∀ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), seatOf x = seatOf y → x = y)
    (hW : ∃ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), seatOf x = (vAt Z N₁).w ∧ (x.1.l.get x.2).1 = (vAt Z N₁).wShape)
    (hI : ∃ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), seatOf x = (vAt Z N₁).index ∧
      (x.1.l.get x.2).1 = (vAt Z N₁).indexShape)
    (hRW : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.w)).all
        fun y => radB (p14At Z).codes H2K.Member.rWFull st y) = true)
    (hRI : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.index)).all
        fun y => radB (p14At Z).codes H2K.Member.rWFull st y) = true)
    (hDI : ∀ st rest, stages = st :: rest → ∀ y ∈ ms₁, y.1.seat y.2 = N₁.index →
      ∀ o, G'.oracleAt (seatOf y).1 = some o → o.logLength ≤ st.Z.a) :
    ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), ∀ st rest, stages = st :: rest →
      LLT25.PlanAt (p14At Z).codes G' (frameAt D (allOf D) key ft) H2K.Member.rWFull st y := by
  refine planAt_field_w Z N G G' hx h hN hT file D hp hd key ft ms₁ N₁ a b stages hS h1 hW hRW ?_
  intro st rest hst
  rw [List.all_eq_true]
  intro y hy
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
  have es : y.1.seat y.2 = N₁.index := of_decide_eq_true hy2
  have hboth : y ∈ ms₁.filter fun y =>
      decide (y.1.seat y.2 = N₁.w) || decide (y.1.seat y.2 = N₁.index) :=
    List.mem_filter.2 ⟨hy1, by rw [hy2, Bool.or_true]⟩
  have hm := List.mem_append_left ((Sh.ms (Sh.planAt Z N G)).filter fun x =>
    decide (x.1.seat x.2 = (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G))
      (Sh.layO (Sh.planAt Z N G)) a b).tenant .oOmega)) hboth
  have hsh := shape_at_I Z N₁ _ h1 hI y hm es
  unfold elder3B
  rw [tie_I Z hz N₁ y hsh, List.all_eq_true.1 (hRI st rest hst) y hy,
    fits_I G' Z hz N₁ st y hsh (hDI st rest hst y hy1 es)]
  rfl

end P2Law.PlanIndex

#print axioms P2Law.PlanIndex.shape_at_I
#print axioms P2Law.PlanIndex.tie_I
#print axioms P2Law.PlanIndex.fits_I
#print axioms P2Law.PlanIndex.planAt_field_i
