-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanAtW.lean: THE FIELD planAt OF `LLT25.PlanOk₃` (hP) AT W's MEMBER: ITS FIRST AND FIFTH
CLAUSES, from `Written Z x` and two other fields of hP (oneSeat · mineW at V := `vAt Z N₁`).
  `shape_at_W`: whoever of mine sits at N₁.w has the shape (p14At Z).S.w: by mineW and oneSeat.
  `w_real`: two closed facts by the kernel at the typed shape's W: K1's tie; main rows, and a mask's
    code only where it has mask rows.
  `tie_W` · `fits_W`: PlanAt's first and fifth clauses at such a member, at every stage.
  **`planAt_field_w`**: the field planAt, in its own text, as `planAt_field_deep`
    (Johnson/LLT25R/PlanAtDeep.lean) has it, WITH hE NARROWED: at W's member THE RADIUS ALONE (hRW:
    `radB`, Johnson/P2LawR/PlanLeftAt.lean), at the index masks' member the three (hEI: `elder3B`).
THE COUNT: of the twelve clauses that the field seats does not give: EIGHT ARE PAID, FOUR STAY: the
radius at W's member; the tie, the radius and the shape's fit at the index masks' member.
Limits. oneSeat and mineW are premises here (fields of hP; elsewhere they are theorems from the
head). `Written`, the named tests, the field seats, hRW and hEI are premises. Nothing on soundness.

-/
import Johnson.LLT25R.PlanAtDeep
import Johnson.LLT25R.LastAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25.PlanB
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K12.Coin (ShapeFits)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open ToldDesc (p14At tieB)

/-- **Whoever of mine sits at W's seat has W's shape.** -/
theorem shape_at_W (Z : ProofFile.Pub) (N₁ : Numbers) (mine : List Mem)
    (h1 : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y)
    (hW : ∃ x ∈ mine, seatOf x = (vAt Z N₁).w ∧ (x.1.l.get x.2).1 = (vAt Z N₁).wShape)
    (y : Mem) (hy : y ∈ mine) (hs : y.1.seat y.2 = N₁.w) :
    (y.1.l.get y.2).1 = (p14At Z).S.w := by
  obtain ⟨x, hx, e1, e2⟩ := hW
  obtain rfl : y = x := h1 y hy x hx (hs.trans e1.symm)
  exact e2

/-- Two closed facts at the typed shape's W. -/
theorem w_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    tieB codesFull2 x.shape.w = true ∧
    (0 < x.shape.w.mainRows ∧ (x.shape.w.maskRows = 0 → codesFull2.mask.size ≤ x.shape.w.maskCode))
    := by
  obtain ⟨x, a1, -⟩ := full_real
  have h : (realSized.any fun p => tieB p.2 p.1.shape.w &&
      decide (0 < p.1.shape.w.mainRows ∧
        (p.1.shape.w.maskRows = 0 → p.2.mask.size ≤ p.1.shape.w.maskCode))) = true := by
    decide +kernel
  rw [a1, Option.any_some, Bool.and_eq_true] at h
  exact ⟨x, a1, h.1, of_decide_eq_true h.2⟩

/-- **The first clause at a member with W's shape.** -/
theorem tie_W (Z : ProofFile.Pub) {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) (y : Mem) (hy : (y.1.l.get y.2).1 = (p14At Z).S.w) :
    tieB (p14At Z).codes (y.1.l.get y.2).1 = true := by
  obtain ⟨x', a1, a2, -⟩ := w_real
  obtain rfl := sized_one hx a1
  have ec : (p14At Z).codes = codesFull2 := h.codes
  have es : (p14At Z).S.w = x.shape.w := congrArg (·.w) h.shape
  rw [hy, ec, es]
  exact a2

/-- **The fifth clause at a member with W's shape, at every stage.** -/
theorem fits_W {Xi' : Type} (G' : FileDescription Xi') (Z : ProofFile.Pub) {x : LinSized}
    (hx : realSized = some (x, codesFull2)) (h : Written Z x) (st : Fmt.M1.Stage) (y : Mem)
    (hy : (y.1.l.get y.2).1 = (p14At Z).S.w) : fitsAtB G' (p14At Z).codes st y = true := by
  obtain ⟨x', a1, -, a3⟩ := w_real
  obtain rfl := sized_one hx a1
  have ec : (p14At Z).codes = codesFull2 := h.codes
  have es : (p14At Z).S.w = x.shape.w := congrArg (·.w) h.shape
  refine (fitsAtB_iff G' _ st y).2 fun o _ => Or.inl ?_
  rw [hy, ec, es]
  exact a3

/-- **The field planAt: eight clauses of twelve paid.** -/
theorem planAt_field_w {Xi Xi' : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)
    (G' : FileDescription Xi') {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x)
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
    (hRW : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.w)).all
        fun y => radB (p14At Z).codes H2K.Member.rWFull st y) = true)
    (hEI : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.index)).all
        fun y => elder3B G' (p14At Z).codes H2K.Member.rWFull st y) = true) :
    ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), ∀ st rest, stages = st :: rest →
      LLT25.PlanAt (p14At Z).codes G' (frameAt D (allOf D) key ft) H2K.Member.rWFull st y := by
  refine planAt_field_deep Z N G G' hx h hN hT file D hp hd key ft ms₁ N₁ a b stages hS ?_
  intro st rest hst
  rw [List.all_eq_true]
  intro y hy
  have hm := List.mem_append_left ((Sh.ms (Sh.planAt Z N G)).filter fun x =>
    decide (x.1.seat x.2 = (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G))
      (Sh.layO (Sh.planAt Z N G)) a b).tenant .oOmega)) hy
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
  rcases Bool.or_eq_true_iff.1 hy2 with e | e
  · have es : y.1.seat y.2 = N₁.w := of_decide_eq_true e
    have hsh := shape_at_W Z N₁ _ h1 hW y hm es
    unfold elder3B
    rw [tie_W Z hx h y hsh,
      List.all_eq_true.1 (hRW st rest hst) y (List.mem_filter.2 ⟨hy1, e⟩),
      fits_W G' Z hx h st y hsh]
    rfl
  · exact List.all_eq_true.1 (hEI st rest hst) y (List.mem_filter.2 ⟨hy1, e⟩)

end LLT25.PlanB

#print axioms LLT25.PlanB.shape_at_W
#print axioms LLT25.PlanB.w_real
#print axioms LLT25.PlanB.tie_W
#print axioms LLT25.PlanB.fits_W
#print axioms LLT25.PlanB.planAt_field_w
