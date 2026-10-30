-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanAtDeep.lean: PlanAt's SIXTH CLAUSE ("no column of the frame at that tree is deeper
than the description tells") IS NO TEST ON THE PLAN: AT THE FRAME OF A DESCRIPTION's OWN DATA IT HOLDS
AT EVERY MEMBER, by `depth_of_planOk` (Johnson/Desc/Sound/SeamDesc.lean), from two
facts that hP has as fields of its own (planOk · dataIs) and the tower's head has in `laid`.
  `deep_all`: `noDeeperB G' (frameAt D (allOf D) key ft) y = true` at EVERY y, from
    `G'.planOk = true` and `G'.data file = .ok D`.
  `elder3B`: what is left of `planAt5B` at an elder member: the tie, the radius, the shape's fit.
  **`planAt_field_deep`**: the field planAt, in its own text, as `planAt_field`
    (Johnson/LLT25R/PlanAtField.lean) has it, at Fr := `frameAt D (allOf D) key ft`, WITH hD GONE AND hE
    NARROWED TO `elder3B` at the two elder members.
THE COUNT: of the twelve clauses that the field seats does not give: SIX ARE PAID (Omega's one, two,
five; the sixth at all three), SIX STAY (one, two, five at W's and at the index masks' member).
Limits. G' is the description whose data D are: at the join `F0T o Zp Np cF`. `Written`, the named
tests, the field seats and `elder3B`'s yes are premises. Nothing on soundness.
-/
import Johnson.LLT25R.PlanAtField
import Johnson.Desc.Sound.SeamDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25.PlanB
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open ToldDesc (p14At tieB)

/-- **The sixth clause at every member.** -/
theorem deep_all {Xi' : Type} (G' : FileDescription Xi') (file : String) (D : WholeD)
    (hp : G'.planOk = true) (hd : G'.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (y : Mem) :
    noDeeperB G' (frameAt D (allOf D) key ft) y = true :=
  (noDeeperB_iff G' _ y).2 fun o ho => depth_of_planOk G' file D hp hd key ft _ o ho

/-- What is left of the five at an elder member. -/
def elder3B {Xi' : Type} (G' : FileDescription Xi') (cs : Codes) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage)
    (y : Mem) : Bool :=
  tieB cs (y.1.l.get y.2).1 && radB cs r st y && fitsAtB G' cs st y

/-- **The field planAt: six clauses of twelve paid.** -/
theorem planAt_field_deep {Xi Xi' : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)
    (G' : FileDescription Xi') {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x)
    (hN : H2U.placesOfMade Z.made = .ok N) (hT : Sh.Tests (Sh.planAt Z N G)) (file : String)
    (D : WholeD) (hp : G'.planOk = true) (hd : G'.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ)
    (ms₁ : List Mem) (N₁ : Numbers) (a b : ℕ × ℕ) (stages : List Fmt.M1.Stage)
    (hS : SeatsFit (p14At Z).codes G' (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)))
    (hE : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.w) || decide (y.1.seat y.2 = N₁.index)).all
        fun y => elder3B G' (p14At Z).codes H2K.Member.rWFull st y) = true) :
    ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), ∀ st rest, stages = st :: rest →
      LLT25.PlanAt (p14At Z).codes G' (frameAt D (allOf D) key ft) H2K.Member.rWFull st y := by
  refine planAt_field Z N G G' hx h hN hT _ ms₁ N₁ a b stages hS
    (deep_all G' file D hp hd key ft _) ?_
  intro st rest hst
  rw [List.all_eq_true]
  intro y hy
  have h3 := List.all_eq_true.1 (hE st rest hst) y hy
  unfold elder3B at h3
  simp only [Bool.and_eq_true] at h3
  obtain ⟨⟨h1, h2⟩, h5⟩ := h3
  have hm : y ∈ mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b) := List.mem_append_left _ hy
  unfold planAt5B
  rw [h1, h2, (toldB_iff G' y).2 (told_of_seatFits G' _ y (hS y hm)), h5,
    deep_all G' file D hp hd key ft y]
  rfl

end LLT25.PlanB

#print axioms LLT25.PlanB.deep_all
#print axioms LLT25.PlanB.planAt_field_deep
