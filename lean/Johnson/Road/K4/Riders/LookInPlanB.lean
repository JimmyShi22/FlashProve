-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/LookInPlanB.lean: THE SEVEN LINES ON THE PLAN UNDER WHICH K4's ROW MAKES THE
ITEM lookIn OF THE LOOKUP ON THE DIGITS (LookInPlan, Johnson/Road/K4/Riders/LookInMade.lean), AS ONE
TEST WITH CODE, so that it can be run and decided at a plan. A definition with code, statements and
proofs.

  `lookInPlanB par X3 m n ns`: **THE TEST**: the digits' lookup's place at link m is there and has
    a shape; it is the digits'; two numbers of K4's plan are the layout's; n with the plan's count
    of K4's slots is the lookup's first slot with the calls' lookup's slots; the lookup's slots end
    inside ns.
  `lookInPlan_of`: a yes gives the seven lines, at the place and the shape that the plan gives.
  `lookInPlanB_of`: THE CONVERSE: the seven lines give a yes.
  **`lookIn_made_B`**: lookIn_made under the test.
No new argument.
**Limits.** THE TEST IS A PREMISE: NOTHING HERE SAYS THAT IT IS TRUE AT ANY PLAN. NO RUN OF IT IS
CITED HERE. Its clause on the count is true at a plan only if no block between K4's and the digits'
lookup takes a slot. n and ns are letters: meant: the plan's next free number in front of K4's block
and the ledger's number of slots. Nothing on soundness. K04_law, the law of K4's block itself, IS
NOT PROVED.


-/
import Johnson.Road.K4.Riders.LookInMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (lamSOf nclOf slotsOf)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (S ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillK4 (callerInLayB)
open VerifiableInference.Desc.First.Look (Sent placeAt k3LookInAt)
open VerifiableInference.OnPublicFiles (linkFreshB)

/-- **THE TEST ON THE PLAN.** -/
def lookInPlanB (par : Par) (X3 : Verify.Public) (m n ns : ℕ) : Bool :=
  (placeAt X3 m true).any fun p => p.shape.any fun h3 =>
    p.digits && par.hp.lamS == lamSOf par.P.y && par.hp.NCL == nclOf par.P.y par.g &&
      n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 == p.first + Forest.elems par.P.y.fo &&
      decide (p.first + Forest.elems h3 ≤ ns)

variable {par : Par} {X3 : Verify.Public} {m n ns : ℕ}

/-- A yes gives the seven lines. -/
theorem lookInPlan_of (h : lookInPlanB par X3 m n ns = true) :
    ∃ p h3, LookInPlan par X3 m p h3 n ns := by
  unfold lookInPlanB at h
  cases hp : placeAt X3 m true with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    cases hs : p.shape with
    | none =>
      have h' : (p.shape.any fun h3 =>
        p.digits && par.hp.lamS == lamSOf par.P.y && par.hp.NCL == nclOf par.P.y par.g &&
          n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 ==
            p.first + Forest.elems par.P.y.fo &&
          decide (p.first + Forest.elems h3 ≤ ns)) = true := h
      rw [hs] at h'
      cases h'
    | some h3 =>
      have h' : (p.shape.any fun h3 =>
        p.digits && par.hp.lamS == lamSOf par.P.y && par.hp.NCL == nclOf par.P.y par.g &&
          n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 ==
            p.first + Forest.elems par.P.y.fo &&
          decide (p.first + Forest.elems h3 ≤ ns)) = true := h
      rw [hs] at h'
      have h2 : (p.digits && par.hp.lamS == lamSOf par.P.y &&
          par.hp.NCL == nclOf par.P.y par.g &&
          n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 ==
            p.first + Forest.elems par.P.y.fo &&
          decide (p.first + Forest.elems h3 ≤ ns)) = true := h'
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      exact ⟨p, h3, hp, hs, h2.1.1.1.1, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2⟩

/-- The converse: the seven lines give a yes. -/
theorem lookInPlanB_of {p : VerifiableInference.Desc.First.Look.P} {h3 : Forest.Shape}
    (L : LookInPlan par X3 m p h3 n ns) : lookInPlanB par X3 m n ns = true := by
  unfold lookInPlanB
  rw [L.place]
  show (p.shape.any fun h3 =>
    p.digits && par.hp.lamS == lamSOf par.P.y && par.hp.NCL == nclOf par.P.y par.g &&
      n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 == p.first + Forest.elems par.P.y.fo &&
      decide (p.first + Forest.elems h3 ≤ ns)) = true
  rw [L.shape]
  show (p.digits && par.hp.lamS == lamSOf par.P.y && par.hp.NCL == nclOf par.P.y par.g &&
      n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 == p.first + Forest.elems par.P.y.fo &&
      decide (p.first + Forest.elems h3 ≤ ns)) = true
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨L.digits, L.lamS⟩, L.ncl⟩, L.count⟩, L.room⟩

/-- **K4's row makes lookIn at the digits' lookup, under the test on the plan.** UNDER, beside that
test: KeptAtS; the four public tests at the state in front; hlink: the open link's number is the
number of the place that the plan gives. -/
theorem lookIn_made_B {s s' : S} {D3 : Sent} (K : KeptAtS par s s')
    (hB : lookInPlanB par X3 m n ns = true) (hled : ledgerB s = true)
    (hfa : freeAboveB ns s = true) (hfresh : linkFreshB (D3.arrayOf.getD m #[]) s = true)
    (hcall : callerInLayB n s = true)
    (hlink : ∀ p, placeAt X3 m true = some p → ∀ Lk, s.link? = some Lk → Lk.link = p.link) :
    k3LookInAt X3 D3 m true s' = true := by
  obtain ⟨p, h3, L⟩ := lookInPlan_of hB
  exact lookIn_made K L hled hfa hfresh hcall (hlink p L.place)

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.lookInPlan_of
#print axioms OnBytes.Road.K4.Riders.lookInPlanB_of
#print axioms OnBytes.Road.K4.Riders.lookIn_made_B
