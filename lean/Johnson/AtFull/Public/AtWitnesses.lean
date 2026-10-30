-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AtWitnesses.lean: A CLOSED FACT AT THE MAKERS' TWINS SPEAKS OF WHATEVER THE
PUBLIC PART's OWN MAKERS RETURN. General laws; nothing is evaluated here.

Why. The closed facts on the layers' and the attention's plans at the full size are Bools that
Lean's kernel has evaluated: "at what the makers return, the test t accepts". The theorem that the
public part's maker returns at the stored files (Johnson/AtFull/Public/Join.lean) names its values
by letters, each with its maker's own equation. A maker is a function: so the test accepts at these
very letters. Here that step is taken once, for every test.

  `atMakers t`: the test t at the layers' record L, the layers' plans G and the attention's plans A
    (these with the smallness tests that attentionOwners returns), as the makers make them at a
    layout of the form that layoutLook returns; false where a maker refuses.
    `viewsAt_eq`: viewsAt (Johnson/AtFull/Public/Views.lean) is of that form: by definition.
  `OpensAt y`: "a closed fact withPubC f = true speaks of the layout y": the statement of
    open_pubC (Johnson/AtFull/Public/Kit.lean) with a letter for yFull. A PREMISE here.
  `Makers y sc wsLay rope l ps layers G seenA`: the makers' equations at these letters: seven to the
    letter of the join's conclusion; the rotary table's (the ledger's p10, which the join pays
    inside its proof; in its conclusion the table stands as a term, not as a letter); and three
    small facts on y. A PREMISE here.
  **`at_witnesses`**: OpensAt y · Makers … · atMakers t = true ⊢ t layers G (AOf ps.toArray seenA)
    = true.
  `hB_at`: so viewsBefore G (AOf ps.toArray seenA) is viewsFull's first 24 members (views24_W).
  **`hV_at`**: links_return's premise hV at a public part X with these layers' and attention's
    plans, from the head's link's one view.
  `layersB`, `attB`: two tests, in the letters of armsB_of_fields
    (Johnson/AtFull/Rows/ArmsOfFields.lean): twelve plans; at each group the parts that an arm reads
    are the written numbers, and the view of the smallness test is xShapeFull's
    (Johnson/G/XShapeLit.lean). `layers_of_B`, `att_of_B`: what an accept says, as propositions.
  **`armsB_at`**: armsB X = true at such an X, from: atMakers accepts the two tests (a closed fact:
    Johnson/AtFull/Public/ArmsAtMakers.lean); the head's three parts.
  `tails_at`: from the same closed fact: the views of the 24 smallness tests at the witnesses are
    xShapeFull's segments 0 to 23. That xShapeOf X is xShapeFull is not joined here.

Limits. EVERY PREMISE IS A PREMISE: OpensAt and Makers are paid where the join is imported; the
head's parts by whoever holds the head's plan. Nothing says here that any maker returns. The full
size alone. Nothing on soundness.

-/
import Johnson.AtFull.Public.Views
import Johnson.AtFull.Public.Ledger
import Johnson.AtFull.Rows.ArmsOfFields
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made.Decl (LV viewL viewsFull)
open OnBytes.Road.K4.Trial.AttK7Owners (onOk withPubC PW ttR)
open OnBytes.Road.K4.Trial.AttL2 (AOf seenGOf mqOf)
open OnBytes.Tie.Pv.Plan (scalesF)
open VerifiableInference.PlanWritten (tailView pubOf_fields)
open _root_.AtFull.Rows (lookL numsL smallL claimsL lookA ownA smallA lookH ownH smallH)

/-! ## 1 A test at what the makers return -/

/-- The test t at the layers' record, the layers' plans and the attention's plans as the public
part's makers make them (publicOfO's lines 155-159, the attention's groups by their twins). -/
def atMakers (t : Layer.Pub → Array Layer.HPlan2 → Array Attention.Plan → Bool) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk ((List.range L.y.NGr).mapM (Attention.groupS ttR PW L.y L.sc
          (OnBytes.Road.K4.Trial.AttK7Owners.mqOf L.y) l)) fun ps =>
        onOk (Verify.attentionOwners L.y.h.p4 L.y.NGr
            (G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Verify.SubPlan))
            (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)) fun seenA =>
          t L G (ps.toArray.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } })
            seenA)

theorem viewsAt_eq (w : List LV) :
    viewsAt w = atMakers fun _ G A => decide (viewsBefore G A = w) := rfl

/-- "A closed fact withPubC f = true speaks of the layout y." -/
def OpensAt (y : Layer.Lay) : Prop :=
  ∀ f : Layer.Pub → Bool, withPubC f = true →
    ∃ (sc : Layer.Scales) (wsLay : WsLay) (rope : Array Nat) (L : Layer.Pub),
      Layer.scalesOf y.h scalesF.toArray = .ok sc ∧
      wsLayOf (weightShape PW y) y.h.p3 PW.lkW = .ok wsLay ∧
      Layer.ropeOf y.h = .ok rope ∧
      Layer.Pub.of y sc rope wsLay PW.h.V #[] PW.settings = .ok L ∧ f L = true

/-- The makers' equations at nine letters. -/
structure Makers (y : Layer.Lay) (sc : Layer.Scales) (wsLay : WsLay) (rope : Array Nat)
    (l : List Attention.Line) (ps : List Attention.Plan) (layers : Layer.Pub)
    (G : Array Layer.HPlan2) (seenA : Array SubPlan) : Prop where
  groups : y.NGr = 12
  p3 : y.h.p3 = true
  p4 : y.h.p4 = true
  scales : Layer.scalesOf y.h scalesF.toArray = .ok sc
  weights : wsLayOf (weightShape PW y) true PW.lkW = .ok wsLay
  rotary : Layer.ropeOf y.h = .ok rope
  lines : Attention.readLines PW.polCallsA = .ok l
  twins : (List.range 12).mapM (Attention.groupS ttR PW y sc (mqOf y) l) = .ok ps
  record : Layer.Pub.of y sc rope wsLay PW.h.V #[] PW.settings = .ok layers
  plans : Layer.plansG layers = .ok G
  owners : attentionOwners true 12 (seenGOf G)
    (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩) = .ok seenA

theorem onOk_at {ε α : Type} {x : Except ε α} {f : α → Bool} {a : α} (h : onOk x f = true)
    (e : x = .ok a) : f a = true := by
  rw [e] at h
  exact h

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **A closed fact at the makers speaks of the witnesses.** -/
theorem at_witnesses (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    {t : Layer.Pub → Array Layer.HPlan2 → Array Attention.Plan → Bool}
    (h : atMakers t = true) : t layers G (AOf ps.toArray seenA) = true := by
  obtain ⟨sc', ws', rope', L, e1, e2, e3, e4, hf⟩ := O _ h
  rw [M.p3] at e2
  obtain rfl : sc' = sc := Except.ok.inj (e1.symm.trans M.scales)
  obtain rfl : ws' = wsLay := Except.ok.inj (e2.symm.trans M.weights)
  obtain rfl : rope' = rope := Except.ok.inj (e3.symm.trans M.rotary)
  obtain rfl : L = layers := Except.ok.inj (e4.symm.trans M.record)
  obtain ⟨ey, esc, -⟩ := pubOf_fields M.record
  have h1 := onOk_at hf M.plans
  have h2 := onOk_at h1 M.lines
  rw [ey, esc, M.groups, M.p4] at h2
  have h3 := onOk_at h2 M.twins
  have h4 := onOk_at h3 M.owners
  exact h4

/-! ## 2 The 24 views -/

theorem hB_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) :
    viewsBefore G (AOf ps.toArray seenA) = viewsFull.take 24 :=
  of_decide_eq_true (at_witnesses O M
    (t := fun _ G A => decide (viewsBefore G A = viewsFull.take 24)) views24_W)

/-- **links_return's premise hV at a public part with these plans.** -/
theorem hV_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) {X : Public}
    (hN : X.NGr = 12) (h4 : X.p4 = true) (eG : X.G = G) (eA : X.A = AOf ps.toArray seenA)
    (hHV : [viewL ((Verify.headPlanOf X default).link "H" (1 + X.NGr) 2 0 true)] =
      viewsFull.drop 24) :
    (OnBytes.TieK.listedOf X default).map viewL = viewsFull :=
  hV_of_parts hN h4 (by rw [eG, eA]; exact hB_at O M) hHV

/-! ## 3 The arms -/

/-- Twelve layers' plans; at each group the four parts that the arm reads are the written numbers,
and the view of the smallness test is xShapeFull's at the even segment. -/
def layersB (L : Layer.Pub) (G : Array Layer.HPlan2) : Bool :=
  G.size == 12 && (List.range 12).all fun g => (G[g]?).any fun hp =>
    decide (forestSize L.y.fo = lookL) && decide (layerNumbers L hp g = numsL g) &&
      decide (smallSize hp.tl = smallL) && decide (hp.nBatched = claimsL g) &&
      decide (some (tailView hp.tl) = Johnson.G.xShapeFull.1.getD (2 * g) none)

/-- Twelve attention's plans; at each group the three parts that the arm reads are the written
numbers, and the view of the smallness test is xShapeFull's at the odd segment. -/
def attB (A : Array Attention.Plan) : Bool :=
  A.size == 12 && (List.range 12).all fun g => (A[g]?).any fun a =>
    decide (forestSize a.fs = lookA) && decide (a.own = ownA) &&
      decide (smallSize a.seam.tl = smallA) &&
      decide (some (tailView a.seam.tl) = Johnson.G.xShapeFull.1.getD (2 * g + 1) none)

theorem layers_of_B {L : Layer.Pub} {G : Array Layer.HPlan2} (h : layersB L G = true) :
    G.size = 12 ∧ ∀ g, g < 12 → ∃ hp, G[g]? = some hp ∧ forestSize L.y.fo = lookL ∧
      layerNumbers L hp g = numsL g ∧ smallSize hp.tl = smallL ∧ hp.nBatched = claimsL g ∧
      some (tailView hp.tl) = Johnson.G.xShapeFull.1.getD (2 * g) none := by
  unfold layersB at h
  rw [Bool.and_eq_true] at h
  refine ⟨beq_iff_eq.1 h.1, fun g hg => ?_⟩
  have hg' := List.all_eq_true.1 h.2 g (List.mem_range.2 hg)
  cases e : G[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some hp =>
    rw [e] at hg'
    simp only [Option.any, Bool.and_eq_true, decide_eq_true_eq] at hg'
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, v⟩ := hg'
    exact ⟨hp, rfl, a, b, c, d, v⟩

theorem att_of_B {A : Array Attention.Plan} (h : attB A = true) :
    A.size = 12 ∧ ∀ g, g < 12 → ∃ a, A[g]? = some a ∧ forestSize a.fs = lookA ∧ a.own = ownA ∧
      smallSize a.seam.tl = smallA ∧
      some (tailView a.seam.tl) = Johnson.G.xShapeFull.1.getD (2 * g + 1) none := by
  unfold attB at h
  rw [Bool.and_eq_true] at h
  refine ⟨beq_iff_eq.1 h.1, fun g hg => ?_⟩
  have hg' := List.all_eq_true.1 h.2 g (List.mem_range.2 hg)
  cases e : A[g]? with
  | none =>
    rw [e] at hg'
    cases hg'
  | some a =>
    rw [e] at hg'
    simp only [Option.any, Bool.and_eq_true, decide_eq_true_eq] at hg'
    obtain ⟨⟨⟨b, c⟩, d⟩, v⟩ := hg'
    exact ⟨a, rfl, b, c, d, v⟩

/-- **armsB at a public part with these layers' record and plans**, from the closed fact on the two
tests and the head's three parts. -/
theorem armsB_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    (hW : atMakers (fun L G A => layersB L G && attB A) = true) {X : Public}
    (hN : X.NGr = 12) (h4 : X.p4 = true) (eL : X.layers = layers) (eG : X.G = G)
    (eA : X.A = AOf ps.toArray seenA)
    (hHA : forestSize X.HLy.fs = lookH ∧ X.H.own X.hS = ownH ∧ smallSize X.H.tl = smallH) :
    VerifiableInference.Desc.LinkJoin.armsB X = true := by
  have h := at_witnesses O M hW
  rw [Bool.and_eq_true] at h
  obtain ⟨-, hL⟩ := layers_of_B h.1
  obtain ⟨sA, hA⟩ := att_of_B h.2
  refine _root_.AtFull.Rows.armsB_of_fields h4 hN (fun g hg => ?_) (fun g hg => ?_) ?_ hHA
  · obtain ⟨hp, e0, e1, e2, e3, e4, -⟩ := hL g hg
    exact ⟨hp, by rw [eG]; exact e0, by show forestSize X.layers.y.fo = lookL; rw [eL]; exact e1,
      by rw [eL]; exact e2, e3, e4⟩
  · obtain ⟨a, e0, e1, e2, e3, -⟩ := hA g hg
    exact ⟨a, by rw [eA]; exact e0, e1, e2, e3⟩
  · rw [eA]
    exact Array.getElem?_eq_none (Nat.le_of_eq sA)

/-- The views of the 24 smallness tests at the witnesses are xShapeFull's segments 0 to 23. -/
theorem tails_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    (hW : atMakers (fun L G A => layersB L G && attB A) = true) :
    (∀ g, g < 12 → ∃ hp, G[g]? = some hp ∧
      some (tailView hp.tl) = Johnson.G.xShapeFull.1.getD (2 * g) none) ∧
    ∀ g, g < 12 → ∃ a, (AOf ps.toArray seenA)[g]? = some a ∧
      some (tailView a.seam.tl) = Johnson.G.xShapeFull.1.getD (2 * g + 1) none := by
  have h := at_witnesses O M hW
  rw [Bool.and_eq_true] at h
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hp, e0, -, -, -, -, v⟩ := (layers_of_B h.1).2 g hg
    exact ⟨hp, e0, v⟩
  · obtain ⟨a, e0, -, -, -, v⟩ := (att_of_B h.2).2 g hg
    exact ⟨a, e0, v⟩

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.viewsAt_eq
#print axioms Johnson.AtFull.Public.onOk_at
#print axioms Johnson.AtFull.Public.at_witnesses
#print axioms Johnson.AtFull.Public.hB_at
#print axioms Johnson.AtFull.Public.hV_at
#print axioms Johnson.AtFull.Public.layers_of_B
#print axioms Johnson.AtFull.Public.att_of_B
#print axioms Johnson.AtFull.Public.armsB_at
#print axioms Johnson.AtFull.Public.tails_at
