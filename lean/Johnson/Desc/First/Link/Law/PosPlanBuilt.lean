-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PosPlanBuilt.lean: THE CLOSED SENTENCE `PosPlan` (PosAtBatch.lean: every
table of the sort's skeleton ends inside the third vector's array, or no read names an entry of it)
AT EVERY BUILT SEGMENT OF THE BLANK LETTERS, AS A THEOREM IN THE GOALS' SCOPE; AND "THE THIRD VECTOR
IS PLANNED WITH AT LEAST ONE ENTRY" AT ALL 25, FROM THE HEAD. Statements and proofs: THE LAST STEP
OVER FOUR OTHER FILES.

Whose. The work is four other files' (K9PosHeadPaid.lean, K9PosAttPaid.lean, K9PosLayPaid.lean,
K9NuPaid.lean beside this file): `posAsked_head` and `posAsked_att`: the closed test `posPlanB` says
yes at the head's and at the twelve attention segments of the maker's list; `posTables_lay`: at the
twelve layers' segments its second conjunct holds of every list that `layTriples` returns;
`nuAsked_of_head`: the closed test `nuPosB` says yes at all 25. Here these are brought to the
  sentences that the laws spend, by the ties (K9PosAskLaw.lean, K9NuAskLaw.lean).

  `layShapes_nil`: where `layTriples` returns nothing the layers' skeleton is empty.
  `posPlan_layers`, `posPlan_attention`, `posPlan_head`: **PosPlan Xl.tl Xl.Fp ‹the sort's
    skeleton›, Xl the blank letters' built segment: in the three forms in which
    `aready_layersC`, `aready_attC`, `aready_headC` (Johnson/P5J/K09AreadyC.lean) take their premise
      H. FROM THE SCOPE ALONE.**
  `h0_of_head`: **0 < (ProofFile.k8NU Bs.G₀ Xl).getD 2 0 at l < 25: FROM THE HEAD.**
AT A LAYERS' SEGMENT WHERE `Layer.layTables` REFUSED THE SENTENCE WOULD HOLD IDLY (an empty
skeleton). That it returns in scope is not shown here, and no law spends it.
Limits. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.K9PosAskLaw
import Johnson.Desc.First.Link.Law.K9NuAskLaw
import Johnson.Desc.First.Link.Law.K9PosHeadPaid
import Johnson.Desc.First.Link.Law.K9PosAttPaid
import Johnson.Desc.First.Link.Law.K9PosLayPaid
import Johnson.Desc.First.Link.Law.K9NuPaid
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (PosPlan)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.PlanWritten (publicOfO_older)
open ProofFile (Cl)

/-- Where the list of triples is not there the skeleton is empty. -/
theorem layShapes_nil {P : Layer.Pub} {g : ℕ} (h : layTriples P g = none) :
    layShapes P g = [] := by
  unfold layTriples at h
  unfold layShapes
  rw [Option.map_eq_none_iff.1 h]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem publicOf_open (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
  (publicOfO_older P.pol P.KL (some lay)).symm.trans (ProofFile.Law.pub_public O.pub)

/-- **AT THE LAYERS' SEGMENTS.** -/
theorem posPlan_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) :
    PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g) := by
  obtain ⟨X, x1, x2⟩ := posTables_lay hS hR O.pub (publicOf_open O) hg
  obtain ⟨X', y1, y2, y3⟩ := built_tl_Fp O.blank e3
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [y2, y3, ProofFile.Law.blankBy_W O.blank]
  cases ht : layTriples Z.p.X.layers g with
  | none =>
    rw [layShapes_nil ht]
    intro t ht'
    exact nomatch ht'
  | some ts =>
    have h := x2 ts ht
    rw [layTriples_is ht] at h
    exact all_gives h

/-- **AT THE ATTENTION SEGMENTS.** -/
theorem posPlan_attention (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) :
    ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S)) := by
  obtain ⟨X, x1, x2⟩ := posAsked_att hS hR O.pub (publicOf_open O) hg
  obtain ⟨X', y1, y2, y3⟩ := built_tl_Fp O.blank e3
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [y2, y3, ProofFile.Law.blankBy_W O.blank]
  exact pos_fit_att x2

/-- **AT THE HEAD's SEGMENT.** -/
theorem posPlan_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) :
    ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs) := by
  obtain ⟨X, x1, x2⟩ := posAsked_head hS hR O.pub (publicOf_open O)
  obtain ⟨X', y1, y2, y3⟩ := built_tl_Fp O.blank e3
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [y2, y3, ProofFile.Law.blankBy_W O.blank]
  exact pos_fit_head x2

/-- **h0 AT ALL 25, FROM THE HEAD.** -/
theorem h0_of_head {Zl : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Zl D r Zp Np cF) {F' : FileDescription ProofFile.Inst} {Bs' : ProofFile.PureBase}
    {base' : List (Block S Cl)} {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL F' Zp Bs' base' cF A' B') {l : ℕ}
    (hl : l < 25) {Xl : LinkH} (e3 : Bs'.G₀.built[l]? = some Xl) :
    0 < (ProofFile.k8NU Bs'.G₀ Xl).getD 2 0 :=
  h0_of_asked (nuAsked_of_head h) O hl e3

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.layShapes_nil
#print axioms VerifiableInference.Desc.K9Asks.publicOf_open
#print axioms VerifiableInference.Desc.K9Asks.posPlan_layers
#print axioms VerifiableInference.Desc.K9Asks.posPlan_attention
#print axioms VerifiableInference.Desc.K9Asks.posPlan_head
#print axioms VerifiableInference.Desc.K9Asks.h0_of_head
