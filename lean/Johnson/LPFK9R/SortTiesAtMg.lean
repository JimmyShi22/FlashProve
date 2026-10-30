-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SortTiesAtMg.lean: THE FIELD "ties" OF WHAT IS LEFT OF A LINK's LAW AT EACH SORT OF
LINK (`LayersRest3`, `AttRest3`, `HeadRest3`: Johnson/Desc/First/Link/Law/LinkRestAtSort3.lean), AT
THE CLOSED CONSTANT: AT THE VERY LINK THAT THE CONSTANT's DATA NAME (h.𝔇.lk m). Theorems: calls.
THEY PIN THE SORT's LETTERS p4 | c | hS, iU3, l', piece, p6 AND THE LETTER nU.

By: layers_ties_at, att_ties_at, head_ties_at (TiesWholeAt.lean: the ties whole at a
seated link) · subs_scope (Johnson/IMR/LinkSeat.lean: in scope the
plan's sort at l is subAt l) · at the head's link k6States_at_seat
(Johnson/P4SR/K6StatesAtChain.lean: there is iU3; the plan has 25 built segments) · linkAt_of (the
constant's link at m is the chain's).

What is said. O: the description's opening (IM.Open), as AtMg's own field gives it; Bs: its base;
G₀ := Bs.G₀.
  `link_of_lk`: the link that the constant's data name at m is the chain's m-th.
  `ties_layers_mg`: where subAt m = layers: there are p4 and X with k4ParAt Zp G₀ m = some p4,
    G₀.built.toList[m]? = some X and **LayersTies L p4 (ProofFile.k8NU G₀ X)**.
  `ties_att_mg`: where subAt m = attention: there are Xl, A, X with G₀.built[m]? = some Xl, Xl.kind
    = 1, G₀.W.A[Xl.g]? = some A, G₀.built.toList[m]? = some X and **AttTies L (parCOf A) (ProofFile.k8NU
    G₀ X)**.
  `ties_head_mg`: where subAt m = head: there are iU3 and X with G₀.W.H.tl.ix.U.getD 2 none = some
    iU3, G₀.built.toList[m]? = some X and **HeadTies L G₀.W.hS iU3 24 4 (parOf G₀.W.hS (workAtW
    G₀.W)) (ProofFile.k8NU G₀ X)**.

SO THE LETTERS: nU := ProofFile.k8NU G₀ X at X := the m-th built segment · p4 := k4ParAt's · c := parCOf
A at A := the attention plan of that segment · hS := G₀.W.hS · l' := 24 · piece := 4 · p6 := parOf
hS (workAtW G₀.W).

Limits. o := OnBytes.secondHashFunction. The base Bs is named through O (it is one: O.made is an equation).
Nothing on any state. Nothing on soundness.

-/
import Johnson.LPFK9R.SitsAtConstant
import Johnson.LPFK9R.TiesWholeAt
import Johnson.P4SR.K6StatesAtChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.LinkJoin (LayersTies AttTies HeadTies)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The link that the constant's data name at m is the chain's m-th. -/
theorem link_of_lk (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (L : Link S Cl)
    (hlk : h.𝔇.lk m = some L) : cF.links[m]? = some L := by
  have e : ProofFile.linkAt Zp m = some L := hlk
  rw [ProofFile.Law.linkAt_of Zp cF (chain_of_open O) m] at e
  exact e

/-- **ties AT A LAYERS' LINK OF THE CONSTANT.** -/
theorem ties_layers_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .layers) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ p4 X, k4ParAt Zp Bs.G₀ m = some p4 ∧ Bs.G₀.built.toList[m]? = some X ∧
      LayersTies L p4 (ProofFile.k8NU Bs.G₀ X) := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨Lk, p, X, e, hp, hX, T⟩ := layers_ties_at O.made O.places O.chain m hl
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  exact ⟨p, X, hp, hX, T⟩

/-- **ties AT AN ATTENTION LINK OF THE CONSTANT.** -/
theorem ties_att_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ Xl A X, Bs.G₀.built[m]? = some Xl ∧ Xl.kind = 1 ∧ Bs.G₀.W.A[Xl.g]? = some A ∧
      Bs.G₀.built.toList[m]? = some X ∧ AttTies L (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨Lk, Xl, A, X, e, hXl, hk, hA, hX, T⟩ := att_ties_at O.made O.places O.chain m hl
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  exact ⟨Xl, A, X, hXl, hk, hA, hX, T⟩

/-- **ties AT THE HEAD's LINK OF THE CONSTANT.** -/
theorem ties_head_mg (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∃ iU3 X, Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧ Bs.G₀.built.toList[m]? = some X ∧
      HeadTies L Bs.G₀.W.hS iU3 24 4 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W))
        (ProofFile.k8NU Bs.G₀ X) := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨-, iU3, -, hU, -, sz⟩ := P4.k6States_at_seat h.toAtMg.scope h.toAtMg.reads O
  obtain ⟨Lk, X, e, hX, T⟩ := head_ties_at O.made O.places O.chain m hl iU3 hU
  obtain rfl : Lk = L := Option.some.inj (e.symm.trans (link_of_lk h O m L hlk))
  rw [sz] at T
  exact ⟨iU3, X, hU, hX, T⟩

end LPFK9

#print axioms LPFK9.link_of_lk
#print axioms LPFK9.ties_layers_mg
#print axioms LPFK9.ties_att_mg
#print axioms LPFK9.ties_head_mg
