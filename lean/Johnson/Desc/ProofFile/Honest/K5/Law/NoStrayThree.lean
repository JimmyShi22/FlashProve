-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NoStrayThree.lean: CONDITIONAL, UNDER THE HEAD: NO HALF OF THE
LISTS OF K7 (the reply), K11 (the merge of the weights' claims) AND K8 (the smallness test) STRAYS
IN THE FIRST CHAIN: three of the lines that "the maker onlineProverFromPublicFiles returns" asks at the filling
widerFillAt.

Why. The maker asks of the prover's list of halves that each stands at the place of a sub-protocol
of the description's first chain (`strays`, Johnson/Desc/ProofFile/Honest/Frame.lean).
ReturnsAtWider.lean splits that test by kinds.

Main names:
  `strays_of_ps`: **under the head a list of halves whose places all stand in the library's written
    list of places (`P5J.At.ps`) has no stray.** By the library's `P5J.At.places_paid` and
    `strays_head` (ReturnsHead.lean).
  `replyLot_no_strays`, `headMergeLot_no_strays`: one half each, at the last link's pieces 1 and 9.
  `k8_heard_at`: a closed fact by Lean's kernel: at which number each of the 25 links hears the
    smallness test.
  `smallLot_no_strays`: a half at each built link: by the library's `IM.k8_alone`.

Limits. Conditional on the head, and on hG: G is the ground that is made of the head's public part.
The head has a member at the library's written copy of the full-size public files
(`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the
package's files by no theorem. General in the lists' own letters. Nothing is said of what a half
does. At the library's full size and the function `OnBytes.secondHashFunction` alone. Through its imports the
file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK11
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head a list of halves whose places all stand in the library's written list of places
has no stray in the first chain.** Conditional: h; H. -/
theorem strays_of_ps {V W Y : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {hs : List (Placed V W Y)} (H : ∀ z ∈ hs, z.place ∈ P5J.At.ps) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder hs = [] := by
  rw [strays_head h hs]
  refine strays_of_mem fun z hz => ?_
  have e := H z hz
  rw [← P5J.At.places_paid h.scope h.reads h.laid] at e
  exact e

variable {W₀ Rc Tr X : Type}

/-- **K7's line.** Conditional: h; hG. -/
theorem replyLot_no_strays (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).halves Zp G) = [] := by
  refine strays_of_ps h fun z hz => ?_
  obtain rfl := List.mem_singleton.1 hz
  show (⟨1, some (G.built.size - 1), 1, .K7⟩ : Place) ∈ P5J.At.ps
  rw [FirstFill.built_25 h hG]
  exact List.mem_of_getElem? FirstFill.ps_338

/-- **K11's line.** Conditional: h; hG. -/
theorem headMergeLot_no_strays (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G)
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List OnBytes.Model.WsClaim)
    (weights : W₀ → Weights) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((K11.headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).halves Zp G) = [] := by
  refine strays_of_ps h fun z hz => ?_
  obtain rfl := List.mem_singleton.1 hz
  show (⟨1, some (G.built.size - 1), 9, .K11⟩ : Place) ∈ P5J.At.ps
  rw [FirstFill.built_25 h hG]
  exact List.mem_of_getElem? FirstFill.ps_346

/-- At each of the 25 links the smallness test is heard at the number 4, at the last link at 5. A
closed fact. -/
theorem k8_heard_at : ∀ l < 25,
    (kindsBeforeBatching (IM.subAt l) (l == 0))[if l = 24 then 5 else 4]? = some KindName.K8 := by
  decide +kernel

/-- **K8's line.** Conditional: h; hG. -/
theorem smallLot_no_strays (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat)) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((K8.smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) cells mats).halves Zp G) = [] := by
  rw [strays_head h]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  refine strays_of_mem fun z hz => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  obtain ⟨Xl, l⟩ := y
  have hX : Bs.G₀.built[l]? = some Xl := by
    rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList] at hy
    exact hy
  have hl : l < 25 := by
    rw [← FirstFill.built_25 h hG]
    exact (Array.getElem?_eq_some_iff.1 hX).1
  obtain ⟨Lk, b, Xl', e1, e2, eX, ep, hla⟩ := IM.k8_alone O l (IM.subAt l)
    (IM.subs_scope h.scope h.reads O l hl) (if l = 24 then 5 else 4) (k8_heard_at l hl)
    (by split <;> omega)
  obtain rfl : Xl' = Xl := Option.some.inj (eX.symm.trans hX)
  refine List.mem_map.2 ⟨b, List.mem_of_getElem? (IM.hear_at_flat e1 e2), ?_⟩
  rw [IM.alone_place hla]
  show (⟨1, some l, _, .K8⟩ : Place) = ⟨1, some l, (ProofFile.k8Par Zp Bs.G₀ Xl' l).piece, .K8⟩
  rw [ep]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.strays_of_ps
#print axioms ProofFile.Honest.K5.replyLot_no_strays
#print axioms ProofFile.Honest.K5.headMergeLot_no_strays
#print axioms ProofFile.Honest.K5.k8_heard_at
#print axioms ProofFile.Honest.K5.smallLot_no_strays
