-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/OwesAllAtMg.lean: AT THE TWELVE ATTENTION LINKS AND THE HEAD's LINK OF THE CLOSED
CONSTANT, ON THE SECOND ROAD: THE SORT's OWN FIELDS OF WHAT IS LEFT OF K9 (`AttOwesC`, `HeadOwesC`,
Johnson/Desc/First/Link/Law/LinkRestAtSort4C.lean), WHOLE: THE TWO PREMISES OF attOwesC_whole AND
THE ONE OF headOwesC_whole (the field k3 at "planes" and "join") LAID IN. Theorems: assemblies.
With layersOwesC_whole (LayersOwesWhole.lean): all 25 links.

What is laid in: attOwesC_whole, att_facts (LookAttAtMg.lean) · headOwesC_whole (LookHeadAtMg.lean)
· k3pl_att, k3jn_att, k3pl_head
(Johnson/Desc/First/Link/Law/SortK3PlanesRun.lean: the lookups' laws of "planes" and "join" at K9's
letters, over the fenced clauses on the callers' forms: Johnson/P1K9R/) · at the
head: K3.isHead W 24 = true from the scope (head_24, Johnson/Desc/Kinds/Law/K6PubInScope.lean).

What is said.
  `attOwesC_all`: there are Xl, A, X (with the facts that pin them), and for every Kx, lmC, jC,
    lmD, jD, u, tlD with hK (Kx q gives kxAll ..), hP (Kx q gives PlanesAttOk rdAll (parCOf A)
    (k8NU ..) q) and hlm (the place of the calls' lookup at m has lm = lmC): **AttOwesC m rdAll
    (parCOf A) Kx (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A)) (l3All ..) L u psiAll (k8NU
    ..) p tlD.**
  `headOwesC_all`: the like: **HeadOwesC m W.hS iU3 24 4 (parOf ..) kapAll Kx (t3All lmC jC lmD jD
    (bvHead iU3) (pvHead iU3) kv) (l3All ..) ..**, kv free (the head's order has no "join" of the
    lookup's).

PREMISES THAT ARE LEFT: the head h · the opening O · m < 25 · the sort of m · the link, that it is
a segment, drawB, kp (the list's own: where the tops call this file they come from the head and m <
25 alone: P5J.sits_kp, Johnson/P5J/K09Rest.lean) · hK · hP · hlm.

Limits. THE FIELDS h4 AND k3 SAY WHAT FOLLOWS FROM THE PROMISE; that the promise, WITH THE NEW
CLAUSES OF Kx, holds in front of the batching is AreadyS's. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.LPFK9R.LookAttAtMg
import Johnson.LPFK9R.LookHeadAtMg
import Johnson.Desc.First.Link.Law.SortK3PlanesRun
import Johnson.Desc.Kinds.Law.K6PubInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt bvHead pvHead k3pl_att k3jn_att k3pl_head)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **THE SORT's OWN FIELDS AT AN ATTENTION LINK OF THE CONSTANT, WHOLE**: under the head, the
opening, hlk, seg, drawB, kp and, inside, hK, hP, hlm. -/
theorem attOwesC_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ Xl A X, Bs.G₀.built[m]? = some Xl ∧ Xl.kind = 1 ∧ Bs.G₀.W.A[Xl.g]? = some A ∧
      Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ q, Kx q → PlanesAttOk rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) q) →
        (∀ pl, placeAt Bs.G₀.W m false = some pl → pl.lm = lmC) →
        AttOwesC m rdAll (P.parCOf A) Kx (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A))
          (l3All lmC jC lmD jD) L u psiAll (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨Xl, A, X, h1, h2, h3, h5, H⟩ := attOwesC_whole h O m hm hs L p hlk seg drawB kp
  obtain ⟨h4, g, hg, rfl, hXg⟩ := att_facts h O m hm hs
  have ha : Bs.G₀.W.A[g]? = some A := by rw [← hXg Xl h1]; exact h3
  have hL := link_of_lk h O (2 * g + 1) L hlk
  refine ⟨Xl, A, X, h1, h2, h3, h5, fun Kx lmC jC lmD jD u tlD hK hP hlm => ?_⟩
  exact H Kx lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A) u tlD hK
    (k3pl_att h.toAtMg.scope h.toAtMg.reads O h4 ha hm hL u tlD (ProofFile.k8NU Bs.G₀ X) Kx hK hP hlm)
    (k3jn_att O h4 hg ha hL u tlD (ProofFile.k8NU Bs.G₀ X) Kx hK hP)

/-- **THE SORT's OWN FIELDS AT THE HEAD's LINK OF THE CONSTANT, WHOLE**: under the head, the
opening, hlk, seg, drawB, kp and, inside, hK, hP, hlm. -/
theorem headOwesC_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ iU3 X, Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧ Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ)
        (kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ q, Kx q → PlanesHeadOk iU3 kapAll (ProofFile.k8NU Bs.G₀ X) q) →
        (∀ pl, placeAt Bs.G₀.W m false = some pl → pl.lm = lmC) →
        HeadOwesC m Bs.G₀.W.hS iU3 24 4 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) kapAll Kx
          (t3All lmC jC lmD jD (bvHead iU3) (pvHead iU3) kv) (l3All lmC jC lmD jD) L u psiAll
          (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨iU3, X, h1, h2, H⟩ := headOwesC_whole h O m hm hs L p hlk seg drawB kp
  obtain rfl := eq24_of_head hs
  obtain ⟨h4, hN⟩ := head_24 h.toAtMg.scope O.public
  have hH : VerifiableInference.Desc.K3.isHead Bs.G₀.W 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [h4, hN]
    rfl
  have hL := link_of_lk h O 24 L hlk
  refine ⟨iU3, X, h1, h2, fun Kx lmC jC lmD jD kv u tlD hK hP hlm => ?_⟩
  exact H Kx lmC jC lmD jD (bvHead iU3) (pvHead iU3) kv u tlD hK
    (k3pl_head h.toAtMg.scope h.toAtMg.reads O hL hH h1 Bs.G₀.W.hS
      (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) u tlD (ProofFile.k8NU Bs.G₀ X) Kx hK hP hlm)

end LPFK9

#print axioms LPFK9.attOwesC_all
#print axioms LPFK9.headOwesC_all
