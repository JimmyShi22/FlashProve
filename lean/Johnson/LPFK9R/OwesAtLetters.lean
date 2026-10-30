-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/OwesAtLetters.lean: attOwesC_all AND headOwesC_all (OwesAllAtMg.lean) ONCE MORE,
ENDING IN THE LETTERS IN WHICH THE FIELD AreadyS IS PAID AT THE THIRTEEN LINKS (
Johnson/P5J/K09AreadyHd2.lean), SO THAT THE JOIN OF THE TWO IS PLAIN CALLS. Theorems: bridges
between letters.

The bridges. (a) the attention's plan A stands at Bs.G₀.W.A[g]? at the link 2 * g + 1 (there: at
W.A[Xl.g]?, Xl the built segment): Xl.g = g by att_facts (LookAttAtMg.lean) · (b) ONE built segment
X, bound as Bs.G₀.built[..]? = some X (there: Xl by built[m]? and X by built.toList[m]?):
Array.getElem?_toList · (c) the place of the calls' lookup is read at P5J.At.X Zp (there: at
Bs.G₀.W): one record, by the opening (IM.Open.W) · (d) at the head: iU3 := readsOf Bs.G₀.W (there:
under "there is an iU3 with W.H.tl.ix.U.getD 2 none = some iU3"): readsOf is that entry's value ·
(e) parOf W.hS (workOf W) (there: workAtW W): one text under two names.

What is said. `attOwesC_g`: at the link 2 * g + 1, g < 12: there are A and X with Bs.G₀.W.A[g]? =
some A and Bs.G₀.built[2 * g + 1]? = some X, and for all Kx, lmC, jC, lmD, jD, u, tlD with hK, hP,
hlm': AttOwesC (2 * g + 1) rdAll (parCOf A) Kx (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A))
(l3All ..) L u psiAll (k8NU Bs.G₀ X) p tlD · `headOwesC_24`: the like at link 24 in the letters
readsOf, workOf.

Limits. BOOK-KEEPING ON LETTERS: nothing is paid here that OwesAllAtMg.lean does not pay. Its
limits are that file's. Nothing on soundness.

-/
import Johnson.LPFK9R.OwesAllAtMg
import Johnson.Desc.Kinds.Law.RowRides

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
open VerifiableInference.Desc.Kinds.Head.Law (readsOf workOf)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt bvHead pvHead)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **attOwesC_all IN THE LETTERS OF THE LINK 2 g + 1.** -/
theorem attOwesC_g (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : subAt (2 * g + 1) = .attention) (L : Link S Cl) (p : Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (subAt (2 * g + 1)) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) :
    ∃ A X, Bs.G₀.W.A[g]? = some A ∧ Bs.G₀.built[2 * g + 1]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ q, Kx q → PlanesAttOk rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) q) →
        (∀ pl, placeAt (P5J.At.X Zp) (2 * g + 1) false = some pl → pl.lm = lmC) →
        AttOwesC (2 * g + 1) rdAll (P.parCOf A) Kx
          (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A)) (l3All lmC jC lmD jD) L u psiAll
          (ProofFile.k8NU Bs.G₀ X) p tlD := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨Xl, A, X, h1, _, h3, h5, H⟩ := attOwesC_all h O (2 * g + 1) hm hs L p hlk seg drawB kp
  obtain ⟨_, g', _, e, hXg⟩ := att_facts h O (2 * g + 1) hm hs
  obtain rfl : g' = g := by omega
  rw [Array.getElem?_toList] at h5
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  refine ⟨A, X, by rw [← hXg Xl h1]; exact h3, h5,
    fun Kx lmC jC lmD jD u tlD hK hP hlm => H Kx lmC jC lmD jD u tlD hK hP fun pl hp => ?_⟩
  rw [eW] at hp
  exact hlm pl hp

/-- **headOwesC_all IN THE LETTERS readsOf, workOf, AT LINK 24.** -/
theorem headOwesC_24 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂)
    (hs : subAt 24 = .head) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk 24 = some L)
    (seg : SegAt 24 (subAt 24) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) :
    ∃ X, Bs.G₀.built[24]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ)
        (kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ q, Kx q → PlanesHeadOk (readsOf Bs.G₀.W) kapAll (ProofFile.k8NU Bs.G₀ X) q) →
        (∀ pl, placeAt (P5J.At.X Zp) 24 false = some pl → pl.lm = lmC) →
        HeadOwesC 24 Bs.G₀.W.hS (readsOf Bs.G₀.W) 24 4 (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          Kx (t3All lmC jC lmD jD (bvHead (readsOf Bs.G₀.W)) (pvHead (readsOf Bs.G₀.W)) kv)
          (l3All lmC jC lmD jD) L u psiAll (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨iU3, X, hi, h5, H⟩ := headOwesC_all h O 24 (by omega) hs L p hlk seg drawB kp
  have e : readsOf Bs.G₀.W = iU3 := by
    unfold readsOf
    rw [hi]
    rfl
  subst e
  rw [Array.getElem?_toList] at h5
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  refine ⟨X, h5, fun Kx lmC jC lmD jD kv u tlD hK hP hlm =>
    H Kx lmC jC lmD jD kv u tlD hK hP fun pl hp => ?_⟩
  rw [eW] at hp
  exact hlm pl hp

end LPFK9

#print axioms LPFK9.attOwesC_g
#print axioms LPFK9.headOwesC_24
