-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/LayersOwesWhole.lean: AT THE TWELVE LAYERS' LINKS OF THE CLOSED CONSTANT, ON THE
SECOND ROAD: THE SORT's OWN FIELDS OF WHAT IS LEFT OF K9 (`LayersOwesC`,
Johnson/Desc/First/Link/Law/LinkRestAtSort4C.lean), WHOLE, AT THE WRITTEN LETTERS. A theorem: an
assembly of what lies.

What is laid in: layersOwesC_at (SortOwesAtMgC.lean: seg, ties, hψ, drawB, rows at the constant; it
leaves SortRest at the bare promise, and k3k) · sortRest_of_look with h4_of_core (SortFour.lean: h4
from the core: the bare promise gives OkCore by the named Ok's field core) · lookRest_layers_at and
k3k_layers_at (LookLayersAtMg.lean: the lookup argument's seven and k3k, by
three files over the lookups' own).

What is said. `layersOwesC_whole`: there are p4 and X with k4ParAt Zp Bs.G₀ m = some p4 and
Bs.G₀.built.toList[m]? = some X, and for every Kx that gives K3's promise (hK : Kx q gives kxAll
lmC jC lmD jD q), all u, tlD, bv, pv, kv: **LayersOwesC m p4 Kx (t3All ..) (l3All ..) L u psiAll
(ProofFile.k8NU Bs.G₀ X) p tlD.**

PREMISES THAT ARE LEFT: h : AtMgA OnBytes.secondHashFunction .. (THE HEAD) · the opening O · m < 25 · subAt m =
.layers · the link, that it is a segment, drawB, kp (fields of the list's own "Sits" and kp: where
the tops call this file they come from the head and m < 25 alone: P5J.sits_kp,
Johnson/P5J/K09Rest.lean) · hK.

Limits. THE FIELDS h4 AND k3 SAY WHAT FOLLOWS FROM THE PROMISE; that the promise holds in front of
the batching is AreadyS's (CoreLeftC). The other sorts' own fields want the caller's clauses at
"planes" and "join" besides. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.LPFK9R.SortOwesAtMgC
import Johnson.LPFK9R.LookLayersAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- A layers' link is not the head's. -/
theorem ne24_of_layers {m : ℕ} (hs : subAt m = .layers) : m ≠ 24 := by
  rintro rfl
  exact absurd hs (by decide)

/-- **THE SORT's OWN FIELDS AT A LAYERS' LINK OF THE CONSTANT, WHOLE**: under the head, the
opening, hlk, seg, drawB, kp and, inside, hK. -/
theorem layersOwesC_whole (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .layers) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ p4 X, k4ParAt Zp Bs.G₀ m = some p4 ∧ Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ)
        (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
        (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        LayersOwesC m p4 Kx (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) L u psiAll
          (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨p4, X, h1, h2, H⟩ := layersOwesC_at h O m hm hs L p hlk seg drawB kp
  refine ⟨p4, X, h1, h2, fun Kx lmC jC lmD jD bv pv kv u tlD hK => ?_⟩
  have h24 := ne24_of_layers hs
  exact H Kx (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) u tlD
    (sortRest_of_look (tlD := tlD) (rests_all u) (fun _ hq => hq.1.core)
      (lookRest_layers_at h O m hm h24 L hlk u _ (ProofFile.k8NU Bs.G₀ X) lmC jC lmD jD bv pv kv
        (fun q hq => hK q hq.2)))
    (k3k_layers_at h O m hm h24 L hlk)

end LPFK9

#print axioms LPFK9.ne24_of_layers
#print axioms LPFK9.layersOwesC_whole
