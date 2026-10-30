-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SortOwesAtMgC.lean: ON THE SECOND ROAD: THE SORTS' OWN FIELDS OF WHAT IS LEFT OF K9
(`LayersOwesC`, `AttOwesC`, `HeadOwesC`) AT THE CLOSED CONSTANT, AT THE PINNED LETTERS, WITH EVERY
FIELD THAT HAS A PAYER LAID IN. Theorems: calls. This file's text is made by program.

The named rest SortRest stands at the BARE promise fun q => ‹the named Ok› q ∧ Kx q (without the
public sentence); beside it stands the field k3k (a yes of each of the lookup argument's runs keeps
the ledger's map of weights, the plan's number and the count).

What is said. `layersOwesC_at`, `attOwesC_at`, `headOwesC_at`: there are the sort's pinned letters
(with the facts that pin them), and for all Kx, t3, l3, u, tlD: SortRest at these letters and k3k
give the sort's own fields whole.

Limits. BOOK-KEEPING AT THE CONSTANT. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortRestC
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.LPFK9R.SortTiesAtMg
import Johnson.LPFK9R.RowsNeZero

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

/-- **A LAYERS' LINK's OWN FIELDS AT THE CONSTANT.** -/
theorem layersOwesC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .layers) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ p4 X, k4ParAt Zp Bs.G₀ m = some p4 ∧ Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (t3 : ℕ × String → ℕ → Phi BetaAll × Option Pub9 →
        Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (l3 : ℕ × String → Phi BetaAll × Option Pub9 → ℕ) (u tlD
        : HTailF2), SortRest L u psiAll (fun q => OkLayers p4 (ProofFile.k8NU Bs.G₀ X) tlD q ∧
        Kx q) (ProofFile.k8NU Bs.G₀ X) [(1, "objects"), (6, "objects")] t3 l3 → (∀ o ∈ [(1, "objects"),
                (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → kapOf e₁ = kapOf
                e) → LayersOwesC m p4 Kx t3 l3 L u psiAll (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨p4, X, h1, h2, T⟩ := ties_layers_mg h O m hm hs L hlk
  rw [hs] at seg
  exact ⟨p4, X, h1, h2, fun Kx t3 l3 u tlD R k3k => layersOwesC_of_rest p4 Kx t3 l3 u tlD seg T
    (rests_all u) drawB (rows_ne_zero h.toAtMg m hm p kp) k3k R⟩

/-- **AN ATTENTION LINK's OWN FIELDS AT THE CONSTANT.** -/
theorem attOwesC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ Xl A X, Bs.G₀.built[m]? = some Xl ∧ Xl.kind = 1 ∧ Bs.G₀.W.A[Xl.g]? = some A ∧
      Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (t3 : ℕ × String → ℕ → Phi BetaAll × Option Pub9 →
        Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (l3 : ℕ × String → Phi BetaAll × Option Pub9 → ℕ) (u tlD
        : HTailF2), SortRest L u psiAll (fun q => OkAtt rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀
        X) tlD q ∧ Kx q) (ProofFile.k8NU Bs.G₀ X) [(1, "objects"), (2,
              "join"), (1, "planes"), (6, "objects")] t3 l3 → (∀ o ∈ [(1, "objects"), (2, "join"), (1,
                "planes"), (6, "objects")], ∀ run, At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) →
                kapOf e₁ = kapOf e) → AttOwesC m rdAll (P.parCOf A) Kx t3 l3 L u
        psiAll (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨Xl, A, X, h1, h2, h3, h4, T⟩ := ties_att_mg h O m hm hs L hlk
  rw [hs] at seg
  exact ⟨Xl, A, X, h1, h2, h3, h4, fun Kx t3 l3 u tlD R k3k => attOwesC_of_rest rdAll (P.parCOf A)
    Kx
    t3 l3 u tlD seg T (rests_all u) (hrd_all u) drawB (rows_ne_zero h.toAtMg m hm p kp) k3k R⟩

/-- **THE HEAD's LINK's OWN FIELDS AT THE CONSTANT.** -/
theorem headOwesC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ iU3 X, Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧ Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (t3 : ℕ × String → ℕ → Phi BetaAll × Option Pub9 →
        Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (l3 : ℕ × String → Phi BetaAll × Option Pub9 → ℕ) (u tlD
        : HTailF2), SortRest L u psiAll (fun q => OkHead Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS
        (workAtW Bs.G₀.W)) kapAll (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)
        (ProofFile.k8NU Bs.G₀ X) [(2, "objects"), (2, "planes"), (7, "objects")] t3 l3 → (∀ o ∈ [(2,
                "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok
                (c, e₁) → kapOf e₁ = kapOf e) → HeadOwesC m
        Bs.G₀.W.hS iU3 24 4 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) kapAll Kx t3 l3 L u psiAll
        (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨iU3, X, h1, h2, T⟩ := ties_head_mg h O m hm hs L hlk
  rw [hs] at seg
  exact ⟨iU3, X, h1, h2, fun Kx t3 l3 u tlD R k3k => headOwesC_of_rest Bs.G₀.W.hS iU3 24 4
    (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) kapAll Kx t3 l3 u tlD seg T (rests_all u) (hkap_all u)
    drawB (rows_ne_zero h.toAtMg m hm p kp) k3k R⟩

end LPFK9

#print axioms LPFK9.layersOwesC_at
#print axioms LPFK9.attOwesC_at
#print axioms LPFK9.headOwesC_at
