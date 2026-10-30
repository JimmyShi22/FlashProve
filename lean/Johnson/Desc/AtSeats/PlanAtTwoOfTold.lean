-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanAtTwoOfTold.lean: THE TWO FIELDS W_HP, G_HP OF KIND K1's CONDITION
(`PlanAt` at the data's own two rounds, at W's commitment and at the first segment's opening), AT
THE FIRST TABLE's CLOSED CONSTANT, IN THE FIELDS' OWN TYPES: EACH FROM ITS FIELD "told" ALONE. Two
statements, made by program out of `W_HP_atAll`, `G_HP_atAll`
(Johnson/Desc/K1/Law/RadiiAtTwo.lean): each a call of that, with its premise hlist paid by
`listed_W_atD`, `listed_G_atD` (Johnson/Desc/AtSeats/ListedAtD.lean) and its premise on the radii
by `hRad_atAll` (Johnson/Desc/K1/Law/RadiiAtAllPaid.lean). LEFT: htold: the stretch's trees are
told by the description as the data have them. BESIDE: the head hA, the opening O, the two pins
hP1, hP2. A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed.
htold. That the head can be met. Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.ListedAtD
import Johnson.Desc.K1.Law.RadiiAtAllPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull msOf nTrees six_together Frame Mem SeatFits
  ListedAt)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt wMsgFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5T (N0Full psFull)
open ProofFile (Cl)
open IM (Open)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
  (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hA O hP1 hP2

/-- **W_HP, from "told" alone.** -/
theorem W_HP_of_told
    (htold : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parWZ Zp wMsgFull)
        (radRec 81 (parWZ Zp wMsgFull)) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)))
        d₁ d₂ [hA.𝔇.N.w] := by
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  exact W_HP_atAll hA O hP1 hP2 (hRad_atAll hA hP1)
    (fun d₁ d₂ _ _ hds => listed_W_atD hA.scope hA.reads O hD hA.laid.planOk q₁ q₂ q₃ d₁ d₂ hds)
      htold

/-- **G_HP, from "told" alone.** -/
theorem G_HP_of_told
    (htold : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) →
      d₁.kind = .seeds → ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (firstPar Bs.G₀.first (gpOf Zp))
        (radRec 0 (firstPar Bs.G₀.first (gpOf Zp)))
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) d₁ d₂
        (First.sampledIn hA.𝔇.N (openAt Sound.linksFull psF (2 + 1))) := by
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  exact G_HP_atAll hA O hP1 hP2 (hRad_atAll hA hP1)
    (fun d₁ d₂ _ _ hds => listed_G_atD hA.scope hA.reads O hD hA.laid.planOk q₁ q₂ q₃ d₁ d₂ hds)
      htold

end

end VerifiableInference.Desc.K1
