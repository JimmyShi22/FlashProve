-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/RoadPaid.lean: THE ROAD "WHO PAYS K3RanAt" AT A LOOKUP, WITH ITS INNER
PREMISE GONE: `RoadAtN` (KindsAtPure.lean) asks, link by link, that the hearing blocks behind b step
where their tests on the plan say yes. Here b is a block of the kind K3, and that premise is paid by
StepsAtPure.lean under the kinds' laws. A definition, and theorems with their proofs.

  `RoadAtK3 hd cut o Z F`: `RoadAtN hd o Z F` to the letter, but: in the place of the premise on h₂
    stand "b is of the kind K3" and "cut h₁.length" (which of a link's two lookups is meant, by the
    number of hearing blocks in front).
  **`roadAtCalls`**: `RoadAtN hd o Z F` and the seven laws at hd (`KindsStep hd Z G` at every G)
    give `RoadAtK3 hd (fun _ => True) o Z F`: at both lookups of every link.
  **`roadAtDigits`**: `RoadAtN hd o Z F` and the merge's law at hd give `RoadAtK3 hd (6 ≤ ·) o Z F`:
    at the second lookup of every link: behind it stands the merge, or nothing.

Limits. Frame's laws: no error; nothing on soundness. The kinds' laws are premises here. WHAT STAYS
INSIDE `RanUpTo` | `RanAllUpTo`: that the record behind b's decision holds something as heard, and a
ledger with its sizes. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.StepsAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open ProofFile (Pub Cl Inst pureSeat onlineDescription pureRoad)

/-- `RoadAtN` at a lookup: the premise on the hearing blocks behind b is gone. cut: which of the
link's lookups, by the number of hearing blocks in front of it. -/
def RoadAtK3 (hd : S → Option Forest.Heard) (cut : ℕ → Prop) (o : ProofFile.SecondHashFunctionArgument) (Z : Pub)
    (F : FileDescription Inst) : Prop :=
  ∃ B c A B₂ H several c₀, ProofFile.baseOf Z (pureSeat o Z) = .ok B ∧
    F = ProofFile.fileDescBy o pureRoad.links Z A B₂ (fun s => s) (ProofFile.startS Z) c ∧
    First.firstChainWithoutReplyGuard H (ProofFile.subsOf Z) several = some c₀ ∧
    c = c₀.guarded H.same First.hearsReply ∧
    HIs Z (pureSeat o Z) B H ∧
    (∀ L ∈ c₀.links, ∀ M ∈ L.hear, SeatedAs (pureSeat o Z) B M) ∧
    (∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∀ n y, foldBlocks 0 (c₀.blocksInOrder.take n) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
          (withEmptySealRound v₁).opened = .ok y →
        foldBlocks 0 (c.blocksInOrder.take n) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
          (withEmptySealRound v₁).opened = .ok y) ∧
    ∀ (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl), c₀.links = Ls₁ ++ L :: Ls₂ →
    ∀ (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
      b.place.kind = KindName.K3 → cut h₁.length →
    ∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∃ y ∈ (ProofFile.subsOf Z).zipIdx, First.linkAt H y.2 y.1 = some L ∧
        ∃ m c', foldBlocks 0 (c₀.upToLink Ls₁) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened =
            .ok (m, behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds, c') ∧
          ∃ t t₁ u₀ z u e cls,
            Traced (CF hd) (QN Z (First.batchPlaceOf y.2 y.1)) L h₁ b 0 m
              (behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds) c' t t₁ u₀ z u e cls ∧
            RanUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
            RanAllUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls

/-- **At both lookups of every link, under the seven laws.** -/
theorem roadAtCalls {hd : S → Option Forest.Heard} {o : ProofFile.SecondHashFunctionArgument} {Z : Pub}
    {F : FileDescription Inst} (h : RoadAtN hd o Z F) (K : ∀ G, KindsStep hd Z G) :
    RoadAtK3 hd (fun _ => True) o Z F := by
  obtain ⟨B, c, A, B₂, H, several, c₀, hB, hF, h₀, hc, hIs, hS, hfold, road⟩ := h
  refine ⟨B, c, A, B₂, H, several, c₀, hB, hF, h₀, hc, hIs, hS, hfold,
    fun Ls₁ Ls₂ L hl h₁ h₂ b hh hb _ => ?_⟩
  have hL : L ∈ c₀.links := by rw [hl]; simp
  obtain ⟨y, -, hy⟩ := First.bare_link H (ProofFile.subsOf Z) several c₀ h₀ L hL
  exact road Ls₁ Ls₂ L hl h₁ h₂ b hh
    (stepsBehindLookup hB (K _) H y.2 y.1 L hy (hS L hL) h₁ h₂ b hh hb)

/-- **At the second lookup of every link, under the merge's law alone.** -/
theorem roadAtDigits {hd : S → Option Forest.Heard} {o : ProofFile.SecondHashFunctionArgument} {Z : Pub}
    {F : FileDescription Inst} (h : RoadAtN hd o Z F)
    (k11 : ∀ G, ∀ b ∈ (K11.lot Z).blocks G, b.planOk = true → b.Steps (CF hd)) :
    RoadAtK3 hd (6 ≤ ·) o Z F := by
  obtain ⟨B, c, A, B₂, H, several, c₀, hB, hF, h₀, hc, hIs, hS, hfold, road⟩ := h
  refine ⟨B, c, A, B₂, H, several, c₀, hB, hF, h₀, hc, hIs, hS, hfold,
    fun Ls₁ Ls₂ L hl h₁ h₂ b hh hb h6 => ?_⟩
  have hL : L ∈ c₀.links := by rw [hl]; simp
  obtain ⟨y, -, hy⟩ := First.bare_link H (ProofFile.subsOf Z) several c₀ h₀ L hL
  exact road Ls₁ Ls₂ L hl h₁ h₂ b hh
    (stepsBehindDigits hB (k11 _) H y.2 y.1 L hy (hS L hL) h₁ h₂ b hh hb h6)

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.roadAtCalls
#print axioms VerifiableInference.Desc.K9.roadAtDigits
