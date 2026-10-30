-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/ThruMade.lean: a trial, part of no list. What the maker `onlineProverFromPublicFiles`
asks of a filling is not touched by reading the filling through a pair of total maps; and, by calls
of the K5 authors' laws with the index a letter, what it asks at `widerFillAtC`.

  `strays_thru`          `strays` reads places, and a side read through keeps its place
  `makerAsks_through`    `MakerAsks` at a filling gives it at the filling read through
  `makerAsks_widerC_at`  under the head: `MakerAsks` at `widerFillAtC I o' S O`, at any I whose
                         named member is in range

Limits.
  * `makerAsks_through` asks that the new named member, read through `g`, is in range.
  * `makerAsks_widerC_at` is conditional on the head, on the library's test on the public files
    and on the book's return at the written description.
  * Nothing is said of what the maker's prover does.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsAtWiderC
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFill
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFromWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

section
variable {S Cl V V' W W' X : Type}

/-- `strays` reads places alone. -/
theorem strays_thru (bs : List (VerifiableInference.Desc.Block S Cl))
    (see : V' → V) (wit : W' → W) (hs : List (Placed V W X)) :
    strays bs (hs.map (Placed.thru see wit)) = strays bs hs := by
  unfold strays
  rw [List.filter_map, List.map_map]
  rfl
end

end ProofFile.Honest

namespace ProofFile.Honest.Term
open K5

variable {W₀ W₀' Rc Rc' Tr X₀ X : Type}

/-- **What the maker asks, at the filling read through.** -/
theorem makerAsks_through (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {Z : Pub} {G : Ground} {F : VerifiableInference.Desc.FileDescription Inst}
    (a : MakerAsks P Z G F) (hd : P.inRange (g d') = true) :
    MakerAsks (OnlineProverParts.through g rd d' P) Z G F := by
  refine ⟨(strays_firstOf_iff F.first.blocksInOrder Z G _).2 fun M hM => ?_, ?_, ?_, hd⟩
  · obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hM
    show strays _ ((L.halves Z G).map _) = []
    rw [strays_thru]
    exact (strays_firstOf_iff F.first.blocksInOrder Z G _).1 a.first L hL
  · show strays _ ((P.shared Z G).map _) = []
    rw [strays_thru]
    exact a.shared
  · show strays _ ((P.second Z G).map _) = []
    rw [strays_thru]
    exact a.second

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- **What the maker asks at `widerFillAtC I o' S O`, at any I whose named member is in range.**
CONDITIONAL: h, hl, hB. The K5 authors' road at `fullIn`, with the index a letter. -/
theorem makerAsks_widerC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (range : I.inRange I.dummy = true) :
    ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks (widerFillAtC I o' S O) Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF) := by
  intro G hG
  obtain ⟨A, hA, eZ, eF⟩ :=
    atPure_returns_two h hl I o' S O (K14.book_for_atPure_of_written hB h) range
  obtain ⟨m, a⟩ := parts_of_atPure hA
  have eG : A.G = G := by
    have g := m.ground
    rw [eZ, hG] at g
    exact (Option.some.inj g).symm
  rw [eZ, eG, eF] at a
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  exact makerAsks_ownC_of_own () (LongLots.plain o' S O) I o' S O Op a

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.strays_thru
#print axioms ProofFile.Honest.Term.makerAsks_through
#print axioms ProofFile.Honest.Term.makerAsks_widerC_at
