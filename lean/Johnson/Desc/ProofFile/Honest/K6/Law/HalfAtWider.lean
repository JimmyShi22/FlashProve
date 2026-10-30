-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HalfAtWider.lean: WHICH HALF OF THE PROVER's STANDS AT THE
PLACE OF THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6), AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT THE FILLING
`widerFillAt` (Honest/AtPureWiderAt.lean), UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN. The
sister of Honest/K6/Law/HalfAtSixKinds.lean, which says the like at `nowFill`. CONDITIONAL. Four
theorems.

Why. `widerFillAt` is general in the type of the index, and by its own file's words it is the
filling of record. There every list of prover's sides that reads the index stands inside
`HLot.byPub`, since the reader of the index depends on the public part. So this sub-protocol's list
at one reader is no member of the field `lots`; what is a member has the same sides.

  `widerFillOwn_k6`   in `widerFillOwn` the ninth of the ten lists has, at a public part, the sides
                      of the argument `L.k6` at the reader of that public part
  `widerFillAt_k6`    in `widerFillAt` these are the sides of `headLot headFitsB (headWit' id wt)`
                      at that reader wt
  `k6_half_wider`     **among the returned prover's halves of the first chain the first that stands
                      at K6's place is this sub-protocol's row**, at the library's own public
                      numbers
  `k6_half_wider'`    the same without the premise hG, at the returned prover's own ground

Against HalfAtSixKinds.lean. The conclusion there has the small input's reader `headWit' id id`: two
readers, of the cells and of the index. Here the second alone differs: it is `I.weights Zp`, the
reader of the index at the public part. The trace's type is `Cells` in both fillings.

WHAT IT IS NOT. hA, THAT `onlineProverFromPublicFiles` RETURNS AT THE HYPOTHESIS' THREE PUBLIC FILES, IS A HYPOTHESIS: we
know of no proof of it: THE TWO TOPS MAY HOLD EMPTILY. ho, that every other list of the filling has
no side at a place of the kind K6, is a hypothesis too, WHOLE, in the form in which
`atPure_first_find_kind` (Honest/FirstFindKind.lean) asks it: of the nine other lists not one is
paid here. At K6's own entry it is met by its right arm. NOTHING NEW IS REASONED: a joining of
others' lemmas. Nothing on what the half sends; nothing on any run; nothing on the filling in which
sides keep tables. THE FULL SIZE ALONE. Nothing on any property.

WHO PAYS WHAT. That the returned prover's public part and ground are the hypothesis' own:
`atPure_at_laid_ground` (Honest/AtHeadGround.lean), which is general in the filling. That what is
found in the whole list is what is found in the one list: `atPure_first_find_kind`. That the wrapped
list's sides are the list's at the reader of the public part: by the definition of `HLot.byPub`
(`HLot.byPub_halves`, Honest/AtPureWiderLots.lean, says it by `rfl`). That the list lays just one
half, at K6's place, at the library's public numbers: `headLot_one_half`
(Honest/K6/Law/HalfAtSixKinds.lean), which is general in the four types and in the reader. That there is
a ground under h: `head_ground_at_head` (Honest/K6/Law/RowsSeated.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.HalfAtSixKinds
import Johnson.Desc.ProofFile.Honest.AtPureWiderLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

variable {W₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **K6's list in the choice of fields**: a member of `lots`, the ninth, whose sides at a public
part are those of the argument `L.k6` at the reader of that public part. -/
theorem widerFillOwn_k6 (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∃ M ∈ (widerFillOwn own₀ L I o S O).lots,
      M.halves Z G = (L.k6 (I.weights Z)).halves Z G :=
  ⟨HLot.byPub I.weights L.k6,
    .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), rfl⟩

/-- At the filling of record that argument is this sub-protocol's first list. -/
theorem widerFillAt_k6 (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) :
    ∃ M ∈ (widerFillAt I o S O).lots,
      M.halves Z G = (headLot headFitsB (headWit' id (I.weights Z)) :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Z G :=
  widerFillOwn_k6 () (LongLots.plain o S O) I o S O Z G

/-- **THE HALF AT K6's PLACE, AT THE PROVER THAT `onlineProverFromPublicFiles` RETURNS AT `widerFillAt`.** CONDITIONAL:
the hypothesis h; hG; hA: `onlineProverFromPublicFiles` returns: we know of no proof of it; ho: every list of the filling
has no side at a place of the kind K6, or has the sides of K6's list. -/
theorem k6_half_wider (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A)
    (ho : ∀ M ∈ (widerFillAt I OnBytes.secondHashFunction S O).lots,
      (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K6) ∨
        M.halves A.Z A.G = (headLot headFitsB (headWit' id (I.weights A.Z)) :
          HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ := by
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  refine atPure_first_find_kind hA
    (L := HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k6)
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
    ho ?_
  show ((headLot headFitsB (headWit' id (I.weights A.Z)) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves A.Z
        A.G).find? (fun g => g.place == IM.k6Place) = _
  rw [eZ, eG, headLot_one_half h hG]
  exact List.find?_cons_of_pos (by simp)

/-- **The same without hG, at the returned prover's own ground**: under h there is such a ground
(`head_ground_at_head`), and hA pins it. CONDITIONAL: the hypothesis h; hA; ho. -/
theorem k6_half_wider' (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {I : WiderIn W₀}
    {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I OnBytes.secondHashFunction S O) = .ok A)
    (ho : ∀ M ∈ (widerFillAt I OnBytes.secondHashFunction S O).lots,
      (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K6) ∨
        M.halves A.Z A.G = (headLot headFitsB (headWit' id (I.weights A.Z)) :
          HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves A.Z A.G) :
    A.H.first.find? (fun g => g.place == IM.k6Place) =
      some ⟨IM.k6Place, headRow (headWit' id (I.weights Zp) Zp A.G)
        (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
          (VerifiableInference.Desc.Kinds.Head.Law.workOf (P5J.At.X Zp))) IM.k6Place⟩ := by
  obtain ⟨G, hG⟩ := head_ground_at_head h
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  rw [eG]
  exact k6_half_wider h hG hA ho

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.widerFillOwn_k6
#print axioms ProofFile.Honest.K6.widerFillAt_k6
#print axioms ProofFile.Honest.K6.k6_half_wider
#print axioms ProofFile.Honest.K6.k6_half_wider'
