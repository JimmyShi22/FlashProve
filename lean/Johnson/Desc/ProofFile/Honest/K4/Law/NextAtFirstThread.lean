-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/NextAtFirstThread.lean: CONDITIONAL.

Can the hypotheses be met together? NOT KNOWN. The statement asks a return A of the maker at a
filling P (hA), a head at that return (h), that the filling lays K4's lot and no other half of the
kind K4 (hM, hE, ho), g < 12, and hyes: THE RUN ON SHAPES OVER ALL 358 MEMBERS SAYS YES FROM THE
SHAPE a₀. hyes is a closed test once a₀ and the public part are values; that it is true at any
public part is not shown here: it is a premise that all kinds of the first chain share.

What is here. THE SIXTH DEBT OF THE THREADS' WRITERS' SECOND FORM (`FiveAtBorderJ`,
Honest/Thread/FiveAtBorder.lean): `NextJ` (Honest/Thread/ShapeJ.lean) AT THE TWELVE MEMBERS OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (kind K4), the members number 28 g + 4, g < 12, at `firstThread h
parts w` (Honest/Thread/TheFirstThread.lean), at the family J := "the run on shapes over the members
in front returns the state's shape" (`shapeJ`) at the library's table of shapes (`firstZA`,
Johnson/AtFull/Shape/) at the return's public part and the thread's own ground (`seatGround A`), and
at the thread's own list of falls. It says: from the thread in front and J there, where nothing of
the member stops and no fall speaks, behind the member's accepting step J holds at the next border.
No definition; one statement with its proof: calls.

  `k4_next_at_first_thread`   **`NextJ` at b = 28 g + 4**, general in the filling.

Whence. The frame's `nextJ_of_shapeV` (Honest/Thread/ShapeJV.lean) asks three things beside hyes.
That the shape's step returns the shape behind a yes, with the member's tests on values in hand
(`CarriesU`): the library's `table_all` (Johnson/AtFull/Shape/TableBatch.lean) has it at every
member. That these tests accept the honest play (`ValuesJ`): `k4_layers_valuesJ`
(Law/ValuesAtHead.lean), whose two hypotheses on the prover's half and on the fall are paid as in
Law/TopsAt.lean: `half_atPure_at` (Law/HalfAtPureBy.lean), and `hf_head` (Law/HalfHead.lean) with
`k4_falls_first` (Law/TwoAtFirstThread.lean). That the seat makes a base is had from the head.

Limits. CONDITIONAL, as said at the top. It holds for nothing at a Said, or at a thread, whose
invariant holds of nothing, and at a state of which J does not hold. THE FULL SIZE ALONE, AND THE
FORMAT's EARLIER HASH ALONE. A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file
that defines a part may build on it; it states no goal. Nothing on soundness, on completeness or on
any other property.
No property is claimed.
-/
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.Desc.ProofFile.Honest.K4.Law.TwoAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.ValuesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls seatGround
  seatGround_of_base)
open ProofFile.Honest.K4.SeatedHead (laid_at)
open Johnson.AtFull.Shape (Tab.g Tab.vals firstZA ShA table_all carriesU_of_V)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL: on h, hA, hM, hE, ho, hyes and hg. **THE STATE's SHAPE ONE MEMBER ON, AT K4's
BORDER 28 g + 4, AT THE FIRST THREAD, AT THE FALLS OF THAT THREAD's OWN LIST**, general in the
filling. -/
theorem k4_next_at_first_thread {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes a₀ 358 = true)
    {g : ℕ} (hg : g < 12) :
    NextJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) a₀)
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (28 * g + 4) := by
  obtain ⟨Bs, _, O⟩ := h.head.laid.opened
  rw [seatGround_of_base O.made] at hyes ⊢
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  exact nextJ_of_shapeV _ Said _ (n := 358) (by omega) hyes
    (carriesU_of_V (table_all h.head O.made (28 * g + 4) (by omega) _).1)
    (k4_layers_valuesJ h.head _ _ _ _ _ _ _ _ _ _ _ w O.made Said Lh
      (half_atPure_at h.head Lh hA cells weights look hM hE ho)
      (hf_head Lh (k4_falls_first h parts hA _ (k4Fall_mem_atPure h.head Lh hA))) a₀)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_next_at_first_thread
