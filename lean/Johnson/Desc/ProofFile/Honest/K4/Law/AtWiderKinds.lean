-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderKinds.lean: CONDITIONAL.

What is here. ho, THE HYPOTHESIS ON THE OTHER LOTS, FOLLOWS AT `widerFillAt` FROM «EACH LOT's HALVES
STAND AT PLACES OF ITS OWN KIND»: IT IS MOVED, NOT PAID. The statements of this folder on which half
is found in the prover that the frame's maker `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns, and all that
build on them, ask ho: each lot of the filling has no half at a place of the kind K4, or has the
halves of the lot of the layers' own rounds (kind K4). `WiderKinds` (Honest/Thread/FirstFill.lean)
is a structure with a field for nine of the ten lots of `widerFillAt`: all its halves stand at
places of its kind (the tenth's is a lemma, `replyLot_kind`); `WiderKinds.all`, `widerPairs_nodup`
and `widerFillAt_lots` of that file say the same over a written list of pairs (lot, kind) in which
no kind stands twice. From such a list ho follows at any filling; so it follows at `widerFillAt`
from `WiderKinds`. half: at the place of K4's member the first chain of that prover holds K4's own
half (Law/AtWiderLots.lean). The six statements of Law/AtWiderAt.lean and the three of
Law/AtWiderAtWo.lean that ask ho, called so: Law/AtWiderKindsTops.lean. Statements with their
proofs.

  `ho_of_pairs`   ho at any list of lots that is the first column of a list of pairs (lot, kind)
      with each lot's halves at its kind, no kind twice, and a pair of the kind K4 in it.
  `ho_widerAt`   **ho at `widerFillAt`, from `WiderKinds`.**
  `half_widerKinds`   half at `widerFillAt`, with `WiderKinds` in ho's stead.

Limits. CONDITIONAL: `ho_of_pairs` on hk, hn, h4 and hE (the four clauses named above; hE: the K4
pair's lot has the halves H); `ho_widerAt` on K : `WiderKinds`; `half_widerKinds` on h · LaidK4 · hA
(the maker returns at that filling: shown here of no files) · K. K IS A HYPOTHESIS HERE, AND ASKS
MORE THAN ho: this file turns a form and pays nothing; K's field k4 is not read.
Honest/Thread/FirstFillAll.lean, which this file does not import, proves K with no hypothesis
(`FirstFill.widerKinds`): Law/AtWiderPaid.lean calls it. AT `widerFillAt` ALONE: for `widerFillOwn`
with a free `LongLots` L, no such list of pairs is written in
Honest/Thread/FirstFill.lean or here. `ho_of_pairs` and `ho_widerAt` are general in the public part
and the ground; `half_widerKinds` stands under h: THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH
ALONE; that h holds of any files is not shown here: the side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with
LaidK4 · hA · K no example is known to us.
Beneath `half_widerOwn` stand comparisons by Lean's own kernel that no
independent checker has replayed (Law/HalfAtPure.lean's head names them). IT IS A LAW, NOT A PART:
it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it states no
goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFill
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block KindName)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- CONDITIONAL: on hk, hn, h4 and hE. **ho FROM A LIST OF PAIRS (LOT, KIND).** -/
theorem ho_of_pairs {V W X : Type} {Zq : ProofFile.Pub} {G : ProofFile.Ground}
    {ps : List (HLot V W X × KindName)}
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves Zq G, x.place.kind = r.2) (hn : (ps.map (·.2)).Nodup)
    {L4 : HLot V W X} (h4 : (L4, KindName.K4) ∈ ps) {H : List (Placed V W X)}
    (hE : L4.halves Zq G = H) :
    ∀ M' ∈ ps.map (·.1), (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨ M'.halves Zq G = H := by
  intro M' hM'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM'
  by_cases e : r.2 = KindName.K4
  · rw [List.inj_on_of_nodup_map hn hr h4 e]
    exact Or.inr hE
  · exact Or.inl fun y hy e' => e ((hk r hr y hy).symm.trans e')

variable {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}

/-- CONDITIONAL: on K. **ho AT `widerFillAt`, FROM `WiderKinds`.** -/
theorem ho_widerAt {Zq : ProofFile.Pub} {G : ProofFile.Ground} (K : WiderKinds I o S O Zq G) :
    ∀ M' ∈ (widerFillAt I o S O).lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot id (I.weights Zq) (fun _ _ => k4LookAt)).halves Zq G := by
  rw [widerFillAt_lots]
  exact ho_of_pairs K.all widerPairs_nodup
    (L4 := HLot.byPub I.weights fun wt => k4HLot id wt fun _ _ => k4LookAt)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))) rfl

/-- CONDITIONAL: on h, Lh, hA and K. **half AT `widerFillAt`, WITH `WiderKinds` IN ho's STEAD.** -/
theorem half_widerKinds {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half id (I.weights A.Z) k4Tokens (k4LookAt) (k4PubAt cF k x)) :=
  half_widerOwn h Lh hA (ho_widerAt K)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ho_of_pairs
#print axioms ProofFile.Honest.K4.ho_widerAt
#print axioms ProofFile.Honest.K4.half_widerKinds
