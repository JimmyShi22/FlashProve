-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/DescAtPure.lean: CONDITIONAL.

What is here. (1) THE FIELD F, THE PROOF FILE's DESCRIPTION, OF THE STRUCTURE THAT THE FRAME's MAKER
`onlineProverFromPublicFiles` RETURNS (Honest/AtPure.lean) AT THE PUBLIC FILES OF h : AtMgA IS THE LIBRARY's OWN TERM
`P5J.F0T OnBytes.secondHashFunction Zp Np cF`: by the third clause of the frame's `atPure_ok`
(Honest/AtPureLaw.lean) and its `head_value` (Honest/Thread/FirstSits.lean). It stands beside
`atPure_pub` and `atPure_ground` (Law/HgAtPure.lean). What it is for: a hypothesis such as "a ready
run" is typed at `F0T` in this folder's statements; whoever holds what the maker returns has A.F:
the equation carries the one to the other (`k4Seated_lookAt_run`, Law/SeatedAtMaker.lean, spends it
so). THE FRAME HAS THE SAME EQUATION, at every hash function and under less than h: `atPure_at_laid`
(Honest/AtHead.lean); its `atPure_is` is the form to use where a list of A.F's own is spoken of,
since the types of the states and claims hang on A.F. It is stated again here because this folder's
files do not import that file. (2) ONE CALL OF `ho_of_kinds` (Law/HgAtPure.lean). ho: no other lot
of a list has a half at a place of the kind K4. At the list of two lots, K4's and the frame's own
lot of the next token (`replyLot`, Honest/K7.lean), ho holds: K4's lot by itself, the other by the
frame's `replyLot_kind` (Honest/FirstFindKind.lean): so Lean holds that the lemma which the frame
asks of each lot fits the premise of `ho_of_kinds`. (3) ONE CALL OF `hf_of_falls`
(Law/LotFallsLaws.lean), under h and `LaidK4`, at the ground `ProofFile.blankBy ProofFile.pureRoad.links Zp`.
hf: if no fall of the list speaks at member k, then `k4CoinZero`, the verifier's test on one sampled
element, is silent too. It holds at every list of falls that holds the lot's own (`k4LotFalls`,
Honest/K4/LotFalls.lean). Each proof is a call or two.

Not shown here. THAT `onlineProverFromPublicFiles` RETURNS AT ANY FILLING (hA): a hypothesis of (1). Nothing on the book
A.B. (2) IS AN EXAMPLE AT TWO LOTS: no filling has that list; for the other lots of a filling the
like lemma on kinds must come from whoever wrote that lot. THE ENDS OF (2) AND (3) ARE HANDED TO NO
STATEMENT HERE: that they fit the statements which ask ho and hf is by reading. NO STATEMENT CALLS
(3) YET; it takes the end of `k4LotFalls_sub` (Law/FallsJoin.lean) as it stands. The same end stands
from one fall's membership (`hf_head`, Law/HalfHead.lean), and at the maker's prover
`k4_accepted_falls` (Law/FillFalls.lean) goes by that membership. That any list of falls holds the
lot's own: whoever lays the list. THAT h CAN HOLD: the side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). OF h TOGETHER WITH hA
NO EXAMPLE IS KNOWN TO US. `hf_falls_head` takes h, `LaidK4`, hG and hfs, and not hA: `LaidK4` and
hG ask nothing beyond h (`laid_head`, Law/SeatedHead.lean; `IM.Open.blank`); hfs speaks of a list of
falls that the caller picks. (1) and (3): THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone.
Beneath (3) stand comparisons by Lean's own kernel, as Law/HgAtPure.lean's head says of `hg_atPure`;
no independent checker has replayed them. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one: its imports reach modules under Johnson/Goal/, as
those of Law/HgAtPure.lean do. Which modules it imports in all has not been counted.
No property is claimed.

  `atPure_desc`   **the description that the maker returns is the library's term.**
  `ho_k4_reply`   ho at the list of K4's lot and the lot of the next token.
  `hf_falls_head`   hf at the member, at every list that holds the lot's own falls.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HgAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.LotFallsLaws
import Johnson.Desc.ProofFile.Honest.FirstFindKind
import Johnson.Desc.ProofFile.Honest.Thread.FirstSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

/-- CONDITIONAL: on h and hA. **THE DESCRIPTION THAT THE MAKER RETURNS IS THE LIBRARY's TERM.** -/
theorem atPure_desc (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans (FirstThread.head_value h))

/-- **ho AT THE LIST OF K4's LOT AND THE LOT OF THE NEXT TOKEN**: one call of `ho_of_kinds`. General
in the public part and the ground. -/
theorem ho_k4_reply (Zq : ProofFile.Pub) (G : ProofFile.Ground) (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    ∀ M ∈ [k4HLot (Rc := Rc) (X := X') cells weights look, replyLot],
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ .K4) ∨
        M.halves Zq G = (k4HLot (Rc := Rc) (X := X') cells weights look).halves Zq G :=
  ho_of_kinds fun M hM => by
    rcases List.mem_cons.1 hM with e | hM'
    · exact Or.inl (by rw [e])
    · obtain rfl := List.mem_singleton.1 hM'
      exact Or.inr ⟨.K7, by decide, replyLot_kind Zq G⟩

/-- CONDITIONAL: on h, `LaidK4`, hG and hfs. **hf AT THE MEMBER, AT EVERY LIST OF FALLS THAT HOLDS
THE LOT's OWN**: one call of `hf_of_falls`. -/
theorem hf_falls_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {fs : List (Fall TS)}
    (hfs : ∀ f ∈ k4LotFalls Zp G₀, f ∈ fs) :
    ∀ s ds, fallsBy fs cF.blocksInOrder k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none := by
  obtain ⟨G₁, hG₁, hx⟩ := Lh.lot
  obtain rfl : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
  exact hf_of_falls hfs hx (k4Pub_head h Lh) (tableFits_member h Lh) Lh.member
    ((IM.alone_place Lh.laid).trans
      ((pubAt_place Lh).symm.trans (k4Place_block (k4Pub_head h Lh))))

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.atPure_desc
#print axioms ProofFile.Honest.K4.ho_k4_reply
#print axioms ProofFile.Honest.K4.hf_falls_head
