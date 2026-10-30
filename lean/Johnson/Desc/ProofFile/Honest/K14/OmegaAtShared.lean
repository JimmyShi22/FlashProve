-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaAtShared.lean: kind K14: ChainAt
(Honest/K14/AcceptedAt.lean), TailLike AND TailAt (Honest/K14/OmegaTwelve.lean) AND THE NUMBER OF
MEMBERS, TWELVE, AT THE LIST OF lettersShared (Honest/Thread/SharedHead.lean): the shared chain's
flat list of the IOP as written in Lean, P5J.F0T; so second_door_five (Honest/K14/OmegaJoin.lean) at
that Thread, at the border (F0T …).shared.blocksInOrder.length. Statements with their proofs; no definition.
IT IMPORTS Honest/Thread/SharedHead.lean: it can stand only behind that folder.

  shared_flat_at  F0T's shared chain's flat list is the carried chain's: by unfolding, with no
                  premise. (flat_pure, Johnson/Desc/K14/Honest/FlatPure.lean, has the equation by a
                  longer way, where the eight are made)
  shared_twelve   **F0T's shared chain's flat list has twelve members**, where the eight are made
                  and the plan has a second test. (The library's shared_flat_of_pin and
                  closed_lengths, Johnson/Road/Tables/FlatLengths.lean, have the number under other
                  premises: the test on the plan and the pin on the declared rounds, in the goals'
                  scope. That Seat.tests Np has two members is unfolded inside the proof, in three
                  lines, as in Honest/K14/OmegaTail.lean: the library's ToldDesc.tests_two,
                  Johnson/ToldDescR/OmegaAtLaid.lean, says it; it is not imported)
  chainAt_shared  **ChainAt at lettersShared's own Thread**, at Q := p14Of Zp.p.chains
                  (beforePointOf Np), c := Zp.p.chains, key := the input's key, whatever the other
                  arguments of lettersShared are: a check of two of its fields: bs and first. Where
                  the library's maker of the eight returns nothing ChainAt's first field is empty
  tailLike_shared, tailAt_shared **TailLike and TailAt at that Thread's list**, at the library's own
                  numbers of the two proximity tests. Asked: the maker of the eight sub-protocols of
                  the linear claim's shared rounds returns them; the plan has a second test; for
                  TailAt beside: the two tests' own tests on the plan accept
  second_door_shared **secondDoor from secondRest5, hW and sW, at lettersShared's own Thread, at the
                  border (F0T …).shared.blocksInOrder.length**: ChainAt and TailAt's three members are no
                  premises any more; TailAt's two tests on the plan stay (h9, h10), and Np.O = some
                  nO. The other fifteen arguments of lettersShared are read by no line of the proof

s: the state that the start of the last chain (FileDescription.start₃ of P5J.F0T) returns. hW: the weights
at the border of s name no written-out variable twice and only their own variables (WeightsFit,
Honest/K14/DotPads.lean); sW: each place of W's pad in its main table, in the statement of s, lies
inside W's table at an entry numbered at least 2 ^ kCol (PadsBehind, DotPads.lean); h5: the five
tests of secondRest5 (Honest/K14/OmegaJoin.lean).

OF THE ELEVEN TESTS OF secondDoor (Honest/K14/SecondDoor.lean: a list of this kind's own; that it is
all true is by itself no accept of the sub-protocol: door_owed there) SIX ARE READ OFF THE RUN THAT
Thr HOLDS, THE LAST FOLLOWS FROM hW, sW AND THE RUN, AND THE REST ARE PREMISES: three of
secondRest5's five are entries of secondDoor to the letter.

What is not claimed. h9, h10 and Np.O = some nO (Honest/K14/OmegaAtPlan.lean has them from F0T's
test on the plan). Plan2 (Honest/K14/PlanAtHead.lean). hW, sW, secondRest5 at any state. That Thr
holds at any run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaJoin
import Johnson.Desc.ProofFile.Honest.K14.OmegaTail
import Johnson.Desc.ProofFile.Honest.Thread.SharedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay linLayW)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St p14Of beforePointOf blocks chainOf)
open Desc.K14.Law (flat_retype_all)
open Desc.K14.Honest (flatOf_carried)

/-- F0T's shared chain's flat list is the carried chain's flat list. -/
theorem shared_flat_at (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder =
      ((chainOf Zp.p.chains (p14Of Zp.p.chains (beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last).retype (Cl' := ProofFile.Cl)).blocksInOrder := rfl

/-- **F0T's shared chain's flat list has twelve members**, where the eight are made and the plan has
a second proximity test. The library's shared_flat_of_pin with closed_lengths has the number under
other premises. The last three lines of the proof unfold again what ToldDesc.tests_two says. -/
theorem shared_twelve (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (hb : blocks (p14Of Zp.p.chains (beforePointOf Np)) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = 12 := by
  rw [shared_flat_at, flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb]
  unfold VerifiableInference.Desc.K12.Seat.tests
  rw [hO]
  rfl

section letters
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **ChainAt at lettersShared's own Thread**, whatever its other arguments are: a check of its
fields bs and first. -/
theorem chainAt_shared :
    ChainAt (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread (p14Of Zp.p.chains (beforePointOf Np)) Zp.p.chains fun v => v.key := by
  refine ⟨fun B => ?_, fun _ _ _ _ h => h⟩
  show Desc.K14.Honest.FlatAt (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
    wit table fixed n₁ n₂ Vd Rd Kp w).bs _ B
  rw [SharedThread.shared_bs, shared_flat_at]
  exact flatOf_carried Zp.p.chains _ B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8
    (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last B.made

/-- **TailLike at the list of lettersShared's own Thread.** -/
theorem tailLike_shared (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (nO : H2U.PlaceNums)
    (hO : Np.O = some nO)
    (hb : blocks (p14Of Zp.p.chains (beforePointOf Np)) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    TailLike (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread.bs (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++ VerifiableInference.Desc.K12.Seat.tests Np) := by
  show TailLike (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
    n₁ n₂ Vd Rd Kp w).bs _ _ _
  rw [SharedThread.shared_bs, shared_flat_at]
  exact tailLike_carried _ _ b1 b2 b3 b4 b5 b6 b7 b8 Np nO hO hb

/-- **TailAt at the list of lettersShared's own Thread**, where the two proximity tests' own tests
on the plan accept. -/
theorem tailAt_shared (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (nO : H2U.PlaceNums)
    (hO : Np.O = some nO)
    (hb : blocks (p14Of Zp.p.chains (beforePointOf Np)) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (h9 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) : Block T12 Unit).planOk = true)
    (h10 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).planOk = true) :
    TailAt (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread.bs (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++ VerifiableInference.Desc.K12.Seat.tests Np) :=
  ⟨tailLike_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w b1 b2 b3
    b4 b5 b6 b7 b8 nO hO hb, h9, h10⟩

variable {sentU : Array OracleNotice} {layO : TreeLay}

/-- **secondDoor from secondRest5, hW and sW, at lettersShared's own Thread, at the border
(F0T …).shared.blocksInOrder.length.** Of ChainAt and TailAt nothing is left as a premise but the plan's
second test and the two tests' own tests on the plan. -/
theorem second_door_shared (hQ : Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO)
    (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (h9 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) : Block T12 Unit).planOk = true)
    (h10 : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).planOk = true)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hW : ∀ b, s.loc.border = some b → WeightsFit b.g)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h5 : ok (secondRest5 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨B⟩ := hQ.eight
  rw [shared_twelve Zp Np cF B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made] at hA
  exact second_door_five Zp Np cF (beforePointOf Np) hQ
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
    (tailAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w B.b1
      B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made h9 h10) hA x s₁ s hs hW sW h5

end letters

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shared_flat_at
#print axioms ProofFile.Honest.K14.shared_twelve
#print axioms ProofFile.Honest.K14.chainAt_shared
#print axioms ProofFile.Honest.K14.tailLike_shared
#print axioms ProofFile.Honest.K14.tailAt_shared
#print axioms ProofFile.Honest.K14.second_door_shared
