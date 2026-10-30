-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ShapesReachedZero.lean (kind K10): `ShapesAre` AT A REACHED STATE IN FRONT OF THE CLOSING KIND's OWN SUB-PROTOCOL OF LINK 0 (the number 12), AT THE SIX-LIST (the 0th written list: its
members are the five with a main row): the like of MembersPublic.lean | ShapesReached.lean | MembersAtFull.lean | HingeMore.lean (beside this file) at l = 0, where the group has no message of a code switch in
front. A definition with code, closed facts by the kernel, statements and proofs: calls.

What is said. lo := linksFullLit.getD 0 [].
  `membersPubZero N sh`: the members of link 0's group, in their order, off public numbers: the three sendings' messages: the first from 0 on, the later two from the table's counts at the places 5 and 7.
  `members_public_zero`: in scope, under the opening at OnBytes.secondHashFunction and F.planOk, at the cuts 8 + n, n ≤ 4 (n = 4: in front of K10): the open link L of number 0, its frame's group 0, the group G at 0:
    G.members.toList = membersPubZero N sh; and the flags in the shape's words.
  `keptZeroB` [BY THE KERNEL]: at shapeFull these flags are (membersOf lo).map (kbAt shapeFull 0 lo). `keptZeroB_no`: with every flag turned they are not.
  `t3ZeroB` [BY THE KERNEL]: at the written tellings the public list is (membersOf lo).map (noK10 seatsPlanW lo P5T.psFull 0). `t3ZeroB_told`: with the first five tellings dropped it is not.
  `t3_zero`, `t3_zero_at_cut`, `t3_zero_at_laid`: so at any numbers beneath; where the first chain's cut is the written one; where the value is laid.
  `shapesAre_at_fold_zero`, `shapesAre_reached_zero`: **THE JOIN**, at a fold, and at a state reached at 12, under hsh, hT3, hH4.
BY: `flags_zero_named` (Johnson/IMR/FlagsZeroNamed.lean), `members_at` (Johnson/IMR/FrameEntry.lean: the frame's group), `size_at_table`, `flat_358`.

Limits. hsh, hT3, hH4 are premises of the join. In scope; o := OnBytes.secondHashFunction. At a fold that returns. AT THE SIX-LIST: the move to the five-list is in ShapesFiveOfSix.lean. Nothing on soundness.

-/
import Johnson.IMR.FlagsZeroNamed
import Johnson.IMR.EndFive
import Johnson.Desc.First.Close.Law.HingeMore
import Johnson.Desc.First.Close.Law.ShapesReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

/-- **The members of link 0's group, in their order, off public numbers.** -/
def membersPubZero (N : Numbers) (sh : Params.ReqShape) : List Nat :=
  (List.range (Meaning.K2.msgsAt sh 0 0)).map (· + 0) ++
    (List.range (Meaning.K2.msgsAt sh 0 1)).map (· + N.msgsAt IM.placesW[5]?) ++
    (List.range (Meaning.K2.msgsAt sh 0 2)).map (· + N.msgsAt IM.placesW[7]?)

/-- The flags of link 0's group, in the shape's words. -/
def flagsZero (sh : Params.ReqShape) : List Bool :=
  (((K2.frameAtLink sh 0).atMoment 0).map fun m => decide (0 < m.life)) ++
    (((K2.frameAtLink sh 0).atMoment 1).map fun m => decide (0 < m.life)) ++
    (((K2.frameAtLink sh 0).atMoment 2).map fun m => decide (0 < m.life))

/-! ## 1 The closed facts -/

set_option maxRecDepth 1000000 in
/-- **(W) The flags are the written ones.** -/
theorem keptZeroB :
    decide (flagsZero shapeFull = (membersOf (linksFullLit.getD 0 [])).map
      (kbAt shapeFull 0 (linksFullLit.getD 0 []))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With every flag turned they are not. -/
theorem keptZeroB_no :
    decide ((flagsZero shapeFull).map (!·) = (membersOf (linksFullLit.getD 0 [])).map
      (kbAt shapeFull 0 (linksFullLit.getD 0 []))) = false := by decide +kernel

theorem membersPubZero_free (N₀ N₁ : Numbers) (ps : List Place) (told : List (List Oracle))
    (sh : Params.ReqShape) :
    membersPubZero (N₀.withTold ps told) sh = membersPubZero (N₁.withTold ps told) sh := rfl

set_option maxRecDepth 1000000 in
/-- **(W) The two lists are one at link 0.** -/
theorem t3ZeroB :
    decide (membersPubZero (P5T.N0Full.withTold IM.placesW toldCut) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With the first five tellings dropped they differ. -/
theorem t3ZeroB_told :
    decide (membersPubZero (P5T.N0Full.withTold IM.placesW (toldCut.drop 5)) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0)) = false := by
  decide +kernel

theorem t3_zero (N₀ : Numbers) :
    membersPubZero (N₀.withTold IM.placesW toldCut) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0) := by
  rw [membersPubZero_free N₀ P5T.N0Full]
  exact of_decide_eq_true t3ZeroB

theorem t3_zero_at_cut {St Cl : Type} {bs : List (Block St Cl)}
    (hc : VerifiableInference.PlanWritten.cutOf bs = VerifiableInference.PlanWritten.cutFirstFull)
    (N₀ : Numbers) :
    membersPubZero (N₀.withTold IM.placesW (toldOf bs)) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0) := by
  rw [(told_at_written hc).2]
  exact t3_zero N₀

theorem t3_zero_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (N₀ : Numbers) :
    membersPubZero (N₀.withTold IM.placesW (toldOf cF.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 0 []) P5T.psFull 0) :=
  t3_zero_at_cut (hc_at_laid hZ L) N₀

/-! ## 2 At a fold, and at a reached state -/

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE ORDER OF LINK 0's GROUP's MEMBERS IS PUBLIC; AND ITS FLAGS.** -/
theorem members_public_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List Col} {n : Nat} (hn : n ≤ 4)
    {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = 0 ∧ L.check.frame.group = 0 ∧
      t.st.groups[0]? = some G ∧
      G.members.toList =
        membersPubZero (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) Z.first.shape ∧
      G.kept.toList = flagsZero Z.first.shape := by
  obtain ⟨t₃, t₅, R₃, R₅, C₃, C₅, L, G, f₃, f₅, hL, e2, hG, em, -, eo, ek⟩ :=
    Meaning.K2.flags_zero_named hS hR O hn g
  obtain ⟨L', -, -, hL', -, e3, -⟩ := Meaning.K2.members_at hS hR O (l := 0) (by omega)
    (n := 5 + n) (by omega) (by rw [show 14 * 0 + 3 + (5 + n) = 8 + n by omega]; exact g)
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  have hlen := Meaning.K2.flat_358 hS O
  have s3 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 5) (by omega) f₃
  have s5 := Meaning.K2.size_at_table hS hR O hF N₀ (k := 7) (by omega) f₅
  refine ⟨L, G, hL, e2, e3, hG, ?_, ek⟩
  unfold membersPubZero
  rw [← s3, ← s5, em, eo]
  simp [Array.toList_append, Array.toList_map, Array.toList_range]

/-- **THE JOIN, AT A FOLD.** -/
theorem shapesAre_at_fold_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List Col} {n : Nat} (hn : n ≤ 4) {t : S} {r : List Fmt.RoundView} {q : List Col}
    (g : foldBlocks 0 (c.blocksInOrder.take (8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (no : Fin (linksFullLit.getD 0 []).length → Nat)
    (hT3 : membersPubZero (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD 0 []),
      (t.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD 0 []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), t.link? = some L ∧ L.link = 0 ∧ L.check.frame.group = 0 ∧
      t.st.groups[0]? = some G ∧
      ShapesAre t.st G (linksFullLit.getD 0 []) (kbAt shapeFull 0 (linksFullLit.getD 0 []))
        no := by
  obtain ⟨L, G, hL, e2, e3, hG, hm, hk⟩ := members_public_zero hS hR O hF N₀ hn g
  rw [hsh] at hm hk
  exact ⟨L, G, hL, e2, e3, hG, ⟨hm.trans hT3, hk.trans (of_decide_eq_true keptZeroB), hH4⟩⟩

/-- **THE SAME AT A REACHED STATE IN FRONT OF THE CLOSING KIND's OWN SUB-PROTOCOL.** -/
theorem shapesAre_reached_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hsh : Z.first.shape = shapeFull) (N₀ : Numbers) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 12 (z, s))
    (no : Fin (linksFullLit.getD 0 []).length → Nat)
    (hT3 : membersPubZero (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 0 [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD 0 []),
      (s.st.oracles[no i]?).map (fun x : OnBytes.Oracle => x.shape) =
        some ((linksFullLit.getD 0 []).get i).1) :
    ∃ (L : LinkCtx) (G : Group), s.link? = some L ∧ L.link = 0 ∧ L.check.frame.group = 0 ∧
      s.st.groups[0]? = some G ∧
      ShapesAre s.st G (linksFullLit.getD 0 []) (kbAt shapeFull 0 (linksFullLit.getD 0 []))
        no := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact shapesAre_at_fold_zero hS hR O hF hsh N₀ (n := 4) (Nat.le_refl 4) f no hT3 hH4

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.keptZeroB
#print axioms VerifiableInference.Desc.First.Close.keptZeroB_no
#print axioms VerifiableInference.Desc.First.Close.t3ZeroB
#print axioms VerifiableInference.Desc.First.Close.t3ZeroB_told
#print axioms VerifiableInference.Desc.First.Close.t3_zero_at_laid
#print axioms VerifiableInference.Desc.First.Close.members_public_zero
#print axioms VerifiableInference.Desc.First.Close.shapesAre_at_fold_zero
#print axioms VerifiableInference.Desc.First.Close.shapesAre_reached_zero
