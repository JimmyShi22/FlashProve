-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2HeadOk.lean: THE HEAD's OWN HALF OF THE TEST ON THE PLAN AT «H:2» (the
code switch's lot's block at the head's link, link 24: the 24th of the lot's 25 blocks): the
hypothesis hH of Johnson/AtFull/Desc/Lots/K2Row.lean ((pureLetters G 24).map headPlanOk = some
true: the head's link's letters are there and pass the three tests of
Johnson/Top/H0/Tw/K2C/Head.lean): WHAT OF IT IS A LAW BY THE MAKE, off the planner's return, and
what stays owed by field. General in the files: no «decide», no opening, no pin «in scope»; the
full size's numerals 24, 12 and 400 stand in statements. NO BLOCK IMPORTS THIS FILE.
  hH_of_six          THE JOIN: hH from the built link at 24 and six clauses: the list of arrays is
                     closed · it has the plan's entries · the arrays are the plan's by name, rows,
                     columns and number of virtual rows · the owner has a stream's table · its
                     last key is the border's · the head's plan has a third index
  U3 · U3.same · shapeF_u3   the tail that is shaped with the third vector alone numbers it 0:
                             after shapeF_u (OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean),
                             whose own proof shows the whole numbering and keeps «some one of the
                             four»
  planH2_three       BY THE MAKE: Head.planH2 … = .ok hp ⟹ hp.Tp.planned = true ∧
                     O.tl.ix.TX.isEmpty = false ∧ hp.tl.ix.U.getD 2 none = some 0
  public_head_three  the same at Verify.publicOf's return, at X's own fields: none of the three
                     reads the trimmed Fp
  hH_of_public       hH from publicOf's return at the ground's public parameters, WITH WHAT STAYS
                     OWED BY FIELD: hb · hTp · hFp (the built link at 24 has the head's plan's
                     list and arrays) · hK (the owner's last table's key is the border's)
  hH_of_public_400   the same with hK cut into two equations with the numeral 400, each on one
                     field: for whoever holds the owner's plan and the layout as closed terms
  head_link_at_blank · hH_at_blank   hb · hTp · hFp PAID at a blank ground: from pubPlain's and
                                     blankBy's returns, twelve groups and attention on: so of hH
                                     there stay the three returns, these two facts and hK
  rejects_of · no_planned · no_nt · no_sig · no_TX · no_key · no_U3   NEGATIVE FACTS, general in
                                                                      the ground: where one of the
                                                                      six clauses fails, the test
                                                                      rejects
  OF THE LAST SIX: the premises of no_TX and no_U3 cannot be met where the ground's public
  parameters are publicOf's value (public_head_three); those of no_nt and no_sig cannot be met
  where the built link at 24 has the head's plan's list and arrays, as at a blank ground with
  twelve groups and attention on (head_link_at_blank); no_planned's cannot be met where both
  conditions hold; no_key's cannot be met where hK holds
planH2_three's cut of the planner follows planH2_u's script (OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean)
line for line; the two local tactics are that file's.
THE OTHER HALF of that block's test on the plan (the switch's own four tests; that the place's
numbers are found; that it stands at the head, at link 24) lies in K2Row.lean: by Lean's kernel at
the written sizes.
LIMITS. hK IS NO TEST OF planH2's AND IS NOT SHOWN HERE: it stays a premise of every statement that
needs it. At VerifierAndGoals.storedPublicFiles's public part, at the second hash function (synthetic weights), Lean's
evaluator has once said true of it: evidence, no proof; the sheet is not in this library. hTp and
hFp ask the whole list and the whole arrays, where the test reads less. The full size alone: at a
size with fewer links nothing is built at 24. That publicOf returns is not shown here.
No soundness is claimed.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHasU
import Johnson.Desc.ProofFile.Lot.K2
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Tw.K2C.Yard
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok ite_ok)
open Fo (SameP)
open P1K2 (pureLetters)
open VerifiableInference.Desc.First.K2 (headPlanOk headPlanOk_iff handedOk_iff arraySig)

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-- **THE JOIN.** -/
theorem hH_of_six {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (p1a : b.Tp.planned = true) (p1b : b.Tp.nt = G.W.H.Tp.nt)
    (p1c : b.Fp.trees.map arraySig = G.W.H.Fp.trees.map arraySig)
    (p2a : G.W.owner.tl.ix.TX.isEmpty = false)
    (p2b : G.W.owner.tl.kTX.back? = some (Verify.borderOf G.W.y).kxb)
    (p3 : (G.W.H.tl.ix.U.getD 2 none).isSome = true) :
    (pureLetters G 24).map headPlanOk = some true := by
  unfold pureLetters
  rw [hb]
  simp only [Option.map_some]
  rw [(headPlanOk_iff _).2 ⟨(handedOk_iff _ _ _).2 ⟨p1a, p1b, p1c⟩, ⟨p2a, p2b⟩, p3⟩]

/-- The third vector has the number 0. -/
def U3 (tl : HTailF2) : Prop := tl.ix.U.getD 2 none = some 0

theorem U3.same {a b : HTailF2} (h : U3 a) (k : SameP a b) : U3 b := by
  have e : b.ix = a.ix := congrArg (·.ix) k.eq
  unfold U3
  rw [e]
  exact h

theorem shapeF_u3 {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (e : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') : U3 tl' := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨r2, h2, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj h2
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨_, _, _, hi, _⟩ := Fo.PiecesF.piecesF_pieceOK_walk e
  unfold U3
  rw [hi]
  show (#[none, none, some 0, none] : Array (Option Nat)).getD 2 none = some 0
  rfl

/-- **BY THE MAKE.** -/
theorem planH2_three (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    hp.Tp.planned = true ∧ O.tl.ix.TX.isEmpty = false ∧ hp.tl.ix.U.getD 2 none = some 0 := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp2, hT, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    refine ⟨?_, ?_, (shapeF_u3 hS).same ((addTreesF_sameP hA).trans (ownerHeld_sameP hO))⟩
    · unfold t2Plan at hT
      split at hT
      · cases hT
      · cases hT
        rfl
    · unfold Head.ownerHeld at hO
      dsimp only at hO
      split at hO
      · rename_i t ht
        cases hE : O.tl.ix.TX.isEmpty with
        | false => rfl
        | true =>
          have h0 : O.tl.ix.TX = #[] := by simpa using hE
          rw [h0] at ht
          simp at ht
      · obtain ⟨_, hx, _⟩ := bindE_ok hO
        cases hx
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem public_head_three {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    X.H.Tp.planned = true ∧ X.owner.tl.ix.TX.isEmpty = false ∧
      X.H.tl.ix.U.getD 2 none = some 0 := by
  obtain ⟨H0, h0, e⟩ := public_H h
  obtain ⟨a, b, c⟩ := planH2_three _ _ _ _ _ _ _ H0 h0
  rw [e]
  exact ⟨a, b, c⟩

/-- **hH, with what stays owed by field.** -/
theorem hH_of_public {pol KL : ByteArray} {layout : Option ByteArray} {G : ProofFile.Ground} {b}
    (hX : Verify.publicOf pol KL layout = .ok G.W) (hb : G.built[24]? = some b)
    (hTp : b.Tp = G.W.H.Tp) (hFp : b.Fp = G.W.H.Fp)
    (hK : G.W.owner.tl.kTX.back? = some (Verify.borderOf G.W.y).kxb) :
    (pureLetters G 24).map headPlanOk = some true := by
  obtain ⟨a, c, d⟩ := public_head_three hX
  exact hH_of_six hb (by rw [hTp]; exact a) (by rw [hTp]) (by rw [hFp]) c hK
    (by rw [d]; rfl)

/-- hK cut into two equations with a numeral, each on one field. -/
theorem hH_of_public_400 {pol KL : ByteArray} {layout : Option ByteArray} {G : ProofFile.Ground} {b}
    (hX : Verify.publicOf pol KL layout = .ok G.W) (hb : G.built[24]? = some b)
    (hTp : b.Tp = G.W.H.Tp) (hFp : b.Fp = G.W.H.Fp)
    (k1 : G.W.owner.tl.kTX.back? = some 400) (k2 : (Verify.borderOf G.W.y).kxb = 400) :
    (pureLetters G 24).map headPlanOk = some true :=
  hH_of_public hX hb hTp hFp (by rw [k1, k2])

/-- **The built link at 24 of a blank ground has the head's plan's list and arrays.** -/
theorem head_link_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hN : Z.p.X.NGr = 12)
    (hq : Z.p.X.p4 = true) :
    ∃ b, G.built[24]? = some b ∧ b.Tp = G.W.H.Tp ∧ b.Fp = G.W.H.Fp := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  obtain ⟨ls, hl, eW, eB, -⟩ := IM.blank_ground hG
  unfold ProofFile.Plain.linksPlain at h₀ hl
  rw [hN, hq] at h₀ hB hl
  obtain ⟨-, -, l, e24, I⟩ := Meaning.links_alternate h₀ hB hl
  exact ⟨l, by rw [eB]; exact e24, by rw [eW]; exact I.Tp, by rw [eW]; exact I.Fp⟩

/-- **hH at a blank ground.** -/
theorem hH_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray}
    {layout : Option ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hN : Z.p.X.NGr = 12) (hq : Z.p.X.p4 = true)
    (hX : Verify.publicOf pol' KL' layout = .ok Z.p.X)
    (hK : Z.p.X.owner.tl.kTX.back? = some (Verify.borderOf Z.p.X.y).kxb) :
    (pureLetters G 24).map headPlanOk = some true := by
  obtain ⟨b, hb, hTp, hFp⟩ := head_link_at_blank hZ hG hN hq
  obtain ⟨-, -, eW, -, -⟩ := IM.blank_ground hG
  exact hH_of_public (by rw [eW]; exact hX) hb hTp hFp (by rw [eW]; exact hK)

/-! ## Negative facts: where one of the six clauses fails, the test rejects -/

theorem rejects_of {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (hn : ¬ (b.Tp.planned = true ∧ b.Tp.nt = G.W.H.Tp.nt ∧
      b.Fp.trees.map arraySig = G.W.H.Fp.trees.map arraySig ∧
      G.W.owner.tl.ix.TX.isEmpty = false ∧
      G.W.owner.tl.kTX.back? = some (Verify.borderOf G.W.y).kxb ∧
      (G.W.H.tl.ix.U.getD 2 none).isSome = true)) :
    (pureLetters G 24).map headPlanOk = some false := by
  unfold pureLetters
  rw [hb]
  simp only [Option.map_some]
  congr 1
  apply Bool.eq_false_iff.2
  intro hk
  obtain ⟨k1, ⟨k2, k3⟩, k4⟩ := (headPlanOk_iff _).1 hk
  obtain ⟨j1, j2, j3⟩ := (handedOk_iff _ _ _).1 k1
  exact hn ⟨j1, j2, j3, k2, k3, k4⟩

theorem no_planned {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : b.Tp.planned = false) : (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => by rw [h] at k; cases k.1

theorem no_nt {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : b.Tp.nt ≠ G.W.H.Tp.nt) : (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => h k.2.1

theorem no_sig {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : b.Fp.trees.map arraySig ≠ G.W.H.Fp.trees.map arraySig) :
    (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => h k.2.2.1

theorem no_TX {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : G.W.owner.tl.ix.TX.isEmpty = true) : (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => by rw [h] at k; cases k.2.2.2.1

theorem no_key {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : G.W.owner.tl.kTX.back? ≠ some (Verify.borderOf G.W.y).kxb) :
    (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => h k.2.2.2.2.1

theorem no_U3 {G : ProofFile.Ground} {b} (hb : G.built[24]? = some b)
    (h : G.W.H.tl.ix.U.getD 2 none = none) : (pureLetters G 24).map headPlanOk = some false :=
  rejects_of hb fun k => by rw [h] at k; cases k.2.2.2.2.2

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.hH_of_six
#print axioms Johnson.AtFull.Lots.K2.U3.same
#print axioms Johnson.AtFull.Lots.K2.shapeF_u3
#print axioms Johnson.AtFull.Lots.K2.planH2_three
#print axioms Johnson.AtFull.Lots.K2.public_head_three
#print axioms Johnson.AtFull.Lots.K2.hH_of_public
#print axioms Johnson.AtFull.Lots.K2.hH_of_public_400
#print axioms Johnson.AtFull.Lots.K2.head_link_at_blank
#print axioms Johnson.AtFull.Lots.K2.hH_at_blank
#print axioms Johnson.AtFull.Lots.K2.rejects_of
#print axioms Johnson.AtFull.Lots.K2.no_planned
#print axioms Johnson.AtFull.Lots.K2.no_nt
#print axioms Johnson.AtFull.Lots.K2.no_sig
#print axioms Johnson.AtFull.Lots.K2.no_TX
#print axioms Johnson.AtFull.Lots.K2.no_key
#print axioms Johnson.AtFull.Lots.K2.no_U3
