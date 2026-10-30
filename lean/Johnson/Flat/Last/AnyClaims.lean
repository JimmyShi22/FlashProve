-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/AnyClaims.lean: THE KIND K12's BLOCK RUNS ALIKE AT EVERY TYPE OF CLAIMS. The kind's text (proximityTestKind, Johnson/Desc/K12/Frame.lean) is typed at a letter Cl, the type of the claims that a block's runs make; it makes no claim. The kind's law in the plain form
stands at Cl := Unit; at a description the pieces stand at the description's own Cl. Here: what a chain of one block says does not read Cl.

  Block.Alike b' b (b' at Cl', b at Cl): one name, the same rounds, the same decision.
  alike_andThen, alike_at, alike_asks, alike_inside, alike_below, alike_lift: the makers keep it.
  stagesFrom_alike, **k12_alike**: (proximityTestKind X p : Block T Cl') is alike to (proximityTestKind X p : Block T Cl): by induction along the stages.
  **chainAt_alike**: chainAt name ft [b'] s v = chainAt name ft [b] s v where b' is alike to b.

Every "there is", walked: no statement has one.
Limits. Of name, rounds and decision alone: NOT of planOk, oracles, before, place (they agree too, by the same road: not typed: nobody here spends them). Nothing on soundness.

-/
import Johnson.Desc.K12.Frame
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S T Cl Cl' : Type}

/-- One name, the same rounds, the same decision: at two types of claims. -/
def Block.Alike (b' : Block S Cl') (b : Block S Cl) : Prop :=
  b'.name = b.name ∧ b'.rounds = b.rounds ∧ b'.decide = b.decide

theorem openings_alike {b' : Block S Cl'} {b : Block S Cl} (h : b'.Alike b) : b'.openings = b.openings := by
  unfold Block.openings
  rw [h.2.1]

theorem alike_andThen (name : String) {p' q' : Block S Cl'} {p q : Block S Cl} (hp : p'.Alike p) (hq : q'.Alike q) :
    (p'.andThen name q').Alike (p.andThen name q) := by
  refine ⟨rfl, ?_, ?_⟩
  · show p'.rounds ++ q'.rounds = p.rounds ++ q.rounds
    rw [hp.2.1, hq.2.1]
  · show (fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) =>
        (p'.decide s (rs.take p'.rounds.length) (gs.take p'.openings)).bind fun s' =>
        q'.decide s' (rs.drop p'.rounds.length) (gs.drop p'.openings)) =
      fun (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) => (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s' =>
        q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)
    rw [hp.2.2, hq.2.2, hp.2.1, openings_alike hp]

theorem alike_inside (enter : S → Except String T) (leave : S → T → Except String S) {b' : Block T Cl'} {b : Block T Cl}
    (h : b'.Alike b) : (b'.inside enter leave).Alike (b.inside enter leave) := by
  refine ⟨h.1, h.2.1, ?_⟩
  show (fun s rs gs => (enter s).bind fun t => (b'.decide t rs gs).bind (leave s)) =
    fun s rs gs => (enter s).bind fun t => (b.decide t rs gs).bind (leave s)
  rw [h.2.2]

theorem alike_below {b' : Block S Cl'} {b : Block S Cl} (h : b'.Alike b) : (Sound.below b').Alike (Sound.below b) := by
  refine ⟨h.1, h.2.1, ?_⟩
  show (fun s rs gs => if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime") =
    fun s rs gs => if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime"
  rw [h.2.2]

theorem alike_lift (get : T → S) (set : T → S → T) {b' : Block S Cl'} {b : Block S Cl} (h : b'.Alike b) :
    (b'.lift get set).Alike (b.lift get set) := by
  refine ⟨h.1, h.2.1, ?_⟩
  show (fun t rs gs => (b'.decide (get t) rs gs).map (set t)) = fun t rs gs => (b.decide (get t) rs gs).map (set t)
  rw [h.2.2]

/-- **What a chain of one block says does not read the type of its claims.** -/
theorem chainAt_alike {b' : Block S Cl'} {b : Block S Cl} (h : b'.Alike b) (name : String) (ft : ℕ) (s : S) (v : Fmt.View) :
    chainAt name ft [b'] s v = chainAt name ft [b] s v := by
  have hs : ∀ rs cols, b'.step ft s rs cols = b.step ft s rs cols := by
    intro rs cols
    unfold Block.step
    rw [h.2.1, h.2.2]
  have hf : foldBlocks ft [b'] s v.rounds v.opened = foldBlocks ft [b] s v.rounds v.opened := by
    simp only [foldBlocks, List.splitAt_eq]
    rw [h.2.1, h.1, hs]
  unfold chainAt
  rw [hf]
  rfl

namespace K12
open Fmt.M1 (Stage)

theorem alike_at (x : Part T) (name : String) (place : Place) (l : Laid) :
    (x.at name place l : Block T Cl').Alike (x.at name place l : Block T Cl) := ⟨rfl, rfl, rfl⟩

theorem alike_asks (name : String) (place : Place) (ok : T → Bool) :
    (asks name place ok : Block T Cl').Alike (asks name place ok : Block T Cl) := ⟨rfl, rfl, rfl⟩

theorem stagesFrom_alike (X : Parts T) (p : P12) : ∀ (rest : List Stage) (j : ℕ) (cur : Stage) (l : Laid),
    (stagesFrom X p j cur rest l : Block T Cl').Alike (stagesFrom X p j cur rest l : Block T Cl)
  | [], j, cur, l => by
    unfold stagesFrom
    exact alike_at _ _ _ _
  | next :: rest, j, cur, l => by
    unfold stagesFrom
    exact alike_andThen _ (alike_andThen _ (alike_andThen _ (alike_andThen _ (alike_at _ _ _ _) (alike_at _ _ _ _))
      (alike_at _ _ _ _)) (alike_asks _ _ _)) (stagesFrom_alike X p rest _ _ _)

/-- **The proximity test's block runs alike at every type of claims.** -/
theorem k12_alike (X : Parts T) (p : P12) : (proximityTestKind X p : Block T Cl').Alike (proximityTestKind X p : Block T Cl) := by
  unfold proximityTestKind
  rcases p.nums.stages with _ | ⟨first, rest⟩
  · exact ⟨rfl, rfl, rfl⟩
  · rcases H2U.roundsOfNums p.nums with _ | rs
    · exact ⟨rfl, rfl, rfl⟩
    · rcases H2U.testOracles p.nums with _ | os
      · exact ⟨rfl, rfl, rfl⟩
      · -- the refusal's words of the frame's test on the group are not written out: the goal gives them
        have H := fun words : String => alike_andThen (Cl' := Cl') (Cl := Cl) "the test"
          (alike_andThen "the batching" (alike_andThen "the front" (alike_at (X.front p) "the front" p.place [])
            (alike_at (X.bat p (((rs.zip p.oracles).take 1).map (·.1))) "the batching" p.place ((rs.zip p.oracles).take 1)))
            (alike_asks words p.place fun t => (X.group t).any (firstFits first)))
          (stagesFrom_alike X p rest 0 first ((rs.zip p.oracles).drop 1))
        exact ⟨rfl, (H _).2.1, (H _).2.2⟩

end K12

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.chainAt_alike
#print axioms VerifiableInference.Desc.K12.stagesFrom_alike
#print axioms VerifiableInference.Desc.K12.k12_alike
