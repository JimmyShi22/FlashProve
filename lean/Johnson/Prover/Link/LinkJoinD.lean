-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinD.lean: THE JOIN, FOURTH PART: THE WALK OVER THE CHAIN's LAST TWO
SUB-PROTOCOLS, general in P. Statement and proof: where the test's front, its batching, the test's
question whether the group is the first stage's and the stages accept "BAT"'s round, the stages'
rounds and the groups that
the chain's walk reads, and nothing is left untested at the state that the stages leave, the chain's
walk (Walks, ChainDefs.lean) goes through the test's sub-protocol and the chain's end as Chain.blocksInOrder
lays them.
The join: the proof of link_yes (LinkJoinF.lean), in six files: LinkJoinA to LinkJoinF.

  laid_cons     a plan whose first laid round passes batCut: laidOf is that round, which reads no
                column, and the rest
  walk_tail     the statement

By: k12_yes (TestYes.lean) · testBlock_yes | end_yes (TestEnd.lean) · k12_letters (LinkJoinB.lean) ·
the library's H2K.Sw.k12_rounds.
Not shown here. That any of these accepts. Nothing on soundness; nothing on what any value that is
sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkJoinB
import Johnson.Prover.Link.TestYes
import Johnson.Prover.Link.TestEnd
import Johnson.Prover.Link.FormBat
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (readG)
open _root_.Desc.K15 (P15 St p12Of t12Of testBlock linkProtocolChain)
open H2K.JointK (laidOf)

theorem laid_cons (l : Laid) (h : batCut ((l.take 1).map (·.1)) = true) :
    ∃ a, l = a :: l.drop 1 ∧ a.1.stored = [] ∧ a.1.opens = [] := by
  cases l with
  | nil => cases h
  | cons a tl =>
    have h' : (batEntry a.1.entry && a.1.stored.isEmpty && a.1.opens.isEmpty) = true := h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h'
    exact ⟨a, rfl, h'.1.2, h'.2⟩

theorem walk_tail (P : P15) (L : ℕ → ℕ → Option (List UInt64)) (d' : St) (D5 : Fmt.Drawn)
    (Brs : List Fmt.RoundView) (Bgs : List (List (ℕ × List UInt64))) (first : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (t₁ t' : T12)
    (hp : (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).planOk = true)
    (hs : (p12Of P).nums.stages = first :: rest)
    (hlen : Brs.length = ((laidOf (p12Of P)).drop 1).length)
    (hcut : batCut (((laidOf (p12Of P)).take 1).map (·.1)) = true)
    (h0 : (guardedProximityTestParts.front (p12Of P)).decide (t12Of d') [] [] = .ok (t12Of d'))
    (h1 : (guardedProximityTestParts.bat (p12Of P) (((laidOf (p12Of P)).take 1).map (·.1))).decide (t12Of d')
      [noDigest ⟨[], D5⟩] [] = .ok t₁)
    (h2 : (guardedProximityTestParts.group t₁).any (firstFits first) = true)
    (h3 : (stagesFrom guardedProximityTestParts (p12Of P) 0 first rest ((laidOf (p12Of P)).drop 1) :
      Block T12 Unit).decide t₁ (Brs.map noDigest) Bgs = .ok t')
    (hg : (groupsOf 0 (((laidOf (p12Of P)).drop 1).map (·.1)) (Brs.map (·.drawn))).map (readG L) =
      Bgs)
    (hN : ChainEnd.NothingLeft t'.st) :
    Walks 0 L
      [{ testBlock P with planOk := (testBlock P).planOk && (testBlock P).hasNoClaimsAndNothingAfter },
        { (linkProtocolChain P).last with planOk := (linkProtocolChain P).last.planOk && (linkProtocolChain P).last.hasNoClaimsAndNothingAfter }]
      d' (⟨[], D5⟩ :: Brs) { d' with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨a, hl, ha1, ha2⟩ := laid_cons _ hcut
  obtain ⟨f', r', ds, os, e1, e2, e3⟩ := k12_letters (p12Of P) hp
  have ez : ds.zip (p12Of P).oracles = laidOf (p12Of P) := by
    unfold laidOf
    rw [e2]
    rfl
  have hr : (testBlock P).rounds = (laidOf (p12Of P)).map (·.1) :=
    H2K.Sw.k12_rounds guardedProximityTestParts (p12Of P) hp
  have hn : (testBlock P).rounds.length = (⟨[], D5⟩ :: Brs : List Fmt.RoundView).length := by
    rw [hr, List.length_map, hl, List.length_cons, List.length_cons, hlen]
  have hk : (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide (t12Of d')
      ((⟨[], D5⟩ :: Brs : List Fmt.RoundView).map noDigest) Bgs = .ok t' := by
    refine k12_yes guardedProximityTestParts (p12Of P) first rest ds os (t12Of d') (t12Of d') t₁ t' _ _ hs e2 e3 h0
      ?_ h2 ?_
    · rw [ez]
      have q1 :
          (batAt guardedProximityTestParts (p12Of P) (laidOf (p12Of P)) : Block T12 Unit).rounds.length = 1 := by
        show (((laidOf (p12Of P)).take 1).map (·.1)).length = 1
        rw [hl]
        rfl
      have q2 : (batAt guardedProximityTestParts (p12Of P) (laidOf (p12Of P)) : Block T12 Unit).openings = 0 := by
        show (((laidOf (p12Of P)).take 1).map (·.1)).foldl
          (fun n r => n + r.stored.length + r.opens.length) 0 = 0
        rw [hl]
        show 0 + a.1.stored.length + a.1.opens.length = 0
        rw [ha1, ha2]
        rfl
      rw [q1, q2]
      exact h1
    · rw [ez]
      have q1 :
          (batAt guardedProximityTestParts (p12Of P) (laidOf (p12Of P)) : Block T12 Unit).rounds.length = 1 := by
        show (((laidOf (p12Of P)).take 1).map (·.1)).length = 1
        rw [hl]
        rfl
      have q2 : (batAt guardedProximityTestParts (p12Of P) (laidOf (p12Of P)) : Block T12 Unit).openings = 0 := by
        show (((laidOf (p12Of P)).take 1).map (·.1)).foldl
          (fun n r => n + r.stored.length + r.opens.length) 0 = 0
        rw [hl]
        show 0 + a.1.stored.length + a.1.opens.length = 0
        rw [ha1, ha2]
        rfl
      rw [q1, q2]
      exact h3
  have hG : (groupsOf 0 (testBlock P).rounds ((⟨[], D5⟩ :: Brs : List Fmt.RoundView).map (·.drawn))).map
      (readG L) = Bgs := by
    rw [hr, hl]
    show (groupsOf 0 (a.1 :: ((laidOf (p12Of P)).drop 1).map (·.1))
      (D5 :: Brs.map (·.drawn))).map (readG L) = Bgs
    unfold groupsOf
    rw [ha1, ha2]
    exact hg
  refine ⟨{ d' with st := t'.st, book := t'.book, roots := t'.roots }, ?_,
    { d' with st := t'.st, book := t'.book, roots := t'.roots }, ?_, ?_, rfl⟩
  · show (testBlock P).decide d'
      (((⟨[], D5⟩ :: Brs : List Fmt.RoundView).take (testBlock P).rounds.length).map noDigest)
      ((groupsOf 0 (testBlock P).rounds
        (((⟨[], D5⟩ :: Brs : List Fmt.RoundView).take (testBlock P).rounds.length).map (·.drawn))).map
        (readG L)) = _
    rw [hn, List.take_length, hG]
    exact testBlock_yes P d' (t12Of d') t' _ _ rfl hk
  · exact end_yes P _ [] [] hN
  · show (((⟨[], D5⟩ :: Brs : List Fmt.RoundView).drop (testBlock P).rounds.length).drop
      (linkProtocolChain P).last.rounds.length) = []
    rw [hn, List.drop_length]
    rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.laid_cons
#print axioms Johnson.Prover.Link.walk_tail
