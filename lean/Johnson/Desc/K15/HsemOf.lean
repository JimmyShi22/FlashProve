-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/HsemOf.lean: THE RECORDS' ROAD, THE GLUE: from a yes of the link's decision to a
yes of K12's own block's decision at the record in front of the test.
  t12Of d          what the test's enter makes of the carried record
  tail_yes         where the format's fold over the link's two last blocks says yes with nothing
  left over: the rounds that are left fit the test's declared rounds; the columns that are
                   left are just those that Block.step matches and hands; (proximityTestKind guardedProximityTestParts (p12Of
                   P)).decide says yes at t12Of d on them
  test_planOk      where the tests on the plan of the link's description pass, K12's own block's
  test on the plan has passed
No run of `verify-on-bytes`. Nothing on soundness by itself.
-/
import Johnson.Desc.K15.HsemSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)

def t12Of (d : St) : T12 :=
  { st := d.st, book := d.book, roots := d.roots, g := d.loc.g, pass := .nothing, mask :=
      d.loc.firstMask }

theorem testBlock_eq (P : P15) : testBlock P = Block.inside enter (proximityTestKind guardedProximityTestParts (p12Of P)) leave :=
    rfl

theorem tail_yes (P : P15) (d5 d' : St) (rest : List Fmt.RoundView) (cols' : List OpenedColumn)
    (h : foldBlocks 0 (tailOf P) d5 rest cols' = .ok (d', [], [])) :
    ∃ (tE : T12) (k : Nat),
      roundsFit (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds rest = true ∧
      k = ((groupsOf 0 (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds
          (rest.map (·.drawn))).flatMap id).length ∧
      (cols'.take k).map (fun c => (c.1, c.2.1, c.2.2.length)) =
        (groupsOf 0 (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds (rest.map (·.drawn))).flatMap
            id ∧
      (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide (t12Of d5) (rest.map noDigest)
        (regroup ((groupsOf 0 (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds
            (rest.map (·.drawn))).map (·.length))
          (cols'.take k)) = .ok tE := by
  unfold tailOf at h
  obtain ⟨s1, k, _, t1, h⟩ := foldBlocks_cons _ _ _ _ _ _ _ h
  obtain ⟨s2, k2, l2, _, h⟩ := foldBlocks_cons _ _ _ _ _ _ _ h
  have h := foldBlocks_nil _ _ _ _ _ h
  simp only [Prod.mk.injEq] at h
  have hr2 : (chainEnd 1 7 false ((blocksOr P ++ [testBlock P]).flatMap (·.rounds)) fun d : St =>
    untestedL d.st :
      Block St Unit).rounds = [] := rfl
  rw [hr2] at h
  simp only [List.length_nil, List.drop_zero] at h
  have hd : rest.drop (testBlock P).rounds.length = [] := h.2.1.symm
  have ht : rest.take (testBlock P).rounds.length = rest := by
    have := List.take_append_drop (testBlock P).rounds.length rest
    rw [hd, List.append_nil] at this
    exact this
  rw [ht] at t1
  obtain ⟨f1, hk, hc, q⟩ := step_inv 0 (testBlock P) _ _ _ _ _ t1
  rw [testBlock_eq] at f1 hk hc q
  change ((enter d5).bind fun t =>
    ((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide t _ _).bind (leave d5)) = .ok s1 at q
  change (((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide (t12Of d5) _ _).bind (leave d5)) = .ok
      s1 at q
  cases hq : (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide (t12Of d5) (rest.map noDigest)
      (regroup ((groupsOf 0 (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds
          (rest.map (·.drawn))).map (·.length))
        (cols'.take k)) with
  | error e =>
    exfalso
    change (((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).decide (t12Of d5) (rest.map noDigest)
      (regroup ((groupsOf 0 (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds
          (rest.map (·.drawn))).map (·.length))
        (cols'.take k))).bind (leave d5)) = .ok s1 at q
    rw [hq] at q
    cases q
  | ok tE => exact ⟨tE, k, f1, hk, hc, hq⟩

theorem test_planOk (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (descOf P plan ok).planOk = true) :
    (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).planOk = true := by
  have hb := OneChainFileDescription.planOk_blocks _ h
  change blocksOk (chainOf P).blocksInOrder = true at hb
  unfold blocksOk at hb
  rw [List.all_eq_true] at hb
  have hm : ({ testBlock P with planOk := (testBlock P).planOk && (testBlock P).hasNoClaimsAndNothingAfter } : Block St
      Unit) ∈ (chainOf P).blocksInOrder := by
    unfold Chain.blocksInOrder chainOf
    simp
  have := hb _ hm
  simp only [Bool.and_eq_true] at this
  have h1 : (testBlock P).planOk = true := this.1.1
  rw [testBlock_eq] at h1
  change ((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).planOk && _ && _) = true at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

end Desc.K15

#print axioms Desc.K15.tail_yes
#print axioms Desc.K15.test_planOk
