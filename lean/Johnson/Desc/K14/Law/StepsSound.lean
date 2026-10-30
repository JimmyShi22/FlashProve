-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/StepsSound.lean: the laws of the linear claim's shared rounds, said of the
format's step at each of the shared chain's eight blocks; and the law of (loc_x) of the blocks' own
decisions.

  steps_means        where the eight steps say yes one behind the other and the state reaches the
                     two proximity tests: if all constraints on the two groups hold of words, the
                     three families' equations hold of these words.
  fold_sound_steps   the count at z_fd, of the seventh and the eighth block's steps behind the first
                     six.
  loc_sound_blocks   the first three decisions have said yes; the words of o_u and the table's
                     columns are fixed: the lists of c locations at which the other five decisions
                     can say yes, the fourth at a round that draws these locations and off columns
                     that are the table's, and the state reach the tests so that all constraints
                     hold of words that agree with the fixed ones on o_u, are no more than g ^ c.

What is not claimed. A step shows a decision its rounds without the sealed digest: the laws speak of
these. Two codes are a premise. That the steps stand one behind the other in a file's fold, on
consecutive rounds, is not shown here. That the constraints hold of words is the proximity tests'
law's to give. Nothing on the number g. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.BlocksSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest OpenedColumn)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- A round without the sealed digest draws the same elements. -/
theorem drawn_noDigest (r : Fmt.RoundView) : drawn (noDigest r) = drawn r := rfl

/-- **What the state that the eight steps hand to the two proximity tests means.** -/
theorem steps_means (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d0 d1 d2 d3 d4 d5 d6 d7 d8 eU eO : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView)
    (c1 c2 c3 c4 c5 c6 c7 c8 : List OpenedColumn) (k1 k2 k3 k4 k5 k6 k7 k8 : Nat)
    (h1 : b1.step ft d0 rs1 c1 = .ok (d1, k1)) (h2 : b2.step ft d1 rs2 c2 = .ok (d2, k2))
    (h3 : b3.step ft d2 rs3 c3 = .ok (d3, k3)) (h4 : b4.step ft d3 rs4 c4 = .ok (d4, k4))
    (h5 : b5.step ft d4 rs5 c5 = .ok (d5, k5)) (h6 : b6.step ft d5 rs6 c6 = .ok (d6, k6))
    (h7 : b7.step ft d6 rs7 c7 = .ok (d7, k7)) (h8 : b8.step ft d7 rs8 c8 = .ok (d8, k8))
    (hU : Reaches d8 eU d8.loc.gU) (hO : Reaches d8 eO d8.loc.gOmega) (m : Words K)
    (sU : Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m)
    (sO : Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m) :
    ∃ (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)), rs4.map noDigest = [r4] ∧
    (∀ x ∈ d2.loc.key.seeds.zipIdx,
      RecEq P.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (fun r => ρ.val ((weights P.S d2.loc).getD r zeroE))
        (fun k => ρ.val (d2.loc.key.record.getD k zeroE))
        (fun k => m d2.loc.oU.oracle .main (d2.loc.oU.lay.index k))) ∧
    (∀ x ∈ locations P.par r4, ∃ col, cols.lookup x = some col ∧
      LocEq ρ P.S.fold (generatorAt P.S.fold.index.code x)
        (fun r => ρ.val ((weights P.S d3.loc).getD r zeroE)) (weights P.S d3.loc).size
        (fun r => ρ.val (ofF (col.toArray.getD r 0)))
        (fun k => m d3.loc.oU.oracle .main (d3.loc.oU.lay.index k))) ∧
    FoldEq P.S ((d7.loc.psiSh.take P.S.kLo).map ρ.val) (d7.loc.zFd.map ρ.val)
      (omegaOf d7.loc (linLayOmega d7.st.codes P.S) m) (uOf d7.loc m) := by
  obtain ⟨g1, e1⟩ := step_decides ft b1 d0 d1 rs1 c1 k1 h1
  obtain ⟨g2, e2⟩ := step_decides ft b2 d1 d2 rs2 c2 k2 h2
  obtain ⟨g3, e3⟩ := step_decides ft b3 d2 d3 rs3 c3 k3 h3
  obtain ⟨g4, e4⟩ := step_decides ft b4 d3 d4 rs4 c4 k4 h4
  obtain ⟨g5, e5⟩ := step_decides ft b5 d4 d5 rs5 c5 k5 h5
  obtain ⟨g6, e6⟩ := step_decides ft b6 d5 d6 rs6 c6 k6 h6
  obtain ⟨g7, e7⟩ := step_decides ft b7 d6 d7 rs7 c7 k7 h7
  obtain ⟨g8, e8⟩ := step_decides ft b8 d7 d8 rs8 c8 k8 h8
  obtain ⟨r4, cols, f4, _, hM⟩ := blocks_means ρ P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
    d0 d1 d2 d3 d4 d5 d6 d7 d8 eU eO _ _ _ _ _ _ _ _ g1 g2 g3 g4 g5 g6 g7 g8
    e1 e2 e3 e4 e5 e6 e7 e8 hU hO m sU sO
  exact ⟨r4, cols, f4, hM⟩

open Classical in
/-- **The law of (fold), of the blocks' steps.** -/
theorem fold_sound_steps [Fintype K] (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d0 d1 d2 d3 d4 d5 d6 : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 : List Fmt.RoundView) (c1 c2 c3 c4 c5 c6 : List OpenedColumn)
    (k1 k2 k3 k4 k5 k6 : Nat)
    (h1 : b1.step ft d0 rs1 c1 = .ok (d1, k1)) (h2 : b2.step ft d1 rs2 c2 = .ok (d2, k2))
    (h3 : b3.step ft d2 rs3 c3 = .ok (d3, k3)) (h4 : b4.step ft d3 rs4 c4 = .ok (d4, k4))
    (h5 : b5.step ft d4 rs5 c5 = .ok (d5, k5)) (h6 : b6.step ft d5 rs6 c6 = .ok (d6, k6))
    (m : Words K)
    (hgap : ∃ j < P.S.matrixRows, omegaOf d6.loc (linLayOmega d6.st.codes P.S) m j ≠
      ∑ t ∈ Finset.range (2 ^ P.S.kLo),
        eqK ((d6.loc.psiSh.take P.S.kLo).map ρ.val) t * uOf d6.loc m (t + 2 ^ P.S.kLo * j)) :
    (Finset.univ.filter fun z : Fin P.S.kRow → K =>
      ∃ (r7 : Fmt.RoundView) (rs8 : List Fmt.RoundView) (c7 c8 : List OpenedColumn) (k7 k8 : Nat)
        (d7 d8 eU eO : St) (m' : Words K),
        (drawn r7).map ρ.val = List.ofFn z ∧ b7.step ft d6 [r7] c7 = .ok (d7, k7) ∧
        b8.step ft d7 rs8 c8 = .ok (d8, k8) ∧
        Reaches d8 eU d6.loc.gU ∧ Reaches d8 eO d6.loc.gOmega ∧
        AgreeOn d6.loc.oOmega m m' ∧ AgreeOn d6.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d6.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d6.loc.gOmega) m').card ≤
      P.S.kRow * Fintype.card K ^ (P.S.kRow - 1) := by
  obtain ⟨g1, e1⟩ := step_decides ft b1 d0 d1 rs1 c1 k1 h1
  obtain ⟨g2, e2⟩ := step_decides ft b2 d1 d2 rs2 c2 k2 h2
  obtain ⟨g3, e3⟩ := step_decides ft b3 d2 d3 rs3 c3 k3 h3
  obtain ⟨g4, e4⟩ := step_decides ft b4 d3 d4 rs4 c4 k4 h4
  obtain ⟨g5, e5⟩ := step_decides ft b5 d4 d5 rs5 c5 k5 h5
  obtain ⟨g6, e6⟩ := step_decides ft b6 d5 d6 rs6 c6 k6 h6
  refine le_trans (Finset.card_le_card ?_)
    (fold_sound_blocks ρ P b1 b2 b3 b4 b5 b6 b7 b8 hb hS d0 d1 d2 d3 d4 d5 d6 _ _ _ _ _ _
      g1 g2 g3 g4 g5 g6 e1 e2 e3 e4 e5 e6 m hgap)
  intro z hz
  rw [Finset.mem_filter] at hz
  obtain ⟨_, r7, rs8, c7, c8, k7, k8, d7, d8, eU, eO, m', hzs, h7, h8, hU, hO, aO, aU, sU, sO⟩ :=
    hz
  obtain ⟨g7, e7⟩ := step_decides ft b7 d6 d7 [r7] c7 k7 h7
  obtain ⟨g8, e8⟩ := step_decides ft b8 d7 d8 rs8 c8 k8 h8
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, noDigest r7, _, g7, g8, d7, d8, eU, eO, m',
    hzs, e7, e8, hU, hO, aO, aU, sU, sO⟩

open Classical in
/-- **The law of (loc_x), of the blocks' own decisions.** -/
theorem loc_sound_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 : St) (rs1 rs2 rs3 : List Fmt.RoundView)
    (gs1 gs2 gs3 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (m : Words K) (tab : Nat → List UInt64) (c : Nat) :
    (Finset.univ.filter fun Q : Fin c → Fin (2 ^ P.S.fold.index.code.logN) =>
      ∃ (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)) (rs5 rs6 rs7 rs8 : List Fmt.RoundView)
        (gs5 gs6 gs7 gs8 : List (List (Nat × List UInt64))) (d4 d5 d6 d7 d8 eU eO : St)
        (m' : Words K),
        r4.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
        (∀ x col, cols.lookup x = some col → col = tab x) ∧
        b4.decide d3 [r4] [cols] = .ok d4 ∧ b5.decide d4 rs5 gs5 = .ok d5 ∧
        b6.decide d5 rs6 gs6 = .ok d6 ∧ b7.decide d6 rs7 gs7 = .ok d7 ∧
        b8.decide d7 rs8 gs8 = .ok d8 ∧
        Reaches d8 eU d8.loc.gU ∧ Reaches d8 eO d8.loc.gOmega ∧ AgreeOn d3.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m').card ≤
    (Finset.univ.filter fun x : Fin (2 ^ P.S.fold.index.code.logN) =>
      LocAt ρ P.par d3 m tab x.val).card ^ c := by
  refine le_trans (Finset.card_le_card ?_) (loc_sound_run ρ P.par d0 d2 d3 m tab c)
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  obtain ⟨_, r4, cols, rs5, rs6, rs7, rs8, gs5, gs6, gs7, gs8, d4, d5, d6, d7, d8, eU, eO, m',
    hr, htab, h4, h5, h6, h7, h8, hU, hO, aU, sU, sO⟩ := hQ
  obtain ⟨r4', cols', e4, f4, hR⟩ := sharedRun_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
    d0 d1 d2 d3 d4 d5 d6 d7 d8 rs1 rs2 rs3 [r4] rs5 rs6 rs7 rs8 gs1 gs2 gs3 [cols] gs5 gs6 gs7 gs8
    h1 h2 h3 h4 h5 h6 h7 h8
  obtain rfl : r4 = r4' := by simpa using e4
  obtain rfl : cols = cols' := by simpa using f4
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, r4, cols, d7, d8, eU, eO, m', hr, htab, hR,
    hU, hO, aU, sU, sO⟩

end Desc.K14.Law
