-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BlocksSound.lean: the laws of the linear claim's shared rounds, said of the
shared chain's eight blocks' own decisions.

  blocks_means       where the eight decisions say yes one behind the other and the state reaches
                     the two proximity tests: if all constraints on the two groups hold of words,
                     the three families' equations hold of these words.
  fold_sound_blocks  the first six decisions have said yes; the words of o_omega and o_u are fixed;
                     omega_col is not col_psi_lo(u) at a row of M: then at no more than
                     kRow |K| ^ (kRow - 1) points z_fd can the seventh and the eighth decision say
                     yes, the seventh at a round whose drawn elements read as z_fd, and the state
                     reach the tests so that all constraints hold of words that agree with the fixed
                     ones on these two messages.
  fold_sound_step8   the law of (fold) at the format's step of the eighth block.

What is not claimed. Two codes are a premise. That the constraints hold of words is the proximity
tests' law's to give; that the state behind the eighth block reaches each test's is a premise.
Nothing on how z_fd is drawn, on (rec_gamma) and (loc_x) pinning the folded row, or on "LIN point".
No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.AtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- Where the first six decisions say yes one behind the other, the places up to the joinings have
said yes. -/
theorem sharedFront_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 d4 d5 d6 : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 : List Fmt.RoundView)
    (gs1 gs2 gs3 gs4 gs5 gs6 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (h4 : b4.decide d3 rs4 gs4 = .ok d4)
    (h5 : b5.decide d4 rs5 gs5 = .ok d5) (h6 : b6.decide d5 rs6 gs6 = .ok d6) :
    ∃ r4 cols, rs4 = [r4] ∧ gs4 = [cols] ∧ SharedFront P.par d0 d2 d3 d6 r4 cols := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have k1 : linPoint P.par d0 rs1 = some d1 := why_some h1
  obtain ⟨idsU, a1, a2, rU, cU, cUl, k2⟩ := sendAt_inv _ _ _ _ _ _ d1 d2 rs2 gs2 h2
  have k3 : laysRec P.par d2 rs3 = some d3 := why_some h3
  have k4 : loc P.par d3 rs4 gs4 = some d4 := why_some h4
  obtain ⟨idsO, c1, c2, rO, cO, cOl, k5⟩ := sendAt_inv _ _ _ _ _ _ d4 d5 rs5 gs5 h5
  have k6 : joins P.par d5 rs6 = some d6 := why_some h6
  obtain ⟨r4, cols, rfl, rfl⟩ := loc_one _ _ _ _ _ k4
  rw [parK1_sent] at rU rO
  exact ⟨r4, cols, rfl, rfl, hS, d1, a1, a2, d4, c1, c2, d5, rs1, rs3, rs6, _, _,
    sentU, idsU, idsO, k1, hU, rU, cU, cUl, k2, k3, k4, rO, cO, cOl, k5, k6⟩

/-- The seventh block decides by "LIN zeta". -/
theorem zeta_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ d rs gs d', b7.decide d rs gs = .ok d' → linZeta d rs = some d' := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact fun d rs gs d' h => why_some h

/-- **What the state that the eight blocks hand to the two proximity tests means.** -/
theorem blocks_means (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 d4 d5 d6 d7 d8 eU eO : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView)
    (gs1 gs2 gs3 gs4 gs5 gs6 gs7 gs8 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (h4 : b4.decide d3 rs4 gs4 = .ok d4)
    (h5 : b5.decide d4 rs5 gs5 = .ok d5) (h6 : b6.decide d5 rs6 gs6 = .ok d6)
    (h7 : b7.decide d6 rs7 gs7 = .ok d7) (h8 : b8.decide d7 rs8 gs8 = .ok d8)
    (hU : Reaches d8 eU d8.loc.gU) (hO : Reaches d8 eO d8.loc.gOmega) (m : Words K)
    (sU : Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m)
    (sO : Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m) :
    ∃ r4 cols, rs4 = [r4] ∧ gs4 = [cols] ∧
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
  obtain ⟨r4, cols, e4, f4, hR⟩ := sharedRun_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
    d0 d1 d2 d3 d4 d5 d6 d7 d8 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 gs1 gs2 gs3 gs4 gs5 gs6 gs7 gs8
    h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨r4, cols, e4, f4, shared_means ρ P.par d0 d2 d3 d7 d8 eU eO r4 cols hR hU hO m sU sO⟩

open Classical in
/-- **The law of (fold), of the blocks' own decisions.** -/
theorem fold_sound_blocks [Fintype K] (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 d4 d5 d6 : St)
    (rs1 rs2 rs3 rs4 rs5 rs6 : List Fmt.RoundView)
    (gs1 gs2 gs3 gs4 gs5 gs6 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (h4 : b4.decide d3 rs4 gs4 = .ok d4)
    (h5 : b5.decide d4 rs5 gs5 = .ok d5) (h6 : b6.decide d5 rs6 gs6 = .ok d6) (m : Words K)
    (hgap : ∃ j < P.S.matrixRows, omegaOf d6.loc (linLayOmega d6.st.codes P.S) m j ≠
      ∑ t ∈ Finset.range (2 ^ P.S.kLo),
        eqK ((d6.loc.psiSh.take P.S.kLo).map ρ.val) t * uOf d6.loc m (t + 2 ^ P.S.kLo * j)) :
    (Finset.univ.filter fun z : Fin P.S.kRow → K =>
      ∃ (r7 : Fmt.RoundView) (rs8 : List Fmt.RoundView) (gs7 gs8 : List (List (Nat × List UInt64)))
        (d7 d8 eU eO : St) (m' : Words K),
        (drawn r7).map ρ.val = List.ofFn z ∧ b7.decide d6 [r7] gs7 = .ok d7 ∧
        b8.decide d7 rs8 gs8 = .ok d8 ∧
        Reaches d8 eU d6.loc.gU ∧ Reaches d8 eO d6.loc.gOmega ∧
        AgreeOn d6.loc.oOmega m m' ∧ AgreeOn d6.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d6.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d6.loc.gOmega) m').card ≤
      P.S.kRow * Fintype.card K ^ (P.S.kRow - 1) := by
  obtain ⟨r4, cols, _, _, hF⟩ := sharedFront_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
    d0 d1 d2 d3 d4 d5 d6 rs1 rs2 rs3 rs4 rs5 rs6 gs1 gs2 gs3 gs4 gs5 gs6 h1 h2 h3 h4 h5 h6
  refine le_trans (Finset.card_le_card ?_)
    (fold_sound_run ρ P.par d0 d2 d3 d6 r4 cols hF m hgap)
  intro z hz
  rw [Finset.mem_filter] at hz
  obtain ⟨_, r7, rs8, gs7, gs8, d7, d8, eU, eO, m', hzs, h7, h8, hU, hO, aO, aU, sU, sO⟩ := hz
  have k7 := zeta_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb _ _ _ _ h7
  have k8 := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb _ _ _ _ h8
  obtain ⟨r8, rfl⟩ := split_one _ _ _ _ hS k8
  exact Finset.mem_filter.2
    ⟨Finset.mem_univ _, r7, r8, d7, d8, eU, eO, m', hzs, k7, k8, hU, hO, aO, aU, sU, sO⟩

/-- **The law of (fold) at the format's step of the eighth block.** -/
theorem fold_sound_step8 [Fintype K] (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) : FoldSoundStep ρ P.par b8 :=
  foldSound_step ρ P.par b8 (decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb)

end Desc.K14.Law
