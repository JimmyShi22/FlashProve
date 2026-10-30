-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/TwoAnswers.lean: how the first answer of the link prover's algorithm changes
when the first table's rows change in one coefficient.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Where the first table's rows change in one coefficient, the first answer of
the link prover's algorithm changes by an explicit product of three factors, at the same coins and
verifier challenges. Where none of the factors is 0, the entry is not the pad's and the list of
stages is not empty, the two runs disclose different values. The prover's algorithm writes two
answers to the link proof's own OOD samples in the clear, in its third round (lFront,
Johnson/Prover/Link/LinkAll.lean). The first reads the prover's data through the first table's rows'
polynomials alone, the coins through one pad, and the verifier challenges through the first two
rounds. Let the first table's rows of the data X' be those of X plus δ at the coefficient k₀ of row
r₀ (oneCoeff r₀ k₀ δ), with k₀ in the message's part.
  answer_moves   at the same coins and challenges, the first answer for X' is the first answer
                 for X plus (the sample's coefficient at that entry) · eqk γ r₀ · δ. Here γ is
                 the point, sampled in round 0, at which the fold combines the rows.
  front_moves    so, if the entry is not the pad's and the three factors are not 0, the two
                 runs' fronts differ.
  shown_moves    where the list of stages is not empty, if the fronts of two runs differ, what
                 the two runs disclose (shownOf of linkAll) differs.
This is a negative fact: two things differ.

How it fits. Johnson/LinkSim/AtHome/TwoIndices.lean applies these at the full size, to two indices
that differ in one cell (OneCell.lean).

Other names (namespace OnBytes.LinkSim.AtText).
  oneCoeff r₀ k₀ δ   the table that holds δ at the coefficient k₀ of the row r₀, and 0 elsewhere.
  foldAll_oneCoeff   its fold at γ holds eqk γ r₀ · δ at k₀.
  membMsg_one        a polynomial with one coefficient, in the message's part, is placed at one
                     entry.
  lMem_moves         so the first member's message changes at one entry.
  mat_putAt          the sample's coefficient at an entry that is not the pad's.
  ans_of_fronts      two equal fronts have the same answers.
  length_lFront      a front has five rounds.

Limits.
- All of this is for arbitrary parameters: that verifier challenges at which the two factors that
  they determine are not 0 come from a verifier message, and that two indices give such data, is not
  said here.

Notes.
- Both open points of the limit above are proved at the full size, at one verifier message and one
  change of one cell, in Johnson/LinkSim/AtHome/TwoIndices.lean (eqk_seed_home, eqk_fold_home,
  homeIn_bump, answer_home).
- The second table's rows are arbitrary: they may move too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ShortTail

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open Johnson.Prover.Link

/-- δ at the coefficient k₀ of the row r₀; 0 elsewhere. -/
def oneCoeff {S : Sz} (r₀ : Fin S.P.v → Bool) (k₀ : S.Co) (δ : GE) :
    (Fin S.P.v → Bool) → S.Co → GE := fun r => if r = r₀ then Pi.single k₀ δ else 0

theorem foldAll_oneCoeff {S : Sz} (γ : Fin S.P.v → GE) (r₀ : Fin S.P.v → Bool) (k₀ : S.Co)
    (δ : GE) :
    foldAll γ (oneCoeff r₀ k₀ δ) = Pi.single k₀ (Alg.eqk γ r₀ * δ) := by
  show (∑ v, Alg.eqk γ v • oneCoeff r₀ k₀ δ v) = _
  rw [Finset.sum_eq_single r₀ (fun v _ hv => by
    unfold oneCoeff
    rw [if_neg hv, smul_zero]) fun h => absurd (Finset.mem_univ _) h]
  unfold oneCoeff
  rw [if_pos rfl]
  funext k
  by_cases hk : k = k₀
  · rw [hk]
    show Alg.eqk γ r₀ * (Pi.single k₀ δ : S.Co → GE) k₀ = _
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · show Alg.eqk γ r₀ * (Pi.single k₀ δ : S.Co → GE) k = _
    rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero]

/-- One coefficient of the message's part is placed at one entry. -/
theorem membMsg_one (S : Sz) (k₀ : S.Co) (hk : S.P.T.r ≤ k₀.val) (d : GE) :
    membMsg S (Pi.single k₀ d) 0 = Pi.single (S.putAt k₀) d := by
  funext j
  by_cases hj : j = S.putAt k₀
  · rw [hj, membMsg_putAt, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj]
    rcases j with x | x
    · have e1 : S.entryOf k₀ = k₀.val - S.P.T.r := by
        unfold Sz.entryOf
        rw [if_neg (Nat.not_lt.2 hk)]
      simp only [membMsg]
      split_ifs with h1 h2
      · refine Pi.single_eq_of_ne (fun e => hj ?_) _
        have e2 : S.P.T.r + (x.1.val * S.P.C.l + x.2.val) = k₀.val := congrArg Fin.val e
        have e3 : S.entryOf k₀ = x.1.val * S.P.C.l + x.2.val := by omega
        have e4 : S.entryOf k₀ / S.P.C.l = x.1.val := by
          rw [e3, Nat.mul_comm, Nat.mul_add_div S.hl, Nat.div_eq_of_lt x.2.isLt, Nat.add_zero]
        have e5 : S.entryOf k₀ % S.P.C.l = x.2.val := by
          rw [e3, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt x.2.isLt]
        exact congrArg Sum.inl (Prod.ext (Fin.ext e4.symm) (Fin.ext e5.symm))
      · refine Pi.single_eq_of_ne (fun e => ?_) _
        have e2 : x.1.val * S.P.C.l + x.2.val - S.P.t0 = k₀.val := congrArg Fin.val e
        omega
      · rfl
    · exact x.1.elim

section
variable {P : P15} {S : Sz} {t : ℕ} {X X' : LIn S} {C C' : LCoins} {D : ℕ → Fmt.Drawn}

/-- The first member's message changes at one entry. -/
theorem lMem_moves (r₀ : Fin S.P.v → Bool) (k₀ : S.Co) (hk : S.P.T.r ≤ k₀.val) (δ : GE)
    (h0 : X'.M₀ = X.M₀ + oneCoeff r₀ k₀ δ) :
    lMem S X' C D false =
      lMem S X C D false + Pi.single (S.putAt k₀) (Alg.eqk (lGam S D) r₀ * δ) := by
  show membMsg S (foldAll (lGam S D) X'.M₀) (fun j => if j = S.padJ then C.pad false else 0) =
    membMsg S (foldAll (lGam S D) X.M₀) (fun j => if j = S.padJ then C.pad false else 0) + _
  rw [h0, foldAll_add, foldAll_oneCoeff, ← membMsg_one S k₀ hk, ← membMsg_add, add_zero]

/-- The sample's coefficient at an entry that is not the pad's. -/
theorem mat_putAt (σ : (S.fam.om false).Z.D) (j : S.MJ) (hj : j ≠ S.padJ) :
    S.memb.Z.mat σ () j = Alg.eqk σ.1 fun t => (S.idxJ j).testBit t.val :=
  mat_std_data S.memb σ ⟨j, hj⟩

/-- If the first table's rows change by δ at one coefficient of row r₀, the first answer changes by
the sample's coefficient times eqk γ r₀ times δ. -/
theorem answer_moves (r₀ : Fin S.P.v → Bool) (k₀ : S.Co) (hk : S.P.T.r ≤ k₀.val) (δ : GE)
    (h0 : X'.M₀ = X.M₀ + oneCoeff r₀ k₀ δ) :
    smAt S t (lSeed S D) (mu0 S t (lMem S X' C D)) false =
      smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) false +
        S.memb.Z.mat (lSeed S D) () (S.putAt k₀) * (Alg.eqk (lGam S D) r₀ * δ) := by
  rw [smAt_val, smAt_val, lMem_moves r₀ k₀ hk δ h0]
  exact val_add_single S.memb.Z (lSeed S D) _ _ _ ()

/-- Two equal fronts have the same answers. -/
theorem ans_of_fronts (h : lFront S t X C D = lFront S t X' C' D) (a : Bool) :
    smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) a =
      smAt S t (lSeed S D) (mu0 S t (lMem S X' C' D)) a := by
  unfold lFront at h
  have e := congrArg Fmt.RoundView.vals (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
  cases a
  · exact ofE_inj (Fmt.ItemValue.answer.inj (List.cons.inj e).1)
  · exact ofE_inj (Fmt.ItemValue.answer.inj (List.cons.inj (List.cons.inj e).2).1)

/-- Where the entry is not the pad's and the three factors are not 0, the two runs' fronts
differ. -/
theorem front_moves (r₀ : Fin S.P.v → Bool) (k₀ : S.Co) (hk : S.P.T.r ≤ k₀.val) (δ : GE)
    (h0 : X'.M₀ = X.M₀ + oneCoeff r₀ k₀ δ) (hj : S.putAt k₀ ≠ S.padJ)
    (h1 : Alg.eqk (lSeed S D).1 (fun t => (S.idxJ (S.putAt k₀)).testBit t.val) ≠ 0)
    (h2 : Alg.eqk (lGam S D) r₀ ≠ 0) (h3 : δ ≠ 0) :
    lFront S t X C D ≠ lFront S t X' C D := by
  intro h
  have e := ans_of_fronts h false
  rw [answer_moves r₀ k₀ hk δ h0, mat_putAt _ _ hj] at e
  exact mul_ne_zero h1 (mul_ne_zero h2 h3) (left_eq_add.mp e)

theorem length_lFront (X : LIn S) (C : LCoins) : (lFront S t X C D).length = 5 := by
  unfold lFront
  rfl

/-- Where the list of stages is not empty, two runs of the prover's algorithm whose fronts differ
disclose different values. -/
theorem shown_moves {first : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hst : (p12Of P).nums.stages = first :: rest)
    (hf : lFront S t X C D ≠ lFront S t X' C' D) :
    shownOf (linkAll P S t X C D) ≠ shownOf (linkAll P S t X' C' D) := by
  intro h
  have hrs : (linkAll P S t X C D).rs = (linkAll P S t X' C' D).rs := congrArg Prod.fst h
  rw [linkAll_rs_at hst X C, linkAll_rs_at hst X' C', List.append_assoc, List.append_assoc] at hrs
  exact hf (List.append_inj hrs ((length_lFront X C).trans (length_lFront X' C').symm)).1

end

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.foldAll_oneCoeff
#print axioms OnBytes.LinkSim.AtText.membMsg_one
#print axioms OnBytes.LinkSim.AtText.lMem_moves
#print axioms OnBytes.LinkSim.AtText.mat_putAt
#print axioms OnBytes.LinkSim.AtText.answer_moves
#print axioms OnBytes.LinkSim.AtText.ans_of_fronts
#print axioms OnBytes.LinkSim.AtText.front_moves
#print axioms OnBytes.LinkSim.AtText.length_lFront
#print axioms OnBytes.LinkSim.AtText.shown_moves
