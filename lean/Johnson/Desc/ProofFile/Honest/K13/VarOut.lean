-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/VarOut.lean: kind K13, the members' batching: THE VARIABLES'
ROUNDS OF THE MASKED SUMCHECK's PART (`varOut`, Honest/SumLaw/Said.lean), at n variables that are
summed plainly with three coefficients each, ARE THE ROUNDS OF THE SCALARS `sentL`
(Johnson/Desc/K13/Honest/Moves.lean), each laid into words below the prime. Statements with their
proofs. The summand is a parameter.
Main names:
  `elemOf_k13Dr`: the element of a challenge that is one element.
  `plainFrom_length`: a round's message has two scalars. `map_two`: a function over two members.
  `plain_shown`: one round, as the frame shows it.
  `varOut_plain`: **all rounds.**

What is not claimed. Other shapes of a call. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Said
import Johnson.Desc.ProofFile.Honest.K13.SumReads
import Johnson.Desc.ProofFile.Honest.K13.Shown
import Johnson.Desc.K13.Law.Pin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E addE mulE zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Var valueAt psiAt)
open VerifiableInference.Desc.K13.Law (ρg)
open VerifiableInference.Desc.K13.Honest (sentL tailU codeRounds shownRound)
open ProofFile.Honest.SumLaw (varOut varOut_cons varOut_nil rvSaid elemOf)

/-- The element of a challenge that is one element. -/
theorem elemOf_k13Dr (c : E) : elemOf (k13Dr c) = c := rfl

/-- The message for the first of n + 1 variables that are left, with no challenge of these heard
yet, at three coefficients of the summand, has two scalars. -/
theorem plainFrom_length : ∀ (n : Nat) (u : List E) (eps g0 g1 g2 a : E),
    (plainFrom (n + 1) u eps [] [g0, g1, g2] a).length = 2
  | 0, u, _, _, _, _, _ => by
    unfold plainFrom
    rw [vwOf_one]
    rfl
  | n + 1, u, _, _, _, _, _ => by
    unfold plainFrom
    rw [vwOf_succ]
    rfl

/-- A function over a list of two members. -/
theorem map_two {β : Type} (F : E → β) : ∀ l : List E, l.length = 2 →
    l.map F = [F (l.getD 0 zeroE), F (l.getD 1 zeroE)]
  | [_, _], _ => rfl
  | [], h => by simp only [List.length_nil] at h; omega
  | [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- **One round, as the frame shows it**: the two scalars, read and laid back. -/
theorem plain_shown (n : Nat) (u : List E) (eps g0 g1 g2 a g : E) :
    rvSaid (plainFrom (n + 1) u eps [] [g0, g1, g2] a) (k13Dr g) =
      shownRound [k13E (readPair ρg (plainFrom (n + 1) u eps [] [g0, g1, g2] a)).1,
        k13E (readPair ρg (plainFrom (n + 1) u eps [] [g0, g1, g2] a)).2] g := by
  unfold rvSaid
  rw [said_shown, map_two _ _ (plainFrom_length n u eps g0 g1 g2 a)]
  rfl

/-- **All rounds.** f: the coins' readings by their number, from i on. past: the challenges of the
variables that were passed. gs: those of the n variables that are left. -/
theorem varOut_plain (f : Nat → OnBytes.Slice.GE) (eps : E) {N : Nat} {G : List E → List E}
    {q : List OnBytes.Slice.GE → OnBytes.Slice.GE × OnBytes.Slice.GE × OnBytes.Slice.GE}
    (hG : ReadsAs ρg N G q) : ∀ (n : Nat) (u : List E) (i : Nat) (past gs : List E) (a : E),
    past.length + n = N →
    (∀ j, j < 2 * n + 1 → ρg.val (u.getD j zeroE) = f (i + j)) → gs.length = n →
    varOut eps G (vwOf n u) a past (gs.map k13Dr) =
      (codeRounds k13E (sentL f (ρg.val eps) q n i (past.map ρg.val) (gs.map ρg.val)) gs).map
        fun p => shownRound p.1 p.2
  | 0, _, _, _, [], _, _, _, _ => by
    rw [List.map_nil, varOut_nil]
    rfl
  | 1, u, i, past, [g], a, hN, h, _ => by
    obtain ⟨g0, g1, g2, e1, e2⟩ := hG past (by omega)
    have hv : vwOf 1 u =
        ((.plain 3 : Var), [u.getD 0 zeroE, u.getD 1 zeroE, u.getD 2 zeroE]) :: [] :=
      vwOf_one u
    rw [hv]
    show varOut eps G _ a past [k13Dr g] = _
    rw [varOut_cons, varOut_nil, ← hv, e1]
    show [rvSaid (plainFrom 1 u eps [] [g0, g1, g2] a) (k13Dr g)] = _
    rw [plain_shown 0, round_last ρg f u i h]
    show _ = [shownRound [k13E (f i + ρg.val eps * (q (past.map ρg.val)).1),
      k13E (f (i + 2) + ρg.val eps * (q (past.map ρg.val)).2.2)] g]
    rw [e2]
  | n + 2, u, i, past, g :: gs, a, hN, h, hg => by
    obtain ⟨g0, g1, g2, e1, e2⟩ := hG past (by omega)
    have ih := varOut_plain f eps hG (n + 1) (u.drop 2) (i + 2) (past ++ [g]) gs
      (addE (mulE a g) (valueAt [zeroE, u.getD 0 zeroE, u.getD 1 zeroE] g))
      (by rw [List.length_append, List.length_singleton]; omega)
      (fun j hj => by
        rw [getD_drop_two, h (j + 2) (by omega)]
        congr 1
        omega)
      (by simp only [List.length_cons] at hg; omega)
    have hv := vwOf_succ n u
    rw [hv, List.map_cons, varOut_cons, ← hv, e1, elemOf_k13Dr]
    have ep : psiAt (.plain 3) g = g := rfl
    rw [ep, ih]
    show rvSaid (plainFrom (n + 2) u eps [] [g0, g1, g2] a) (k13Dr g) :: _ = _
    rw [plain_shown (n + 1), round_first ρg f n u i h]
    have e3 : past.map ρg.val ++ [ρg.val g] = (past ++ [g]).map ρg.val := by simp
    show _ = shownRound [k13E (tailU f (n + 1) (i + 2) + ρg.val eps * (q (past.map ρg.val)).1),
        k13E (f (i + 1) + ρg.val eps * (q (past.map ρg.val)).2.2)] g ::
      (codeRounds k13E (sentL f (ρg.val eps) q (n + 1) (i + 2) (past.map ρg.val ++ [ρg.val g])
        (gs.map ρg.val)) gs).map fun p => shownRound p.1 p.2
    rw [e2, e3]
  | 0, _, _, _, _ :: _, _, _, _, hg => by simp only [List.length_cons] at hg; omega
  | 1, _, _, _, [], _, _, _, hg => by simp only [List.length_nil] at hg; omega
  | 1, _, _, _, _ :: _ :: _, _, _, _, hg => by simp only [List.length_cons] at hg; omega
  | _ + 2, _, _, _, [], _, _, _, hg => by simp only [List.length_nil] at hg; omega

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.elemOf_k13Dr
#print axioms ProofFile.Honest.K13.plainFrom_length
#print axioms ProofFile.Honest.K13.map_two
#print axioms ProofFile.Honest.K13.plain_shown
#print axioms ProofFile.Honest.K13.varOut_plain
