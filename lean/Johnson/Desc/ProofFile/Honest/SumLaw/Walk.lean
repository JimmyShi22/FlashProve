-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Walk.lean: ALL ROUNDS OF THE MASKED SUMCHECK, THE HONEST PART's
TEXT AGAINST THE VERIFIER's: under the three premises told below, the verifier's fold `after`
(Johnson/Desc/Part/MaskedSum4.lean) over the lists of `sentRounds` (that these are what is read of
`sumPart`'s rounds: Out.lean, Reads.lean) ends at the value of a walk plus eps times the summand's
last claim; and, at as many challenges as variables, that walk is what the verifier's `hidingAt`
makes of the hiding polynomial's coefficients. Definitions that the statements need, and statements
with their proofs. ρ, cn: as in Honest/SumLaw/Round.lean.

THE THREE PREMISES OF `after_reads`. (1) Every variable has at least two coefficients, and its share
of the hiding polynomial has as many members (`wOf_sizes` gives the second from the first; the first
follows from the verifier's test on the plan: `all_two`, Reads.lean). (2) The first claim c reads as
a + B + tailSum L + eps cS: a: the accumulator of the part's walk; B: any element; cS: the summand's
claim in front. (3) `SumsTo` (Terms.lean): WHAT A CALLER HAS TO SHOW: round by round the summand's
lists sum from cS to cf.
Main names:
  `walkK ρ L A rs`: the walk, in the field: from A, at each variable: times psi at the challenge,
    plus the variable's share of the hiding polynomial at the challenge.
  `sentRounds cn eps poly L a seen rs`: for each variable what the part sends, written anew by cn,
    with the challenge: L: the variables that are left, each with its share; a: the accumulator of
    the part's own walk; seen: the challenges passed.
  `after_cons`: a step of the verifier's fold. `sentRounds_lens`: the lists have the right lengths.
  `after_reads`: **the last running claim.**
  `valueAt_sum`, `getD_drop`, `wOf_sizes`: tools.
  `walk_hiding`: **the walk is the verifier's form on the hiding polynomial's coefficients, plus A
    times its product of all psi.**

Limits. Nothing on a ledger, nor on rounds as a view shows them. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum
open Polynomial

/-- For each variable what the part sends, written anew, with the challenge. -/
def sentRounds (cn : E → E) (eps : E) (poly : List E → List E) :
    List (Var × List E) → E → List E → List E → List (List E × E)
  | (v, w) :: rest, a, seen, r :: rs =>
    ((sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps (poly seen)))).map cn, r) ::
      sentRounds cn eps poly rest (addE (mulE a (psiAt v r)) (valueAt w r)) (seen ++ [r]) rs
  | _, _, _, _ => []

theorem sentRounds_cons (cn : E → E) (eps : E) (poly : List E → List E) (v : Var) (w : List E)
    (rest : List (Var × List E)) (a : E) (seen : List E) (r : E) (rs : List E) :
    sentRounds cn eps poly ((v, w) :: rest) a seen (r :: rs) =
      ((sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps (poly seen)))).map cn, r) ::
        sentRounds cn eps poly rest (addE (mulE a (psiAt v r)) (valueAt w r)) (seen ++ [r]) rs := by
  rw [sentRounds.eq_def]

/-- A step of the verifier's fold. -/
theorem after_cons (v : Var) (vs : List Var) (sent : List E) (r : E) (rs : List (List E × E))
    (c : E) :
    after (v :: vs) ((sent, r) :: rs) c = after vs rs (valueAt (complete v sent c) r) := by
  rw [after.eq_def]

theorem after_nil (c : E) : after [] [] c = c := by
  rw [after.eq_def]

/-- The lists have the lengths that the verifier's reader asks. -/
theorem sentRounds_lens (cn : E → E) (eps : E) (poly : List E → List E) :
    ∀ (L : List (Var × List E)) (a : E) (seen rs : List E), (∀ x ∈ L, 2 ≤ x.1.d) →
      L.length = rs.length → Lens (L.map (·.1)) (sentRounds cn eps poly L a seen rs)
  | [], _, _, [], _, _ => by
    rw [sentRounds.eq_def]
    trivial
  | (v, w) :: rest, a, seen, r :: rs, h, hl => by
    rw [sentRounds_cons]
    have h2 : 2 ≤ v.d := h (v, w) List.mem_cons_self
    refine ⟨?_, h2, sentRounds_lens cn eps poly rest _ _ rs
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (by simp only [List.length_cons] at hl; omega)⟩
    show ((sentOfL v _).map cn).length + 1 = v.d
    rw [List.length_map, sentOfL_eq]
    exact cutOf_length v _ (padTo_length _ _) h2
  | [], _, _, _ :: _, _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, _, [], _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega

/-- Their challenges are the challenges. -/
theorem sentRounds_chal (cn : E → E) (eps : E) (poly : List E → List E) :
    ∀ (L : List (Var × List E)) (a : E) (seen rs : List E), L.length = rs.length →
      (sentRounds cn eps poly L a seen rs).map (·.2) = rs
  | [], _, _, [], _ => by
    rw [sentRounds.eq_def]
    rfl
  | (v, w) :: rest, a, seen, r :: rs, hl => by
    rw [sentRounds_cons, List.map_cons, sentRounds_chal cn eps poly rest _ _ rs
      (by simp only [List.length_cons] at hl; omega)]
  | [], _, _, _ :: _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, _, [], hl => by simp only [List.length_cons, List.length_nil] at hl; omega

variable {K : Type} [Field K] (ρ : Reading K)

/-- The walk, in the field. -/
def walkK : List (Var × List E) → K → List E → K
  | (v, w) :: rest, A, r :: rs => walkK rest (A * ρ.val (psiAt v r) + ρ.val (valueAt w r)) rs
  | _, A, _ => A

/-- **The last running claim**: where the first claim reads as a + B + tailSum L + eps cS and the
summand's lists sum, round by round, from cS to cf (`SumsTo`): the walk from a + B, plus eps cf. -/
theorem after_reads (cn : E → E) (hcn : ∀ x, ρ.val (cn x) = ρ.val x) (eps : E)
    (poly : List E → List E) :
    ∀ (L : List (Var × List E)) (a : E) (seen rs : List E) (c : E) (B cS cf : K),
      (∀ x ∈ L, 2 ≤ x.1.d ∧ x.2.length = x.1.d) →
      ρ.val c = ρ.val a + B + ρ.val (tailSum L) + ρ.val eps * cS →
      SumsTo ρ (L.map (·.1)) poly seen rs cS cf →
      ρ.val (after (L.map (·.1)) (sentRounds cn eps poly L a seen rs) c) =
        walkK ρ L (ρ.val a + B) rs + ρ.val eps * cf
  | [], a, seen, [], c, B, cS, cf, _, hc, hS => by
    have e : cS = cf := hS
    have e0 : tailSum [] = zeroE := rfl
    rw [sentRounds.eq_def]
    show ρ.val (after [] [] c) = ρ.val a + B + ρ.val eps * cf
    rw [after_nil, hc, e0, ρ.zero, e, add_zero]
  | (v, w) :: rest, a, seen, r :: rs, c, B, cS, cf, h, hc, hS => by
    obtain ⟨h1, h2⟩ := hS
    obtain ⟨hd, hw⟩ := h (v, w) List.mem_cons_self
    rw [← h1] at hc
    have hr := round_reads ρ cn hcn v hd w hw rest a eps (poly seen) c r B hc
    rw [sentRounds_cons]
    show ρ.val (after (v :: rest.map (·.1)) (_ :: _) c) =
      walkK ρ rest ((ρ.val a + B) * ρ.val (psiAt v r) + ρ.val (valueAt w r)) rs + ρ.val eps * cf
    rw [after_cons, after_reads cn hcn eps poly rest _ (seen ++ [r]) rs _
      (B * ρ.val (psiAt v r)) _ cf (fun x hx => h x (List.mem_cons_of_mem _ hx)) hr h2]
    congr 2
    rw [ρ.add, ρ.mul]
    ring
  | [], _, _, _ :: _, _, _, _, _, _, _, hS => hS.elim
  | _ :: _, _, _, [], _, _, _, _, _, _, hS => hS.elim

/-! ## The walk against the verifier's form -/

/-- A polynomial's value as a sum. -/
theorem valueAt_sum (l : List E) (r : E) (n : Nat) (hl : l.length = n) :
    ρ.val (valueAt l r) = ∑ i ∈ Finset.range n, ρ.val (l.getD i zeroE) * ρ.val r ^ i := by
  rw [← polyOf_eval]
  cases n with
  | zero =>
    have e : l = [] := List.length_eq_zero_iff.1 hl
    rw [e]
    simp [polyOf]
  | succ n =>
    rw [eval_eq_sum_range' (n := n + 1) (by
      have := polyOf_natDegree_lt ρ l (by omega)
      omega)]
    exact Finset.sum_congr rfl fun i _ => by rw [polyOf_coeff]

theorem getD_drop (u : List E) (n j : Nat) : (u.drop n).getD j zeroE = u.getD (n + j) zeroE := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Each variable's share has as many coefficients as the variable. -/
theorem wOf_sizes : ∀ (vs : List Var) (u : List E), (∀ v ∈ vs, 2 ≤ v.d) →
    ∀ x ∈ vs.zip (wOf vs u), 2 ≤ x.1.d ∧ x.2.length = x.1.d
  | [], _, _, x, hx => by cases hx
  | [v], u, h, x, hx => by
    have e : [v].zip (wOf [v] u) = [(v, padTo v.d u)] := rfl
    rw [e, List.mem_singleton] at hx
    rw [hx]
    exact ⟨h v List.mem_cons_self, padTo_length _ _⟩
  | v :: v' :: vs, u, h, x, hx => by
    have e : (v :: v' :: vs).zip (wOf (v :: v' :: vs) u) =
        (v, zeroE :: padTo (v.d - 1) u) :: (v' :: vs).zip (wOf (v' :: vs) (u.drop (v.d - 1))) := rfl
    rw [e] at hx
    have h2 : 2 ≤ v.d := h v List.mem_cons_self
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨h2, ?_⟩
      show (padTo (v.d - 1) u).length + 1 = v.d
      rw [padTo_length]
      omega
    · exact wOf_sizes (v' :: vs) _ (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

theorem wOf_length : ∀ (vs : List Var) (u : List E), (wOf vs u).length = vs.length
  | [], _ => rfl
  | [_], _ => rfl
  | v :: v' :: vs, u => by
    show (wOf (v' :: vs) (u.drop (v.d - 1))).length + 1 = (v' :: vs).length + 1
    rw [wOf_length (v' :: vs)]

/-- **The walk is the verifier's form on the coefficients, plus A times its product of all psi.**
-/
theorem walk_hiding : ∀ (vs : List Var) (u rs : List E) (A : K) (hcoef : Nat → K),
    vs.length = rs.length → (∀ j, ρ.val (u.getD j zeroE) = hcoef j) →
    walkK ρ (vs.zip (wOf vs u)) A rs =
      dotFrom ρ hcoef (hidingAt (vs.zip rs)).1 + A * ρ.val (hidingAt (vs.zip rs)).2
  | [], u, [], A, hcoef, _, _ => by
    show A = dotFrom ρ hcoef [] + A * ρ.val oneE
    rw [ρ.one, mul_one]
    simp [dotFrom]
  | [v], u, [r], A, hcoef, _, hu => by
    show A * ρ.val (psiAt v r) + ρ.val (valueAt (padTo v.d u) r) =
      dotFrom ρ hcoef (powersFrom r v.d oneE) + A * ρ.val (psiAt v r)
    rw [dotFrom_powers, ρ.one, one_mul, valueAt_sum ρ _ r v.d (padTo_length _ _), add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [padTo_getD, if_pos (Finset.mem_range.1 hi), hu]
  | v :: v' :: vs, u, r :: r' :: rs, A, hcoef, hl, hu => by
    have ih := walk_hiding (v' :: vs) (u.drop (v.d - 1)) (r' :: rs)
      (A * ρ.val (psiAt v r) + ρ.val (valueAt (zeroE :: padTo (v.d - 1) u) r))
      (fun j => hcoef (v.d - 1 + j))
      (by simp only [List.length_cons] at hl ⊢; omega)
      (fun j => by rw [getD_drop, hu])
    show walkK ρ ((v' :: vs).zip (wOf (v' :: vs) (u.drop (v.d - 1))))
        (A * ρ.val (psiAt v r) + ρ.val (valueAt (zeroE :: padTo (v.d - 1) u) r)) (r' :: rs) =
      dotFrom ρ hcoef (powersFrom r (v.d - 1)
          (mulE (hidingAt ((v' :: vs).zip (r' :: rs))).2 r) ++
            (hidingAt ((v' :: vs).zip (r' :: rs))).1) +
        A * ρ.val (mulE (hidingAt ((v' :: vs).zip (r' :: rs))).2 (psiAt v r))
    rw [ih, dotFrom_append, dotFrom_powers, powersFrom_length, ρ.mul, ρ.mul]
    have ev : ρ.val (valueAt (zeroE :: padTo (v.d - 1) u) r) =
        ρ.val r * ∑ i ∈ Finset.range (v.d - 1), hcoef i * ρ.val r ^ i := by
      have e : valueAt (zeroE :: padTo (v.d - 1) u) r =
          addE (mulE (valueAt (padTo (v.d - 1) u) r) r) zeroE := rfl
      rw [e, ρ.add, ρ.mul, ρ.zero, add_zero, valueAt_sum ρ _ r (v.d - 1) (padTo_length _ _),
        mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [padTo_getD, if_pos (Finset.mem_range.1 hi), hu]
    rw [ev]
    ring
  | [], _, _ :: _, _, _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | [_], _, [], _, _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | [_], _, _ :: _ :: _, _, _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _ :: _, _, [], _, _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _ :: _, _, [_], _, _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

end ProofFile.Honest.SumLaw

end

#print axioms ProofFile.Honest.SumLaw.sentRounds_cons
#print axioms ProofFile.Honest.SumLaw.after_cons
#print axioms ProofFile.Honest.SumLaw.after_nil
#print axioms ProofFile.Honest.SumLaw.sentRounds_lens
#print axioms ProofFile.Honest.SumLaw.sentRounds_chal
#print axioms ProofFile.Honest.SumLaw.after_reads
#print axioms ProofFile.Honest.SumLaw.valueAt_sum
#print axioms ProofFile.Honest.SumLaw.getD_drop
#print axioms ProofFile.Honest.SumLaw.wOf_sizes
#print axioms ProofFile.Honest.SumLaw.wOf_length
#print axioms ProofFile.Honest.SumLaw.walk_hiding
