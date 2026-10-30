-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesHeld.lean: the form in which a stated share is compared with
its test, and how local shares add up. A stated share (`Odds`, Honest/Frame.lean) is a number that
somebody writes down. The probability space is the library's own: the typed verifier's messages of a
list of rounds, uniform (`Iop.prRho`, Iop/InteractiveOracleProof.lean), read as lists of challenges (`drawnT`,
OnBytes/Maker/Trees.lean); that a run's challenges follow this law is not derived here. The
condition (`Held`): the denominator is not 0, and the probability of the messages at which the test
fires is at most the share's value. Adding up (`gates_le`): take tests that follow one another, each
on the challenges heard before its own and on its own rounds' challenges. Suppose that each fires,
over its own rounds' messages, with probability at most its number, at every list of such challenges
at which no earlier test has fired. Then the probability of the messages at which some test fires is
at most the sum of the numbers.

What this is. Definitions, and lemmas about the library's own probability. No description, no prover
and no run occurs in this file. None of the library's goals. Probabilities are over the verifier's
messages, drawn uniformly (`Iop.prRho`), at a fixed private input and instance, where a lemma names
one.

Trivially met. The share 1 of 1 satisfies `Held` at every test. A test that never fires satisfies it
with 0 of 1. Whether a stated number is small is not said.

  1  `Odds.val`, `Held`   the condition
  2  `joinR`, `cutR`, `cut_join`, `join_cut`, `splitE`, `drawn_join`   two lists of rounds in a row
  3  `fibre_le`   a first part in S, or a second part in the set that belongs to the first
  4  `Gate`, `spoken`, `GatesHeld`, `gates_le`   adding up

Limits.
  * The probability is no count of lists of challenges: two typed challenges can be shown as the
    same challenge.
  * The kit C of verifier's messages is a parameter. How a probability over its typed challenges
    follows from a count of what they show depends on the kit, and is not treated here.
  * `Held` is a hypothesis of `markDebt_of_held` and, through `Fall.HeldOn`
    (Honest/Law/SharesFalls.lean), of `fallDebt_of_heldOn` (both in Honest/Law/CoverSeat.lean).
    Hypotheses of the like kind: `GatesHeld` (this file), `ChainHeld` (Honest/Law/SharesChain.lean),
    `LocalDebts` (Honest/Law/CoverHeld.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Iop.ViewKit
import Johnson.Desc.ProofFile.Honest.Shares
import Johnson.Desc.ProofFile.Honest.Law.Due

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-! ## 1 The condition -/

/-- The value of a stated share. At the denominator 0 it is not meant to be read: `Held` excludes
that. -/
noncomputable def Odds.val (o : Odds) : ℝ≥0∞ := (o.num : ℝ≥0∞) / (o.den : ℝ≥0∞)

/-- **The share o bounds the probability that the test T fires, at the rounds ds**: over the typed
verifier's messages of these rounds, uniform. A definition, meant as a hypothesis. -/
def Held (C : CK) (ds : List RDT) (T : List Fmt.Drawn → Bool) (o : Odds) : Prop :=
  o.ok = true ∧ Iop.prRho {ρ : Iop.Rho (uLT C ds) | T (drawnT C ds ρ) = true} ≤ o.val

/-! ## 2 Two lists of rounds in a row -/

/-- The verifier's messages of two lists of rounds, as a message of the two lists in a row. -/
def joinR (C : CK) : (a b : List RDT) → Iop.Rho (uLT C a) → Iop.Rho (uLT C b) →
    Iop.Rho (uLT C (a ++ b))
  | [], _, _, y => y
  | _ :: a, b, (c, x), y => (c, joinR C a b x y)

/-- The inverse. -/
def cutR (C : CK) : (a b : List RDT) → Iop.Rho (uLT C (a ++ b)) →
    Iop.Rho (uLT C a) × Iop.Rho (uLT C b)
  | [], _, ρ => ((), ρ)
  | _ :: a, b, (c, ρ) => ((c, (cutR C a b ρ).1), (cutR C a b ρ).2)

theorem cut_join (C : CK) : ∀ (a b : List RDT) (x : Iop.Rho (uLT C a)) (y : Iop.Rho (uLT C b)),
    cutR C a b (joinR C a b x y) = (x, y)
  | [], _, _, _ => rfl
  | d :: a, b, (c, x), y => by
    show (((c, (cutR C a b (joinR C a b x y)).1) : Iop.Rho (uLT C (d :: a))),
      (cutR C a b (joinR C a b x y)).2) = _
    rw [cut_join C a b x y]
    rfl

theorem join_cut (C : CK) : ∀ (a b : List RDT) (ρ : Iop.Rho (uLT C (a ++ b))),
    joinR C a b (cutR C a b ρ).1 (cutR C a b ρ).2 = ρ
  | [], _, _ => rfl
  | d :: a, b, (c, ρ) => by
    show ((c, joinR C a b (cutR C a b ρ).1 (cutR C a b ρ).2) :
      Iop.Rho (uLT C (d :: (a ++ b)))) = _
    rw [join_cut C a b ρ]

/-- The two as one equivalence. -/
def splitE (C : CK) (a b : List RDT) :
    Iop.Rho (uLT C a) × Iop.Rho (uLT C b) ≃ Iop.Rho (uLT C (a ++ b)) where
  toFun := fun p => joinR C a b p.1 p.2
  invFun := cutR C a b
  left_inv := fun p => cut_join C a b p.1 p.2
  right_inv := join_cut C a b

theorem drawn_join (C : CK) : ∀ (a b : List RDT) (x : Iop.Rho (uLT C a))
    (y : Iop.Rho (uLT C b)), drawnT C (a ++ b) (joinR C a b x y) = drawnT C a x ++ drawnT C b y
  | [], _, _, _ => rfl
  | d :: a, b, (c, x), y => by
    show C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c) ::
        drawnT C (a ++ b) (joinR C a b x y) =
      C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c) ::
        (drawnT C a x ++ drawnT C b y)
    rw [drawn_join C a b x y]

/-! ## 3 A first part in S, or a second part in the set that belongs to the first -/

/-- As the library's `prRho_le_of_fibre` (Ior/ChainProofs.lean), at two lists of rounds in a row.
The bound on the second part is asked only at first parts outside S. -/
theorem fibre_le (C : CK) (a b : List RDT) (S : Set (Iop.Rho (uLT C a)))
    (T : Iop.Rho (uLT C a) → Set (Iop.Rho (uLT C b))) (U : Set (Iop.Rho (uLT C (a ++ b))))
    (q p : ℝ≥0∞) (hS : Iop.prRho S ≤ q)
    (hU : ∀ x y, joinR C a b x y ∈ U → x ∉ S → y ∈ T x)
    (hT : ∀ x, x ∉ S → Iop.prRho (T x) ≤ p) : Iop.prRho U ≤ q + p := by
  unfold Iop.prRho at hS hT ⊢
  rw [← map_unif_equiv (splitE C a b), pr_map, unif_prod]
  unfold Prob.prod
  refine le_trans (pr_bind_le_add _ _ _ S (fun x _ hx => ?_)) (add_le_add hS le_rfl)
  rw [pr_map]
  refine le_trans (pr_mono _ ?_) (hT x hx)
  intro y hy
  exact hU x y hy hx

/-! ## 4 Adding up -/

/-- **A test at a stretch of rounds.** `ds`: the rounds' data; `test`: a function of the challenges
heard before its own and of its own rounds' challenges; `p`: a number. -/
structure Gate where
  ds : List RDT
  test : List Fmt.Drawn → List Fmt.Drawn → Bool
  p : ℝ≥0∞

/-- Some gate fires, each at the challenges before it. `fr`: the challenges heard before the first
gate's own; the last argument: the challenges of all gates' rounds in a row. -/
def spoken : List Gate → List Fmt.Drawn → List Fmt.Drawn → Bool
  | [], _, _ => false
  | g :: gs, fr, ds =>
    g.test fr (ds.take g.ds.length) ||
      spoken gs (fr ++ ds.take g.ds.length) (ds.drop g.ds.length)

/-- **Each gate fires, over its own rounds' messages, with probability at most its number, at every
list of challenges heard before its own at which no earlier gate has fired.** A definition, meant as
a hypothesis. -/
def GatesHeld (C : CK) : List Gate → List Fmt.Drawn → Prop
  | [], _ => True
  | g :: gs, fr =>
    Iop.prRho {ρ : Iop.Rho (uLT C g.ds) | g.test fr (drawnT C g.ds ρ) = true} ≤ g.p ∧
      ∀ ρ : Iop.Rho (uLT C g.ds), g.test fr (drawnT C g.ds ρ) = false →
        GatesHeld C gs (fr ++ drawnT C g.ds ρ)

/-- **Local shares add up.** -/
theorem gates_le (C : CK) : ∀ (gs : List Gate) (fr : List Fmt.Drawn), GatesHeld C gs fr →
    Iop.prRho {ρ : Iop.Rho (uLT C (gs.flatMap (·.ds))) |
      spoken gs fr (drawnT C (gs.flatMap (·.ds)) ρ) = true} ≤ (gs.map (·.p)).sum
  | [], fr, _ =>
    le_trans (Iop.prRho_empty _ fun ρ hρ => by
      have h' : false = true := hρ
      cases h') (zero_le _)
  | g :: gs, fr, h => by
    obtain ⟨h1, h2⟩ := h
    have key := fibre_le C g.ds (gs.flatMap (·.ds))
      {x | g.test fr (drawnT C g.ds x) = true}
      (fun x => {y | spoken gs (fr ++ drawnT C g.ds x) (drawnT C (gs.flatMap (·.ds)) y) = true})
      {ρ | spoken (g :: gs) fr (drawnT C (g.ds ++ gs.flatMap (·.ds)) ρ) = true}
      g.p (gs.map (·.p)).sum h1
      (fun x y hxy hx => by
        have hxy' : spoken (g :: gs) fr
            (drawnT C (g.ds ++ gs.flatMap (·.ds)) (joinR C g.ds _ x y)) = true := hxy
        rw [drawn_join] at hxy'
        have hl := drawnT_len C g.ds x
        have e1 : (drawnT C g.ds x ++ drawnT C (gs.flatMap (·.ds)) y).take g.ds.length =
            drawnT C g.ds x := List.take_left' hl
        have e2 : (drawnT C g.ds x ++ drawnT C (gs.flatMap (·.ds)) y).drop g.ds.length =
            drawnT C (gs.flatMap (·.ds)) y := List.drop_left' hl
        unfold spoken at hxy'
        rw [e1, e2, Bool.or_eq_true] at hxy'
        rcases hxy' with g1 | g1
        · exact absurd g1 hx
        · exact g1)
      (fun x hx => gates_le C gs _ (h2 x (by
        cases ht : g.test fr (drawnT C g.ds x) with
        | false => rfl
        | true => exact absurd ht hx)))
    rw [List.map_cons, List.sum_cons]
    exact key

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_join
#print axioms ProofFile.Honest.join_cut
#print axioms ProofFile.Honest.drawn_join
#print axioms ProofFile.Honest.fibre_le
#print axioms ProofFile.Honest.gates_le
