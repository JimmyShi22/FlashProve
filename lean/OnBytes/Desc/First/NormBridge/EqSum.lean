-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/EqSum.lean: THE MASKED SUMCHECK's PROVED LAW AT A SUM OF PRODUCTS
(OnBytes/Desc/First/P1/PscProducts.lean: products_sound), ONCE MORE, AT EQUALITY WEIGHTS
OF A
POINT, THE ROUNDS IN THE ORDER OF THE COORDINATES, with the tables written as the library writes
them:
vectors on numbers, extended by Blocks.ext. Definitions, statements and proofs. Nothing new is shown
of a sumcheck: the law is taken, its letters are turned (TotExt.lean).

  eqWs zs: the weights of the rounds: the equality weight at each coordinate, three coefficients.
  Heard1: one masked sumcheck as it was heard: the record, mu, the rounds, the further round, the
  end
    term. PLAIN RECORDS ALONE (Model.Psc, lists, elements); no routine in a context.
  Heard1.Shape: that record and rounds fit each other: products_sound's six premises on them.
  eq_products_sound: the law.
  pscBadE, pscBad: ITS BAD SETS AS FUNCTIONS, by choice from the law: THEIR ARGUMENTS ARE ALL THAT
  THEY
    READ: the reading, the point zs, the tables A, the end values' masks m, the terms ts, the hiding
    coefficients hcoef, T (the start form on what was shown), Cv (its value at the hidden values);
    then mu; then eps, the rounds in front and the round's polynomial.
  pscBadE_card (at most 1), pscBad_card (at most 2), psc_law.

LIBRARY LEMMAS TAKEN: OnBytes/Tie/Pv/Psc/PscHeld.lean fits_equality, weightHeld_equality.
ALSO TAKEN:
products_sound, two_equality, Twos, dAt, NoBad, movesP, claimAfter.
NOT CLAIMED: more than products_sound claims. Counts of elements of K, not of drawn words.

-/
import OnBytes.Desc.First.P1.PscProducts
import OnBytes.Tie.Pv.Psc.PscHeld
import OnBytes.Desc.First.NormBridge.TotExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset Polynomial
open OnBytes OnBytes.Model
open Blocks (ext ofList)
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-- The rounds' weights at the coordinates zs. -/
def eqWs (zs : List E) : List OnBytes.Psc.Weight := zs.map fun z => OnBytes.Psc.Weight.equality z 3

/-- The further variable's weight. -/
abbrev wY : OnBytes.Psc.Weight := OnBytes.Psc.Weight.atZero 3

theorem held_eq (z : E) : Held (OnBytes.Psc.Weight.equality z 3) :=
  ⟨(OnBytes.PscRun.fits_equality z 3).mpr (by omega), OnBytes.PscRun.weightHeld_equality z 3⟩

theorem held_eqWs (zs : List E) : ∀ w ∈ eqWs zs, Held w := by
  intro w hw
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw
  exact held_eq z

theorem twos_eqWs : ∀ zs : List E, Twos 3 ((eqWs zs).map (wtOf ρ)) (wts (zs.map ρ.val))
  | [] => trivial
  | z :: zs => ⟨two_equality ρ z 3 (by omega), le_refl 3, twos_eqWs zs⟩

theorem dAt_le (vs : List (Wt K)) (k : ℕ) (hk : 1 ≤ k) (h : ∀ w ∈ vs, w.d ≤ k) (i : ℕ) :
    dAt vs i ≤ k := by
  unfold dAt
  cases hi : vs[i]? with
  | none => simpa using hk
  | some w => simpa using h w (List.mem_of_getElem? hi)

/-- One masked sumcheck as it was heard. -/
structure Heard1 where
  /-- the record behind the further round -/
  p : Psc
  /-- the hiding polynomial's sum, as sent -/
  mu : E
  /-- the variables' rounds: weight, what was sent, challenge -/
  ms : List Rnd
  /-- the further variable's round -/
  y : Rnd
  /-- the end term: the summand on what was shown -/
  S0 : E

/-- The challenges of the variables' rounds, read. -/
def Heard1.r (h : Heard1) : List K := h.ms.map fun x => ρ.val x.2.2

/-- The further round's challenge, read. -/
def Heard1.beta (h : Heard1) : K := ρ.val h.y.2.2

/-- Record and rounds fit each other, at the coordinates zs. -/
structure Heard1.Shape (h : Heard1) (zs : List E) : Prop where
  weights : h.ms.map (·.1) = eqWs zs
  further : h.y.1 = wY
  lengths : ∀ x ∈ h.ms ++ [h.y], x.2.1.length + 1 = x.1.d
  vars : h.p.vars.toList = eqWs zs ++ [wY]
  chals : h.p.r.toList = (h.ms ++ [h.y]).map (·.2.2)
  claim : h.p.claim = claimAfter (h.ms ++ [h.y]) (addE h.mu (mulE h.p.eps h.p.target))

/-- **The law at equality weights, in the library's letters.** -/
theorem eq_products_sound (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K))
    (hcoef : ℕ → K) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧ (∀ mu eps pre g, (bad mu eps pre g).card ≤ 2) ∧
      ∀ (W : World K) (h : Heard1) (sh : ℕ → K), h.Shape zs →
        ρ.val h.p.target = T → h.p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (eqWs zs ++ [wY]) → W.slot (h.p.first + i) = hcoef i) →
        (h.p.rowForm h.S0 {}).value ρ W = 0 →
        ρ.val h.S0 = sumTerms ts sh →
        (∀ i, sh i = ext zs.length (A i) (ofList (h.r ρ)) + h.beta ρ * m i) →
        ρ.val h.p.eps ∉ badE (ρ.val h.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val h.mu) (ρ.val h.p.eps))
          (movesP ρ (h.ms ++ [h.y]) (addE h.mu (mulE h.p.eps h.p.target)))) →
        Cv = ext zs.length (fun X => sumTerms ts fun i => A i X) (ofList (zs.map ρ.val)) := by
  obtain ⟨badE, bad, hE, hB, hrun⟩ := products_sound ρ (eqWs zs) (held_eqWs zs) (wts (zs.map ρ.val))
    (twos_eqWs ρ zs) (fun i b => A i (numFrom 0 b)) m ts hcoef T Cv (held_eq zeroE)
  refine ⟨badE, bad, hE, fun mu eps pre g => ?_, ?_⟩
  · have h1 := hB mu eps pre g
    have h2 := dAt_le ((eqWs zs ++ [wY]).map (wtOf ρ)) 3 (by omega) (by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_append.mp hv with h | h
      · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h
        exact le_refl 3
      · rw [List.mem_singleton] at h
        subst h
        exact le_refl 3) pre.length
    exact Nat.le_of_lt_succ (lt_of_lt_of_le h1 h2)
  · intro W h sh hs hT hC hslots hzero hS0 hsh hne hnb
    have hlen : (eqWs zs).length = zs.length := List.length_map _
    have hrl : (h.r ρ).length = zs.length := by
      unfold Heard1.r
      rw [List.length_map, ← hlen, ← hs.weights, List.length_map]
    have hfin := hrun W h.p h.mu h.ms h.y h.S0 sh hs.weights hs.further hs.lengths hs.vars hs.chals
      hs.claim hT hC hslots hzero hS0 (fun i => by
        rw [hsh i, hlen]
        have e := mle_ext (ofList (h.r ρ)) zs.length (A i)
        rw [← hrl, coords_ofList, hrl] at e
        rw [← e]
        rfl) hne hnb
    rw [hfin]
    have e := tot_ext (ofList (zs.map ρ.val)) zs.length fun X => sumTerms ts fun i => A i X
    have hl : (zs.map ρ.val).length = zs.length := List.length_map _
    rw [← hl, coords_ofList, hl] at e
    exact e

/-- The bad eps, as a function of what stands in front. -/
def pscBadE (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K)) (hcoef : ℕ → K)
    (T Cv : K) : K → Finset K :=
  (eq_products_sound ρ zs A m ts hcoef T Cv).choose

/-- The bad challenges, as a function of what stands in front. -/
def pscBad (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K)) (hcoef : ℕ → K)
    (T Cv : K) : K → K → List (K[X] × K) → K[X] → Finset K :=
  (eq_products_sound ρ zs A m ts hcoef T Cv).choose_spec.choose

theorem pscBadE_card (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K))
    (hcoef : ℕ → K) (T Cv mu : K) : (pscBadE ρ zs A m ts hcoef T Cv mu).card ≤ 1 :=
  (eq_products_sound ρ zs A m ts hcoef T Cv).choose_spec.choose_spec.1 mu

theorem pscBad_card (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K))
    (hcoef : ℕ → K) (T Cv mu eps : K) (pre : List (K[X] × K)) (g : K[X]) :
    (pscBad ρ zs A m ts hcoef T Cv mu eps pre g).card ≤ 2 :=
  (eq_products_sound ρ zs A m ts hcoef T Cv).choose_spec.choose_spec.2.1 mu eps pre g

/-- No element of this sumcheck was bad. -/
def Heard1.Clean (h : Heard1) (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K))
    (hcoef : ℕ → K) (T Cv : K) : Prop :=
  ρ.val h.p.eps ∉ pscBadE ρ zs A m ts hcoef T Cv (ρ.val h.mu) ∧
    (haveI := Classical.decEq K
     NoBad (pscBad ρ zs A m ts hcoef T Cv (ρ.val h.mu) (ρ.val h.p.eps))
      (movesP ρ (h.ms ++ [h.y]) (addE h.mu (mulE h.p.eps h.p.target))))

/-- **The law, with the bad sets by name.** -/
theorem psc_law (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K)) (hcoef : ℕ → K)
    (W : World K) (h : Heard1) (sh : ℕ → K) (hs : h.Shape zs)
    (hslots : ∀ i, i < OnBytes.Psc.hidingEntries (eqWs zs ++ [wY]) →
      W.slot (h.p.first + i) = hcoef i)
    (hzero : (h.p.rowForm h.S0 {}).value ρ W = 0)
    (hS0 : ρ.val h.S0 = sumTerms ts sh)
    (hsh : ∀ i, sh i = ext zs.length (A i) (ofList (h.r ρ)) + h.beta ρ * m i)
    (hc : h.Clean ρ zs A m ts hcoef (ρ.val h.p.target) (h.p.start.value ρ W)) :
    h.p.start.value ρ W =
      ext zs.length (fun X => sumTerms ts fun i => A i X) (ofList (zs.map ρ.val)) :=
  (eq_products_sound ρ zs A m ts hcoef (ρ.val h.p.target)
    (h.p.start.value ρ W)).choose_spec.choose_spec.2.2 W h sh hs rfl rfl hslots hzero hS0 hsh
    hc.1 hc.2

end D6.Bridge

#print axioms D6.Bridge.eq_products_sound
#print axioms D6.Bridge.psc_law
