-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Stages.lean
(kind K9's soundness lemma): THEOREMS: the count where the claims are added IN
SEVERAL STEPS, with other steps between: the form of a fold in which K9.adds stands at several
places (Batch/Kind.lean), as well as K9.batch's form (one step).
A stage is a list of claims and the steps behind their adding. runStages: for each stage in turn,
the claims are added, then the stage's steps run.
  KeepCore            the premise on the steps between: they leave alone the ledger's sums
                      (Measure.lean: sums), chi, the count of claims and the plan's number.
  runStages_total     the ledger's value grows by the sum of ALL stages' claims, numbered through.
  PremisesS, PassesS  as Premises and Passes (Law/Statements.lean), with stages.
  batch_sound_stages  the count.
  PassesRowS, batch_sound_row_stages   the count at the row on the tables.
The world is taken at the ledger at which the equation is made, behind the last stage.

-/
import Johnson.Desc.First.Batch.Law.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St ledgerEmpty)

/-- Claims, and the steps behind their adding. -/
abbrev Stage : Type := List Claim × (Fork → Option Fork)

/-- What the steps between must leave alone. -/
def core (F : Fork) : (Array (Array (Array E × Nat)) × Array E × E × Nat) × E × Nat × Nat :=
  (sums F, F.theta, F.nClaim, F.planClaimsF)

/-- The stages in turn. -/
def runStages (add : Fork → Claim → Option Fork) : Fork → List Stage → Option Fork
  | F, [] => some F
  | F, s :: l => (s.1.foldlM add F).bind fun G => (s.2 G).bind fun H => runStages add H l

def KeepCore (l : List Stage) : Prop := ∀ s ∈ l, ∀ G H, s.2 G = some H → core H = core G

/-- All stages' claims, in order. -/
def allClaims (l : List Stage) : List Claim := l.flatMap (·.1)

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem sumFrom_append {α : Type} (g : Nat → α → K) : ∀ (a b : List α) (s : Nat),
    sumFrom g s (a ++ b) = sumFrom g s a + sumFrom g (s + a.length) b
  | [], b, s => by simp [sumFrom]
  | x :: a, b, s => by
    simp only [List.cons_append, sumFrom, sumFrom_append g a b (s + 1), List.length_cons]
    rw [show s + 1 + a.length = s + (a.length + 1) by omega, add_assoc]

theorem claimsSum_append (x : K) (n c : Nat) (a b : List Claim) :
    claimsSum ρ W x n c (a ++ b) = claimsSum ρ W x n c a + claimsSum ρ W x n (c + a.length) b :=
  sumFrom_append _ a b c

theorem runStages_sizes : ∀ (l : List Stage) (F H : Fork), KeepCore l →
    runStages addClaim F l = some H → H.LS.size = F.LS.size ∧ H.ns = F.ns
  | [], F, H, _, h => by
    have e : F = H := Option.some.inj h
    rw [e]
    exact ⟨rfl, rfl⟩
  | s :: l, F, H, hk, h => by
    rw [runStages] at h
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨H1, hH1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a1, a2⟩ := addAll_sizes s.1 F G hG
    have k := hk s (List.mem_cons_self ..) G H1 hH1
    simp only [core, sums, Prod.mk.injEq] at k
    obtain ⟨b1, b2⟩ := runStages_sizes l H1 H
      (fun s' hs' => hk s' (List.mem_cons_of_mem _ hs')) h
    exact ⟨by rw [b1, k.1.2.1, a1], by rw [b2, k.1.2.2.2, a2]⟩

/-- **The ledger's value behind all stages.** -/
theorem runStages_total : ∀ (l : List Stage) (F H : Fork), F.LS.size = F.ns → KeepCore l →
    runStages addClaim F l = some H →
    H.total ρ W = F.total ρ W +
      claimsSum ρ W (ρ.val F.theta) F.planClaimsF F.nClaim (allClaims l)
  | [], F, H, _, _, h => by
    have e : F = H := Option.some.inj h
    rw [e]
    simp [allClaims, claimsSum, sumFrom]
  | s :: l, F, H, hs, hk, h => by
    rw [runStages] at h
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨H1, hH1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t1, e1, s1, _⟩ := addAll_total ρ W s.1 F G hs hG
    have k := hk s (List.mem_cons_self ..) G H1 hH1
    have ksum : sums H1 = sums G := congrArg Prod.fst k
    have kθ : H1.theta = G.theta := congrArg (fun x => x.2.1) k
    have kn : H1.nClaim = G.nClaim := congrArg (fun x => x.2.2.1) k
    have kp : H1.planClaimsF = G.planClaimsF := congrArg (fun x => x.2.2.2) k
    have ks := ksum
    simp only [sums, Prod.mk.injEq] at ks
    have hs1 : H1.LS.size = H1.ns := by rw [ks.2.1, ks.2.2.2]; exact s1
    have gθ : G.theta = F.theta := by rw [e1]
    have gn : G.nClaim = F.nClaim + s.1.length := by rw [e1]
    have gp : G.planClaimsF = F.planClaimsF := by rw [e1]
    rw [runStages_total l H1 H hs1 (fun s' hs' => hk s' (List.mem_cons_of_mem _ hs')) h,
      total_of_sums ρ W G H1 ksum, t1, kθ, kn, kp, gθ, gn, gp]
    simp only [allClaims, List.flatMap_cons]
    rw [claimsSum_append]
    ring

end

/-! ## The count -/

/-- The premises, by name. stages chi: the stages if the element drawn is chi. In a segment the
steps act on the whole state, and a stage's claims are made at the state behind the earlier stages:
that they are functions of chi alone rests on all else being fixed before the draw. -/
structure PremisesS (add : Fork → Claim → Option Fork) {K : Type} [Field K] (ρ : Reading K)
    (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (stages : E → List Stage) (t : List (ℕ × K))
    (d : ℕ) : Prop where
  holdsChi : ∀ chi, (F chi).theta = chi
  startsEmpty : ∀ chi, ledgerEmpty (F chi) = true
  keepCore : ∀ chi, KeepCore (stages chi)
  termsOk : TermsOk t d
  fixedBefore : ∀ chi H, runStages add (F chi) (stages chi) = some H →
    claimsSum ρ (worldAt ρ (L chi) H D) (ρ.val chi) (F chi).planClaimsF (F chi).nClaim
      (allClaims (stages chi)) = termsSum t (ρ.val chi)

def PassesS (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    {K : Type} [Field K] (ρ : Reading K) (D : Bound K) (L : E → LinkCtx) (F : E → Fork)
    (stages : E → List Stage) (chi : E) : Prop :=
  ∃ H q G', runStages add (F chi) (stages chi) = some H ∧ eqn (L chi) H = .ok (q, G') ∧
    eqValue ρ (dimsOf (L chi).check) D q = 0

variable {K : Type} [Field K] (ρ : Reading K)

theorem passesS_root (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (stages : E → List Stage)
    (t : List (ℕ × K)) (d : ℕ) (P : PremisesS addClaim ρ D L F stages t d) (chi : E)
    (h : PassesS addClaim equation ρ D L F stages chi) : termsSum t (ρ.val chi) = 0 := by
  obtain ⟨H, q, G', hr, he, hv⟩ := h
  have hs : (F chi).LS.size = (F chi).ns := by
    obtain ⟨s1, s2⟩ := runStages_sizes (stages chi) (F chi) H (P.keepCore chi) hr
    rw [← s1, ← s2]
    exact equation_sized (L chi) H G' q he
  have b := equation_total ρ D (L chi) H G' q he
  rw [runStages_total ρ _ (stages chi) (F chi) H hs (P.keepCore chi) hr,
    total_of_empty ρ _ (F chi) (P.startsEmpty chi), zero_add, P.holdsChi chi,
    P.fixedBefore chi H hr] at b
  rw [← b, hv]

/-- **THE COUNT, with stages.** -/
theorem batch_sound_stages [Fintype K] (D : Bound K) (L : E → LinkCtx) (F : E → Fork)
    (stages : E → List Stage) (t : List (ℕ × K)) (d : ℕ)
    (P : PremisesS addClaim ρ D L F stages t d) (hne : ∃ y ∈ t, y.2 ≠ 0) :
    Prob.cnt (fun x : K =>
      ∃ chi, ρ.val chi = x ∧ PassesS addClaim equation ρ D L F stages chi) ≤ d :=
  le_trans
    (Prob.cnt_mono fun x hx => by
      obtain ⟨chi, hc, hp⟩ := hx
      rw [← hc]
      exact passesS_root ρ D L F stages t d P chi hp)
    (count_terms K t d P.termsOk hne)

def PassesRowS (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    (mk : ReqRows → ReqFrame → Equation → St Unit → Ans (OnBytes.Row × St Unit))
    (tab : Nat → OnBytes.Part → Nat → K) (N : Nat) (L : E → LinkCtx) (F : E → Fork)
    (stages : E → List Stage) (dd : E → St Unit) (chi : E) : Prop :=
  ∃ H q G' row d', runStages add (F chi) (stages chi) = some H ∧ eqn (L chi) H = .ok (q, G') ∧
    mk (L chi).check.rows (L chi).check.frame q (dd chi) = .ok (row, d') ∧
    rowSum ρ (dd chi).st N tab row = ρ.val row.target

/-- **THE COUNT AT THE ROW, with stages.** -/
theorem batch_sound_row_stages [Fintype K] (tab : Nat → OnBytes.Part → Nat → K) (N : Nat)
    (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (stages : E → List Stage) (dd : E → St Unit)
    (t : List (ℕ × K)) (d : ℕ) (P : PremisesS addClaim ρ D L F stages t d)
    (Q : DoorPremises equation (fun chi H => runStages addClaim (F chi) (stages chi) = some H) tab N
      D L dd) (hne : ∃ y ∈ t, y.2 ≠ 0) :
    Prob.cnt (fun x : K => ∃ chi, ρ.val chi = x ∧
      PassesRowS ρ addClaim equation asRow tab N L F stages dd chi) ≤ d :=
  le_trans
    (Prob.cnt_mono fun _ hx => by
      obtain ⟨chi, hc, H, q, G', row, d', h1, h3, h4, h5⟩ := hx
      refine ⟨chi, hc, H, q, G', h1, h3, ?_⟩
      have e := asRow_sum ρ (L chi).check q (dd chi) d' row N tab (equation_k9 _ _ _ _ h3)
        (Q.facts chi H q G' h1 h3) h4
      rw [Q.doorFixed chi, h5, sub_self] at e
      exact e.symm)
    (batch_sound_stages ρ D L F stages t d P hne)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.runStages_total
#print axioms VerifiableInference.Desc.K9L.batch_sound_stages
#print axioms VerifiableInference.Desc.K9L.batch_sound_row_stages
