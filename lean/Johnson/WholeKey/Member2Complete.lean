-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Member2Complete.lean: COMPLETENESS AT THE SECOND MEMBER: the scheme with the whole
key published, at the very letters and THE SAME HONEST SIDES at which all premises of the statement
of index privacy hold together (Johnson/WholeKey/Member2.lean), has completeness error at most 1/16.

Definitions, statements and proofs. A toy: nothing here is about the protocol of the release. This
file states no goal of the release.

Why. Index privacy alone is cheap: honest sides that say nothing meet it. A member is worth its name
only if the same honest sides also convince the verifier. Here the five premises of the theorem on
completeness (complete_argW, Johnson/WholeKey/Complete.lean) are met at W2, S2, cA2, p2 and
at2.side, and the theorem is called.
  THE TRUE INSTANCES (Yes2): the one instance, at the two indices in range.
  THE NUMBER: 1/16. It is the chance that the search of the session's first round fails: a test of
    one bit, four tries. All other summands of alphaAll are 0: no other round has a test; no seed is
    set aside; at an index in range the sets outside which the verifiers accept are empty.
  THE STOPS FIRE: at the index out of range every test for a stop says yes. StopsIn is asked at all
    indices, so the sets (bads2) are everything there; their measures are asked at true instances
    alone.

Main names (namespace OnBytes.WholeKey.Member2).
  Yes2, bads2      the true instances; the sets.
  wiresFit2, lawFit2, sideFit2, accLaws2, stopsIn2   the five premises.
  accLawT, accLawL, accLawB   each verifier accepts every transcript that is the honest run but for
                   nonces.
  alpha2           the number: alphaAll at these letters is 1/16.
  complete_pad2    complete_argW, CALLED.
Completeness, index privacy, index binding (idle there) and the honest side's work at one scheme,
with their numbers: joined_pad2, Johnson/WholeKey/Member2Bundle.lean.

Limits. A toy's: those of Johnson/WholeKey/Member2.lean. Completeness in the library's form: one
commitment and one request, fixed before the oracles are drawn. 1/16 is an upper bound. WHAT THE
THEOREM ON COMPLETENESS HAS AND THIS TOY LEAVES IDLE: no seed is set aside (Z₁, Z₂ are empty); at a
true instance the three sets of verifier's randomness are empty, so their measures are 0; the
verifier's test on the copy's number in a session's plain parts (S2.num) says yes always. That an
honest side that says nothing FAILS completeness is meant and is stated by no theorem here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Member2
import Johnson.WholeKey.Complete

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey.Member2
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open Hiop.Seeded.Two
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A block of 32 bits (Hiop/Seeded/Pad2.lean). -/
local notation "Blk₂" => Hiop.Seeded.Two.Blk

/-- The true instances: the one instance, at an index in range. -/
def Yes2 : Option Bool → Unit → Prop := fun i _ => i ≠ none

/-- The sets outside which the verifiers accept: no seed; of the verifier's randomness nothing at an
index in range, everything at the index out of range. -/
def bads2 (i : Option Bool) : Bads pad2 :=
  ⟨∅, ∅, fun _ => {_ρ | i = none}, fun _ _ => {_ρ | i = none}, fun _ => {_ρ | i = none}⟩

/-! ## Wires and caps -/

theorem fmt2 : aT.Fmt ∧ aL.Fmt ∧ pad2.onlineBatch.ann.Fmt :=
  ⟨RoundSplits.fmt_allLocal _, RoundSplits.fmt_allLocal _, RAnn.noShared_ofSlot .lo rB1, trivial⟩

theorem wiresFit2 : WiresFit W2 cA2 where
  oka := oka
  fewT := ⟨⟨by decide, trivial⟩, ⟨by decide, trivial⟩⟩
  fewL := ⟨⟨by decide, trivial⟩, ⟨by decide, trivial⟩⟩
  fewB := ⟨⟨by decide, by decide, trivial⟩, ⟨by decide, by decide, trivial⟩⟩
  loc := ⟨localT _, localL _, localB _⟩
  coh := ⟨BatchOne.BAnn.allLocal_coherent _, BatchOne.BAnn.allLocal_coherent _,
    RAnn.ofSlot_coherent .lo rB1, RAnn.ofShared_coherent .sh rB2, trivial⟩
  fmt := fmt2

theorem lawFit2 : LawFit W2 S2 at2.side.capT at2.side.capL at2.side.capB where
  offT := fun q _ => seedQ_other (W := W2) (S := S2) (by decide) q
  offL := fun q _ => seedQ_other (W := W2) (S := S2) (by decide) q
  offB := seedQ_off (W := W2) (S := S2) (seedsOff_of_depth rfl rfl)
  okT := okgT
  okL := okgL
  okB := okgB
  fmt := fmt2
  putsT := ⟨fun _ e => (by cases e), trivial⟩
  putsL := ⟨fun _ e => (by cases e), trivial⟩
  putsB := ⟨fun g e α n n' _ _ hp => by
    have e' : gr = g := Option.some.inj e
    rw [← e'] at hp
    exact congrArg Prod.snd hp, fun _ e => (by cases e), trivial⟩

/-! ## Lengths -/

theorem fit_co2 (v : Bool) (a : Fin (co2.n + 1)) :
    (dress (L' := C2) (fun _ _ _ => [v]) (fun _ => []) 2 1 1 (List.replicate 32 false)
      (co2.e a)).Fit 33 32 0 where
  salt := List.length_ofFn
  leaf := fun i b k j => by
    show ([v] ++ if i < 2 ∧ k < 1 ∧ j < 1 then (co2.e a).leaf i b k j
      else List.replicate 32 false).length = 33
    by_cases hw : i < 2 ∧ k < 1 ∧ j < 1
    · rw [if_pos hw]
      show ([v] ++ if h : i < 2 ∧ k < 1 ∧ j < 1 then List.ofFn _ else []).length = 33
      rw [dif_pos hw, List.length_append, List.length_ofFn]
      rfl
    · rw [if_neg hw, List.length_append, List.length_replicate]
      rfl
  slot := Nat.one_pos
  path := List.length_ofFn

theorem sideFit2 : SideFit W2 p2 at2.side where
  sl := fun a j hj => by
    have hj' : j < 2 ^ 0 := hj
    show (if j < 2 ^ 0 then (if h : j < 2 ^ 0 then [false] ++ List.ofFn _ else []) else []).length
      = 33
    rw [if_pos hj', dif_pos hj', List.length_append, List.length_ofFn]
    rfl
  coT := fun a c => fit_co2 _ a
  coL := fun a c => fit_co2 _ a
  coB := fun a c => fit_co2 _ a

/-! ## The verifiers accept; the stops -/

/-- The first table's verifier accepts every transcript that is the honest run but for nonces:
whatever the set B. -/
theorem accLawT (i : Option Bool) (r : Bool × Bool) (e κ : Bool) (B : Set (Rho pad2.offline.shape)) :
    AccLaw (batTC pad2 aT) (wTC W2) (pad2.recOf i r e) (pad2.encodeIndex i r)
      (recs2.T.strat (i, r, e) (pad2.recOf i r e) κ) B := fun τ _ hp _ => by
  show (orT τ == xor (bit i) r.1) = true
  have h : orT τ = xor (bit i) r.1 := hp.1
  rw [h]
  exact beq_self_eq_true _

/-- The same for a link. -/
theorem accLawL (i : Option Bool) (r : Bool × Bool) (e : Bool) (r' : Bool × Bool) (e' κ : Bool)
    (B : Set (Rho pad2.link.shape)) :
    AccLaw (batLC pad2 aL) (wLC W2) (pad2.recOf i r e, pad2.recOf i r' e')
      (pad2.encodeIndex i r, pad2.encodeIndex i r')
      (recs2.Lk.strat (i, (r, e), (r', e')) (pad2.recOf i r e, pad2.recOf i r' e') κ) B :=
  fun τ _ hp _ => by
  show ((plL τ).1 == xor (xor (bit i) r.1) (xor (bit i) r'.1)) = true
  have h : plL τ = (xor (xor (bit i) r.1) (xor (bit i) r'.1), κ) := by
    rcases hp.2.2.1 with h | ⟨g, n, _, hg, _⟩ | ⟨g, n, hk, _⟩
    · exact h
    · cases hg
    · cases hk
  rw [h]
  exact beq_self_eq_true _

/-- The same for a session. -/
theorem accLawB (i : Option Bool) (r : Bool × Bool) (e : Bool) (x : Unit) (n : ℕ) (κ : Bool)
    (B : Set (Rho pad2.onlineBatch.loc.shape)) :
    AccLaw pad2.onlineBatch (wBC W2) (x, pad2.recOf i r e) (pad2.encodeIndex i r)
      (recs2.B.strat (i, r, e, n) (x, pad2.recOf i r e) κ) B := fun τ _ hp _ => by
  show (((plB1 τ).1.1 == xor (bit i) r.1) && (plB2 τ == chB1 τ 0 1)) = true
  have h1 : (plB1 τ).1 = (xor (bit i) r.1, κ) := by
    rcases hp.2.2.1 with h | ⟨g, m, _, hg, h⟩ | ⟨g, m, hk, _⟩
    · exact congrArg Prod.fst h
    · have e' : gr = g := Option.some.inj hg
      rw [← e'] at h
      exact congrArg Prod.fst h
    · cases hk
  have h2 : plB2 τ = chB1 τ 0 1 := by
    rcases hp.2.2.2.2.2.1 with h | ⟨g, m, hk, _⟩ | ⟨g, m, _, hg, _⟩
    · exact h
    · cases hk
    · cases hg
  rw [h1, h2, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem accAt2 (i : Option Bool) (r₁ : Bool × Bool) (x : Unit)
    (d : Draw 32 pad2 Bool aT aL (Bool × Bool × Bool)) :
    AccAt W2 S2 at2.side.st.joint i r₁ x d (bads2 i) where
  T := fun e₁ _ => accLawT i r₁ e₁ d.κ.1 _
  Lk := fun e₁ e₂ _ _ => accLawL i r₁ e₁ d.r e₂ d.κ.2.1 _
  B := fun e₂ _ => accLawB i d.r e₂ x d.n d.κ.2.2 _
  num := fun _ _ _ => rfl

theorem accLaws2 : AccLaws W2 S2 at2.side.st.joint Yes2 (fun i _ _ _ => bads2 i) 0 0 0 0 0 where
  acc := fun i r₁ x d _ => accAt2 i r₁ x d
  small := fun _ _ _ _ hY =>
    ⟨le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
      le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
      fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hY h),
      fun _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hY h),
      fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hY h)⟩

theorem stopsIn2 : StopsIn (lam := 32) (Bd := Bool) (aT := aT) (aL := aL) at2.side.st
    (fun i _ _ _ => bads2 i) where
  T := fun i r₁ _ _ e ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _ (at2.dc.T (i, r₁, e) (pad2.recOf i r₁ e) ρ) hs)).elim
      (fun h => h.elim) fun h => h
  Lk := fun i r₁ _ d e e' ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _
        (at2.dc.Lk (i, (r₁, e), (d.r, e')) (pad2.recOf i r₁ e, pad2.recOf i d.r e') ρ) hs)).elim
      (fun h => h.elim) fun h => h
  B := fun i _ x d e ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _ (at2.dc.B (i, d.r, e, d.n) (x, pad2.recOf i d.r e) ρ) hs)).elim
      (fun h => h.elim) fun h => h

/-! ## The number, and the theorem called -/

/-- The number: the chance that four tries at a test of one bit all fail. -/
theorem alpha2 : alphaAll W2 at2.side.capT at2.side.capL at2.side.capB 0 0 0 0 0 = 16⁻¹ := by
  show ((0 : ℝ≥0∞) + 0) + (0 + 0) + ((1 - ((2 : ℝ≥0∞) ^ 1)⁻¹) ^ (3 + 1) + (0 + 0)) + (0 + 0) +
    (0 + 0 + 0) = 16⁻¹
  rw [pow_one, ENNReal.one_sub_inv_two, ← ENNReal.inv_pow]
  norm_num

/-- **complete_argW, called**: at the second member's letters and honest sides the verifier says no
to a true instance with probability at most 1/16. -/
theorem complete_pad2 (r₀ : pad2.Rec) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes2))
      (argW W2 S2 cA2 r₀ p2 at2.side) 1 16⁻¹ := by
  rw [← alpha2]
  exact complete_argW W2 S2 cA2 r₀ p2 at2.side Yes2 (fun i _ _ _ => bads2 i) lawFit2 wiresFit2
    sideFit2 accLaws2 stopsIn2

end OnBytes.WholeKey.Member2

#print axioms OnBytes.WholeKey.Member2.complete_pad2
