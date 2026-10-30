-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Member2Bundle.lean: THE SECOND MEMBER AT ONE SCHEME, WITH NUMBERS: completeness,
index privacy and the honest side's work at ONE term, argW at the letters of
Johnson/WholeKey/Member2.lean, each with its number; and index binding there, which holds idly.

Statements and proofs. A toy: nothing here is about the protocol of the release. This file states no
goal of the release.

Why. Johnson/WholeKey/Bundle.lean has five clauses at one term (bundle_argW) and says that they want
bars: theorems at named letters that the errors are small. Here all eleven premises of bundle_argW
are met at the second member, SIX WITH A CASE, INDEX BINDING's FIVE IDLY (for lack of a case: see
Limits), and the numbers are written. NOTHING ON BINDING FOLLOWS FROM THIS FILE.
  honFit2      the premise of completeness at honest sides (HonFit,
               Johnson/Prover/All/OfHonest.lean) at recs2: no fall, no seed set aside, all four
               numbers 0.
  soundAt_pad2 the soundness of the three interactive protocols (HolographicProtocol.SoundAtR,
               Hiop/RecInterface.lean) at pad2, with all errors 0: FOR LACK OF A CASE, see Limits.
  bundle_pad2  bundle_argW, CALLED, with no premise left.
  eps_pad2     what the general theorem's formula for binding's error gives at the honest side's own
               count of queries, one commitment and three requests: 313632 / 2^32. AN IDLE NUMBER
               HERE, see Limits.
  joined_pad2  WITHOUT A PREMISE, at argW W2 S2 cA2 r₀ p2 at2.side and one pair of relations:
      completeness at 1/16;
      index binding, extractor named, at soundnessBoundOverTypedOracles W2 0, which at 26 and 3 · 11 queries is below 1: AN
        IDLE CLAUSE HERE, see Limits;
      index privacy on the range ok2, simulator named, at zetaW, and zetaW 1 3 + zetaW 1 3 < 1
        (where the statement begins to speak, no more: Johnson/WholeKey/Half.lean);
      the committer asks at most 26 typed queries on every path, the prover at most 11.

Limits. NEVER QUOTE joined_pad2 OR bundle_pad2 FOR BINDING: at this toy their clause on index
binding holds of every scheme. INDEX BINDING IS IDLE AT THIS TOY. pad2's index decoder answers one
fixed index at every word, and no seed is a collision seed. So the three languages of SoundAtR hold
every word; the wider relation RnoW holds of everything; and soundAt_pad2 holds for lack of a case,
at εs = 0. What binding says here: an adversary's accepted proof is for an instance that is in the
wider relation with the extracted index: which is no news. Its bad event is empty here, so the
clause would hold of any verifier at the error 0; the number of eps_pad2 is what the general
theorem's formula gives at these counts, and bounds nothing at this toy.
CORRECTNESS OF EXTRACTION IS FALSE AT THIS TOY (read off the definitions; no theorem here states
it). The type of indices has three members, two of them in range, and the extractor names the bit 0
WHATEVER WAS COMMITTED: after an honest commitment to the bit 1 it still says 0. The library's law
for it (WiredR.dec_enc, Hiop/RecInterface.lean) fails at the bit 1; neither PremW nor the bundle
asks it. It cannot be mended at this toy: the word is one symbol, wholly padded.
WHAT THE TOY's SESSIONS PROVE: NOTHING ABOUT THE INDEX. There is one instance; it is true at the
indices in range; a session's verifier checks that the prover knows the symbol that it reads itself,
and a bit of its own message.
"BELOW 1" IS NO GUARD, ON EITHER SIDE: THE NUMBERS TELL. For hiding an error says nothing until it
is below one half (Johnson/WholeKey/Half.lean). For completeness: by arithmetic that is not typed,
honest sides of this toy that send fixed messages are accepted by luck with probability 15/128, so
their true completeness error is 113/128, below 1, and they are private. What sets the honest sides
of this member apart is 1/16 against 113/128, and about 1/4 against 1/2. No theorem here says that
honest sides that send fixed messages fail.
"PASSES THE BAR" IS NOT "HIDES": ζ + ζ < 1 is where the statement begins to speak: necessary, not
enough. Argued, not typed: a prover that tells its index and hands no string in a share β of its
proofs, with a simulator that mixes the two indices, would sit at (1 - β)/2 and, if β is not 0, pass
it (of the teller of Johnson/WholeKey/FoeScheme.lean Lean has β ≤ 1/16 alone: so 15/32 or more).
What shuts out a prover that tells outright is ζ + ζ + α < 1, with α the error of completeness,
which β does not exceed (the typed half: teller_not_private there: 1 ≤ ζ + ζ + 1/16). QUOTE THE
NUMBER: twice the error is at most about 0.50 here, at one query and three requests (at the first
member at most about 0.23). So this member shows little on hiding: it shows that the premises can be
met together.
The two bars, and binding's idle number, speak of different numbers of requests: completeness of
one; privacy of three; binding's count of three.
The other limits are those of Johnson/WholeKey/Member2.lean, Johnson/WholeKey/Member2Complete.lean
and Johnson/WholeKey/Bundle.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Bundle
import Johnson.WholeKey.Member2Complete
import Ior.KnowWide

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey.Member2
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open Hiop.Seeded.Two
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The relations -/

/-- True: the index is in range. The witness is of the type with one member. -/
def RyesW : Option Bool → Unit → Unit → Prop := fun i _ _ => i ≠ none

/-- The wider relation: everything. -/
def RnoW : Option Bool → Unit → Unit → Prop := fun _ _ _ => True

theorem sub2 : ∀ i x, (∃ w, RyesW i x w) → ∃ w, RnoW i x w := fun _ _ _ => ⟨(), trivial⟩

/-- The pair of relations. -/
abbrev R2 : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit :=
  relPair (fun i x => ∃ w, RyesW i x w) (fun i x => ∃ w, RnoW i x w) sub2

theorem inRange {i : Option Bool} {x : Unit} (h : ∃ w, RyesW i x w) : i ≠ none :=
  h.elim fun _ h => h

/-- Every index with a true instance is in the range. -/
theorem tie2 : ∀ i, (∃ x w, RyesW i x w) → ok2 i := fun _ h => h.elim fun _ h => inRange h

/-! ## The premise of completeness at honest sides -/

theorem honFit2 : HonFit recs2 (Falls.none recs2) W2 S2 (fun i x => ∃ w, RyesW i x w)
    (fun _ _ => ∅) 0 0 0 0 where
  extT := fun _ _ _ => rfl
  extL := fun _ _ _ _ _ => rfl
  extB := fun _ _ _ _ => rfl
  whT := fun _ _ _ _ h => h
  whL := fun _ _ _ _ h => h
  whB := fun _ _ _ _ h => h
  accT := fun i _ r e c _ _ => accLawT i r e c _
  accL := fun i _ r e r' e' c _ _ _ => accLawL i r e r' e' c _
  accB := fun i x r e n c _ _ => accLawB i r e x n c _
  prZ := fun _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)
  prT := fun _ _ _ _ _ hY => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
    h.elim (fun h => h.elim (fun h => h) fun h => inRange hY h) fun h => h)
  prL := fun _ _ _ _ _ _ _ hY => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
    h.elim (fun h => h.elim (fun h => h) fun h => inRange hY h) fun h => h)
  prB := fun _ _ _ _ _ _ hY => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
    h.elim (fun h => h.elim (fun h => h) fun h => inRange hY h) fun h => h)
  num := fun _ _ _ _ _ _ _ _ _ => rfl

/-! ## The premises of index binding -/

/-- A property that nothing has is had by at most e. -/
theorem cnt_none_le {C : Type} [Fintype C] {P : C → Prop} (h : ∀ c, ¬ P c) (e : ℕ) :
    cnt P ≤ e := by
  classical
  rw [cnt_eq_card_filter]
  refine (Finset.card_le_card (t := (∅ : Finset C)) fun c hc =>
    absurd (Finset.mem_filter.1 hc).2 (h c)).trans ?_
  rw [Finset.card_empty]
  exact Nat.zero_le e

/-- States that are 0 everywhere meet the law on verifier messages at all errors. -/
theorem jointLaw_false (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (ε : Err s)
    (St : Fin N → Option (PTr s → Bool)), (∀ j S, St j = some S → ∀ τ, S τ = false) →
    JointLaw N s A ε St
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), St, h => by
    intro m0 m
    refine ⟨?_, fun v => jointLaw_false N s A ε _ fun j S hS τ => ?_⟩
    · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k
      · exact cnt_none_le (fun c ⟨j, S, hS, _, h1⟩ => by
          rw [h j S hS] at h1
          cases h1) e
      · exact fun j S hS _ => cnt_none_le (fun c h1 => by
          rw [h j S hS] at h1
          cases h1) e
    · obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.1 hS
      exact h j S' hS' _

/-- the errors of the rounds: all 0 -/
def εT0 : Err pad2.offline.shape := ((0, ()) : ℕ × Unit)
def εL0 : Err pad2.link.shape := ((0, ()) : ℕ × Unit)
def εB0 : Err pad2.onlineBatch.loc.shape := ((0, (0, ())) : ℕ × (ℕ × Unit))

/-- the witness map: there is one witness -/
def wit0 : Unit × pad2.Rec → (oneExternalString pad2.wordLength pad2.Symbol).Str → Tr pad2.onlineBatch.loc.shape → Unit :=
  fun _ _ _ => ()

/-- **The three protocols are sound at pad2, for lack of a case**: every word decodes. -/
theorem soundAt_pad2 : pad2.SoundAtR RnoW wit0 0 εT0 εL0 εB0 where
  noneColl := fun _ _ h => h.elim
  rcd := fun _ => cnt_none_le (fun _ h => h) 0
  sndT := fun _ _ h =>
    (h (Or.inr fun e : (some (some false) : Option (Option Bool)) = none => by cases e)).elim
  sndL := fun _ _ h => absurd (Or.inr (Or.inr rfl)) h
  sndB := fun rec => (sndBP_iff _ _ (pad2.batAt rec) 1 _ εB0).2
    ⟨fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ _ => Or.inr ⟨some false, rfl, trivial⟩,
      fun _ x => jointLaw_false 1 _ _ _ _ fun j S hS τ => by
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hS
        rfl⟩

theorem law_S2 : S2.Law 0 := fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)

theorem cast0_le (z : ℝ≥0∞) : ((0 : ℕ) : ℝ≥0∞) ≤ z := by
  rw [Nat.cast_zero]
  exact zero_le z

theorem belowT : Err.Below (Err.timesShared (2 ^ W2.depthReqT) aT εT0) 0 := ⟨cast0_le _, trivial⟩

theorem belowL : Err.Below (Err.timesShared (2 ^ W2.depthReqL) aL εL0) 0 := ⟨cast0_le _, trivial⟩

theorem belowB : Err.Below εB0 0 := ⟨cast0_le _, cast0_le _, trivial⟩

/-! ## The counts, and binding's idle number -/

theorem commitN2 : commitN W2 at2.side = 26 := by decide
theorem proveN2 : proveN W2 at2.side = 11 := by decide
theorem tVC2 : tVC W2 = 19 := by decide

/-- What the general theorem's formula for binding's error gives at the honest side's own count of
queries: one commitment, three requests. It bounds nothing at this toy. -/
theorem eps_pad2 :
    soundnessBoundOverTypedOracles W2 0 (commitN W2 at2.side) (3 * proveN W2 at2.side) = 313632 / 4294967296 ∧
      soundnessBoundOverTypedOracles W2 0 (commitN W2 at2.side) (3 * proveN W2 at2.side) < 1 := by
  have e : soundnessBoundOverTypedOracles W2 0 (commitN W2 at2.side) (3 * proveN W2 at2.side) = 313632 / 4294967296 := by
    unfold soundnessBoundOverTypedOracles
    rw [commitN2, proveN2, tVC2]
    norm_num
  refine ⟨e, ?_⟩
  rw [e]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

/-! ## At one scheme -/

/-- **The five clauses of bundle_argW at the second member.** No premise is left; index binding's
five are met idly. -/
theorem bundle_pad2 (r₀ : pad2.Rec) (i₀ : Option Bool) :
    ZKCP.Gen.HasCompletenessError R2 (argW W2 S2 cA2 r₀ p2 at2.side) 1
        (alphaAll W2 at2.capT at2.capL at2.capB 0 0 0 0 0) ∧
      ZKCP.Gen.HasIndexBindingWith R2 (argW W2 S2 cA2 r₀ p2 at2.side) (extractorC0 W2)
        (soundnessBoundOverTypedOracles W2 0) ∧
      ZKCP.Gen.PrivacyOn R2 (argW W2 S2 cA2 r₀ p2 at2.side) 1
        (simWholeKey W2 S2 cA2 r₀ at2.side sm2 i₀ nu2.s1 (fun _ => True) Unit)
        (zetaW W2 S2 p2 at2 cn2 nu2) ok2 ∧
      (∀ i, (commitW W2 S2 cA2 at2.side i).QueryBound (commitN W2 at2.side)) ∧
      ∀ isk b, (proveW W2 cA2 r₀ at2.side isk b).QueryBound (proveN W2 at2.side) :=
  bundle_argW W2 S2 cA2 r₀ p2 at2 sm2 ok2 (fun _ => True) cn2 nu2 i₀ RyesW RnoW wit0 0 εT0 εL0 εB0
    0 sub2 (Falls.none recs2) (fun _ _ => ∅) 0 0 0 0 tie2 (premW_pad2 _) soundAt_pad2 law_S2 belowT
    belowL belowB honFit2 lawFit2 wiresFit2 sideFit2

/-- **COMPLETE, PRIVATE AND OF BOUNDED WORK, AT ONE SCHEME, WITH THE NUMBERS**; the clause on index
binding holds idly (the head's Limits). -/
theorem joined_pad2 (r₀ : pad2.Rec) (i₀ : Option Bool) :
    (ZKCP.Gen.HasCompletenessError R2 (argW W2 S2 cA2 r₀ p2 at2.side) 1 16⁻¹ ∧
        (16⁻¹ : ℝ≥0∞) < 1) ∧
      (ZKCP.Gen.HasIndexBindingWith R2 (argW W2 S2 cA2 r₀ p2 at2.side) (extractorC0 W2)
          (soundnessBoundOverTypedOracles W2 0) ∧
        soundnessBoundOverTypedOracles W2 0 26 (3 * 11) < 1) ∧
      (ZKCP.Gen.PrivacyOn R2 (argW W2 S2 cA2 r₀ p2 at2.side) 1
          (simWholeKey W2 S2 cA2 r₀ at2.side sm2 i₀ nu2.s1 (fun _ => True) Unit)
          (zetaW W2 S2 p2 at2 cn2 nu2) ok2 ∧
        zetaW W2 S2 p2 at2 cn2 nu2 1 3 + zetaW W2 S2 p2 at2 cn2 nu2 1 3 < 1) ∧
      (∀ i, (commitW W2 S2 cA2 at2.side i).QueryBound 26) ∧
      ∀ isk b, (proveW W2 cA2 r₀ at2.side isk b).QueryBound 11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := bundle_pad2 r₀ i₀
  refine ⟨⟨?_, ENNReal.inv_lt_one.2 (by norm_num)⟩, ⟨h2, ?_⟩, ⟨h3, zeta_pad2_half⟩, ?_, ?_⟩
  · rw [← alpha2]
    exact h1
  · have e := eps_pad2.2
    rw [commitN2, proveN2] at e
    exact e
  · rw [← commitN2]
    exact h4
  · rw [← proveN2]
    exact h5

end OnBytes.WholeKey.Member2

#print axioms OnBytes.WholeKey.Member2.honFit2
#print axioms OnBytes.WholeKey.Member2.soundAt_pad2
#print axioms OnBytes.WholeKey.Member2.eps_pad2
#print axioms OnBytes.WholeKey.Member2.bundle_pad2
#print axioms OnBytes.WholeKey.Member2.joined_pad2
