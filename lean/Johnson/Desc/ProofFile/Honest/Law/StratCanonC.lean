-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratCanonC.lean: the words of the field elements in every message
that a speaker of Honest/StratC.lean writes are below the prime. This holds at every verifier's
message and at every state of the walk, halted or not, and for the fixed substitutes too. It covers
the words of the elements of the message's plain part, and of every symbol of its oracle part, read
or not. Of an item that is a word or a root nothing is asked (`LtGot`, Honest/Law/StratCanon.lean),
as in the library's `viewWordsBelowPrime`. There is no hypothesis. It is the counterpart of
Honest/Law/StratCanon.lean, which has the same for the speakers of Honest/Strat.lean, and it uses
that file's lemmas. The main lemma is `trOfC_words`.

  1  `sub_lt`, `tellC_lt`   what a round sends, a prover's side's message or the fixed substitute
  2  `trOfC_vals_lt`, `trOfC_cols_lt`, `trOfC_words`   a chain's transcript

Limits.
  * Nothing is said on acceptance.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratCanon
import Johnson.Desc.ProofFile.Honest.Law.StratChainC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (fieldPrimeWord viewWordsBelowPrime Oracle)
open OnBytes.Maker (RDT uLT roundT rvT PosT colT zeroT colOfSym)
open _root_.Run.PQ (CK PlainOf)

variable {S Cl W Y : Type}

/-! ## 1 What a round sends -/

theorem sub_lt (d : Fmt.DeclaredRound) (os : List Oracle) : ∀ a ∈ (subTold d os).vals, LtGot a := by
  intro a ha
  have ha' : a ∈ (d.items.flatMap subSaid).map Said.got := ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha'
  exact ltGot_said v

theorem tellC_lt {z : ChainProgress S Cl W Y} {s : Option (Step W Y)} {x : Told}
    (h : tellC z s = some x) : ∀ a ∈ x.vals, LtGot a := by
  cases s with
  | none => cases h
  | some s =>
    have h' : some (((z.say s).toOption).getD (subTold s.decl s.oracles)) = some x := h
    have h'' := Option.some.inj h'
    cases hs : z.say s with
    | error e =>
      rw [hs] at h''
      have e' : subTold s.decl s.oracles = x := h''
      rw [← e']
      exact sub_lt _ _
    | ok y =>
      rw [hs] at h''
      have e' : y = x := h''
      subst e'
      cases hm : z.mid with
      | none =>
        have hs' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok y := by
          rw [← hs]
          unfold ChainProgress.say
          rw [hm]
        cases hs'
        exact sub_lt _ _
      | some m =>
        have hs' : s.tell none m = .ok y := by
          rw [← hs]
          unfold ChainProgress.say
          rw [hm]
        exact told_lt hs'

/-! ## 2 A chain's transcript -/

theorem trOfC_vals_lt (C : CK) (L : Lay) : ∀ (ds : List RDT) (ss : List (Step W Y))
    (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)),
    ∀ r ∈ rvT C ds (trOfC C L ds ss z ρ), ∀ a ∈ r.vals, LtGot a
  | [], _, _, _, _, h => by cases h
  | d :: ds, ss, z, (c, ρ), r, h => by
    have h' : r ∈ (⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (msgOf C d (tellC z ss.head?)).2), drOf C d c⟩ : Fmt.RoundView) ::
          rvT C ds (trOfC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) ρ) := h
    rcases List.mem_cons.1 h' with rfl | h'
    · show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (msgOf C d (tellC z ss.head?)).2), LtGot a
      cases ht : tellC z ss.head? with
      | none =>
        show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
          (Iop.GPlain.mk d.entry.work (PlainOf.dflt d.items) (default : ℕ))), LtGot a
        rw [Iop.GPlain.old_mk]
        exact gots_dflt_lt _
      | some x =>
        show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
          (Iop.GPlain.mk d.entry.work (plainOf d.items x.vals) (0 : ℕ))), LtGot a
        rw [Iop.GPlain.old_mk]
        exact gots_plainOf_lt _ _ (tellC_lt ht)
    · exact trOfC_vals_lt C L ds ss.tail _ ρ r h'

theorem trOfC_cols_lt (C : CK) (L : Lay) : ∀ (ds : List RDT) (ss : List (Step W Y))
    (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)) (q : Iop.OPos (uLT C ds)),
    ∀ a ∈ colOfSym C ds q ((trOfC C L ds ss z ρ).read q), a < fieldPrimeWord
  | [], _, _, _, q => nomatch q
  | d :: ds, ss, z, (c, ρ), .inl p => by
    show ∀ a ∈ colT d.trees p ((msgOf C d (tellC z ss.head?)).1 p), a < fieldPrimeWord
    cases tellC z ss.head? with
    | none => exact colT_zeroT_lt d.trees p
    | some x => exact colT_orcOf_lt d.trees x.tables p
  | d :: ds, ss, z, (c, ρ), .inr q => trOfC_cols_lt C L ds ss.tail _ ρ q

/-- Every message that a speaker writes, at every ρ, substitutes included: the words of the field
elements among its plain part's items (f, e, answer), and of every symbol of its oracle part, read
or not, are below the prime. Of an item that is a word or a root nothing is asked. -/
theorem trOfC_words (C : CK) (L : Lay) : ∀ (ds : List RDT) (ss : List (Step W Y))
    (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)),
    viewWordsBelowPrime ⟨(rvT C ds (trOfC C L ds ss z ρ)).map fun r => ⟨r.vals, ⟨[], [], [], none⟩⟩, []⟩ =
      true ∧
    ∀ (q : Iop.OPos (uLT C ds)),
      ∀ a ∈ OnBytes.Maker.colOfSym C ds q ((trOfC C L ds ss z ρ).read q), a < fieldPrimeWord := by
  intro ds ss z ρ
  refine ⟨?_, trOfC_cols_lt C L ds ss z ρ⟩
  have h := trOfC_vals_lt C L ds ss z ρ
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, List.all_map, List.all_eq_true,
    Function.comp, Bool.true_and]
  intro r hr g hg
  have h1 := h r hr g hg
  cases g with
  | f x => exact decide_eq_true h1
  | e x => simpa [LtGot, and_assoc] using h1
  | answer x => simpa [LtGot, and_assoc] using h1
  | word x => rfl
  | root x => rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.sub_lt
#print axioms ProofFile.Honest.tellC_lt
#print axioms ProofFile.Honest.trOfC_vals_lt
#print axioms ProofFile.Honest.trOfC_cols_lt
#print axioms ProofFile.Honest.trOfC_words
