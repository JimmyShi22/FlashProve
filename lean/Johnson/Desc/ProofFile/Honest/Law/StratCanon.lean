-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratCanon.lean: the words of the field elements in every message
that a speaker of Honest/Strat.lean writes are below the prime. This holds at every verifier's
message and at every state of the run, after an error or not, and for the fixed substitutes too. It
covers the words of the elements of the message's plain part, and of every symbol of its oracle
part, read or not. Of an item that is a word or a root nothing is asked (`LtGot`), as in the
library's `viewWordsBelowPrime`. There is no hypothesis: it holds by the types in which a prover's side gives
its items and tables (Honest/Frame.lean: `Said`, `Table`), and, for the substitutes, because they
are zeros. It is stated in the library's own readers: `rvT`, `colOfSym` (OnBytes/Maker/Trees.lean,
TreesLaws.lean), `viewWordsBelowPrime` (Johnson/Desc/Block.lean). The main lemma is `trOf_words`.

  1  `LtGot`, `zero_lt`, `ltGot_said`, `told_lt`, `tellAt_lt`, `gots_dflt_lt`, `gots_plainOf_lt`   a
     plain part
  2  `colT_zeroT_lt`, `colT_orcOf_lt`   an oracle part
  3  `trOf_vals_lt`, `trOf_cols_lt`, `trOf_words`   a chain's transcript

Limits.
  * Nothing is said on acceptance.
  * The lemmas prove no property of a prover or a protocol.
-/
import OnBytes.Maker.TreesLaws
import Johnson.Desc.ProofFile.Honest.Law.Play
import Johnson.Desc.ProofFile.Honest.Law.StratChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (fieldPrimeWord viewWordsBelowPrime)
open OnBytes.Maker (RDT uLT roundT rvT PosT colT zeroT colOfSym)
open _root_.Run.PQ (CK PlainOf)

variable {W Y : Type}

/-! ## 1 A plain part -/

/-- The words of an item's field elements (f, e, answer) are below the prime. True at a word and at
a root. -/
def LtGot : Fmt.ItemValue → Prop
  | .f x => x < fieldPrimeWord
  | .e x => x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord
  | .answer x => x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord
  | .word _ => True
  | .root _ => True

theorem zero_lt : (0 : UInt64) < fieldPrimeWord := by decide

theorem ltGot_said : ∀ v : Said, LtGot v.got
  | .f x => ofF_lt x
  | .e x => ofE_lt x
  | .word _ => trivial
  | .answer x => ofE_lt x

theorem told_lt {s : Step W Y} {m : Mid W Y} {x : Told} (h : s.tell none m = .ok x) :
    ∀ a ∈ x.vals, LtGot a := by
  obtain ⟨-, h2, h3⟩ := tell_yields h
  intro a ha
  cases hm : s.move.isSome with
  | true =>
    obtain ⟨u, -, hv, -⟩ := h2 hm
    rw [hv] at ha
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact ltGot_said v
  | false =>
    obtain ⟨hv, -⟩ := h3 hm
    rw [hv] at ha
    simp at ha

theorem tellAt_lt {s : Option (Step W Y)} {m : Option (Mid W Y)} {x : Told}
    (h : tellAt s m = some x) : ∀ a ∈ x.vals, LtGot a := by
  cases s with
  | none => cases h
  | some s =>
    cases m with
    | none => cases h
    | some m =>
      have h' : (s.tell none m).toOption = some x := h
      cases ht : s.tell none m with
      | error e =>
        rw [ht] at h'
        cases h'
      | ok z =>
        rw [ht] at h'
        cases h'
        exact told_lt ht

theorem gots_dflt_lt : ∀ l : List Fmt.Item, ∀ a ∈ PlainOf.gots l (PlainOf.dflt l), LtGot a
  | [], _, h => by cases h
  | .root :: l, a, h => gots_dflt_lt l a h
  | .f :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact zero_lt
    · exact gots_dflt_lt l a h
  | .word :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact gots_dflt_lt l a h
  | .e :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨zero_lt, zero_lt, zero_lt⟩
    · exact gots_dflt_lt l a h
  | .answer :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨zero_lt, zero_lt, zero_lt⟩
    · exact gots_dflt_lt l a h

theorem gots_plainOf_lt : ∀ (l : List Fmt.Item) (g : List Fmt.ItemValue), (∀ a ∈ g, LtGot a) →
    ∀ a ∈ PlainOf.gots l (plainOf l g), LtGot a
  | [], _, _, _, h => by cases h
  | .root :: l, g, hg, a, h => gots_plainOf_lt l g hg a h
  | .f :: l, [], _, a, h => gots_dflt_lt (.f :: l) a h
  | .f :: l, .f x :: g, hg, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hg (.f x) List.mem_cons_self
    · exact gots_plainOf_lt l g (fun b hb => hg b (List.mem_cons_of_mem _ hb)) a h
  | .f :: l, .e _ :: _, _, a, h => gots_dflt_lt (.f :: l) a h
  | .f :: l, .word _ :: _, _, a, h => gots_dflt_lt (.f :: l) a h
  | .f :: l, .root _ :: _, _, a, h => gots_dflt_lt (.f :: l) a h
  | .f :: l, .answer _ :: _, _, a, h => gots_dflt_lt (.f :: l) a h
  | .word :: l, [], _, a, h => gots_dflt_lt (.word :: l) a h
  | .word :: l, .word x :: g, hg, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact gots_plainOf_lt l g (fun b hb => hg b (List.mem_cons_of_mem _ hb)) a h
  | .word :: l, .f _ :: _, _, a, h => gots_dflt_lt (.word :: l) a h
  | .word :: l, .e _ :: _, _, a, h => gots_dflt_lt (.word :: l) a h
  | .word :: l, .root _ :: _, _, a, h => gots_dflt_lt (.word :: l) a h
  | .word :: l, .answer _ :: _, _, a, h => gots_dflt_lt (.word :: l) a h
  | .e :: l, [], _, a, h => gots_dflt_lt (.e :: l) a h
  | .e :: l, .e x :: g, hg, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hg (.e x) List.mem_cons_self
    · exact gots_plainOf_lt l g (fun b hb => hg b (List.mem_cons_of_mem _ hb)) a h
  | .e :: l, .f _ :: _, _, a, h => gots_dflt_lt (.e :: l) a h
  | .e :: l, .word _ :: _, _, a, h => gots_dflt_lt (.e :: l) a h
  | .e :: l, .root _ :: _, _, a, h => gots_dflt_lt (.e :: l) a h
  | .e :: l, .answer _ :: _, _, a, h => gots_dflt_lt (.e :: l) a h
  | .answer :: l, [], _, a, h => gots_dflt_lt (.answer :: l) a h
  | .answer :: l, .answer x :: g, hg, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hg (.answer x) List.mem_cons_self
    · exact gots_plainOf_lt l g (fun b hb => hg b (List.mem_cons_of_mem _ hb)) a h
  | .answer :: l, .f _ :: _, _, a, h => gots_dflt_lt (.answer :: l) a h
  | .answer :: l, .e _ :: _, _, a, h => gots_dflt_lt (.answer :: l) a h
  | .answer :: l, .word _ :: _, _, a, h => gots_dflt_lt (.answer :: l) a h
  | .answer :: l, .root _ :: _, _, a, h => gots_dflt_lt (.answer :: l) a h

/-! ## 2 An oracle part -/

theorem colT_zeroT_lt : ∀ (ts : List Fmt.Shape) (p : PosT ts),
    ∀ a ∈ colT ts p (zeroT ts p), a < fieldPrimeWord
  | [], p => p.elim
  | s :: _, .inl _ => by
    intro a ha
    have ha' : a ∈ List.ofFn fun _ : Fin s.W => (0 : UInt64) := ha
    obtain ⟨_, rfl⟩ := List.mem_ofFn.1 ha'
    exact zero_lt
  | _ :: ts, .inr p => colT_zeroT_lt ts p

theorem colT_orcOf_lt : ∀ (ts : List Fmt.Shape) (l : List (Option Table)) (p : PosT ts),
    ∀ a ∈ colT ts p (orcOf ts l p), a < fieldPrimeWord
  | [], _, p => p.elim
  | s :: _, l, .inl x => by
    intro a ha
    have ha' : a ∈ List.ofFn fun i : Fin s.W =>
        (((l.head?.join.map fun t => t.col x.val).getD [])[i.val]?).getD 0 := ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha'
    cases hc : ((l.head?.join.map fun t => t.col x.val).getD [])[i.val]? with
    | none => exact zero_lt
    | some b =>
      have hb := List.mem_of_getElem? hc
      cases ht : l.head?.join with
      | none =>
        rw [ht] at hb
        cases hb
      | some t =>
        rw [ht] at hb
        exact col_lt t x.val b hb
  | _ :: ts, l, .inr p => colT_orcOf_lt ts l.tail p

/-! ## 3 A chain's transcript -/

theorem trOf_vals_lt (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)), ∀ r ∈ rvT C ds (trOf C ds ss m ρ), ∀ a ∈ r.vals, LtGot a
  | [], _, _, _, _, h => by cases h
  | d :: ds, ss, m, (c, ρ), r, h => by
    have h' : r ∈ (⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (msgOf C d (tellAt ss.head? m)).2), drOf C d c⟩ : Fmt.RoundView) ::
          rvT C ds (trOf C ds ss.tail
            (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) ρ) := h
    rcases List.mem_cons.1 h' with rfl | h'
    · show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (msgOf C d (tellAt ss.head? m)).2), LtGot a
      cases ht : tellAt ss.head? m with
      | none =>
        show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
          (Iop.GPlain.mk d.entry.work (PlainOf.dflt d.items) (default : ℕ))), LtGot a
        rw [Iop.GPlain.old_mk]
        exact gots_dflt_lt _
      | some x =>
        show ∀ a ∈ PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
          (Iop.GPlain.mk d.entry.work (plainOf d.items x.vals) (0 : ℕ))), LtGot a
        rw [Iop.GPlain.old_mk]
        exact gots_plainOf_lt _ _ (tellAt_lt ht)
    · exact trOf_vals_lt C ds ss.tail _ ρ r h'

theorem trOf_cols_lt (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)) (q : Iop.OPos (uLT C ds)),
    ∀ a ∈ colOfSym C ds q ((trOf C ds ss m ρ).read q), a < fieldPrimeWord
  | [], _, _, _, q => nomatch q
  | d :: ds, ss, m, (c, ρ), .inl p => by
    show ∀ a ∈ colT d.trees p ((msgOf C d (tellAt ss.head? m)).1 p), a < fieldPrimeWord
    cases tellAt ss.head? m with
    | none => exact colT_zeroT_lt d.trees p
    | some x => exact colT_orcOf_lt d.trees x.tables p
  | d :: ds, ss, m, (c, ρ), .inr q => trOf_cols_lt C ds ss.tail _ ρ q

/-- Every message that a speaker writes, at every ρ, substitutes included: the words of the field
elements among its plain part's items (f, e, answer), and of every symbol of its oracle part, read
or not, are below the prime. Of an item that is a word or a root nothing is asked. -/
theorem trOf_words (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)),
    viewWordsBelowPrime ⟨(rvT C ds (trOf C ds ss m ρ)).map fun r => ⟨r.vals, ⟨[], [], [], none⟩⟩, []⟩ = true ∧
    ∀ (q : Iop.OPos (uLT C ds)), ∀ a ∈ OnBytes.Maker.colOfSym C ds q ((trOf C ds ss m ρ).read q),
      a < fieldPrimeWord := by
  intro ds ss m ρ
  refine ⟨?_, trOf_cols_lt C ds ss m ρ⟩
  have h := trOf_vals_lt C ds ss m ρ
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

#print axioms ProofFile.Honest.zero_lt
#print axioms ProofFile.Honest.ltGot_said
#print axioms ProofFile.Honest.told_lt
#print axioms ProofFile.Honest.tellAt_lt
#print axioms ProofFile.Honest.gots_dflt_lt
#print axioms ProofFile.Honest.gots_plainOf_lt
#print axioms ProofFile.Honest.colT_zeroT_lt
#print axioms ProofFile.Honest.colT_orcOf_lt
#print axioms ProofFile.Honest.trOf_vals_lt
#print axioms ProofFile.Honest.trOf_cols_lt
#print axioms ProofFile.Honest.trOf_words
