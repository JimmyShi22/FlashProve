-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/MeetsStratLaw.lean: the two strategies of Honest/Strat.lean,
zipped, satisfy `StratLaw` (Johnson/Prover/Print/StratLaw.lean), which is a condition on a
strategy's own run at every verifier's message. Whatever the description, the book, the prover,
the private input, the coins and the instance: the joining round's run value and the seam's plain
part are fixed; and the words of the field elements in every written round's plain part, and of
every symbol of every oracle, read or not, are below the prime; of an item that is a word or a root
`StratLaw` asks nothing. There is no hypothesis. The main lemma is `meets_stratLaw`.

  `okF_of_lt`        a word below the prime, in the two files' terms
  `canonI_of_gots`   a plain part whose items meet `LtGot` (Honest/Law/StratCanon.lean) is `CanonI`
  `wordsP_of_rv`     a chain's plain parts likewise: `WordsP`
  `meets_stratLaw`   the main lemma

It uses `trOf_vals_lt`, `trOf_cols_lt` (Honest/Law/StratCanon.lean) and `zip_parts`
(Honest/Law/StratForm.lean).

Limits.
  * Nothing is said on acceptance.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Prover.Print.StratLaw
import Johnson.Desc.ProofFile.Honest.Law.StratCanon
import Johnson.Desc.ProofFile.Honest.Law.StratForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription fieldPrimeWord)
open OnBytes.Maker (RDT WholeD uLT rvT chainsOf FrontMsg)
open OnBytes.Maker.Carrier (okF okE)
open OnBytes.Prover.Print (CanonI WordsP)
open Johnson.Prover.Print (StratLaw)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK PlainOf)

variable {Xi W₀ Rc Ky Tr X₀ X Sd : Type}

theorem okF_of_lt {a : UInt64} (h : a < fieldPrimeWord) : okF a := by
  have hp : fieldPrimeWord.toNat = Fmt.Fld.two.p := by decide
  unfold okF
  rw [← hp]
  exact UInt64.lt_iff_toNat_lt.1 h

theorem canonI_of_gots : ∀ (l : List Fmt.Item) (x : PlainOf l),
    (∀ a ∈ PlainOf.gots l x, LtGot a) → CanonI l x
  | [], _, _ => trivial
  | .root :: l, x, h => canonI_of_gots l x h
  | .f :: l, (x : UInt64 × PlainOf l), h =>
    ⟨okF_of_lt (h (.f x.1) List.mem_cons_self),
      canonI_of_gots l x.2 fun a ha => h a (List.mem_cons_of_mem _ ha)⟩
  | .word :: l, (x : UInt64 × PlainOf l), h =>
    canonI_of_gots l x.2 fun a ha => h a (List.mem_cons_of_mem _ ha)
  | .e :: l, (x : Fmt.Ext × PlainOf l), h =>
    ⟨⟨okF_of_lt (h (.e x.1) List.mem_cons_self).1, okF_of_lt (h (.e x.1) List.mem_cons_self).2.1,
      okF_of_lt (h (.e x.1) List.mem_cons_self).2.2⟩,
      canonI_of_gots l x.2 fun a ha => h a (List.mem_cons_of_mem _ ha)⟩
  | .answer :: l, (x : Fmt.Ext × PlainOf l), h =>
    ⟨⟨okF_of_lt (h (.answer x.1) List.mem_cons_self).1,
      okF_of_lt (h (.answer x.1) List.mem_cons_self).2.1,
      okF_of_lt (h (.answer x.1) List.mem_cons_self).2.2⟩,
      canonI_of_gots l x.2 fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem wordsP_of_rv (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)),
    (∀ r ∈ rvT C ds τ, ∀ a ∈ r.vals, LtGot a) → WordsP C ds τ.plains
  | [], _, _ => trivial
  | d :: ds, (_, _, τ), h =>
    ⟨canonI_of_gots d.items _ (h _ List.mem_cons_self),
      wordsP_of_rv C ds τ fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky (FrontMsg (List OnBytes.E)) (JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- **The two strategies, zipped, satisfy `StratLaw`**: at every description, book, prover, private
input, coins and instance. -/
theorem meets_stratLaw :
    StratLaw C D tF tJ t3
      (Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀) (requestStrategy C D tF tJ t3 F B H J w c₀ x c))
      (J₀.join w.1 w.2.1 w.2.2).run (J.seam w.1 w.2.1 w.2.2 x) := by
  have key := zip_parts C D tF tJ t3 F B H J₀ J w c₀ x c
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ q => ?_,
    fun ρ q => ?_, fun ρ q => ?_⟩
  · rw [(key ρ).2.2.1]
  · rw [(key ρ).2.2.2.2.1]
  · obtain ⟨ss, m, e⟩ := (key ρ).2.1
    rw [e]
    exact wordsP_of_rv C _ _ (trOf_vals_lt C _ ss m _)
  · obtain ⟨ss, m, e⟩ := (key ρ).2.2.2.1
    rw [e]
    exact wordsP_of_rv C _ _ (trOf_vals_lt C _ ss m _)
  · obtain ⟨ss, m, e⟩ := (key ρ).2.2.2.2.2
    rw [e]
    exact wordsP_of_rv C _ _ (trOf_vals_lt C _ ss m _)
  · obtain ⟨ss, m, e⟩ := (key ρ).2.1
    rw [e]
    exact fun a ha => okF_of_lt (trOf_cols_lt C _ ss m _ q a ha)
  · obtain ⟨ss, m, e⟩ := (key ρ).2.2.2.1
    rw [e]
    exact fun a ha => okF_of_lt (trOf_cols_lt C _ ss m _ q a ha)
  · obtain ⟨ss, m, e⟩ := (key ρ).2.2.2.2.2
    rw [e]
    exact fun a ha => okF_of_lt (trOf_cols_lt C _ ss m _ q a ha)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.okF_of_lt
#print axioms ProofFile.Honest.canonI_of_gots
#print axioms ProofFile.Honest.wordsP_of_rv
#print axioms ProofFile.Honest.meets_stratLaw
