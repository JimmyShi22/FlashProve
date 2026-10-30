-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ViewWords.lean: TWO OF THE THREE PARTS OF THE TEST "EVERY WORD OF THE VIEW IS
BELOW THE PRIME" (viewWordsBelowPrime, Johnson/Desc/Block.lean) THAT HANG ON NO STRATEGY: every element that a
round samples, at every verifier's randomness; every word of a column of a committed table whose
rows are the format's code words. And the test, of its three parts, as lists. No function that makes
a view is named.

Main names (namespace Johnson.Prover.Link).
  ltE   the three words of an element are below the prime: viewWordsBelowPrime's own form.
  lt_toU, ltE_toU3, ltE_collect, ltE_dr   a typed sample's value is a number below the prime,
    written as a word.
  ltE_drawnSL   AT EVERY ρ: every element that any round of the protocol samples.
  lt_symF, lt_honestTab   a symbol over the base field is a sum's value or 0; a committed table's
    column.
  okViewW_of   the test returns true if the sampled elements, the sent items and the opened columns
    pass.

By: ok_toU (OnBytes/Slice/Draws.lean) · Fmt.Fld.ok_add (Fmt/FieldE.lean). Kin, not called: ok_symF
(Johnson/Pack/TabMeets.lean [not in this library]) says of a symbol what lt_symF says, in the
format's own test.

Limits. The SENT items and the prover's OWN opened columns are premises of okViewW_of: they are paid
piece by piece elsewhere. Nothing here says that any verifier accepts.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import OnBytes.TypedOracleCompiler.Run.PlanQS
import OnBytes.Slice.Honest
import Run.PlanPull
import Fmt.FieldEFast

set_option autoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc (fieldPrimeWord viewWordsBelowPrime)
open _root_.Run (ckP toU toU3 out outAll drawnOf FV EV Vals)

/-- the three words of an element are below the prime: in viewWordsBelowPrime's own form -/
def ltE (x : Fmt.Ext) : Bool :=
  decide (x.1 < fieldPrimeWord) && decide (x.2.1 < fieldPrimeWord) && decide (x.2.2 < fieldPrimeWord)

theorem lt_of_ok {w : UInt64} (h : Fmt.Fld.two.ok w = true) : w < fieldPrimeWord := by
  have h' : w.toNat < Fmt.Fld.two.p := of_decide_eq_true h
  exact UInt64.lt_iff_toNat_lt.2 h'

theorem lt_toU (x : FV .two) : toU x < fieldPrimeWord := lt_of_ok (OnBytes.Slice.ok_toU x)

theorem ltE_toU3 (e : EV .two) : ltE (toU3 e) = true := by
  unfold ltE toU3
  simp only [lt_toU, decide_true, Bool.and_self]

/-- **Every element among typed samples' values, as a view shows them.** -/
theorem ltE_collect : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    ∀ x ∈ (Fmt.collect (outAll .two ds v)).elems, ltE x = true
  | [], _, _, h => nomatch h
  | .elem :: ds, v, x, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ltE_toU3 _
    · exact ltE_collect ds v.2 x h'
  | .elemNZ :: ds, v, x, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ltE_toU3 _
    · exact ltE_collect ds v.2 x h'
  | .pos _ :: ds, v, x, h => ltE_collect ds v.2 x h
  | .trits _ :: ds, v, x, h => ltE_collect ds v.2 x h
  | .sealed :: ds, v, x, h => ltE_collect ds v.2 x h

/-- one round's samples under the kit of the programs' field -/
theorem ltE_dr (e : Fmt.Entry) (k : Fmt.Kind) (u : (ckP .two).Ch e k) :
    ∀ x ∈ ((ckP .two).dr e k u).elems, ltE x = true :=
  ltE_collect _ _

/-- **AT EVERY ρ: every element that any round samples has its three words below the prime.** -/
theorem ltE_drawnSL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD)
    (ρ : Iop.Rho (TypedOracleCompiler.Run.PQ.uL (ckP .two) ds)),
    ∀ D ∈ TypedOracleCompiler.Run.PQ.drawnSL (ckP .two) ds ρ, ∀ x ∈ D.elems, ltE x = true
  | [], _, _, h, _, _ => nomatch h
  | d :: ds, (c, ρ), D, h, x, hx => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ltE_dr d.entry d.kind _ x hx
    · exact ltE_drawnSL ds ρ D h' x hx

/-- a symbol over the base field is below the prime -/
theorem lt_symF (C : Fmt.M1.Code) (x : ℕ) (m rho : List UInt64) :
    Fmt.M1.symF C x m rho < fieldPrimeWord := by
  unfold Fmt.M1.symF Fmt.M1.hornerF
  cases Fmt.M1.fitL 0 C.r rho ++ Fmt.M1.fitL 0 C.l m with
  | nil =>
    show (0 : UInt64) < fieldPrimeWord
    decide
  | cons c cs => exact lt_of_ok (Fmt.Fld.ok_add _ _ _)

/-- **Every word of a column of an honest committed table is below the prime.** -/
theorem lt_honestTab (S : OnBytes.Slice.Sz) (msg tl : ℕ → List UInt64) (x : S.Pos) :
    ((OnBytes.Slice.honestTab S msg tl x).2.all (· < fieldPrimeWord)) = true := by
  refine List.all_eq_true.2 fun w hw => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
  exact decide_eq_true (lt_symF _ _ _ _)

/-- **viewWordsBelowPrime, of its three parts**, as lists. -/
theorem okViewW_of (v : Fmt.View)
    (hd : ∀ r ∈ v.rounds, ∀ x ∈ r.drawn.elems, ltE x = true)
    (hs : ∀ r ∈ v.rounds, ∀ g ∈ r.vals, (match g with
      | .f x => decide (x < fieldPrimeWord)
      | .e x => ltE x
      | .answer x => ltE x
      | .word _ => true
      | .root _ => true) = true)
    (ho : ∀ o ∈ v.opened, (o.2.2.all (· < fieldPrimeWord)) = true) : viewWordsBelowPrime v = true := by
  unfold viewWordsBelowPrime
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun r hr => ?_, List.all_eq_true.2 ho⟩
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun x hx => hd r hr x hx, List.all_eq_true.2 fun g hg => ?_⟩
  have := hs r hr g hg
  cases g <;> exact this

end Johnson.Prover.Link
