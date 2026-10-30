-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutN.lean: the lookup of a sub-proof, with one condition more on
what it puts out: the statement that it puts out has a known number of rows.

The lookup's out-statement holds a list of rows. By type that list has any length. A later block
that batches one form for each row needs a bound on the number of rows, as a condition on its input
statements. Here the joint behind the lookup's block (the relations and the condition on statements
between two blocks, IOR.Rels) says that number in its condition. All is stated at the library's
field Cb.Gl.E.

What the file states.
 - OutLen h L n: every statement that the lookup's verifier puts out has n rows.
 - forOutN h L R0 msg₀ n: the joint Cb.Fo.forOut with one clause more in its condition on
   statements: the list of rows has length n. The relations and the core are forOut's.
 - holeC_rowsOf: under FoNums.ok h = true and OutLen the lookup's block has the four clauses on the
   verifier (TWhole.KnowAt, Cb/G6/Cut.lean) from Cb.Fo.forIn to forOutN, with the same extractor and
   the same error counts as between forIn and forOut. Of the four only onOut reads the condition
   behind the block, so it alone says more than before.
 - outLen_rows, holeC_rows: OutLen holds at n := Fo.nRows h
   (OnBytes/Tie/Pv/Lookup/Forest/FoOutLen.lean: Fo.out_rows_len), a number made of the record of
   public numbers alone; so the block ends at forOutN at that number, under the test FoNums.ok and
   nothing else.

Limits. The condition says the number of rows and nothing else of them.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoArrowRun
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import OnBytes.Tie.Pv.Lookup.Forest.FoOutLen

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh) (L : Lay Cb.Gl.E St₀ J₀)
  {Ex : ExtSpec} {Kc M Wp : Type} (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) (n : ℕ)

/-- Every statement that the lookup's verifier puts out has n rows. -/
def OutLen (Ex : ExtSpec) : Prop :=
  ∀ (a : St₀ × Ex.Str) (τ : Tr (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape)
    (b : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) × Ex.Str),
    (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some b → b.1.2.2.length = n

/-- The lookup's joint behind the block, whose condition says the number of rows. -/
def forOutN : Rels Kc (TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) Ex (M × Wp) :=
  ⟨(forOut Cb.Gl.E h L R0 msg₀).rel, (forOut Cb.Gl.E h L R0 msg₀).relR,
    fun b => (forOut Cb.Gl.E h L R0 msg₀).on b ∧ b.1.2.2.length = n,
    (forOut Cb.Gl.E h L R0 msg₀).core⟩

/-- The lookup's block ends at the joint whose condition says the number of rows. -/
theorem holeC_rowsOf (H : FoNums.ok h = true) (hn : OutLen h L n Ex) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
      (forOutN h L R0 msg₀ n) (fun _ _ _ wp => wp) (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_into (holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H)
    (fun b hb hr => hr.elim fun a ha => ha.elim fun τ hτ => ⟨hb, hn a τ b hτ.2⟩)
    fun _ _ _ _ hw => hw

/-- The number of rows is the record's own: Fo.nRows h. -/
theorem outLen_rows : OutLen h L (Fo.nRows h) Ex := fun a τ b hb =>
  Fo.out_rows_len h L Ex a τ b hb

/-- **The lookup's block, with the number of rows in the condition behind it.** -/
theorem holeC_rows (H : FoNums.ok h = true) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
      (forOutN h L R0 msg₀ (Fo.nRows h)) (fun _ _ _ wp => wp)
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e :=
  holeC_rowsOf h L R0 msg₀ (Fo.nRows h) H (outLen_rows h L)

end

#print axioms Cb.Fo.holeC_rows
#print axioms Cb.Fo.holeC_rowsOf

end Cb.Fo
