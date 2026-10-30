-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryAcceptsTrue.lean: the statement at which OnBytes/Flat/EntryAccepts.lean writes a
transcript (two stored tables of zeros, each with the record `recW`) is a true one, by the last
clause of the language and by none of its ways out.

Why. The language of the link's soundness has ways out: where one is open, the theorem says nothing
of the statement. A yes of the verifier at such a statement would show acceptance where nothing is
promised.

Main theorems (`decW`: the decoder with a record at the small files, `srS.toDecR srZ 524285`).
 `not_coll_tabW`   the table of zeros has no collision, at any seed: it is a table of code words,
                   the radius of decoding is below the code's distance (`dist_small`,
                   `radius_small`: the numbers by Lean's kernel), so no other table of code words
                   lies within it.
 `dcd_tabW`        with the record it decodes to the messages 0 (`LdIx.dec_of_cand`,
                   Cb/Ld/LdFoldEqProofs.lean).
 `written_true`    of the language `Sz.LangE2T` (OnBytes/Slice/LinkSoundRec.lean), in which
                   `sr_family` (OnBytes/Slice/LinkFamily.lean) is stated: none of the three ways out
                   is open (the first table decodes; neither table has a collision at its record's
                   seed), and the last clause holds.
 `written_in_lang`   so the statement lies in that language.
 `written_in_langA`  in the language of `entrySmall_sound` (OnBytes/Flat/EntrySound.lean) the last
                   clause holds too, for every A and R: by rfl: one table, one record.

Not claimed. `entrySmall_sound`'s language speaks of the INDEX that a reading A makes of a decoded
table. Whether its first way out ("the first table gives no index with its record") is shut at the
tables of zeros hangs on A: on whether A counts the matrix of zeros as in range. A is a letter: it
is not decided here. Its second way out (a collision of the copy) is shut if `(DecR.configurationOfStoredTable A R).coll`
is `decW.coll`: not shown here. The two tables are equal and so are the two records: nothing is
shown on a copy made under fresh coins, or on tables that are not 0. All that the head of
OnBytes/Flat/EntryAccepts.lean does not claim.


-/
import OnBytes.Flat.EntryAccepts
import OnBytes.Flat.EntrySound
import OnBytes.Slice.LangTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Hiop _root_.Run _root_.Run.PQ Blocks OnBytes.Slice

/-- The decoder with a record at the small files. -/
abbrev decW : DecR := srS.toDecR srZ 524285

theorem dist_small : HasDist decW.ix.G (2 ^ srS.P.T.a - (srS.P.T.r + srS.P.T.l) + 1) :=
  hasDist_genOf srS.P.T (by decide +kernel) (by decide +kernel)

theorem radius_small : decW.ix.eM < 2 ^ srS.P.T.a - (srS.P.T.r + srS.P.T.l) + 1 := by
  decide +kernel

/-- The table of zeros is the table of the code words of the messages 0. -/
theorem tab_tabW : decW.tab (tabW srS.P.T.a).1 =
    fun r => decW.ix.G.mulVec ((fun _ => 0 : decW.ix.Row → decW.toDec.Co → GE) r) :=
  funext fun r => funext fun j => by
    show algebraMap GF GE (toF ((List.replicate 256 (0 : UInt64)).getD (Sz.rowNo r) 0)) =
      decW.ix.G.mulVec 0 j
    rw [getD_copies, toF_zero, map_zero, Matrix.mulVec_zero]
    rfl

/-- The answers of the vector 0 are 0, at every seed. -/
theorem val_zero {E J : Type} [Field E] [Fintype J] (Z : Sample E J) (ρ : Z.D) :
    Z.val ρ (fun _ => 0) = fun _ => 0 := by
  funext s
  unfold Sample.val
  simp

/-- **No collision**, at any seed: within the radius of a table of code words lies no other. -/
theorem not_coll_tabW (ρ : decW.Z.D) : ¬ decW.coll (tabW srS.P.T.a).1 ρ := by
  unfold DecR.coll
  rw [tab_tabW]
  rintro ⟨u, u', ⟨M, hM, rfl⟩, ⟨M', hM', rfl⟩, hne, -⟩
  have h0 := decodesTo_mulVec decW.ix.G 0 (fun _ => 0 : decW.ix.Row → decW.toDec.Co → GE)
  have e1 : M = fun _ => 0 := funext fun r =>
    DecodesTo.row_unique dist_small (by have := radius_small; omega) hM h0 (a := r) (a' := r) rfl
  have e2 : M' = fun _ => 0 := funext fun r =>
    DecodesTo.row_unique dist_small (by have := radius_small; omega) hM' h0 (a := r) (a' := r) rfl
  exact hne (by rw [e1, e2])

set_option maxRecDepth 100000 in
/-- The messages 0 have the record's answers at its seed. -/
theorem hasRec_recW : decW.ix.HasRec recW (fun _ => 0) :=
  (val_zero decW.ix.ZR recW.1).trans (funext fun _ => toE_zeroE.symm)

/-- **It decodes**, with its record, to the messages 0. -/
theorem dcd_tabW : decW.dcd (tabW srS.P.T.a).1 recW = some (decW.ix.view fun _ => 0) := by
  have hc : ¬ decW.ix.Coll (decW.tab (tabW srS.P.T.a).1) recW.1 := not_coll_tabW recW.1
  unfold DecR.dcd
  rw [tab_tabW] at hc ⊢
  exact decW.ix.dec_of_cand hc (decodesTo_mulVec _ _ _) hasRec_recW

/-- **The written statement is true by the last clause of the family's language, and none of its
three ways out is open.** -/
theorem written_true :
    decW.dcd (tabW srS.P.T.a).1 recW ≠ none ∧ ¬ decW.coll (tabW srS.P.T.a).1 recW.1 ∧
      ¬ decW.coll (tabW srS.P.T.a).2 recW.1 ∧
      ∃ u₀ u₁, decW.dcd (tabW srS.P.T.a).1 recW = some u₀ ∧
        decW.dcd (tabW srS.P.T.a).2 recW = some u₁ ∧ decW.Agree u₁ u₀ :=
  ⟨by rw [dcd_tabW]; exact Option.some_ne_none _, not_coll_tabW _, not_coll_tabW _,
    _, _, dcd_tabW, dcd_tabW, fun _ _ _ => rfl⟩

/-- So it lies in the language of the family's soundness (`sr_family`,
OnBytes/Slice/LinkFamily.lean), by that language's last clause. -/
theorem written_in_lang : srS.LangE2T srZ 524285 (recW, recW) (tabW srS.P.T.a) :=
  Or.inr (Or.inr (Or.inr written_true.2.2.2))

/-- In the language of `entrySmall_sound` (OnBytes/Flat/EntrySound.lean), for every reading A of a
decoded table as an index and every rest R, it lies by the last clause too: both tables, with their
records, get the same answer of the decoder, an index or none: they are the same table and the same
record. -/
theorem written_in_langA {X : Type} (A : decW.Claims X) (R : decW.RelationsAndEncoding A) :
    (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).2 recW = (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW := rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.dcd_tabW
#print axioms OnBytes.Flat.not_coll_tabW
#print axioms OnBytes.Flat.written_true
#print axioms OnBytes.Flat.written_in_lang
#print axioms OnBytes.Flat.written_in_langA
