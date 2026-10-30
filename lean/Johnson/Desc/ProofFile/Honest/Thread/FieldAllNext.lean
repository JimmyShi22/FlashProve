-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FieldAllNext.lean: THE FIELD `opened`, AT EVERY SET OF TABLES
BESIDE THE STATE, FROM A BORDER TO THE NEXT. `Thread.field_next` (Honest/Thread/ThrFieldNext.lean)
carries `Thread.Field` at the tables of `Thr`. A letter of `Said`'s type has no tables in its type,
so a clause on the field inside such a letter speaks of every set of tables at which `Thread.Hand`
holds. This file carries that clause.

  `field_all_next`   the clause at border b + 1, from the clause at border b, `Thr`, `Thread.Moved`
    and the sub-protocol's new trees

What this is. A conditional lemma on our own definitions. It is none of the library's goals. It says
nothing of which letter serves: no letter is laid here.

Limits.
  * The clause `∀ E', T.Hand b k m E' → T.Field base b m E'` is true and empty where no `E'` has
    `Thread.Hand`. It says something only at a state where `Thread.Hand` holds at some `E'`.
  * `ho` and `hdp` are premises: `Thread.opensAvailable` and `DepthsAt` at the next border
    (Honest/Thread/OneState.lean). They are shown here of no thread.
  * `base` is a parameter. Nothing here says what a run's own value is.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import Johnson.Desc.ProofFile.Honest.Thread.ThrFieldNext
import Johnson.Desc.ProofFile.Honest.Thread.HandNext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **The clause on the field, from a border to the next, at every set of tables.** `hL`: the clause
at this border. -/
theorem field_all_next {n b : Nat} {blk : Block S Cl} {base : List OpenedColumn}
    (hfit : T.fits n = true) (hb : b ≤ n) (hblk : T.bs[b]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hM : T.Moved blk k m E ds y cols)
    (hT : T.Trees (T.fresh b) k y.2 (E.add y.1))
    (hL : ∀ E', T.Hand b k m E' → T.Field base b m E')
    (ho : T.opensAvailable (b + 1) = true)
    (hdp : DepthsAt T (b + 1) k (y.2.took cols)) :
    ∀ E', T.Hand (b + 1) k (y.2.took cols) E' → T.Field base (b + 1) (y.2.took cols) E' := by
  intro E' hE'
  have hF : T.Field base b m E := hL E hA.1
  have hN := T.field_next hblk hA hF hM
  have hH := T.hand_next hfit hb hA hM hT
  have e := T.colsTo_congr_at hH hE' ho hdp
  obtain ⟨c, hc, hm⟩ := (field_iff T base (b + 1) _ _).1 hN
  exact (field_iff T base (b + 1) _ _).2 ⟨c, e.symm.trans hc, hm⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.field_all_next
