-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepKeyLaw.lean: the job with a kept state at a level of a
lookup's key tree (`keyKeep`, Honest/K3/JobsKeepKey.lean) meets the hypothesis `KeepJob.FaithfulOn`
(Honest/SumKeepLaw.lean) at the condition `KeyOk`; so its part, played alone, shows the rounds of
`sumPart` at the earlier job. Conditional on `KeyOk`; where no store is passed on, `KeyOk` holds.
Theorems alone.

Terms. Honest/K3/GLOSSARY.md. In this file: a store is a value of `Store`
(Honest/K3/KeptTypes.lean); the earlier job is `(keyKeep R row a i k).base`, which is `jobOfAt` at
`fastJobs`, typed at `Option Store`.

What is shown.
  `keyOk_none`: where no store is passed on, `KeyOk` holds.
  `keyKeep_faithful`: `(keyKeep R row a i k).FaithfulOn (KeyOk R row a i k)`. Its three fields are
    the three equations of Honest/K3/JobsKeepKey.lean, which hold at every list of challenges; the
    hypotheses on the number of challenges are not used.
  `keyKeep_alone`: by `Keep.alone_keep_on`: the part `keepPart` at `keyKeep`, played alone from a
    state without a kept state at which `KeyOk` holds, shows what `sumPart` at the earlier job
    shows.
  `keyKeep_alone_none`: the same from a state without a store, under no hypothesis.

Hypotheses that remain.
  `hOk`, in `keyKeep_alone`: `KeyOk R row a i k w h x`. No store at which it holds is exhibited
    here.

Imported: Honest/SumKeepLaw.lean and what it imports.

Users. Honest/K3/Law/Keep/SameRounds.lean. It is the form for the other sorts of stage.

Limits. The earlier job is typed at `Option Store`; the row `lookRow` (Honest/K3/Row.lean) plays
`jobOf`, typed at `Unit`. `jobOfAt_unit` speaks at `Unit` alone: that `sumPart` at the two jobs
shows the same rounds is shown in Honest/K3/Law/Keep/Bridge.lean (`alone_jobOfAt`). Nothing is said
here on who makes a store, nor that `KeyOk` stays true as more is heard: see
Honest/K3/StoreMake.lean and Honest/K3/Law/Keep/.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)
open ProofFile.Honest.SumLaw (alone SumCoins)

/-- Where no store is passed on, `KeyOk` holds. -/
theorem keyOk_none (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) (w : Ask)
    (h : List Fmt.Drawn) : KeyOk R row a i k w h none :=
  fun _ e => nomatch e

/-- **The job at a level of the key tree meets `KeepJob.FaithfulOn` at `KeyOk`.** -/
theorem keyKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) :
    (keyKeep R row a i k).FaithfulOn (KeyOk R row a i k) :=
  ⟨fun w f rs h _ => keyKeep_round R row a i k w f rs h,
    fun w f rs m h _ => keyKeep_inY R row a i k w f rs m h,
    fun w f rs h _ => keyKeep_ends R row a i k w f rs h⟩

/-- **Conditional on `KeyOk` at the state in front of the part: its part, played alone, shows the
rounds of `sumPart` at the earlier job.** -/
theorem keyKeep_alone {V : Type} (name endName : String) (R : Reads) (row : E → Nat → E) (a : At)
    (i k : Nat) (c : SumCoins name endName (keyKeep R row a i k).base) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (hOk : KeyOk R row a i k w h x) (seen : Seen)
    (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) name endName (keyKeep R row a i k)) c ⟨w, h, (x, none)⟩ seen ds =
      alone (sumPart (V := V) name endName (keyKeep R row a i k).base) c ⟨w, h, x⟩ seen ds :=
  Keep.alone_keep_on name endName (keyKeep R row a i k) (KeyOk R row a i k)
    (keyKeep_faithful R row a i k) c w h x hOk seen ds

/-- The same from a state without a store. -/
theorem keyKeep_alone_none {V : Type} (name endName : String) (R : Reads) (row : E → Nat → E)
    (a : At) (i k : Nat) (c : SumCoins name endName (keyKeep R row a i k).base) (w : Ask)
    (h : List Fmt.Drawn) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) name endName (keyKeep R row a i k)) c ⟨w, h, (none, none)⟩ seen ds =
      alone (sumPart (V := V) name endName (keyKeep R row a i k).base) c ⟨w, h, none⟩ seen ds :=
  keyKeep_alone name endName R row a i k c w h none (keyOk_none R row a i k w h) seen ds

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.keyOk_none
#print axioms ProofFile.Honest.K3.keyKeep_faithful
#print axioms ProofFile.Honest.K3.keyKeep_alone
#print axioms ProofFile.Honest.K3.keyKeep_alone_none
