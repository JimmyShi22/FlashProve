-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawKey.lean: both laws for the first chain of a key file: the block `Key.oneTime`
(OnBytes/Key/OneTime.lean), with the routines under it: the lookup (OnBytes/Iop/Lkp.lean) and the
block WF (OnBytes/Iop/Wf.lean). They are walked by the command walk_modules
(OnBytes/TypedOracleCompiler/Laws/LawAuto.lean), which prints what it has proved and how. The two laws, law 1 ("the
descriptions are constants") and law 2 ("blind"), are said in OnBytes/TypedOracleCompiler/Laws/LawAlike.lean.

Main names.
  `carries_getCtx`, `same_of_getCtx`   `Wf.startCheck` takes the whole context (getThe Ctx) and
                  reads the plan's number of answers to a sample off it: a field that is equal
                  in contexts that are alike (`Alike.samples`, OnBytes/TypedOracleCompiler/Laws/LawAlike.lean)
  `carries_oneTime` the block: from contexts that are alike it fails alike, or returns values that
                  are equal but for given sources and leaves contexts that are alike. For every G
                  and d. Its one argument is public, so this one theorem is law 2 (d = false) and
                  law 1 (d = true) at a key's first chain.
  `oneTime_runOn_blind`   law 2 at the whole run on a view: two views that are equal but for digests
                  (`ViewAlike`, OnBytes/TypedOracleCompiler/Laws/LawRun.lean) give one failure, or values that are
                  equal but for given sources (`ExAlike (FirstEndAlike G)`)
  `oneTime_dry_own`       what the dry run returns holds no given source: its book is alike to
                  itself under every G (what `second_rounds_alike`, OnBytes/TypedOracleCompiler/Laws/LawDry.lean,
                  asks of a first chain's end). The dry run itself has no argument that could
                  differ: it is one term.

Not claimed. Nothing on the reading in OnBytes/Key/File.lean, nor on OnBytes/Key/Ranges.lean,
Table.lean, Fixed.lean (no block is written there).

-/
import OnBytes.TypedOracleCompiler.Laws.LawAuto
import OnBytes.TypedOracleCompiler.Laws.LawDry
import OnBytes.Key.OneTime
import OnBytes.Iop.Wf
import OnBytes.Iop.Lkp
import OnBytes.Iop.MatchAux

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Proof

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

theorem carries_getCtx : Carries (Alike G d) (Alike G d) (getThe Ctx) (getThe Ctx) :=
  fun _ _ h => Out.ok h h

/-- A text that takes the whole context and goes on alike from contexts that are alike. -/
theorem same_of_getCtx {β : Type} {f : Ctx → Blk β}
    (hf : ∀ c c', Alike G d c c' → Carries (Alike G d) Eq (f c) (f c')) :
    Same (Alike G d) (getThe Ctx >>= f) :=
  ⟨Carries.bind carries_getCtx hf⟩

macro_rules
  | `(tactic| walk_more) =>
    `(tactic| (
      (with_reducible refine same_of_getCtx (fun _ _ hc => ?_))
      simp only [hc.samples]
      refine Carries.of_same ?_))

walk_modules OnBytes.Iop.Lkp OnBytes.Iop.Wf

theorem carries_oneTime (p : Params.OneTime) :
    Carries (Alike G d) (FirstEndAlike G) (Key.oneTime p) (Key.oneTime p) := by
  unfold Key.oneTime
  refine Carries.bind_same fun ids => ?_
  refine Carries.bind_same fun masks => ?_
  refine Carries.bind_same fun left => ?_
  refine Carries.bind_same fun first => ?_
  exact carries_firstEnd first

theorem startOf_alike (p : Params.OneTime) : StartAlike G (Key.startOf p) (Key.startOf p) :=
  ⟨rfl, rfl, rfl, rfl, ⟨ArrAlike.empty _, rfl⟩⟩

theorem oneTime_runOn_blind (p : Params.OneTime) {v v' : Fmt.View} (hv : ViewAlike v v') :
    ExAlike (FirstEndAlike G) ((Key.oneTime p).runOn (Key.startOf p) v)
      ((Key.oneTime p).runOn (Key.startOf p) v') :=
  (carries_oneTime p).runOn (startOf_alike p) hv

theorem oneTime_dry_own (p : Params.OneTime) {r : List (Fmt.Round × List Fmt.Stored)}
    {e : FirstEnd} (h : (Key.oneTime p).dryRun (Key.startOf p) = some (r, e)) :
    BookAlike G e.book e.book := by
  have k := (carries_oneTime (G := NoGiven) (d := true) p).dryRun (startOf_alike p)
  rw [h] at k
  cases k with
  | some q => exact q.2.book.of_noGiven

#print axioms carries_oneTime
#print axioms oneTime_runOn_blind
#print axioms oneTime_dry_own

end OnBytes.TwoLaws
