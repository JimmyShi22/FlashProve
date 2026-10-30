-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepTie.lean: the stages of a lookup's row that are masked
sumchecks without a variable (the tie's steps and the parts' steps) as jobs with a kept state
(`KeepJob`, Honest/SumKeep.lean), beside the jobs of Honest/K3/JobsFast.lean; the equations between
the two; and `KeepJob.FaithfulOn` (Honest/SumKeepLaw.lean) of each. Conditional on `Tie0Ok`,
`TieOk`, `SplitOk`: where a store is passed on, the levels 0 that the stage reads are those that
Honest/K3/JobsFast.lean makes; at a parts' step also on i below the number of parts. Definitions
with code, three definitions of hypotheses, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a part's root is the one entry of level 0 of its key
tree; the table side's level number 0 holds the planes' roots. A store is a value of `Store`, a kept
state a value of `Kept` (Honest/K3/KeptTypes.lean). The tie and its powers: Honest/K3/JobsFast.lean,
under "The tie".

Why. Each call of these stages' jobs in Honest/K3/JobsFast.lean makes whole trees to read their
roots. Here the stage's two or three values are computed once, by `start`, off the store's levels 0
where a store is passed on, and lie in the kept state's field `vals`.

What is defined.
  `Fast.prodFrom`: the text of `Fast.Src.rootsFrom` over any function from a part's number to an
    element.
  `Fast.keptVals`: the kept state of a stage without a variable: its values, and nothing else.
  `rootOff`: a part's root: off the store where one is passed on, made anew where none is. As
    `tabBelow` (Honest/K3/JobsKeepTab.lean) it is handed the input as a function of the challenges
    (`Ask`) and applies it where no store is passed on alone: an application can be costly.
  `tie0Vals`, `tieVals`, `splitVals`: a stage's values, of the roots. At the tie's step 0 the fourth
    entry is the face's public factor at the shift and alpha: `KeepJob.inY` is not given the run's
    points.
  `tie0Keep`, `tieKeep` (at s: the stage `Stage.tie (s + 1)`), `splitKeep` (at i: `Stage.split i`):
    the jobs with a kept state. The earlier job of each is `jobOfAt` at `fastJobs`, with the call
    that `Stage.call` gives at the stage. `bind` returns the kept state as it is; `round` returns
    the empty list.
  `SplitOk`: the hypothesis on the key side: level 0 of every part's key tree.
  `TieOk`: the hypothesis on the table side: its level number 0.
  `Tie0Ok`: both.

What is shown.
  `Fast.rootsFrom_prodFrom`: `rootsFrom` is `prodFrom` at the roots: by `rfl`.
  `Fast.prodFrom_congr`: `prodFrom` at n parts hangs on the function's values below n alone.
  `Fast.fold_stay`: a fold that returns its state as it is returns the first state.
  `splitOk_none`, `tieOk_none`, `tie0Ok_none`: where no store is passed on, the hypotheses hold.
  `tie0Keep_call`, `tieKeep_call`, `splitKeep_call`: the shape of the earlier job is the call of
    `Stage.call`: by `rfl`.
  `rootOff_ok`, `tabBelow_zero`: under the hypotheses, what `start` reads is what
    Honest/K3/JobsFast.lean makes. `tie0Vals_ok`, `splitVals_ok`: so the values are those of the
    tables that JobsFast.lean makes.
  `tie0Keep_made`, `tieKeep_made`, `splitKeep_made`: the kept state made from the start, at every
    list of challenges, is the one that `start` returns.
  `…_round`, without a hypothesis: both jobs' `round` return the empty list.
  `…_ends`, `…_inY`: at the kept state made from the start, `ends` and `inY` return what the earlier
    job's return: at every list of challenges.
  `tie0Keep_faithful`, `tieKeep_faithful`, `splitKeep_faithful`: `KeepJob.FaithfulOn` of each job at
    its hypothesis.

The clause on `round` in `FaithfulOn` is empty here. These calls have no variable, so that clause
asks for a list of challenges shorter than 0, and there is none. What says something on `round` is
`…_round`. The clauses on `inY` and `ends` are asked at the empty list of challenges alone; the
equations here hold at every list.

Hypotheses that remain.
  `Tie0Ok R row a w f.heard f.own` | `TieOk …` | `SplitOk …`: in the equations as `hOk`, in the
    three last theorems as the second argument of `FaithfulOn`. No store at which one holds is
    exhibited in this file; at `none` they hold.
  `h`: (in `Fast.prodFrom_congr`) the two functions agree below n.
  `hi : i < a.face.parts.length`, at the parts' step alone: `SplitOk` speaks of the parts that the
    face has. In a row the parts' steps are those with i + 1 below the number of parts
    (`stages`, Honest/K3/Stages.lean).

Imported: Honest/SumKeepLaw.lean and Honest/SumKeep.lean, and through them and Honest/K3/Row.lean
the files Honest/Sum.lean, Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.
Honest/K3/JobsKeepTab.lean for `tabBelow`.

Users. Honest/K3/RowKeepFill.lean (`fastKeeps`); Honest/K3/JobsKeepTieToy.lean [not in this library]
(numbers).

Limits. Three sorts of stage. The earlier jobs are typed at `Option Store`; the row of `lookRow`
plays `jobOf`, typed at `Unit`: that `sumPart` at the two jobs shows the same rounds is shown in
Honest/K3/Law/Keep/Bridge.lean (`alone_jobOfAt`). Nothing is said on who makes a store, nor that a
hypothesis stays true as more is heard. s is any number: nothing asks that the stage stands in the
row. Where no store is passed on, `start` makes the trees as Honest/K3/JobsFast.lean does, once a
part of the row.
`inY` of `tie0Keep`, `tieKeep` and `splitKeep` does not reject: a mask entry beyond the list's end
counts as 0. At the list that `sumPart` (the masked sumcheck's part) hands over, entries laid behind
it change nothing in what `inY` returns: `no_pad_at_keep` (Honest/K3/Law/Keep/MasksAtKeep.lean
[not in this library]). `inY` and `ends` read the kept state's values by a default too
(`K.vals.getD`; and the lists that `start` lays hold entries read so: `g.getD`): nothing here bounds
these. How long either job takes is not said and has not been measured. Numbers are tried in
Honest/K3/JobsKeepTieToy.lean [not in this library].

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE subE mulE)

namespace Fast

/-! ## 1 Small things -/

/-- The text of `Src.rootsFrom` over any function: the product of its values from number i on, below
n. -/
def prodFrom (root : Nat → E) (n i : Nat) : E :=
  ((List.range (n - i)).map fun k => root (i + k)).foldl mulE oneE

/-- `rootsFrom` is `prodFrom` at the roots. -/
theorem rootsFrom_prodFrom (S : Src) (n i : Nat) : S.rootsFrom n i = prodFrom S.root n i := rfl

/-- `prodFrom` at n hangs on the function's values below n alone. -/
theorem prodFrom_congr (r r' : Nat → E) (n i : Nat) (h : ∀ j, j < n → r j = r' j) :
    prodFrom r n i = prodFrom r' n i := by
  unfold prodFrom
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' : k < n - i := List.mem_range.1 hk
  exact h (i + k) (by omega)

/-- The kept state of a stage without a variable: its values, and nothing else. -/
def keptVals (vals : List E) : Kept := ⟨[], [], 0, #[], vals⟩

/-- A fold that returns its state as it is returns the first state. -/
theorem fold_stay (k : Kept) : ∀ rs : List E, rs.foldl (fun (K : Kept) (_ : E) => K) k = k
  | [] => rfl
  | _ :: rs => fold_stay k rs

end Fast

/-! ## 2 What the stages read -/

/-- The parts' roots, by the part's number: off the store where one is passed on, made anew where
none is. The input w is applied in the second case alone. -/
def rootOff (f : LFace) (row : E → Nat → E) (w : Ask) (p : Pts) : Option Store → Nat → E
  | some st => fun i => ((st.keyLvls.getD i #[]).getD 0 #[]).getD 0 zeroE
  | none => (Fast.srcOf f row (w p.heard) p.theta p.alpha).root

/-- The values of the tie's step 0: Z, P_1, G_0, and the face's public factor. Here root gives the
parts' roots, g holds the planes' roots. -/
def tie0Vals (f : LFace) (root : Nat → E) (g : Array E) (fac : E) : List E :=
  [Fast.prodFrom root f.parts.length 0, Fast.powerP g f.planes 1, g.getD 0 zeroE, fac]

/-- The values of the tie's step s + 1: P_(s + 2), G_(s + 1). -/
def tieVals (f : LFace) (s : Nat) (g : Array E) : List E :=
  [Fast.powerP g f.planes (s + 2), g.getD (s + 1) zeroE]

/-- The values of the parts' step i: part i's root, the product of the later parts' roots. -/
def splitVals (f : LFace) (i : Nat) (root : Nat → E) : List E :=
  [root i, Fast.prodFrom root f.parts.length (i + 1)]

/-! ## 3 The jobs -/

/-- The job with a kept state at the stage `Stage.tie 0`. -/
def tie0Keep (R : Reads) (row : E → Nat → E) (a : At) : KeepJob Ask (Option Store) Kept :=
  { base := jobOfAt R (fastJobs a.face row).asked a (.tie 0) (VerifiableInference.Desc.K3.noVar 3 3)
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let g := tabBelow a.face row 0 w p x
      Fast.keptVals (tie0Vals a.face (rootOff a.face row w p x) g
        (a.face.factor p.theta p.alpha))
    bind := fun K _ => K
    round := fun _ => []
    inY := fun K mk =>
      Honest.addL [K.vals.getD 0 zeroE, mk.getD 0 zeroE]
        ((Fast.sqMulY (K.vals.getD 1 zeroE) (K.vals.getD 2 zeroE) (mk.getD 1 zeroE)
          (mk.getD 2 zeroE)).map fun y => subE zeroE (mulE (K.vals.getD 3 zeroE) y))
    ends := fun K => [K.vals.getD 0 zeroE, K.vals.getD 1 zeroE, K.vals.getD 2 zeroE] }

/-- The job with a kept state at the stage `Stage.tie (s + 1)`. -/
def tieKeep (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { base :=
      jobOfAt R (fastJobs a.face row).asked a (.tie (s + 1)) (VerifiableInference.Desc.K3.noVar 3 2)
    start := fun w h x =>
      let p := R.pts a.face a.base h
      Fast.keptVals (tieVals a.face s (tabBelow a.face row 0 w p x))
    bind := fun K _ => K
    round := fun _ => []
    inY := fun K mk =>
      Fast.sqMulY (K.vals.getD 0 zeroE) (K.vals.getD 1 zeroE) (mk.getD 0 zeroE) (mk.getD 1 zeroE)
    ends := fun K => [K.vals.getD 0 zeroE, K.vals.getD 1 zeroE] }

/-- The job with a kept state at the stage `Stage.split i`. -/
def splitKeep (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { base :=
      jobOfAt R (fastJobs a.face row).asked a (.split i) (VerifiableInference.Desc.K3.noVar 2 2)
    start := fun w h x =>
      let p := R.pts a.face a.base h
      Fast.keptVals (splitVals a.face i (rootOff a.face row w p x))
    bind := fun K _ => K
    round := fun _ => []
    inY := fun K mk =>
      Fast.mulY zeroE (K.vals.getD 0 zeroE) (K.vals.getD 1 zeroE) (mk.getD 0 zeroE)
        (mk.getD 1 zeroE)
    ends := fun K => [K.vals.getD 0 zeroE, K.vals.getD 1 zeroE] }

/-! ## 4 The hypotheses -/

/-- The hypothesis on the key side: where a store is passed on, level 0 of every part's key tree is
the one that Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as
a hypothesis. -/
def SplitOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → ∀ i, i < a.face.parts.length → (st.keyLvls.getD i #[]).getD 0 #[] =
    (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha).keyLvl i 0

/-- The hypothesis on the table side: where a store is passed on, its level number 0 is the one that
Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def TieOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → st.tabLvls.getD 0 #[] =
    (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha).tabLvl 0

/-- The hypothesis at the tie's step 0: both. A definition, meant as a hypothesis. -/
def Tie0Ok (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  SplitOk R row a w h x ∧ TieOk R row a w h x

/-- Where no store is passed on, `SplitOk` holds. -/
theorem splitOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    SplitOk R row a w h none :=
  fun _ e => nomatch e

/-- Where no store is passed on, `TieOk` holds. -/
theorem tieOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    TieOk R row a w h none :=
  fun _ e => nomatch e

/-- Where no store is passed on, `Tie0Ok` holds. -/
theorem tie0Ok_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    Tie0Ok R row a w h none :=
  ⟨splitOk_none R row a w h, tieOk_none R row a w h⟩

/-- Under `SplitOk` the root that the jobs read of a part that the face has is the one that
Honest/K3/JobsFast.lean makes. -/
theorem rootOff_ok (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (hOk : SplitOk R row a w h x) (i : Nat) (hi : i < a.face.parts.length) :
    rootOff a.face row w (R.pts a.face a.base h) x i =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).root i := by
  cases x with
  | none => rfl
  | some st => exact congrArg (·.getD 0 zeroE) (hOk st rfl i hi)

/-- Under `TieOk` the table side's level number 0 that the jobs read is the one that
Honest/K3/JobsFast.lean makes. -/
theorem tabBelow_zero (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (hOk : TieOk R row a w h x) :
    tabBelow a.face row 0 w (R.pts a.face a.base h) x =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).tabLvl 0 := by
  cases x with
  | none => rfl
  | some st => exact hOk st rfl

/-! ## 5 The calls -/

/-- The shape of the earlier job is the call that `Stage.call` gives at the stage. -/
theorem tie0Keep_call (R : Reads) (row : E → Nat → E) (a : At) :
    (Stage.tie 0).call a.face = some (tie0Keep R row a).base.shape := rfl

/-- The same at the tie's later steps. -/
theorem tieKeep_call (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) :
    (Stage.tie (s + 1)).call a.face = some (tieKeep R row a s).base.shape := rfl

/-- The same at the parts' steps. -/
theorem splitKeep_call (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) :
    (Stage.split i).call a.face = some (splitKeep R row a i).base.shape := rfl

/-! ## 6 The tie's step 0 -/

/-- The kept state made from the start is the one that `start` returns: at every list of
challenges. -/
theorem tie0Keep_made (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (rs : List E) :
    (tie0Keep R row a).madeAt w h x rs =
      Fast.keptVals (tie0Vals a.face
        (rootOff a.face row w (R.pts a.face a.base h) x)
        (tabBelow a.face row 0 w (R.pts a.face a.base h) x)
        (a.face.factor (R.pts a.face a.base h).theta (R.pts a.face a.base h).alpha)) :=
  Fast.fold_stay _ rs

/-- Under `Tie0Ok` the values are those of the tables that Honest/K3/JobsFast.lean makes. -/
theorem tie0Vals_ok (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (hOk : Tie0Ok R row a w h x) (fac : E) :
    tie0Vals a.face
        (rootOff a.face row w (R.pts a.face a.base h) x)
        (tabBelow a.face row 0 w (R.pts a.face a.base h) x) fac =
      tie0Vals a.face
        (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
          (R.pts a.face a.base h).alpha).root
        ((Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
          (R.pts a.face a.base h).alpha).tabLvl 0) fac := by
  rw [tabBelow_zero R row a w h x hOk.2]
  unfold tie0Vals
  rw [Fast.prodFrom_congr _ _ _ 0 (rootOff_ok R row a w h x hOk.1)]

/-- Both jobs' `round` return the empty list. No hypothesis. -/
theorem tie0Keep_round (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) :
    (tie0Keep R row a).round ((tie0Keep R row a).madeAt w f.heard f.own rs) =
      (tie0Keep R row a).base.round w f rs := rfl

/-- At the kept state made from the start, `ends` returns what the earlier job's returns.
Conditional on `Tie0Ok`. -/
theorem tie0Keep_ends (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : Tie0Ok R row a w f.heard f.own) :
    (tie0Keep R row a).ends ((tie0Keep R row a).madeAt w f.heard f.own rs) =
      (tie0Keep R row a).base.ends w f rs := by
  rw [tie0Keep_made, tie0Vals_ok R row a w f.heard f.own hOk]
  rfl

/-- The same of `inY`. Conditional on `Tie0Ok`. -/
theorem tie0Keep_inY (R : Reads) (row : E → Nat → E) (a : At) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hOk : Tie0Ok R row a w f.heard f.own) :
    (tie0Keep R row a).inY ((tie0Keep R row a).madeAt w f.heard f.own rs) m =
      (tie0Keep R row a).base.inY w f rs m := by
  rw [tie0Keep_made, tie0Vals_ok R row a w f.heard f.own hOk]
  rfl

/-- **The kept state of `tie0Keep` gives what the earlier job computes.** Conditional on `Tie0Ok`,
as the second argument of `FaithfulOn`. The clause on `round` is empty: the call has no variable. -/
theorem tie0Keep_faithful (R : Reads) (row : E → Nat → E) (a : At) :
    (tie0Keep R row a).FaithfulOn (Tie0Ok R row a) :=
  ⟨fun w f rs _ _ => tie0Keep_round R row a w f rs,
    fun w f rs m hOk _ => tie0Keep_inY R row a w f rs m hOk,
    fun w f rs hOk _ => tie0Keep_ends R row a w f rs hOk⟩

/-! ## 7 The tie's later steps -/

/-- The kept state made from the start is the one that `start` returns: at every list of
challenges. -/
theorem tieKeep_made (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (rs : List E) :
    (tieKeep R row a s).madeAt w h x rs =
      Fast.keptVals (tieVals a.face s
        (tabBelow a.face row 0 w (R.pts a.face a.base h) x)) :=
  Fast.fold_stay _ rs

/-- Both jobs' `round` return the empty list. No hypothesis. -/
theorem tieKeep_round (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) :
    (tieKeep R row a s).round ((tieKeep R row a s).madeAt w f.heard f.own rs) =
      (tieKeep R row a s).base.round w f rs := rfl

/-- At the kept state made from the start, `ends` returns what the earlier job's returns.
Conditional on `TieOk`. -/
theorem tieKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hOk : TieOk R row a w f.heard f.own) :
    (tieKeep R row a s).ends ((tieKeep R row a s).madeAt w f.heard f.own rs) =
      (tieKeep R row a s).base.ends w f rs := by
  rw [tieKeep_made, tabBelow_zero R row a w f.heard f.own hOk]
  rfl

/-- The same of `inY`. Conditional on `TieOk`. -/
theorem tieKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hOk : TieOk R row a w f.heard f.own) :
    (tieKeep R row a s).inY ((tieKeep R row a s).madeAt w f.heard f.own rs) m =
      (tieKeep R row a s).base.inY w f rs m := by
  rw [tieKeep_made, tabBelow_zero R row a w f.heard f.own hOk]
  rfl

/-- **The kept state of `tieKeep` gives what the earlier job computes.** Conditional on `TieOk`, as
the second argument of `FaithfulOn`. The clause on `round` is empty: the call has no variable. -/
theorem tieKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) (s : Nat) :
    (tieKeep R row a s).FaithfulOn (TieOk R row a) :=
  ⟨fun w f rs _ _ => tieKeep_round R row a s w f rs,
    fun w f rs m hOk _ => tieKeep_inY R row a s w f rs m hOk,
    fun w f rs hOk _ => tieKeep_ends R row a s w f rs hOk⟩

/-! ## 8 The parts' steps -/

/-- The kept state made from the start is the one that `start` returns: at every list of
challenges. -/
theorem splitKeep_made (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (rs : List E) :
    (splitKeep R row a i).madeAt w h x rs =
      Fast.keptVals (splitVals a.face i
        (rootOff a.face row w (R.pts a.face a.base h) x)) :=
  Fast.fold_stay _ rs

/-- Under `SplitOk`, at a part that the face has, the values are those of the tables that
Honest/K3/JobsFast.lean makes. -/
theorem splitVals_ok (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) (w : Ask)
    (h : List Fmt.Drawn) (x : Option Store) (hi : i < a.face.parts.length)
    (hOk : SplitOk R row a w h x) :
    splitVals a.face i
        (rootOff a.face row w (R.pts a.face a.base h) x) =
      splitVals a.face i
        (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
          (R.pts a.face a.base h).alpha).root := by
  unfold splitVals
  rw [Fast.prodFrom_congr _ _ _ (i + 1) (rootOff_ok R row a w h x hOk),
    rootOff_ok R row a w h x hOk i hi]

/-- Both jobs' `round` return the empty list. No hypothesis. -/
theorem splitKeep_round (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) :
    (splitKeep R row a i).round ((splitKeep R row a i).madeAt w f.heard f.own rs) =
      (splitKeep R row a i).base.round w f rs := rfl

/-- At the kept state made from the start, `ends` returns what the earlier job's returns.
Conditional on `SplitOk` and on i below the number of parts. -/
theorem splitKeep_ends (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) (w : Ask)
    (f : Front (Option Store)) (rs : List E) (hi : i < a.face.parts.length)
    (hOk : SplitOk R row a w f.heard f.own) :
    (splitKeep R row a i).ends ((splitKeep R row a i).madeAt w f.heard f.own rs) =
      (splitKeep R row a i).base.ends w f rs := by
  rw [splitKeep_made, splitVals_ok R row a i w f.heard f.own hi hOk]
  rfl

/-- The same of `inY`. Conditional on `SplitOk` and on i below the number of parts. -/
theorem splitKeep_inY (R : Reads) (row : E → Nat → E) (a : At) (i : Nat) (w : Ask)
    (f : Front (Option Store)) (rs m : List E) (hi : i < a.face.parts.length)
    (hOk : SplitOk R row a w f.heard f.own) :
    (splitKeep R row a i).inY ((splitKeep R row a i).madeAt w f.heard f.own rs) m =
      (splitKeep R row a i).base.inY w f rs m := by
  rw [splitKeep_made, splitVals_ok R row a i w f.heard f.own hi hOk]
  rfl

/-- **The kept state of `splitKeep` gives what the earlier job computes.** Conditional on i below
the number of parts, and on `SplitOk` as the second argument of `FaithfulOn`. The clause on `round`
is empty: the call has no variable. -/
theorem splitKeep_faithful (R : Reads) (row : E → Nat → E) (a : At) (i : Nat)
    (hi : i < a.face.parts.length) :
    (splitKeep R row a i).FaithfulOn (SplitOk R row a) :=
  ⟨fun w f rs _ _ => splitKeep_round R row a i w f rs,
    fun w f rs m hOk _ => splitKeep_inY R row a i w f rs m hi hOk,
    fun w f rs hOk _ => splitKeep_ends R row a i w f rs hi hOk⟩

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.Fast.rootsFrom_prodFrom
#print axioms ProofFile.Honest.K3.Fast.prodFrom_congr
#print axioms ProofFile.Honest.K3.Fast.fold_stay
#print axioms ProofFile.Honest.K3.splitOk_none
#print axioms ProofFile.Honest.K3.tieOk_none
#print axioms ProofFile.Honest.K3.tie0Ok_none
#print axioms ProofFile.Honest.K3.rootOff_ok
#print axioms ProofFile.Honest.K3.tabBelow_zero
#print axioms ProofFile.Honest.K3.tie0Keep_call
#print axioms ProofFile.Honest.K3.tieKeep_call
#print axioms ProofFile.Honest.K3.splitKeep_call
#print axioms ProofFile.Honest.K3.tie0Keep_made
#print axioms ProofFile.Honest.K3.tie0Vals_ok
#print axioms ProofFile.Honest.K3.tie0Keep_round
#print axioms ProofFile.Honest.K3.tie0Keep_ends
#print axioms ProofFile.Honest.K3.tie0Keep_inY
#print axioms ProofFile.Honest.K3.tie0Keep_faithful
#print axioms ProofFile.Honest.K3.tieKeep_made
#print axioms ProofFile.Honest.K3.tieKeep_round
#print axioms ProofFile.Honest.K3.tieKeep_ends
#print axioms ProofFile.Honest.K3.tieKeep_inY
#print axioms ProofFile.Honest.K3.tieKeep_faithful
#print axioms ProofFile.Honest.K3.splitKeep_made
#print axioms ProofFile.Honest.K3.splitVals_ok
#print axioms ProofFile.Honest.K3.splitKeep_round
#print axioms ProofFile.Honest.K3.splitKeep_ends
#print axioms ProofFile.Honest.K3.splitKeep_inY
#print axioms ProofFile.Honest.K3.splitKeep_faithful
