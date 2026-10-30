-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/Bends.lean: BENT COPIES OF THE JOINED WRITTEN TERM (MW.lean), for the
negative tests of this folder (No‹Name›.lean): each of the nineteen tests whose yes at MW is a
closed fact here rejects a bent copy or a bent letter. Which bend fells which test was asked of
Lean's evaluator first, outside this tree.

  `onPlan`, `mapE f M`: every entry of M's seven plans turned by f.
  `MWrows`: each entry's rows one higher · `MWdraw`: each entry's drawn field elements one more ·
  `MWname`: each entry's name with a letter more · `MWwork`: each entry's bits of work, where not 0,
    one
  more · `MWwork63`: these set to 63 · `MWlogN`: each entry's logN, where not 0, one more ·
  `MWshort`: without the proof file's last plan · `MWreq`: the most requests in a batch, in the
    sizes of the proof file's test on the table, set to 2 ^ 64.
Definitions alone.
-/
import Johnson.AtFull.ProofPlan.Every.MW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open OnBytes.Params (Configured Planned)

/-- Every entry of a plan turned by f. -/
def onPlan (f : Fmt.Entry → Fmt.Entry) (p : Planned) : Planned :=
  { p with rounds := p.rounds.map fun x => { x with entry := f x.entry } }

/-- Every entry of the seven plans turned by f. -/
def mapE (f : Fmt.Entry → Fmt.Entry) (M : Configured) : Configured :=
  { M with proof := M.proof.map (onPlan f), key := M.key.map (onPlan f), entry := onPlan f M.entry }

abbrev MWrows : Configured := mapE (fun e => { e with rows := e.rows + 1 }) MW
abbrev MWdraw : Configured := mapE (fun e => { e with drawE := e.drawE + 1 }) MW
abbrev MWname : Configured := mapE (fun e => { e with name := e.name ++ "x" }) MW
abbrev MWwork : Configured :=
  mapE (fun e => if e.work != 0 then { e with work := e.work + 1 } else e) MW
abbrev MWwork63 : Configured := mapE (fun e => if e.work != 0 then { e with work := 63 } else e) MW
abbrev MWlogN : Configured :=
  mapE (fun e => if e.logN != 0 then { e with logN := e.logN + 1 } else e) MW
abbrev MWshort : Configured := { MW with proof := MW.proof.dropLast }
abbrev MWreq : Configured :=
  { MW with sized := { MW.sized with proof := { MW.sized.proof with batch :=
      { MW.sized.proof.batch with lines :=
          { MW.sized.proof.batch.lines with requests := 2 ^ 64 } } } } }

end Johnson.AtFull.ProofPlan.Every
