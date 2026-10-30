-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/ThirdPieces.lean: the check `decWith` of a key file's third chain
(Johnson/KeyRun/ThirdAtClaim.lean) once more, piece by piece, so that a print can say which piece
said no.

Each piece has a name, a yes or no, and a note. `stagedFrom` follows the text of `Fmt.M1.iopp`
(Fmt/M1Dec.lean) at `blocksA`, cut at each match, with `baseOK` (Fmt/M1Fold.lean) cut into its two
checks, without its test on four lengths, and with two pieces of its own on whether the columns are
shown. `staged` puts the steps before `iopp` in front. The list ends at the first piece after which
the check cannot go on.
Limits: it decides nothing: the check is `decWith`. Of `third` (Johnson/KeyRun/Third.lean) it lacks
the tests on the plan and the making of the claim, so "all pieces say yes" is not yet a yes of
`third`. That all pieces say yes just where `decWith` says yes is not proved; the files of lean/Ask/
print both answers at the rows where they call it. No theorem. Nothing on soundness.


-/
import Johnson.KeyRun.ThirdAtClaim

set_option autoImplicit false

namespace Johnson.KeyRun.Third

open Fmt (Fld)
open Fmt.M1

/-- One piece of the check. -/
structure Line where
  name : String
  ok : Bool
  note : String := ""

/-- `iopp` from the stage number `no` on, in pieces. The other arguments are those of `iopp`. -/
def stagedFrom (f : Fld) (V : View) : List Stage → (no tree mF mE : Nat) → GRow → Rs → List Line
  | [], _, _, _, _, _, _ => [⟨"the test has a stage", false, ""⟩]
  | [s], no, tree, _, _, G, rs =>
    match nextN 1 1 0 rs with
    | some (⟨[tauS], [lam], _⟩, rs1) =>
      ⟨s!"stage {no} (the last): BASE lambda sends one element and draws one", true, ""⟩ ::
      match nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 with
      | some (v, []) =>
        let M0 := v.sent.take s.C.l
        let M1 := (v.sent.drop s.C.l).take s.Z.l
        let R0 := (v.sent.drop (s.C.l + s.Z.l)).take s.C.r
        let R1 := v.sent.drop (s.C.l + s.Z.l + s.C.r)
        let shown := v.poss.filter fun x => (lastCol V tree x).isSome
        let good := v.poss.filter fun x =>
          match lastCol V tree x with
          | some o => baseB2At f s.C s.Z lam M0 M1 R0 R1 x o
          | none => false
        [⟨s!"stage {no}: BASE has the right counts and no round is left", true, ""⟩,
         ⟨s!"stage {no}: BASE's columns are shown", shown.length == v.poss.length,
           s!"shown at {shown.length} of {v.poss.length} positions"⟩,
         ⟨s!"stage {no}: BASE's linear check", baseB1 f G.c G.d G.t tauS lam M0 M1, ""⟩,
         ⟨s!"stage {no}: BASE's symbols at the drawn positions", good.length == v.poss.length,
           s!"right at {good.length} of {v.poss.length} positions"⟩]
      | _ => [⟨s!"stage {no}: BASE has the right counts and no round is left", false, ""⟩]
    | _ => [⟨s!"stage {no} (the last): BASE lambda sends one element and draws one", false, ""⟩]
  | s :: s' :: more, no, tree, mF, mE, G, rs =>
    match nextN 1 1 0 rs with
    | some (⟨[sigma], [eps], _⟩, rs1) =>
      ⟨s!"stage {no}: FOLD epsilon sends one element and draws one", true, ""⟩ ::
      match takeRounds s.k rs1 with
      | some (qs, g, rs2) =>
        ⟨s!"stage {no}: the {s.k} FOLD rounds have the right counts", true, ""⟩ ::
        match seedOf s'.na rs2 with
        | some (z, beta, rs3) =>
          ⟨s!"stage {no}: SEND seed draws {s'.na + 1} elements", true, ""⟩ ::
          match nextN 1 1 s.t rs3 with
          | some (⟨[alpha], [theta], xs⟩, rs4) =>
            let col := fun x => (colAt V tree x).bind (stageCol s mF mE)
            let shown := xs.filter fun x => (col x).isSome
            ⟨s!"stage {no}: CS sends one element, draws one and {s.t} positions", true, ""⟩ ::
            ⟨s!"stage {no}: CS's columns are shown, at the stage's width",
              shown.length == xs.length, s!"shown at {shown.length} of {xs.length} positions"⟩ ::
            match csStepA f s s' (foldStep f s.k s.h G sigma eps qs g)
                (sampleRow f s'.Am s'.Az z beta alpha) xs theta col with
            | some G' =>
              ⟨s!"stage {no}: the code switch puts out a row", true, ""⟩ ::
                stagedFrom f V (s' :: more) (no + 1) (tree + 1) 0 (2 ^ s'.k) G' rs4
            | none => [⟨s!"stage {no}: the code switch puts out a row", false, ""⟩]
          | _ =>
            [⟨s!"stage {no}: CS sends one element, draws one and {s.t} positions", false, ""⟩]
        | none => [⟨s!"stage {no}: SEND seed draws {s'.na + 1} elements", false, ""⟩]
      | none => [⟨s!"stage {no}: the {s.k} FOLD rounds have the right counts", false, ""⟩]
    | _ => [⟨s!"stage {no}: FOLD epsilon sends one element and draws one", false, ""⟩]

/-- The whole check at a claim, piece by piece. -/
def staged (P : Pub3) (claim : OnBytes.LinClaim) (v₁ v₂ v₃ : _root_.Fmt.View) : List Line :=
  match into3 P claim v₁ v₂ with
  | .error e => [⟨"chains 1 and 2: the plans name the rounds to read", false, e⟩]
  | .ok _ =>
    ⟨"chains 1 and 2: the plans name the rounds to read", true, ""⟩ ::
    match build P claim v₁ v₂ v₃ with
    | .error e => [⟨"the batching round: the row is made", false, e⟩]
    | .ok b =>
      ⟨"the batching round: the row is made", true, ""⟩ ::
      match sideOf P b v₃ with
      | .error e => [⟨"the opened columns are laid for the test", false, e⟩]
      | .ok s =>
        ⟨"the opened columns are laid for the test", true, ""⟩ ::
          stagedFrom .two s.V s.st 1 0 0 s.mE s.G s.V.rounds

end Johnson.KeyRun.Third
