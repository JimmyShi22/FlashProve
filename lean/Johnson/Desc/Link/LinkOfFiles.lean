-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkOfFiles.lean: THE ENTRY FILE's MAKER: the link's description, its rounds' data
and its stored openings, OF THE THREE PUBLIC FILES ALONE.
  Link3            the three letters of the compiled slot as one record: the description (its run is
  dec) · ds · xs
  linkOfFilesV pol lay KL  ANOTHER ROOT (VerifierAndGoals.theDescription does not run it: its decision on
  the entry file is linkDecisionAtParameterFile, Johnson/Desc/Link/LinkWritten.lean, whose head lists what this root
  asks and that one does not): the planner's record c
  (Model.Verify.planned) · the declared rounds off the plan (declLOf) · linkDescV c.chains plan ·
  its dsOf ·
                   its xsTyped. It refuses, with words, where the planner, declLOf or
                   Johnson.G.OfPlan.writtenOf refuse, AND WHERE THE DESCRIPTION's OWN TESTS ON THE
                   PLAN SAY NO: so whoever holds a Link3 out of this maker holds a description that
                   has passed them.
NO LETTER IS LEFT FREE BUT THE FILES: the shape, the codes, the setting, the plan, the prices that
entryOk tests: all come out of one `planned pol KL (some lay)`
(declLOf and sendsOf call the same function at the same three arguments).
Definitions with code; no theorem.
-/
import Johnson.Desc.Link.OneSlotTyped
import Johnson.Desc.Link.LinkDesc
import Johnson.G.RoundsOfPlanLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes VerifiableInference.Desc

structure Link3 where
  F : OneChainFileDescription (TableKey × TableKey)
  ds : List TypedOracleCompiler.Run.PQ.RD
  xs : List _root_.Run.PQ.XO

def linkOfFilesV (pol lay KL : ByteArray) : Except String Link3 :=
  match OnBytes.Model.Verify.planned pol KL (some lay), Johnson.G.OfPlan.declLOf pol lay KL with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok p, .ok plan =>
    let F := linkDescV p.chains plan
    match F.planWord, F.dsOf "entry file" with
    | some w, _ => .error s!"entry file: {w}"
    | _, .error e => .error e
    | none, .ok ds => .ok ⟨F, ds, F.xsTyped⟩

end Desc.K15
