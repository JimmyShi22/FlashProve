-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsTopProofs.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsTopProofs.lean (only what the entry's clause
holds and stands on a declaration that the sibling says again), then turned by hand where it had to
be. THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS
NOT HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND
ONLY: plainsSL_some, pi_typed'.

Run/PageIsTopProofs.lean: the proof of the statement of Run/PageIsTop.lean, and of ONE PART of the
plan of Run/PageIs.lean: pi_typed (the parser's last step does not refuse on what the lenient reader
hands out: a message's items, read, can be typed: ofGots_read; every opening of a trace passes the
parser's own test: opens_ok; with Run/ParseLaws.lean, Run/ParseThin.lean). The top: formula_of (the
verifier's text unfolded once: the chain, the strict format, what follows), kits_of, half_of,
core_of: truth values.

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsTopProofs
import OnBytes.TypedOracleCompiler.Run.PageIs   -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseLaws
import Run.PageIsTop
import OnBytes.TypedOracleCompiler.Run.PageIs
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import OnBytes.TypedOracleCompiler.Run.ParseLaws
import OnBytes.TypedOracleCompiler.Run.ParseThin
import Run.LaxDomProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (ofGots_read ofGots_whole forall2_right opens_ok size_HO)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-! ### The parser's last step does not refuse -/

theorem plainsSL_some (h : HId) (S : _root_.Fmt.Spec) (C : CK) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round)
        (ros : List RoundOut) (c : Chain) (roots : Array ByteArray) (sent : ℕ),
      TraceL h P rs ros c roots → ∃ pl, plainsSL C (rdsFrom S sent rs) ros = some pl
  | [], [], _, _, _, _ => ⟨(), rfl⟩
  | r :: rs, ro :: ros, c, roots, sent, t => by
    obtain ⟨-, hv, -, -, -, t'⟩ := t
    obtain ⟨p, hp⟩ := ofGots_whole P.field r.items ro.msg ro.vals hv
    obtain ⟨pl, hpl⟩ := plainsSL_some h S C P rs ros _ _ (sent + r.entry.roots) t'
    refine ⟨(GPlain.mk r.entry.work p ro.nonce, pl), ?_⟩
    simp only [rdsFrom, plainsSL, hp, hpl]
  | [], _ :: _, _, _, _, t => t.elim
  | _ :: _, [], _, _, _, t => t.elim

theorem pi_typed' (h : HId) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)
    (o : ChainOut) (hf : LaxFacts h S o) :
    ∃ (run : ByteArray) (pl : Plains (uL C (rds S))),
      o.run = some run ∧
      plainsSL C (rds S) o.rounds.toList = some pl ∧
      toBPrfP (PSof C (rds S) dec) (TYS S C dec) o =
        some ([bytesToDig o.pd],
            mkBPrfP (PSof C (rds S) dec) run (rootsB o)
              ((), pl) (opensAt (TYS S C dec).up run o)) := by
  obtain ⟨rnd, -, hr⟩ := hf.run
  obtain ⟨pl, hpl⟩ : ∃ pl, plainsSL C (rds S) o.rounds.toList = some pl :=
    plainsSL_some h S C S.plan S.rounds o.rounds.toList _ _ 0 hf.trace
  refine ⟨_, pl, hr, hpl, ?_⟩
  rw [parseThin_to]
  refine (parseLaws_some (TYS S C dec).up o _).2 ⟨_, ((), pl), hr, ?_, ?_, rfl⟩
  · show (plainsSL C (rds S) o.rounds.toList).map (fun r => ((), r)) = some ((), pl)
    rw [hpl]
    rfl
  · rw [List.all_eq_true]
    intro y hy
    obtain ⟨ro, hro, hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact opens_ok h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx

/-! ### The top, from the parts -/

end TypedOracleCompiler.Run.PQ
