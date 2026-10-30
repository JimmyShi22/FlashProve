-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/Back.lean: the way back from the names fbw t k on the deferred side.

Definitions, statements and proofs. General statements on the second form's oracles; this file
states no goal of the release. A DEVICE OF A PROOF: the names fbw t k, the exchange of queries and
"routed" stand in no statement on the scheme.

A token program writes the later tries of a search under the names fbw t k. Run with its marked
queries deferred (OComp.runDefer, Rom/Handle/Defs.lean), what erase makes of it logs these tries
under these names. The scheme's own algorithm asks fb t, so its log holds them under fb t, and it is
under fb t that they are written into the table when a string that shows them is handed out. Here
the two runs are tied: tables by the exchange of queries (Table.via (ghost W)), logs entry by entry
(ghostQA W), marks by ghostMark W.

Main names (namespace OnBytes.GhostSide).
  ghostQA W        the exchange on a log's entry: (fb t, q, r) with the nonce for k + 1 ↔
                   (fbw t k, q, r); all other entries stay. ghostQA_ghostQA: its own inverse.
  ghostMark W mk   the mark that names a query just when mk names the exchanged query.
  runDefer_ghost   for every algorithm c: the run of c.via (ghost W) under ghostMark W mk, with
                   table and log exchanged at the end, is the run of c under mk from the exchanged
                   table and log.
  runDefer_plainOf the same for a routed token program: plainOf c vs (fb t written back) against
                   erase c vs (the names fbw t k).
  lay_ghost        to write a log and then exchange is to exchange and then write the exchanged log.
  via_via_ghost    exchanging a table twice gives the table.
Limits. The run that answers deferred queries from a list of recorded answers (OComp.runReplay) is
not translated here: such a list holds oracles' names.
Terms: lean/GLOSSARY.md.

-/
import Johnson.GhostSide.Generic
import Johnson.GhostSide.ViaDefer

set_option autoImplicit false

noncomputable section

namespace OnBytes.GhostSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch OnBytes.TokenSide Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L)

/-- The exchange on an entry of a log. -/
def ghostQA : QA (typedOracleFamily lam W.K L) → QA (typedOracleFamily lam W.K L)
  | ⟨.fb t, q, r⟩ => match cls W t q with
      | 0 => ⟨.fb t, q, r⟩
      | k + 1 => ⟨.fbw t k, q, r⟩
  | ⟨.fbw t k, q, r⟩ => if cls W t q = k + 1 then ⟨.fb t, q, r⟩ else ⟨.fbw t k, q, r⟩
  | e => e

/-- The mark that names a query just when mk names the exchanged query. -/
def ghostMark (mk : Mark (typedOracleFamily lam W.K L)) : Mark (typedOracleFamily lam W.K L) :=
  fun o q => mk (ghost W o q).1 (ghost W o q).2.1

theorem ghostQA_fb_zero {t : Tag} {q : FbIn lam L t} (h : cls W t q = 0)
    (r : rngOf lam W.K (.fb t)) :
    ghostQA W ⟨.fb t, q, r⟩ = ⟨.fb t, q, r⟩ := by
  show (match cls W t q with
      | 0 => (⟨.fb t, q, r⟩ : QA (typedOracleFamily lam W.K L))
      | k + 1 => ⟨.fbw t k, q, r⟩) = _
  rw [h]

theorem ghostQA_fb_succ {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1)
    (r : rngOf lam W.K (.fb t)) :
    ghostQA W ⟨.fb t, q, r⟩ = ⟨.fbw t k, q, r⟩ := by
  show (match cls W t q with
      | 0 => (⟨.fb t, q, r⟩ : QA (typedOracleFamily lam W.K L))
      | k + 1 => ⟨.fbw t k, q, r⟩) = _
  rw [h]

theorem ghostQA_fbw_pos {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1)
    (r : rngOf lam W.K (.fbw t k)) :
    ghostQA W ⟨.fbw t k, q, r⟩ = ⟨.fb t, q, r⟩ := if_pos h

theorem ghostQA_fbw_neg {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q ≠ k + 1)
    (r : rngOf lam W.K (.fbw t k)) :
    ghostQA W ⟨.fbw t k, q, r⟩ = ⟨.fbw t k, q, r⟩ := if_neg h

/-- one point: from the value of ghost W at it -/
theorem readsBack_at {o : OracleName} {q : domOf lam L o}
    {z : Σ o' : OracleName, domOf lam L o' × (rngOf lam W.K o' → rngOf lam W.K o)}
    (hz : ghost W o q = z)
    (H : ∀ r : rngOf lam W.K z.1, ghostQA W ⟨z.1, z.2.1, r⟩ = ⟨o, q, z.2.2 r⟩) :
    ∀ r : rngOf lam W.K (ghost W o q).1,
      ghostQA W ⟨(ghost W o q).1, (ghost W o q).2.1, r⟩ = ⟨o, q, (ghost W o q).2.2 r⟩ := by
  subst hz
  exact H

theorem readsBack_ghost : ReadsBack (ghost W) (ghostQA W) := by
  intro o q
  cases o with
  | fb t =>
      rcases h : cls W t q with _ | k
      · exact readsBack_at W (ghost_fb_zero W h) fun r => ghostQA_fb_zero W h r
      · exact readsBack_at W (ghost_fb_succ W h) fun r => ghostQA_fbw_pos W h r
  | fbw t k =>
      by_cases h : cls W t q = k + 1
      · exact readsBack_at W (ghost_fbw_pos W h) fun r => ghostQA_fb_succ W h r
      · exact readsBack_at W (ghost_fbw_neg W h) fun r => ghostQA_fbw_neg W h r
  | leaf => exact fun _ => rfl
  | node => exact fun _ => rfl
  | rleaf => exact fun _ => rfl
  | rnode => exact fun _ => rfl
  | g t => exact fun _ => rfl
  | ann => exact fun _ => rfl
  | other => exact fun _ => rfl

/-- The exchange on entries is its own inverse. -/
theorem ghostQA_ghostQA (e : QA (typedOracleFamily lam W.K L)) : ghostQA W (ghostQA W e) = e := by
  obtain ⟨o, q, r⟩ := e
  cases o with
  | fb t =>
      rcases h : cls W t q with _ | k
      · rw [ghostQA_fb_zero W h, ghostQA_fb_zero W h]
      · rw [ghostQA_fb_succ W h, ghostQA_fbw_pos W h]
  | fbw t k =>
      by_cases h : cls W t q = k + 1
      · rw [ghostQA_fbw_pos W h, ghostQA_fb_succ W h]
      · rw [ghostQA_fbw_neg W h, ghostQA_fbw_neg W h]
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

theorem marksVia_ghost (mk : Mark (typedOracleFamily lam W.K L)) : MarksVia (ghost W) mk (ghostMark W mk) :=
  fun o q => congrArg (fun p : Via.Pnt (typedOracleFamily lam W.K L) => mk p.1 p.2)
    (Via.img_img (ghost_inv W) ⟨o, q⟩)

variable {α : Type}

/-- The run with deferred queries, under the exchange. -/
theorem runDefer_ghost (mk : Mark (typedOracleFamily lam W.K L)) (c : TypedOracleComputation lam W.K L α)
    (T : Table (typedOracleFamily lam W.K L)) (lg : Trace (typedOracleFamily lam W.K L)) :
    ((c.via (ghost W)).runDefer (ghostMark W mk) T lg).map
        (fun x => (x.1, Table.via (ghost W) x.2.1, x.2.2.map (ghostQA W))) =
      c.runDefer mk (Table.via (ghost W) T) (lg.map (ghostQA W)) :=
  OComp.runDefer_via (ghost_inv W) (readsBack_ghost W) (marksVia_ghost W mk) c T lg

/-- The same for a routed token program: with fb t written back, against the names fbw t k. -/
theorem runDefer_plainOf (mk : Mark (typedOracleFamily lam W.K L)) {c : StT lam W.K L α} (h : RoutedT W c)
    (vs : List Bits) (T : Table (typedOracleFamily lam W.K L)) (lg : Trace (typedOracleFamily lam W.K L)) :
    ((plainOf c vs).runDefer (ghostMark W mk) T lg).map
        (fun x => (x.1, Table.via (ghost W) x.2.1, x.2.2.map (ghostQA W))) =
      (erase c vs).runDefer mk (Table.via (ghost W) T) (lg.map (ghostQA W)) := by
  rw [plainOf_via h vs]
  exact runDefer_ghost W mk (erase c vs) T lg

/-- To write a log and then exchange is to exchange and then write the exchanged log. -/
theorem lay_ghost (lg : Trace (typedOracleFamily lam W.K L)) (T : Table (typedOracleFamily lam W.K L)) :
    Table.via (ghost W) (T.lay lg) = (Table.via (ghost W) T).lay (lg.map (ghostQA W)) :=
  Table.via_lay ⟨ghost_inv W, ghost_inv W⟩ (readsBack_ghost W) lg T

/-- Exchanging a table twice gives the table. -/
theorem via_via_ghost (T : Table (typedOracleFamily lam W.K L)) :
    Table.via (ghost W) (Table.via (ghost W) T) = T :=
  Table.via_via ⟨ghost_inv W, ghost_inv W⟩ T

end OnBytes.GhostSide

#print axioms OnBytes.GhostSide.readsBack_ghost
#print axioms OnBytes.GhostSide.ghostQA_ghostQA
#print axioms OnBytes.GhostSide.runDefer_ghost
#print axioms OnBytes.GhostSide.runDefer_plainOf
#print axioms OnBytes.GhostSide.lay_ghost
#print axioms OnBytes.GhostSide.via_via_ghost
