-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Names.lean: the names fbw t k of the later tries of a search, on the way back from
the token programs to the scheme's own terms: small facts on marks and on a log's entries.

General lemmas on the second form's oracles. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

The token programs ask fbw t k; the scheme asks fb t. Two pairs of tests say which queries are
deferred: mkHash, mkTable for the token programs (Johnson/TokenRules/Spec.lean) and mkRun, mkTab for
the scheme's terms (Johnson/WholeKey/Sim.lean). Exchanged (ghostMark, Johnson/GhostSide/Back.lean),
the first pair is the second at every query but those to a name fbw t k, which an algorithm with
fb t written back (realQ) never asks.

  NoW, asksIn_realQ         no query to a name fbw t k; realQ c asks none.
  ghostMark_mkHash, ghostMark_mkTable   the two pairs agree there.
  runDefer_plain_run, runDefer_plain_tab   so plainOf c has the same run with a table and a log
                            under ghostMark W mkHash and mkRun, under ghostMark W mkTable and mkTab.
  notLeaf_ghostQA, filter_notLeaf_ghost   the exchange keeps "no leaf".
  AllLeaf, map_ghostQA_allLeaf, allLeaf_laidK, allLeaf_extLaid   the exchange fixes a leaf's entry;
                            what handOut writes by place are leaves' entries.

-/
import Johnson.GhostSide.Back
import Johnson.TokenRules.Spec
import Johnson.WholeKey.Sim
import Rom.Handle.Congr

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- no name of a later try -/
def NoW : OracleName → Prop
  | .fbw _ _ => False
  | _ => True

theorem asksIn_realQ {K : ℕ} {α : Type} : ∀ c : OComp (typedOracleFamily lam K L) α,
    (realQ c).AsksIn fun o _ => NoW o
  | .pure _ => trivial
  | .sample _ k => fun r => asksIn_realQ (k r)
  | .query .leaf _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query .node _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query .rleaf _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query .rnode _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query (.fb _) _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query (.g _) _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query .ann _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query .other _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩
  | .query (.fbw _ _) _ k => ⟨trivial, fun r => asksIn_realQ (k r)⟩

variable (W : QueryLayout lam L)

theorem ghostMark_mkHash (o : OracleName) (q : domOf lam L o) (h : NoW o) :
    ghostMark W mkHash o q = mkRun (K := W.K) (L := L) o q := by
  cases o with
  | fb t =>
    show mkHash (K := W.K) (L := L) (ghost W (.fb t) q).1 (ghost W (.fb t) q).2.1 = true
    rcases hc : cls W t q with _ | k
    · rw [ghost_fb_zero W hc]
      rfl
    · rw [ghost_fb_succ W hc]
      rfl
  | fbw t k => exact h.elim
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

theorem ghostMark_mkTable (o : OracleName) (q : domOf lam L o) (h : NoW o) :
    ghostMark W mkTable o q = mkTab (K := W.K) (L := L) o q := by
  cases o with
  | fb t =>
    show mkTable (K := W.K) (L := L) (ghost W (.fb t) q).1 (ghost W (.fb t) q).2.1 = false
    rcases hc : cls W t q with _ | k
    · rw [ghost_fb_zero W hc]
      rfl
    · rw [ghost_fb_succ W hc]
      rfl
  | fbw t k => exact h.elim
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

variable {α : Type}

theorem runDefer_plain_run (c : StT lam W.K L α) (vs : List Bits) (T : Table (typedOracleFamily lam W.K L))
    (lg : Trace (typedOracleFamily lam W.K L)) :
    (plainOf c vs).runDefer (ghostMark W mkHash) T lg = (plainOf c vs).runDefer mkRun T lg :=
  OComp.runDefer_congr ((asksIn_realQ (erase c vs)).mono fun o q h => ghostMark_mkHash W o q h) T lg

theorem runDefer_plain_tab (c : StT lam W.K L α) (vs : List Bits) (T : Table (typedOracleFamily lam W.K L))
    (lg : Trace (typedOracleFamily lam W.K L)) :
    (plainOf c vs).runDefer (ghostMark W mkTable) T lg = (plainOf c vs).runDefer mkTab T lg :=
  OComp.runDefer_congr ((asksIn_realQ (erase c vs)).mono fun o q h => ghostMark_mkTable W o q h) T
    lg

/-! ## A log's entries -/

theorem notLeaf_ghostQA (e : QA (typedOracleFamily lam W.K L)) : notLeaf (ghostQA W e) = notLeaf e := by
  obtain ⟨o, q, r⟩ := e
  cases o with
  | fb t =>
    rcases h : cls W t q with _ | k
    · rw [ghostQA_fb_zero W h]
    · rw [ghostQA_fb_succ W h]
      rfl
  | fbw t k =>
    by_cases h : cls W t q = k + 1
    · rw [ghostQA_fbw_pos W h]
      rfl
    · rw [ghostQA_fbw_neg W h]
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

theorem filter_notLeaf_ghost (l : Trace (typedOracleFamily lam W.K L)) :
    ((l.map (ghostQA W)).filter notLeaf).map (ghostQA W) = l.filter notLeaf := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.map_cons]
    cases he : notLeaf e with
    | true =>
      rw [List.filter_cons_of_pos (by rw [notLeaf_ghostQA, he]), List.filter_cons_of_pos he,
        List.map_cons, ghostQA_ghostQA, ih]
    | false =>
      rw [List.filter_cons_of_neg (by rw [notLeaf_ghostQA, he]; simp),
        List.filter_cons_of_neg (by rw [he]; simp), ih]

/-- every entry is a leaf's -/
def AllLeaf {K : ℕ} (l : Trace (typedOracleFamily lam K L)) : Prop :=
  ∀ e ∈ l, (e.1 : OracleName) = TypedOracleCompiler.Compile.Batch.OracleName.leaf

theorem map_ghostQA_allLeaf {l : Trace (typedOracleFamily lam W.K L)} (h : AllLeaf l) :
    l.map (ghostQA W) = l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have he : ghostQA W e = e := by
      obtain ⟨o, q, r⟩ := e
      obtain rfl : o = TypedOracleCompiler.Compile.Batch.OracleName.leaf := h _ List.mem_cons_self
      rfl
    rw [List.map_cons, he, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

theorem AllLeaf.append {K : ℕ} {l l' : Trace (typedOracleFamily lam K L)} (h : AllLeaf l) (h' : AllLeaf l') :
    AllLeaf (l ++ l') := fun e he =>
  (List.mem_append.mp he).elim (h e) (h' e)

theorem allLeaf_laidTree {K : ℕ} {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool)
    (T : TreeK lam L) : AllLeaf (laidTree (K := K) posAt rd T) := by
  intro e he
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
  rfl

theorem allLeaf_laidTrees {K : ℕ} {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) :
    ∀ (k : ℕ) (Ts : List (TreeK lam L)), AllLeaf (laidTrees (K := K) posAt rd k Ts)
  | _, [] => fun _ he => absurd he List.not_mem_nil
  | k, T :: Ts => (allLeaf_laidTree (posAt k) rd T).append (allLeaf_laidTrees posAt rd (k + 1) Ts)

theorem allLeaf_laidK {K : ℕ} : ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A)
    (kp : Kept lam L s) (rd : OPos s → Bool), AllLeaf (laidK s A Ws kp rd)
  | [], _, _, _, _ => fun _ he => absurd he List.not_mem_nil
  | _ :: s, (_, A), (w, Ws), (kp, ks), _ =>
    (allLeaf_laidTrees w.posAtJ _ 0 kp.2.2).append
      ((allLeaf_laidTrees w.posAt0 _ 0 kp.2.1).append (allLeaf_laidK s A Ws ks _))

theorem allLeaf_extLaid {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (x : Y) (xt : ℕ → TreeK lam L) (ρ : Rho Q.loc.shape) :
    AllLeaf (extLaid Q wq x xt ρ) := by
  intro e he
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
  rfl

end OnBytes.LateSide

#print axioms OnBytes.LateSide.runDefer_plain_run
#print axioms OnBytes.LateSide.runDefer_plain_tab
