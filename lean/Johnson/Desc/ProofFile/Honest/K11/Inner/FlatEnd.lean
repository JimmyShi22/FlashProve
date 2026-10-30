-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/FlatEnd.lean: THE LIBRARY's FLAT TEXT OF THE MERGE RETURNS
on rounds that are written out: `flatForkEnd` (OnBytes/K/Kc/QuietLink.lean), and what it hands back.
Lemmas with their proofs; the text is the verifier's; no prover is named.

The steps are the library's: `batch_returns` (OnBytes/Desc/First/P1/BatchPoint.lean),
`pscBegin_returns`, `pscRound_returns`, `pscEnds_returns` (OnBytes/Desc/First/P1/Returns.lean). New
here: a plain round of degree 2, the lk rounds in the column bits, and the chain of all.

  `headMerge_roundIn`   one plain round of degree 2
  `headMerge_rounds`    the rounds in the column bits
  `headMerge_merge`     `Fl.wsForkMerge`
  `headMerge_flatEnd`   `flatForkEnd`

Limits. That the end value goes under its slot, and that it is then shown there, are premises.
Nothing on soundness, on an honest prover or on any property.
-/
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Top.H0.MergeLaw.Fits
import OnBytes.Desc.First.P1.Returns
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E addE mulE zeroE)
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork Psc WsLay WsClaim WsForkOut WsMerged wsForkStart wsRowPart wsEpsT powers
  RoundName)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.Desc.First.P1 (bind_eq must_eq need_eq ask_eq pscBegin_returns pscRound_returns
  pscEnds_returns batch_returns rd stepP runP runP_cons endP Rnd Held stepP_ended runP_marks)
open Johnson.Desc.First.ForkMerge (claimFits)

theorem held_plain_three : Held (Weight.plain 3) :=
  ⟨(OnBytes.PscRun.fits_plain 3).mpr (by omega), OnBytes.PscRun.weightHeld_plain 3 (by omega)⟩

/-- One plain round of degree 2. -/
theorem headMerge_roundIn {p : Psc} (hp : p.ended = false) (k : Nat) {sent : List E}
    (hl : sent.length = 2) (r : E) (F : Fork) (u : Tape) :
    Fl.roundIn .sum2 p zeroE 0 F (rd (k, sent, r) :: u) =
      some ((r, stepP p (Weight.plain 3, sent, r)), { F with next := F.next + 2 }, u) := by
  unfold Fl.roundIn
  refine bind_eq (must_eq (by rw [hp]; rfl) _ _) ?_
  refine bind_eq (need_eq (a := Weight.plain 3) rfl _ _) ?_
  exact pscRound_returns p held_plain_three _ 0 k (by show sent.length + 1 = 3; omega) r F u

/-- A round's number of batched rows, what it sends and what it draws, as a round of a plain
variable with three coefficients. -/
def plainRnd (x : Nat × List E × E) : Rnd := (Weight.plain 3, x.2.1, x.2.2)

/-- The rounds in the column bits. -/
theorem headMerge_rounds : ∀ (xs : List (Nat × List E × E)) (rm : Array E) (p : Psc) (F : Fork)
    (u : Tape), (∀ x ∈ xs, x.2.1.length = 2) → p.ended = false →
    Fl.wsForkRounds xs.length rm p F (xs.map rd ++ u) =
      some (((rm.toList ++ xs.map (·.2.2)).toArray, runP p (xs.map plainRnd)),
        { F with next := F.next + 2 * xs.length }, u)
  | [], rm, p, F, u, _, _ => by
    have e1 : (rm.toList ++ ([] : List (Nat × List E × E)).map (·.2.2)).toArray = rm := by simp
    rw [e1]
    rfl
  | x :: xs, rm, p, F, u, hx, hp => by
    have ih := headMerge_rounds xs (rm.push x.2.2) (stepP p (plainRnd x))
      { F with next := F.next + 2 } u (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      ((stepP_ended p _).trans hp)
    have e1 : ((rm.push x.2.2).toList ++ xs.map (·.2.2)).toArray =
        (rm.toList ++ (x :: xs).map (·.2.2)).toArray := by simp
    have e2 : F.next + 2 + 2 * xs.length = F.next + 2 * (x :: xs).length := by
      rw [List.length_cons]
      omega
    show Fl.wsForkRounds (xs.length + 1) rm p F (rd x :: (xs.map rd ++ u)) = _
    unfold Fl.wsForkRounds
    refine bind_eq (headMerge_roundIn hp x.1 (hx x List.mem_cons_self) x.2.2 F
      (xs.map rd ++ u)) ?_
    rw [← e1, List.map_cons, runP_cons, ← e2]
    exact ih

/-- The record in front of the rounds. -/
def beginP (sv : Array Nat) (x T mu eps : E) (first : Nat) : Psc :=
  { target := T, first := first, eps := eps, claim := addE mu (mulE eps T)
    start := wsForkStart sv (powers x sv.size), started := true }

/-- The tape of a merge: the batching round; the beginning; the rounds in the column bits; the round
in the further variable; the end value. -/
def mergeTapeOf (n : Nat) (x mu eps : E) (w0 : Nat) (xs : List (Nat × List E × E)) (wY : Nat)
    (c beta : E) (wV : Nat) (v : E) : Tape :=
  ⟨some RoundName.batSigma.name, 0, n, [], [x]⟩ ::
    ⟨some RoundName.pscEpsilon.name, 0, w0, [mu], [eps]⟩ ::
    (xs.map rd ++ [⟨some RoundName.pscY.name, 1, wY, [c], [beta]⟩,
      ⟨some RoundName.pscValues.name, 0, wV, [v], []⟩])

/-- `Fl.wsForkMerge` returns. -/
theorem headMerge_merge (lk : Nat) (sv : Array Nat) (F G : Fork) (x mu eps c beta v T fvp : E)
    (w0 wY wV : Nat) (xs : List (Nat × List E × E)) (hn : sv.size ≠ 0) (hxl : xs.length = lk)
    (hx : ∀ y ∈ xs, y.2.1.length = 2)
    (hT : F.publicPart (wsForkStart sv (powers x sv.size)) = some T)
    (hG : ({ F with next := F.next + 1 + 2 * lk + 1 + 1 } : Fork).hideRun (F.next + 1 + 2 * lk + 1)
      #[v] beta = some G)
    (hsh : G.shown (F.next + 1 + 2 * lk + 1) = some fvp) :
    Fl.wsForkMerge lk sv F (mergeTapeOf sv.size x mu eps w0 xs wY c beta wV v) =
      some ((({ fvp := fvp
                beta := (endP (beginP sv x T mu eps F.next) (xs.map plainRnd)
                  (Weight.atZero 2, [c], beta)).r.back?.getD zeroE
                rm := ((Array.emptyWithCapacity lk : Array E).toList ++ xs.map (·.2.2)).toArray
                p := endP (beginP sv x T mu eps F.next) (xs.map plainRnd)
                  (Weight.atZero 2, [c], beta)
                sFv := F.next + 1 + 2 * lk + 1 } : WsMerged), powers x sv.size), G, []) := by
  have hr := headMerge_rounds xs (Array.emptyWithCapacity lk) (beginP sv x T mu eps F.next)
    { F with next := F.next + 1 }
    [⟨some RoundName.pscY.name, 1, wY, [c], [beta]⟩,
      ⟨some RoundName.pscValues.name, 0, wV, [v], []⟩] hx rfl
  rw [hxl] at hr
  have hp : (runP (beginP sv x T mu eps F.next) (xs.map plainRnd)).ended = false :=
    (runP_marks _ _).1
  unfold Fl.wsForkMerge mergeTapeOf
  refine bind_eq (batch_returns hn F x _) ?_
  refine bind_eq (pscBegin_returns hT mu eps w0 _) ?_
  refine bind_eq hr ?_
  refine bind_eq (pscEnds_returns hp (le_refl 1) (le_refl 1) wY wV (sent := [c]) rfl beta
    (v := #[v]) rfl [] hG) ?_
  refine bind_eq (ask_eq hsh _) ?_
  rfl

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headMerge_merge
