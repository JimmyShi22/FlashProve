-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/StackTieFlat.lean: WHERE THE BATCHED SUMCHECK OF THE LAYERS' OWN ROUNDS
RETURNS, IT HAS HEARD A TRANSCRIPT OF THE TYPED BATCHED SUMCHECK. The theorem `plain2_tie`
(OnBytes/Tie/Pv/Lay/SumTop.lean) says this of rounds heard in a context of `verify-on-bytes`. Here
it is said of `hearStack` (OnBytes/Desc/First/K4/Hear.lean) over the plain engine, for every value
of the typed parameters `InnL` (Cb/Pv/Lay/Inner.lean) with as many variables. Statements and proofs.

NO NEW ARGUMENT: the recipe of LevelTieFlat.lean and TokTieFlat.lean (OnBytes/Desc/First/P1/), with
`stack_ended` (StackEnded.lean, beside this file). CALLED: `sum_said`, `sizes_of`
(OnBytes/Tie/Pv/Lay/SumSaid.lean), `plain2_fits` (SumTop.lean), `sum_end_world` (SumTie.lean),
`Road.hideRun_ok` (OnBytes/Tie/Pv/Psc/Run/PscHide.lean). `plain2_tie` and `sum_tie` are not called.
Whether what is called reaches a routine or a context of `verify-on-bytes` is for the walk by
constants to say: this file claims nothing of it.

  `stack_sizes`: each of the sumcheck's rounds sent one scalar fewer than its weight's number of
    coefficients; the further round sent two.
  `stack_tie_flat`: for every `InnL` L, every state st and every numbering num of L's revealed maps
    below the number of end values: if `hearStack engFl P v H L.k NCLp F t` returns (S, G, u), the
    ledger F has arrays of the right sizes, and the reading of the further challenge is not 0: there
    are the end values vals, WHOSE LIST IS WHAT THE TAPE'S ROUND OF THE END VALUES SENT
    (`stackVals`), and the ledger G1 behind them (fixed by a `hideRun` equation); the text's row is
    the form of the record `stackRec` at the product of the two end elements, nothing kept;
    `SumSaid` holds of the typed output at that record, the rounds `stackRs` and the end values read
    under num, UNDER THE PICK `pick` (Cb/Pv/Lay/Merge.lean), which leaves out the linear
    coefficient; and the typed claim on an end value holds exactly if the map at the output's point
    is what that end value's slot is worth in G1's world, for entries whose places are the slots'
    mask entries.

Limits. One direction: from a return. PREMISES: `Road.Sized F`; hnum; hβ: THAT THE READING OF THE
FURTHER CHALLENGE IS NOT 0: not shown here. num IS A FREE LETTER: which end value is which revealed
map is not said. THE ROW'S EQUIVALENCE IS NOT STATED: `SumSaid.row` gives it to a caller who pays
that the pick is lawful and (D1) to (D4); of these (D3) asks that the kept terms sum to 0 (the text
keeps nothing) and (D4) that the typed summand at the end values is the reading of the product of
the two end elements: what these two are is not said here. That a value of `InnL` fits the text's
start form, target and panels is not said. Nothing is said on the image of a written transcript
(`Maps.view`).
-/
import OnBytes.Desc.First.K4.StackEnded
import OnBytes.Tie.Pv.Lay.SumTop
import OnBytes.Tie.Pv.Lay.SumTie
import Cb.Pv.Lay.Inner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open Iop Prob Cb TWhole OnBytes OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork Reading)
open OnBytes.Desc.First.P1 (tapeMu zip_maps)

/-- What the batched sumcheck's rounds sent, by number. -/
theorem stack_sizes {P : Model.Layer.Pub} {v : Model.Layer.Env} {H : Model.Layer.Heard}
    {lamS NCLp : Nat} {F G : Fork} {t u : Tape} {S : Model.Layer.HeardStack}
    (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    (stackRs lamS t).map (·.1.length) = (P1.plainWs lamS).map (fun w => w.d - 1) ∧
      (stackY lamS t).2.1.length = 2 := by
  obtain ⟨a1, _, hlens, _⟩ := stack_heard h
  constructor
  · refine sizes_of _ _ ?_ ?_
    · unfold stackRs
      rw [List.length_map, ← a1, List.length_map]
    · intro x hx
      unfold stackRs at hx
      rw [← a1, zip_maps] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact hlens m (List.mem_append_left _ hm)
  · have e := hlens (stackY lamS t) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have e' : (stackY lamS t).2.1.length + 1 = 3 := e
    omega

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **Where the batched sumcheck of the layers' own rounds returns, it has heard a transcript of the
typed batched sumcheck.** -/
theorem stack_tie_flat (L : InnL K) {P : Model.Layer.Pub} {v : Model.Layer.Env}
    {H : Model.Layer.Heard} {NCLp : Nat} {F G : Fork} {t u : Tape} {S : Model.Layer.HeardStack}
    (h : hearStack engFl P v H L.k NCLp F t = some (S, G, u))
    (hs : OnBytes.Model.Road.Sized F) (hβ : ρ.val (stackY L.k t).2.2 ≠ 0) (st : L.St)
    (num : L.A → ℕ) (hnum : ∀ a, num a < 2 + (1 + P.y.LamM) + NCLp) :
    ∃ (vals : Array E) (G1 : Fork), vals.toList = stackVals L.k t ∧
      ({ F with next := F.next + 1 + 2 * L.k + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork).hideRun
        S.sA0 vals (stackY L.k t).2.2 = some G1 ∧
      S.rowS = (stackRec v H L.k F t).rowForm (mulE S.fin.As S.fin.Bs) {} ∧
      SumSaid ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st (stackRec v H L.k F t)
        (P1.plainWs L.k ++ [Weight.atZero (2 + 1)]) (tapeMu (t.drop 1)) (stackRs L.k t)
        (stackY L.k t).2.1 (stackY L.k t).2.2 hβ
        (fun a => ρ.val (vals.toList.getD (num a) zeroE)) ∧
      ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : L.J → K),
        (∀ a, m (L.cAt a) = mask (S.sA0 + num a)) → ∀ a : L.A,
        (L.toSum.T.par.EHolds
            (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
              (stackRec v H L.k F t).target (tapeMu (t.drop 1)) (stackRec v H L.k F t).eps
              (stackRs L.k t) (stackY L.k t).2.1 (stackY L.k t).2.2 hβ
              fun a => ρ.val (vals.toList.getD (num a) zeroE)) m a ↔
          L.toSum.S.F st m a
              (L.toSum.Q.outPt L.toSum.M
                (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
                  (stackRec v H L.k F t).target (tapeMu (t.drop 1)) (stackRec v H L.k F t).eps
                  (stackRs L.k t) (stackY L.k t).2.1 (stackY L.k t).2.2 hβ
                  fun a => ρ.val (vals.toList.getD (num a) zeroE))) =
            (G1.worldOf ρ mask entry).slot (S.sA0 + num a)) := by
  obtain ⟨_, _, _, hrow, _, vals, G1, hvl, hvs, hG1, _⟩ := stack_heard h
  obtain ⟨z1, z2⟩ := stack_sizes h
  have hl : (stackRs L.k t).map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [z1]
    show (List.replicate L.k (Weight.plain 3)).map (fun w => w.d - 1) =
      List.ofFn fun _ : Fin L.k => 2
    rw [List.map_replicate, List.ofFn_const]
    rfl
  have hFl := OnBytes.Model.Road.hideRun_ok _ G1 S.sA0 vals (stackY L.k t).2.2 hG1
    ⟨hs.vp, hs.mf, hs.got⟩
  refine ⟨vals, G1, hvl, hG1, hrow,
    sum_said ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st (stack_ended h) hβ _
      (plain2_fits ρ L.toSum st (fun _ => rfl) fun _ => rfl) hl z2, ?_⟩
  intro mask entry m hm a
  exact sum_end_world ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st _ _ _ _ _ _ hβ
    vals.toList num (fun a => by rw [Array.length_toList, hvs]; exact hnum a) _ G1 S.sA0 hFl mask
    entry m hm a

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.stack_sizes
#print axioms OnBytes.Desc.First.K4.stack_tie_flat
