-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/LevelTieFlat.lean: WHERE THE FLAT FUNCTION OF A PRODUCT LAYER RETURNS, IT HAS
HEARD A TRANSCRIPT OF THE TYPED PRODUCT LAYER. The theorem `level_tie`
(OnBytes/Tie/Pv/Lay/LevelTie.lean) says this of the program `verify-on-bytes`'s routine in a
context. Here it is said of `Fl.levelIn` (OnBytes/K/Kc/Flat.lean), which the layers' own text runs;
general in mu, rho, C and the order. Statements and proofs.

NO NEW ARGUMENT: `level_tie`'s own proof behind its first three lines, with `level_ended`
(LevelEnded.lean, beside this file) in the place of the routine's seam. CALLED: `sum_said`,
`sizes_of`, `map_ofFn` (OnBytes/Tie/Pv/Lay/SumSaid.lean), `level_fits`, `lvNum` (LevelTie.lean),
`sum_end_world` (SumTie.lean), `Road.hideRun_ok` (OnBytes/Tie/Pv/Psc/Run/PscHide.lean). Also
`SumSaid.row` (SumSaid.lean), `F₀_ok` (Cb/G6/Pick.lean), `ProdL.eq0` (Cb/Pv/Lay/Prod.lean),
`Road.Filled.here`. `level_tie` itself is not called. WHETHER WHAT IS CALLED REACHES A ROUTINE OR A
CONTEXT OF `verify-on-bytes` IS FOR THE WALK BY CONSTANTS TO SAY, from this file's own theorems: a
separate print: this file claims nothing of it.

  `level_sizes`: each of a layer's rounds sent one scalar fewer than its weight's degree; the
    further round sent two.
  `level_tie_flat`: for every `ProdL` L with as many variables and every state st at which the typed
    equality point, at the coordinate that round j binds, is the reading of the text's coordinate
    for the j-th member of the order: if `Fl.levelIn L.k rho C order F t` returns (o, G, u), the
    ledger F has arrays of the right sizes, and the reading of the further challenge is not 0: there
    are two end values v and the ledger F1 behind them (a `hideRun` equation fixes F1 from v; v
    ITSELF IS TIED TO THE TAPE NOWHERE HERE: Johnson/Road/K4/OwnRowsLevel.lean has the end values as
    the tape's words); `SumSaid` holds of the typed output at the record `levelRec …`, the rounds
    `levelRs …` and the end values read; the layer's row is worth 0 exactly if the typed row claim
    holds, for every world and all entries with (D1): the typed hiding coefficients are the world's
    values under the sumcheck's own slots, and (D2): the typed incoming form is the target's reading
    less the start form's worth; and the typed claim on an end value holds exactly if the map at the
    output's point is what that end value's slot is worth in F1's world, for entries whose places
    are the slots' mask entries.

Limits. One direction: from a return. THREE PREMISES: `Road.Sized F`; the premise on the point (hp);
THAT THE READING OF THE FURTHER CHALLENGE IS NOT 0 (hβ): on the tape that round's drawn word is not
the zero word; that its reading is not 0 wants the words canonical: not shown here. (D1) and (D2)
are premises of the row's equivalence, as in `level_tie`. Nothing is said on the image of a written
transcript (`Maps.view`).
-/
import OnBytes.Desc.First.P1.LevelEnded
import OnBytes.Tie.Pv.Lay.LevelTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight)

/-- What a layer's rounds sent, by number. -/
theorem level_sizes {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    (levelRs mu rho order t).map (·.1.length) = (levelWs mu rho order).map (fun w => w.d - 1) ∧
      (levelY mu t).2.1.length = 2 := by
  obtain ⟨_, _, _, a1, hy, _, hlens, _⟩ := levelIn_heard h
  constructor
  · refine sizes_of _ _ ?_ ?_
    · unfold levelRs
      rw [List.length_map, ← a1, List.length_map]
    · intro x hx
      unfold levelRs at hx
      rw [← a1, zip_maps] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact hlens m (List.mem_append_left _ hm)
  · have e := hlens (levelY mu t) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    rw [hy] at e
    have e' : (levelY mu t).2.1.length + 1 = 3 := e
    omega

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **Where the flat function of a product layer returns, it has heard a transcript of the typed
product layer.** -/
theorem level_tie_flat (L : ProdL K) {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {o : Level} (h : Fl.levelIn L.k rho C order F t = some (o, G, u))
    (hs : OnBytes.Model.Road.Sized F) (hβ : ρ.val (levelY L.k t).2.2 ≠ 0) (st : L.St)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE)) :
    ∃ (v : Array E) (F1 : Fork), v.size = 2 ∧
      ({ F with next := F.next + 1 + 2 * L.k + 2 + 2 } : Fork).hideRun o.sL v
        (levelY L.k t).2.2 = some F1 ∧
      SumSaid ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t)
        (levelWs L.k rho order ++ [Weight.atZero (2 + 1)]) (tapeMu t) (levelRs L.k rho order t)
        (levelY L.k t).2.1 (levelY L.k t).2.2 hβ
        (fun b => ρ.val (v.toList.getD (lvNum b) zeroE)) ∧
      (∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
        L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st)
          (levelRec L.k rho C order F t).first →
        L.toSum.T.par.inc st m = ρ.val (levelRec L.k rho C order F t).target -
          (levelRec L.k rho C order F t).start.value ρ W →
        (o.row.value ρ W = 0 ↔
          L.toSum.T.par.UHolds
            (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
              (tapeMu t) (levelRec L.k rho C order F t).eps (levelRs L.k rho order t)
              (levelY L.k t).2.1 (levelY L.k t).2.2 hβ
              fun b => ρ.val (v.toList.getD (lvNum b) zeroE)) m)) ∧
      ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : L.J → K),
        (∀ b, m (L.cAt b) = mask (o.sL + lvNum b)) → ∀ b : Bool,
        (L.toSum.T.par.EHolds
            (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
              (tapeMu t) (levelRec L.k rho C order F t).eps (levelRs L.k rho order t)
              (levelY L.k t).2.1 (levelY L.k t).2.2 hβ
              fun b => ρ.val (v.toList.getD (lvNum b) zeroE)) m b ↔
          L.toSum.S.F st m b
              (L.toSum.Q.outPt L.toSum.M
                (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
                  (tapeMu t) (levelRec L.k rho C order F t).eps (levelRs L.k rho order t)
                  (levelY L.k t).2.1 (levelY L.k t).2.2 hβ
                  fun b => ρ.val (v.toList.getD (lvNum b) zeroE))) =
            (F1.worldOf ρ mask entry).slot (o.sL + lvNum b)) := by
  obtain ⟨ho, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, hv2, hF1, hrow, _⟩ :=
    levelIn_heard h
  obtain ⟨z1, z2⟩ := level_sizes h
  have hl : (levelRs L.k rho order t).map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [z1]
    show (order.map fun v => Weight.equality (rho.getD (L.k - 1 - v) zeroE) 3).map _ = _
    rw [List.map_map, map_ofFn _ 0 L.k order ho]
    rfl
  have hFl := OnBytes.Model.Road.hideRun_ok _ F1 o.sL v (levelY L.k t).2.2 hF1
    ⟨hs.vp, hs.mf, hs.got⟩
  have hh0 := (hFl.here 0 (by rw [Array.length_toList, hv2]; omega)).1
  have hh1 := (hFl.here 1 (by rw [Array.length_toList, hv2]; omega)).1
  rw [Nat.add_zero] at hh0
  have s := sum_said ρ L.toSum (F₀ L.toSum.T.par) st (level_ended h) hβ
    (fun b => ρ.val (v.toList.getD (lvNum b) zeroE)) (level_fits ρ L st rho order ho hp) hl z2
  have hD4 : ∀ z, L.toSum.S.pol st z (fun b => ρ.val (v.toList.getD (lvNum b) zeroE)) =
      ρ.val (mulE (v.toList.getD 0 zeroE) (v.toList.getD 1 zeroE)) := by
    intro z
    rw [ρ.mul]
    show ([(1 : K) * [ρ.val (v.toList.getD (lvNum false) zeroE),
      ρ.val (v.toList.getD (lvNum true) zeroE)].prod]).sum = _
    simp [lvNum]
  refine ⟨v, F1, hv2, hF1, s, ?_, ?_⟩
  · intro Ex y W m D1 D2
    rw [hrow, hh0, hh1]
    exact s.row ρ (F₀_ok _ (L.eq0 : Eq0 L.toSum.T.par)) Ex y W _ {} m D1 D2
      (by
        rw [Aff.value_empty]
        exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) (hD4 _)
  intro mask entry m hm b
  exact sum_end_world ρ L.toSum (F₀ L.toSum.T.par) st _ _ _ _ _ _ hβ v.toList lvNum
    (fun b => by rw [Array.length_toList, hv2]; cases b <;> simp [lvNum]) _ F1 o.sL hFl mask
    entry m hm b

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.level_sizes
#print axioms OnBytes.Desc.First.P1.level_tie_flat
