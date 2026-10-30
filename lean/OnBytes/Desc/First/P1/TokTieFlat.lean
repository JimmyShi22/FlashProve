-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TokTieFlat.lean: WHERE THE FLAT FUNCTION OF A TOKEN SUMCHECK RETURNS, IT HAS
HEARD A TRANSCRIPT OF THE TYPED SUMCHECK. `tok_tie` (OnBytes/Tie/Pv/Lay/SumTop.lean) says
this of the program `verify-on-bytes`'s routine in a context. Here it is said of `Fl.tscIn`
(OnBytes/K/Kc/Flat.lean), which the layers' own text runs. Statements and proofs.

NO NEW ARGUMENT: `tok_tie`'s own proof behind the routine's seam, with `tsc_ended` (TscEnded.lean,
beside this file) in its place. CALLED: `sum_said`, `sizes_of`
(OnBytes/Tie/Pv/Lay/SumSaid.lean), `tok_fits`, `tok_weights` (SumTop.lean), `sum_end_world`
(SumTie.lean), `Road.hideRun_ok` (OnBytes/Tie/Pv/Psc/Run/PscHide.lean). `tok_tie` and `sum_tie` are
not called. Whether what is called reaches a routine or a context of `verify-on-bytes` is left to a
walk through the constants under this file's theorems: this file claims nothing of it.

  `tsc_sizes`: each of a token sumcheck's rounds sent one scalar fewer than its weight's degree; the
    further round sent dY.
  `tok_tie_flat`: for parameters `SumL` all of whose variables are of degree 2 and in the equality
    form at the readings of the text's point: if `Fl.tscIn P L.S.k shown L.M.DY F t` returns (o, G,
    u), the ledger F has arrays of the right sizes, and the reading of the further challenge is not
    0: there are end values v, shown many (TIED TO THE TAPE NOWHERE HERE); `SumSaid` holds of the
    typed output at the record o.p; and the typed claim on an end value holds exactly if the map at
    the output's point is what that end value's slot is worth in G's world, for entries whose places
    are the slots' mask entries.

Limits. One direction: from a return. PREMISES: `Road.Sized F`; hn, hw, num, hnum as in `tok_tie`;
hβ: THAT THE READING OF THE FURTHER CHALLENGE IS NOT 0: not shown here. `Fl.tscIn` makes no row:
`SumSaid.row` serves for the row that a caller makes. NOT HERE, OF WHAT `tok_tie` SAYS: that the
reading of the record's target is the reading of the claimed sum that was sent.
-/
import OnBytes.Desc.First.P1.TscEnded
import OnBytes.Tie.Pv.Lay.SumTop
import OnBytes.Tie.Pv.Lay.SumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight)

/-- What a token sumcheck's rounds sent, by number. -/
theorem tsc_sizes {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    (tscRs P lt t).map (·.1.length) = (tscWs (P.toList.take lt)).map (fun w => w.d - 1) ∧
      (tscY P lt dY t).2.1.length = dY := by
  obtain ⟨_, a1, hy, _, hlens, _⟩ := tscIn_heard h
  constructor
  · refine sizes_of _ _ ?_ ?_
    · unfold tscRs
      rw [List.length_map, ← a1, List.length_map]
    · intro x hx
      unfold tscRs at hx
      rw [← a1, zip_maps] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact hlens m (List.mem_append_left _ hm)
  · have e := hlens (tscY P lt dY t) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    rw [hy] at e
    have e' : (tscY P lt dY t).2.1.length + 1 = dY + 1 := e
    omega

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **Where the flat function of a token sumcheck returns, it has heard a transcript of the typed
sumcheck.** -/
theorem tok_tie_flat (L : SumL K) {P : Array E} {shown : ℕ} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P L.S.k shown L.M.DY F t = some (o, G, u))
    (hs : OnBytes.Model.Road.Sized F) (hβ : ρ.val (tscY P L.S.k L.M.DY t).2.2 ≠ 0) (st : L.St)
    (hn : ∀ i, L.M.n i = 2)
    (hw : ∀ i : Fin L.S.k, L.S.w st i = some (ρ.val ((P.toList.take L.S.k).getD i.1 zeroE)))
    (num : L.S.A → ℕ) (hnum : ∀ a, num a < shown) :
    ∃ v : Array E, v.size = shown ∧
      SumSaid ρ L (F₀ L.T.par) st o.p
        (tscWs (P.toList.take L.S.k) ++ [Weight.atZero (L.M.DY + 1)]) (tapeMu2 t)
        (tscRs P L.S.k t) (tscY P L.S.k L.M.DY t).2.1 (tscY P L.S.k L.M.DY t).2.2 hβ
        (fun a => ρ.val (v.toList.getD (num a) zeroE)) ∧
      ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : L.J → K),
        (∀ a, m (L.M.cAt a) = mask (o.sEnd + num a)) → ∀ a : L.S.A,
        (L.T.par.EHolds
            (sumOut ρ L (F₀ L.T.par) st o.p.target (tapeMu2 t) o.p.eps (tscRs P L.S.k t)
              (tscY P L.S.k L.M.DY t).2.1 (tscY P L.S.k L.M.DY t).2.2 hβ
              fun a => ρ.val (v.toList.getD (num a) zeroE)) m a ↔
          L.S.F st m a
              (L.Q.outPt L.M
                (sumOut ρ L (F₀ L.T.par) st o.p.target (tapeMu2 t) o.p.eps (tscRs P L.S.k t)
                  (tscY P L.S.k L.M.DY t).2.1 (tscY P L.S.k L.M.DY t).2.2 hβ
                  fun a => ρ.val (v.toList.getD (num a) zeroE))) =
            (G.worldOf ρ mask entry).slot (o.sEnd + num a)) := by
  obtain ⟨hlt, _, _, _, _, _, _, _, _, _, _, _, _, v, G0, hG0, _, _, _, hvn, hG⟩ := tscIn_heard h
  obtain ⟨z1, z2⟩ := tsc_sizes h
  have hl : (tscRs P L.S.k t).map (·.1.length) = List.ofFn L.M.n := by
    rw [z1, tscWs_eq, tok_weights P L.S.k hlt, List.map_ofFn]
    congr 1
    funext i
    exact (hn i).symm
  have s0 := (OnBytes.Model.Road.hideRun_ok _ G0 F.next #[tapeCl t] oneE hG0
    ⟨hs.vp, hs.mf, hs.got⟩).sized
  have hFl := OnBytes.Model.Road.hideRun_ok _ G o.sEnd v (tscY P L.S.k L.M.DY t).2.2 hG
    ⟨s0.vp, s0.mf, s0.got⟩
  refine ⟨v, hvn,
    sum_said ρ L (F₀ L.T.par) st (tsc_ended h) hβ _ (tok_fits ρ L st P hlt hn hw) hl z2, ?_⟩
  intro mask entry m hm a
  exact sum_end_world ρ L (F₀ L.T.par) st _ _ _ _ _ _ hβ v.toList num
    (fun a => by rw [Array.length_toList, hvn]; exact hnum a) _ G o.sEnd hFl mask entry m hm a

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tsc_sizes
#print axioms OnBytes.Desc.First.P1.tok_tie_flat
