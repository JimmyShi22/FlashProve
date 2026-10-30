-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReturnsLeft.lean: the returns of leftP (LeftIs, Att/K5LeftAll.lean) and of
pointsOf at every hearing that Said (Att/K5SaidAll.lean)
speaks of, from the public record on the place's seven units (UnitsAll, Att/K05UnitsOk.lean) and the
key points' lengths.

Main names:
  `planesAt_len`, `inner_bits`, `unit_inner`, `scoreW_ret`, `inner_lens`: a unit's inner point has
    its family's length; so the guard of scoreW passes.
  `leftIs_ret`: there is l with LeftIs (geoOf S) zk h G l.
  `points_at`: and pointsOf (geoOf S) zk h l returns.

Premises: UnitsAll; the shape's Norm; 1 ≤ lnT; each of the four key points has as many coordinates
as its call has key bits; P.D = dimOf S; Said at
recOf P rows; the ledger is Sized; for points_at also PlaceIs and two plane messages.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PointsRet
import Johnson.Desc.First.Att.K05UnitsOk
import Johnson.Desc.First.Att.K05UnitsAll
import Johnson.Desc.First.Att.K05Row
import Johnson.Desc.First.Att.Claims.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Tie.Pv.Att (PscH recOf)
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.Part

theorem planesAt_len {G : Fork} : ∀ {js : List Nat} {vs : List (List E)}, PlanesAt js vs G → js.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, c⟩ => by rw [List.length_cons, List.length_cons, planesAt_len c]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem inner_bits {u : UnitG} {zkc : Array E} (h : u.bits ≤ zkc.size) : (inner u zkc).size = u.bits := by
  unfold inner
  rw [Array.size_extract]
  omega

/-- A unit's inner point has its family's length. -/
theorem unit_inner {D : Dim} {C : Calls} {fam : Fam} {q : Fin 4} {u : UnitG} (I : UnitIs D C fam q u)
    {zk : Array (Array E)} (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = C.a q) :
    (inner u (zk.getD u.call #[])).size = fam.l D := by
  rw [inner_bits (by rw [I.call, Kz q, I.bits]; exact I.le), I.bits]

theorem scoreW_ret {g : Geo} {u : UnitG} {zkc : Array E} (r : Array E)
    (hs : (inner u zkc).size = (if u.below then g.lgk + (g.lnT - 1) + g.lnT else g.lgk + g.lnT) + 2 * g.lB) :
    ∃ W, scoreW g u zkc r = some W ∧ W.size = (weights u zkc).size := by
  unfold scoreW
  simp only [Option.bind_eq_bind, Option.pure_def]
  rw [guard_ret (by simp [hs])]
  exact ⟨_, rfl, by simp⟩

section At
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {r1 r2 u1 u2 wl ix wh : UnitG}

/-- The lengths of the seven inner points, in the place's numbers. -/
theorem inner_lens (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT)
    {zk : Array (Array E)} (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q) :
    (inner u1 (zk.getD u1.call #[])).size = S.cf.lgk + (S.lnT - 1) + S.lnT + 2 * S.cf.lB ∧
    (inner u2 (zk.getD u2.call #[])).size = S.cf.lgk + S.lnT + 2 * S.cf.lB ∧
    (inner wl (zk.getD wl.call #[])).size = 1 + S.cf.lgk + S.cf.lt + S.cf.ldh ∧
    (inner ix (zk.getD ix.call #[])).size = S.cf.lgk + S.cf.lt ∧
    (inner wh (zk.getD wh.call #[])).size = S.cf.lgk + S.cf.lt + S.cf.ldh := by
  have hlt := N.lt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [unit_inner U.m2 Kz]
    show S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB = _
    omega
  · rw [unit_inner U.d2 Kz]
    show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB = _
    omega
  · rw [unit_inner U.w3 Kz]
    show 1 + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh = _
    omega
  · rw [unit_inner U.x3 Kz]
    show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = _
    omega
  · rw [unit_inner U.f4 Kz]
    show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh = _
    omega

variable {K M X : Type} [Field K] [Fintype K]

/-- **leftP's returns, at every hearing that Said speaks of.** -/
theorem leftIs_ret (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT)
    {zk : Array (Array E)} (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q)
    (P : OwnPar K M X) (hD : P.D = dimOf S) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (b2 : Said (recOf P rows) h G L) (b3 : Sized G) : ∃ l, LeftIs (geoOf S) zk h G l := by
  obtain ⟨i1, i2, i3, _, _⟩ := inner_lens U N hl Kz
  obtain ⟨o1, o2, _, _, _, _, hos, _, ⟨_, _, a1, _⟩, ⟨_, _, a2, _⟩⟩ := units_two b2.units
  have hnb : P.D.nb = S.NP := by rw [hD]; rfl
  have hsc : h.scores = #[o1, o2] := by
    apply Array.toList_inj.1
    rw [hos]
  have wsz : ∀ {fam : Fam} {q : Fin 4} {u : UnitG}, UnitIs (dimOf S) (callsOf fs) fam q u → ∀ zkc : Array E,
      (weights u zkc).size = S.NP := fun I zkc => I.nPw zkc
  obtain ⟨W1, w1, s1⟩ := scoreW_ret (g := geoOf S) (u := u1) (zkc := zk.getD u1.call #[]) (chal o1.2)
    (by rw [U.below, if_pos rfl]; exact i1)
  obtain ⟨W2, w2, s2⟩ := scoreW_ret (g := geoOf S) (u := u2) (zkc := zk.getD u2.call #[]) (chal o2.2)
    (by rw [U.on]; exact i2)
  obtain ⟨f1, e1⟩ := left_ret b3 o1.2 W1 (n := 2 * P.D.nb) (by rw [s1, wsz U.m2, hnb]) (ends_of_sumAt a1)
  obtain ⟨f2, e2⟩ := left_ret b3 o2.2 W2 (n := 2 * P.D.nb) (by rw [s2, wsz U.d2, hnb]) (ends_of_sumAt a2)
  obtain ⟨fE, eE⟩ := left_ret b3 h.division
    (wDivision (geoOf S) (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) (n := 2 * P.D.nb)
    (by unfold wDivision; rw [Array.size_map, wsz U.w3, hnb]) (ends_of_sumAt b2.sE)
  obtain ⟨fM, eM⟩ := left_ret b3 h.below
    (wBelow (geoOf S) (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) (n := 2 * P.D.nb)
    (by unfold wBelow; rw [Array.size_map, wsz U.w3, hnb]) (ends_of_sumAt b2.sM)
  obtain ⟨fO, eO⟩ := left_ret b3 h.on
    (wOn (geoOf S) (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) (n := 2 * P.D.nb)
    (by unfold wOn; rw [Array.size_map, wsz U.w3, hnb]) (ends_of_sumAt b2.sVD)
  obtain ⟨fF, eF⟩ := left_ret b3 h.atIndex (wAtIndex (geoOf S) h) (n := 2 * P.D.nb)
    (by unfold wAtIndex; rw [Array.size_map, b2.om]; simp [powersFrom_length, recOf]) (ends_of_sumAt b2.sF)
  obtain ⟨fK, eK⟩ := leftKey_ret b3 (geoOf S) h.key (chal h.atIndex) h.om' (n := P.D.nl + P.D.nb * P.D.lT)
    (le_refl _) (by
      show S.Lam + S.NP * S.cf.lt ≤ _
      rw [hD]
      show _ ≤ S.Lam + S.NP * (S.lnT - 1 + 1 + S.cf.lB)
      rw [← N.lt]) (ends_of_sumAt b2.sD)
  obtain ⟨fH, eH⟩ := left_ret b3 h.cells (wCells (geoOf S) h) (n := 2 * P.D.nb)
    (by unfold wCells; rw [Array.size_map, b2.om'']; simp [powersFrom_length, recOf]) (ends_of_sumAt b2.sH)
  refine ⟨⟨#[f1, f2], fE, fM, fO, fF, fK, fH⟩, ?_, ?_, wl, U.sWl, wsz U.w3 _, i3, eE, eM, eO, eF, eK, eH⟩
  · rw [U.sco, hsc]
    rfl
  · rw [U.sco, hsc]
    have ez : (#[u1, u2].zip #[o1, o2]).toList = [(u1, o1), (u2, o2)] := by simp
    show List.Forall₂ (ScoresLeft (geoOf S) zk G) (#[u1, u2].zip #[o1, o2]).toList [f1, f2]
    rw [ez]
    exact .cons ⟨W1, w1, e1⟩ (.cons ⟨W2, w2, e2⟩ .nil)

/-- **pointsOf returns there.** -/
theorem points_at (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT)
    {zk : Array (Array E)} (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q)
    {c0 c1 c2 c3 : Attention.ACall} (Pl : K5Law.PlaceIs S c0 c1 c2 c3)
    (P : OwnPar K M X) (hn : P.npl = 2) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (b2 : Said (recOf P rows) h G L) {l : Left} (li : LeftIs (geoOf S) zk h G l) :
    ∃ p, pointsOf (geoOf S) zk h l = some p := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := inner_lens U N hl Kz
  have nR : h.remainders.size = 2 := by
    have e := planesAt_len b2.planes
    rw [b2.nPlanes] at e
    rw [← Array.length_toList, e]
    exact hn
  refine points_ret (by rw [K5Law.place_kr Pl, nR]; rfl) li.nUnits ?_ ?_ U.sWl U.sIx U.sWh ?_ ?_ ?_ i3 i4 i5
  · have e := li.scores.length_eq
    rw [Array.length_toList, Array.length_toList, Array.size_zip, List.size_toArray, ← li.nUnits, Nat.min_self] at e
    exact e
  · intro u hu
    rw [U.sco] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · rw [U.below, if_pos rfl]
      exact i1
    · obtain rfl := List.mem_singleton.1 hu
      rw [U.on]
      exact i2
  · rw [pieces_size, ← weights_size wl #[]]
    exact U.w3.nPw _
  · rw [pieces_size, ← weights_size ix #[]]
    exact U.x3.nPw _
  · rw [pieces_size, ← weights_size wh #[]]
    exact U.f4.nPw _

end At

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.leftIs_ret
#print axioms VerifiableInference.Desc.First.Att.P.points_at
