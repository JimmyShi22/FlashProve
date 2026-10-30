-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PointsReturn.lean: CONDITIONAL: the first test on the public data of the
kind "an attention segment's own rounds" (K5), in its half on the named points (`aloneOk`,
Johnson/Desc/K5/Honest/Alone.lean), says yes wherever each of the four calls' key points has as many
coordinates as its call has bits of keys. Over the library and this side's definitions: no frame.

  `aloneOk_of_pts`   CONDITIONAL: where the verifier's function for the named points returns, the
                     test says yes: its three comparisons of lengths follow from the return
  `pts_of_keys`      CONDITIONAL: that function returns at key points of the calls' lengths, under
                     public facts on the plan
  `keys_of_sizes`    CONDITIONAL: "the list of the key points' sizes is the list of the calls' bits
                     of keys" gives the sizes call by call, in the library's numbers of the lookup
  `aloneOk_at_head`  CONDITIONAL: **under the hypothesis `P5J.AtMgA`, at the plan of group g: the
                     list of sizes is the calls' ⟹ the test says yes**

How. `points_ret` and `inner_lens` (Johnson/Desc/First/Att/K05PointsRet.lean, K05ReturnsLeft.lean),
after the library's own `points_at`; the counts behind a return:
`K5Law.points_counts` (Johnson/Desc/First/Att/Claims/Place.lean) and `points_counts`
(Johnson/Desc/K5/Honest/Law/FitsSizes.lean); the public facts at the hypothesis:
Johnson/Desc/K5/Honest/Law/PublicAtHead.lean.

Limits. Every theorem is conditional; the hypothesis is not shown here. Lengths alone: nothing is
said of what the key points hold, of which call's they are, or of their order beyond the sizes.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.FitsSizes
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.First.Att.K05ReturnsLeft
import Johnson.Road.Rows.AttReadLong
import Johnson.Road.Lane5KvAll
import Johnson.Goal.Meaning.PlanOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Att.P (Pts pointsOf points_ret inner_lens pieces_size
  weights_size geoOf callOf counts_place)
open P5J (AtMgA TS)

/-- **Where the function for the named points returns, the test says yes.** CONDITIONAL: the return.
-/
theorem aloneOk_of_pts {P : Pub5} {c : Chal} {p : Pts} (hp : ptsOf P c = some p) :
    aloneOk P c = true := by
  have hp' : pointsOf P.g c.zk (heardAt P c fun _ => none) (blankLeft P.x.score.length) = some p :=
    hp
  obtain ⟨e1, e2⟩ := H2K5.Honest.points_counts hp'
  obtain ⟨-, -, e3⟩ := K5Law.points_counts hp'
  have r1 : (heardAt P c fun _ => none).remainders.size = P.x.planeMessages := by simp [heardAt]
  have r2 : (heardAt P c fun _ => none).scores.size = P.x.score.length := by simp [heardAt]
  refine aloneOk_of hp (by rw [e1, r1]; exact Nat.le_add_right _ _) (by rw [e3, r2]) fun k hk => ?_
  have hm : k.claim ∈ p.scores.toList.map (·.claim) :=
    List.mem_map.2 ⟨k, Array.mem_toList_iff.2 hk, rfl⟩
  rw [e2] at hm
  rw [e1]
  exact (List.mem_range'_1.1 hm).2

/-- **The function for the named points returns at key points of the calls' lengths.** CONDITIONAL:
A, N, Pl, h2: public facts on the plan; Kz: each call's key point has as many coordinates as the
call has bits of keys. -/
theorem pts_of_keys {P : Pub5} {fs : Forest.Shape} (A : PublicAll P fs)
    (N : OnBytes.Road.L5.Norm P.S) {c0 c1 c2 c3 : Attention.ACall}
    (Pl : K5Law.PlaceIs P.S c0 c1 c2 c3) (h2 : P.x.planeMessages = 2) {c : Chal}
    (Kz : ∀ q : Fin 4, (c.zk.getD q.1 #[]).size = (callsOf fs).a q) : ∃ p, ptsOf P c = some p := by
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U, -⟩ := A.units
  have hl : 1 ≤ P.S.lnT := Nat.le_trans (by decide) A.sized.Z.lnT
  obtain ⟨i1, i2, i3, i4, i5⟩ := inner_lens U N hl Kz
  show ∃ p, pointsOf (geoOf P.S) c.zk (heardAt P c fun _ => none)
    (blankLeft P.x.score.length) = some p
  refine points_ret ?_ ?_ ?_ ?_ U.sWl U.sIx U.sWh ?_ ?_ ?_ i3 i4 i5
  · rw [K5Law.place_kr Pl]
    simp [heardAt, h2]
  · rw [U.sco]
    simp [heardAt, A.score2]
  · rw [U.sco]
    simp [blankLeft, A.score2]
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

/-- **From the list of sizes to the sizes call by call.** CONDITIONAL: hid: the planner of shapes
returns the shape and the lookup's shape; Pl: the place's four calls; hz: the list of the key
points' sizes is the list of the calls' bits of keys. -/
theorem keys_of_sizes {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) {c0 c1 c2 c3 : Attention.ACall}
    (Pl : K5Law.PlaceIs S c0 c1 c2 c3) {zk : Array (Array E)}
    (hz : zk.map (·.size) = (geoOf S).calls.map (·.n)) (q : Fin 4) :
    (zk.getD q.1 #[]).size = (callsOf fs).a q := by
  have n4 : S.calls.size = 4 := by
    rw [← Array.length_toList, Pl.calls]
    rfl
  have hq : q.1 < S.calls.size := by
    rw [n4]
    exact q.2
  have hs : zk.size = S.calls.size := by
    have := congrArg Array.size hz
    simpa [geoOf] using this
  have e1 : (zk.map (·.size))[q.1]? = ((geoOf S).calls.map (·.n))[q.1]? := by rw [hz]
  have hq' : q.1 < zk.size := by
    rw [hs]
    exact hq
  show _ = ((fs.calls[q.1]?).map fun k => k.n).getD 0
  rw [OnBytes.Road.L5.calls_of_hid hid, Array.getElem?_map, Array.getElem?_eq_getElem hq]
  rw [Array.getElem?_map, Array.getElem?_map, Array.getElem?_eq_getElem hq'] at e1
  have e2 : (geoOf S).calls[q.1]? = some (callOf S.calls[q.1]) := by
    show (S.calls.map callOf)[q.1]? = _
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hq]
    rfl
  rw [e2] at e1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq']
  exact Option.some.inj e1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **AT THE PLAN OF GROUP g: THE KEY POINTS' SIZES ARE THE CALLS' ⟹ THE TEST ON THE NAMED POINTS
SAYS YES.** CONDITIONAL: under the hypothesis h, which is not shown here; g is below 12; ea: the
group's plan; hz: the list of the key points' sizes is the list of the calls' bits of keys. -/
theorem aloneOk_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {c : Chal}
    (hz : c.zk.map (·.size) = (Pub5.g ⟨a.S, a.own⟩).calls.map (·.n)) :
    aloneOk ⟨a.S, a.own⟩ c = true := by
  obtain ⟨hid, Lw⟩ := law_at_head h hg ea
  obtain ⟨A0, hA, eS, eO, -, -⟩ := plan_at_head h hg ea
  have h2 : a.own.planeMessages = 2 := by
    rw [eO, (Meaning.plan_own hA).planeMessages, ← eS]
    exact (counts_place Lw.place).1
  obtain ⟨p, hp⟩ := pts_of_keys (P := ⟨a.S, a.own⟩) (public_at_head h hg ea)
    (OnBytes.Road.Rows.norm_of_hid hid) Lw.place h2 (keys_of_sizes hid Lw.place hz)
  exact aloneOk_of_pts hp

end

end H2K5.Honest

#print axioms H2K5.Honest.aloneOk_of_pts
#print axioms H2K5.Honest.pts_of_keys
#print axioms H2K5.Honest.keys_of_sizes
#print axioms H2K5.Honest.aloneOk_at_head
