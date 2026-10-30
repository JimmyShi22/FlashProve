-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoDraws.lean.
The first routine of the byte-level verifier's lookup: the draws.

Forest.draws h (OnBytes/Model/Look.lean) closes the round of the shift, if the forest has several
calls, then the round of the point alpha at which the two products are compared, and computes the
padding's public factor a.
  drawsEv h θ α: the calls of the channel's routines that it makes: the shift's answer if 1 < NC,
  then alpha's. drawsA h θ α: the routine's fold.
  draws_ok: if a run of Forest.draws returns (θ, α, a), then these calls were made one after the
    other, the sub-proof's state is as before, θ is 0 where the forest has one call, and a = drawsA
    h θ α.
  draws_val: under every reading ρ, ρ (drawsA h θ α) is the plain fold at ρ θ and ρ α; premise:
    callOf[y] is below 2^64 for y < NT.
  draws_fl, draws_open: these calls as rounds of plain data: a round without a scalar for each; no
    message is left open.
  draws_theta, draws_after: what the flat function reads of them, whatever rounds follow: thetaOf is
    ρ θ, and behind the shift the first round draws ρ α. Premise of draws_theta: θ is 0 where the
    forest has one call.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

/-- The calls of the channel's routines that Forest.draws makes. -/
def drawsEv (h : Sh) (θ α : E) : List Ev :=
  (if h.NC > 1 then [Ev.ans .lkpShift θ] else []) ++ [Ev.ans .lkp α]

/-- The routine's fold. -/
def drawsA (h : Sh) (θ α : E) : E :=
  (List.range h.NT).foldl
    (fun a y => mulE a (powE (subE α (Forest.padKeyOf h θ (h.callOf.getD y 0))) (h.pub.getD y 0)))
    (powE (subE α (Forest.padKeyOf h θ 0)) h.emptyKeys)

theorem draws_ok (h : Sh) (F G : Fork) (c c' : Ctx) (θ α a : E)
    (hr : Forest.draws h F c = .ok (((θ, α, a), G), c')) :
    Evs (drawsEv h θ α) c c' ∧ G = F ∧ (¬ h.NC > 1 → θ = zeroE) ∧ a = drawsA h θ α := by
  unfold Forest.draws at hr
  unfold drawsEv
  by_cases hN : h.NC > 1
  · rw [if_pos hN] at hr ⊢
    rw [bind_ok] at hr
    obtain ⟨θ', F1, c1, h1, hr⟩ := hr
    obtain ⟨a1, e1⟩ := (answer_ok _ _ _ _ _ _).1 h1
    rw [bind_ok] at hr
    obtain ⟨α', F2, c2, h2, hr⟩ := hr
    obtain ⟨a2, e2⟩ := (answer_ok _ _ _ _ _ _).1 h2
    rw [pure_ok] at hr
    obtain ⟨⟨⟨t1, t2, t3⟩, t4⟩, t5⟩ : ((θ = θ' ∧ α = α' ∧ a = drawsA h θ' α') ∧ G = F2) ∧ c' = c2 :=
      by
      simpa [Prod.ext_iff, drawsA] using hr
    subst t1 t2 t5
    exact ⟨(evs_append _ _ _ _).2 ⟨c1, a1, a2⟩, t4.trans (e2.trans e1), fun hn => absurd hN hn, t3⟩
  · rw [if_neg hN] at hr ⊢
    rw [bind_ok] at hr
    obtain ⟨θ', F1, c1, h1, hr⟩ := hr
    rw [pure_ok] at h1
    obtain ⟨⟨s1, s2⟩, s3⟩ : (θ' = zeroE ∧ F1 = F) ∧ c1 = c := by simpa [Prod.ext_iff] using h1
    rw [bind_ok] at hr
    obtain ⟨α', F2, c2, h2, hr⟩ := hr
    obtain ⟨a2, e2⟩ := (answer_ok _ _ _ _ _ _).1 h2
    rw [pure_ok] at hr
    obtain ⟨⟨⟨t1, t2, t3⟩, t4⟩, t5⟩ : ((θ = θ' ∧ α = α' ∧ a = drawsA h θ' α') ∧ G = F2) ∧ c' = c2 :=
      by
      simpa [Prod.ext_iff, drawsA] using hr
    subst t1 t2 t5 s3
    exact ⟨a2, t4.trans (e2.trans s2), fun _ => s1, t3⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem draws_val (h : Sh) (θ α : E) (hc : ∀ y, y < h.NT → h.callOf.getD y 0 < 2 ^ 64) :
    ρ.val (drawsA h θ α) =
      (List.range h.NT).foldl (fun a y => a * (ρ.val α - padKeyK h (ρ.val θ) (FoNums.co h y)) ^
          h.pub.getD y 0)
        ((ρ.val α - padKeyK h (ρ.val θ) 0) ^ h.emptyKeys) :=
  fac_val ρ h θ α hc

/-- The calls as rounds of plain data. -/
theorem draws_fl (h : Sh) (θ α : E) :
    flEv ρ (drawsEv h θ α) = (if h.NC > 1 then [(([] : List K), [ρ.val θ])] else []) ++
        [([], [ρ.val α])] := by
  unfold drawsEv
  by_cases hN : h.NC > 1
  · rw [if_pos hN, if_pos hN]
    rfl
  · rw [if_neg hN, if_neg hN]
    rfl

/-- No message is left open. -/
theorem draws_open (h : Sh) (θ α : E) : openAfter ρ [] (drawsEv h θ α) = [] := by
  unfold drawsEv
  by_cases hN : h.NC > 1
  · rw [if_pos hN]
    rfl
  · rw [if_neg hN]
    rfl

/-- The flat function's shift, whatever calls follow. -/
theorem draws_theta (h : Sh) (θ α : E) (hz : ¬ h.NC > 1 → θ = zeroE) (l : List Ev) :
    thetaOf h (flEv ρ (drawsEv h θ α ++ l)) = ρ.val θ := by
  rw [flEv_append ρ _ _ (draws_open ρ h θ α), draws_fl]
  unfold thetaOf FoNums.several
  by_cases hN : h.NC > 1
  · rw [if_pos hN, if_pos (decide_eq_true hN)]
    rfl
  · rw [if_neg (by simpa using hN), hz hN, ρ.zero]

/-- Behind the shift: alpha's round, then the rounds of what follows. -/
theorem draws_after (h : Sh) (θ α : E) (l : List Ev) :
    afterShift h (flEv ρ (drawsEv h θ α ++ l)) = ([], [ρ.val α]) :: flEv ρ l := by
  rw [flEv_append ρ _ _ (draws_open ρ h θ α), draws_fl]
  unfold afterShift FoNums.several
  by_cases hN : h.NC > 1
  · rw [if_pos hN, if_pos (decide_eq_true hN)]
    rfl
  · rw [if_neg hN, if_neg (by simpa using hN)]
    rfl

end
end Fo
