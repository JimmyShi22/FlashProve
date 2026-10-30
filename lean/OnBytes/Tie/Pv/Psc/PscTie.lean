-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscTie.lean: the claim that the verifier's masked sumcheck leaves is worth 0
exactly if the library's output row UHolds holds of the output of the sumcheck with short messages.

The statement (row_iff_UHolds) is for every value Y of the library's parameters PscPar. It stands
under: Fits (the verifier's weights fit the library's variables, one by one), ReadsAs (the
verifier's rounds are read as a short transcript), PscAt (the verifier's state has these weights,
these challenges and that running claim), and four equations that an instance has to show: D1 (the
hiding polynomial's coefficients are the hidden values under the slots from the first on, in the
verifier's order), D2 (the incoming form is the target less the start's value), D3 (the kept maps'
terms), D4 (the summand on the shown values).

Main definitions: Fits, ReadsAs, outS, PscAt. Main theorems: fits_ok, step_read, claimAfter_hFin,
match_of, out_carry, row_iff_UHolds.

What is not claimed. That a run of the verifier's routines yields such a state. ReadsAs says nothing
on the round of the end values. The claims on end values are not treated. That all hypotheses hold
together at one instance is not shown here. Nothing on soundness or hiding.

-/
import OnBytes.Tie.Pv.Psc.PscFit
import Cb.G6.Johnson.Layers.Short
import OnBytes.Tie.Pv.Psc.StepWalk
import OnBytes.Model.Psc

set_option autoImplicit false

namespace Johnson.L5.Layers
open Iop Prob Cb OnBytes OnBytes.Model

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- the port's weights fit the library's variables -/
def Fits : List OnBytes.Psc.Weight → (l : List (PFmt K)) → (d : PDats l) → HFixs (pVars l d) → Prop
  | [], [], _, _ => True
  | w :: ws, f :: l, d, F => Fit1 ρ w (f.var d.1) F.1 ∧ Fits ws l d.2 F.2
  | [], _ :: _, _, _ => False
  | _ :: _, [], _, _ => False

/-- the port's rounds, read as a short transcript -/
def ReadsAs : List (List E × E) → (l : List (PFmt K)) → (t : Shape) → Tr (sRounds l ++ t) → Prop
  | [], [], _, _ => True
  | (sent, r) :: rs, f :: l, t, (m, c, τ) =>
    sent.length = f.n ∧ m.2 = rd ρ f.n sent ∧ f.val c = ρ.val r ∧ ReadsAs rs l t τ
  | [], _ :: _, _, _ => False
  | _ :: _, [], _, _ => False

omit [Fintype K] in
theorem fits_ok : ∀ (ws : List OnBytes.Psc.Weight) (l : List (PFmt K)) (d : PDats l)
    (F : HFixs (pVars l d)), Fits ρ ws l d F → HFixs.OK (pVars l d) F
  | [], [], _, _, _ => trivial
  | _ :: ws, _ :: l, d, F, h => ⟨h.1.inv, fits_ok ws l d.2 F.2 h.2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

omit [Fintype K] in
/-- one round: the port's next claim, read, is the library's -/
theorem step_read {w : OnBytes.Psc.Weight} {v : HVar K} {fx : Fin (v.n + 1) × K} (h : Fit1 ρ w v fx)
    (sent : List E) (c0 r : E) (hs : sent.length = v.n) :
    ρ.val (OnBytes.Psc.polyAt (w.complete sent c0) r) =
      hev (hFill v fx (ρ.val c0) (rd ρ v.n sent)) (ρ.val r) := by
  rw [polyAt_hev ρ _ v.n (le_of_eq (h.clen sent c0 hs)) r, h.cmp sent c0 hs]

omit [Fintype K] in
/-- (P5) -/
theorem claimAfter_hFin : ∀ (ws : List OnBytes.Psc.Weight) (rs : List (List E × E))
    (l : List (PFmt K)) (d : PDats l) (F : HFixs (pVars l d)) (t : Shape) (τ : Tr (sRounds l ++ t))
    (c0 : E), Fits ρ ws l d F → ReadsAs ρ rs l t τ →
    ρ.val (OnBytes.Psc.claimAfter ws rs c0) =
      hFin (pVars l d) (ρ.val c0) (pQ l d (Tr.fst ((cShort l d F (ρ.val c0) t).tr τ)).plains)
        (pH l d (pG l (Tr.fst ((cShort l d F (ρ.val c0) t).tr τ)).rho))
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | w :: ws, (sent, r) :: rs, f :: l, d, F, t, (m, c, τ), c0, hF, hR => by
    obtain ⟨h1, h2, h3, h4⟩ := hR
    have e : ρ.val (OnBytes.Psc.polyAt (w.complete sent c0) r) =
        hev (hFill (f.var d.1) F.1 (ρ.val c0) m.2) (f.val c) := by
      rw [step_read ρ hF.1 sent c0 r h1, h2, h3]
    have ih := claimAfter_hFin ws rs l d.2 F.2 t τ (OnBytes.Psc.polyAt (w.complete sent c0) r)
      hF.2 h4
    rw [e] at ih
    exact ih
  | [], _, _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, _, _, h, _ => h.elim
  | [], _ :: _, [], _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _ :: _, _, _, _, _, _, _, h => h.elim

omit [Fintype K] in
/-- the port's weights with the challenges match the library's variables and point -/
theorem match_of : ∀ (ws : List OnBytes.Psc.Weight) (rs : List (List E × E))
    (l : List (PFmt K)) (d : PDats l) (F : HFixs (pVars l d)) (t : Shape) (τ : Tr (sRounds l ++ t))
    (σ : K), Fits ρ ws l d F → ReadsAs ρ rs l t τ →
    OnBytes.Road.Hd.Match ρ (ws.zip (rs.map (·.2))) (pVars l d)
      (pH l d (pG l (Tr.fst ((cShort l d F σ t).tr τ)).rho))
  | [], [], [], _, _, _, _, _, _, _ => trivial
  | _ :: ws, (_, _) :: rs, _ :: l, d, F, t, (_, _, τ), _, hF, hR =>
    ⟨hF.1.len.symm, hF.1.plen, fun i => (congrFun hF.1.psi i).symm, hR.2.2.1,
      match_of ws rs l d.2 F.2 t τ _ hF.2 hR.2.2.2⟩
  | [], _, _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, _, _, h, _ => h.elim
  | [], _ :: _, [], _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _ :: _, _, _, _, _, _, _, h => h.elim

variable (Y : PscPar K)

/-- the output of the library's verifier on a completed transcript, written out -/
noncomputable def outS (x : K × Y.St) (F : HFixs (Y.vars x.2)) (Ex : ExtSpec) (t : Tr (shapeS Y)) :
    Y.Out :=
  ⟨x.2, Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)),
    Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)),
    hFin (Y.vars x.2)
      (Y.mu (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)) +
        Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)) * x.1)
      (Y.qs x.2 (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)))
      (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr t)))),
    (Tr.snd (s := Y.shapeC) ((carryS Y x F Ex).tr t)).plains.1⟩

theorem out_carry (Ex : ExtSpec) (x : K × Y.St) (F : HFixs (Y.vars x.2))
    (hF : HFixs.OK (Y.vars x.2) F) (y : Ex.Str) (t : Tr (shapeS Y)) :
    (Y.psc Ex).out x y ((carryS Y x F Ex).tr t) = some (outS Y x F Ex t) := by
  obtain ⟨m, ε, τ⟩ := t
  have hc : HCons (Y.vars x.2)
      (Y.mu (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))) +
        Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))) * x.1)
      (Y.qs x.2 (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))))
      (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))))) :=
    cShort_cons Y.fmt (Y.dat x.2) F hF (m.2 + ε * x.1) [pRoundV K Y.A] τ
  show ((Y.outC x (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ)))).bind fun x₂ =>
    (Y.ends Ex).out x₂ y (Tr.snd (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ)))) = _
  unfold PscPar.outC
  rw [if_pos hc]
  rfl

/-- WHAT THE RUN HALF OWES: the port's state after the rounds. -/
structure PscAt (p : OnBytes.Model.Psc) (ws : List OnBytes.Psc.Weight) (rs : List (List E × E))
    (mu : E) : Prop where
  vars : p.vars.toList = ws
  r : p.r.toList = rs.map (·.2)
  claim : p.claim = OnBytes.Psc.claimAfter ws rs (addE mu (mulE p.eps p.target))

/-- (P4) THE TOP OF (A4-pure). -/
theorem row_iff_UHolds (Ex : ExtSpec) (W : World K) (p : OnBytes.Model.Psc)
    (ws : List OnBytes.Psc.Weight) (rs : List (List E × E)) (mu S0 : E) (kept : Aff)
    (st : Y.St) (F : HFixs (Y.vars st)) (τ : Tr (sRounds Y.fmt ++ [pRoundV K Y.A])) (m : Y.J → K)
    (hp : PscAt p ws rs mu) (hF : Fits ρ ws Y.fmt (Y.dat st) F)
    (hR : ReadsAs ρ rs Y.fmt [pRoundV K Y.A] τ) (hne : ws.zip (rs.map (·.2)) ≠ [])
    (D1 : Y.W st m = OnBytes.Road.Hd.place W.slot (Y.vars st) p.first)
    (D2 : Y.inc st m = ρ.val p.target - p.start.value ρ W)
    (D3 : ∑ b, Y.S1 st
        (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt)
        (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).vals b *
      Y.Gb st m b (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt) =
        kept.value ρ W)
    (D4 : Y.S0 st (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt)
        (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).vals = ρ.val S0) :
    (p.rowForm S0 kept).value ρ W = 0 ↔
      Y.UHolds (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)) m := by
  have hM := match_of ρ ws rs Y.fmt (Y.dat st) F [pRoundV K Y.A] τ
    (ρ.val mu + ρ.val p.eps * ρ.val p.target) hF hR
  obtain ⟨a1, a2⟩ := OnBytes.Road.Hd.walk_hU ρ W.slot _ _ _ p.first hne hM
  have hw : p.walk = OnBytes.Psc.hidingWalk (ws.zip (rs.map (·.2))) := by
    unfold OnBytes.Model.Psc.walk
    rw [zipT_eq, hp.vars, hp.r]
  have hc := claimAfter_hFin ρ ws rs Y.fmt (Y.dat st) F [pRoundV K Y.A] τ
    (addE mu (mulE p.eps p.target)) hF hR
  rw [← hp.claim, ρ.add, ρ.mul] at hc
  have key : Y.UHolds (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)) m ↔
      hU (Y.vars st) (Y.W st m)
          (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt) +
        ρ.val p.eps * hPsi (Y.vars st)
          (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt) *
            Y.inc st m +
        ρ.val p.eps * ∑ b, Y.S1 st
            (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt)
            (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).vals b *
          Y.Gb st m b
            (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt) =
      (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).fin -
        ρ.val p.eps * Y.S0 st
          (Y.hp st (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).pt)
          (outS Y (ρ.val p.target, st) F Ex (((), ρ.val mu), ρ.val p.eps, τ)).vals := Iff.rfl
  rw [key, D3, D4, D1, D2, Psc.rowForm_value, hw, a1, a2, hc]
  constructor
  · intro h
    exact sub_eq_zero.1 h
  · intro h
    exact sub_eq_zero.2 h

end Johnson.L5.Layers

#print axioms Johnson.L5.Layers.claimAfter_hFin
#print axioms Johnson.L5.Layers.out_carry
#print axioms Johnson.L5.Layers.row_iff_UHolds
