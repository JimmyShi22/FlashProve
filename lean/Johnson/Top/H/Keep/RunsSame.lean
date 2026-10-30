-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/RunsSame.lean: The kind "lookup" (K3): ITS RUNS "planes" AND "join" ANSWER
BEHIND A K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean) WHAT THEY ANSWERED IN FRONT (RunSame): the
same claims, the same late slots: where what was heard at the run's seat and what the calling kind
hands in (its readers of the columns; its key forms) are the same at both states. Definitions,
statements and proofs.

OBJECT: K3.planesRun, K3.joinRun (Johnson/Desc/First/Look/K3Runs.lean) at a seat whose ledger is the
  state's and whose mark is putFork (AtS2).
Used by Johnson/Top/H/Keep/FormsPassOurs.lean, Johnson/Top/H/Keep/HeadHoleFwd.lean,
  Johnson/Top/H/Keep/HeadOwnAtSeat.lean and 1 more.
LETTERS: seat, lm, readers | keys, s, s', F, G free.
Compiled with the whole library.

Main names:
  Flat x: a flat program that turns neither ledger nor tape and does not read the ledger.
    flat_ret, flat_must, flat_need, flat_andThen, flat_foldlM, flat_planesAt.
  flThen_inv, flThen_some: one step of a flat program, both ways.
  leavesRowOwn_at, planeClaimsOwn_at, joinF_at: WHAT THE PROGRAM ANSWERED AT ONE LEDGER IT ANSWERS
    AT ANOTHER, where its one write on the ledger returns there.
  planes_runSame', join_runSame': THE TWO ENDS: the caller's readers | keys need only answer behind
    WHAT THEY ANSWERED in front (a reader that refuses at a free slot may speak behind).
  planes_runSame, join_runSame: their corollaries under the equation


Limits. PREMISES:
hh (what was heard at the seat is the same) · hread | hkeys (THE CALLING KIND's: its readers | keys
answer the same at both states) · at "planes": hwin: in the ledger in front the window of the
sumcheck over the leaves is free, ends at or below the next slot, and the next slot is at or below
the number of slots (Johnson/Top/H/Keep/K3LeftWindow.lean has these from
the sentence on what the lookup left).

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3PassOf
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.Keep.K3Start
import Johnson.Desc.First.Look.LookPlanesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (planesAtF planeClaimsOwn leavesRowOwn planesAddedF
  joinAddedF joinF paidF planesOk)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun unpaid)
open VerifiableInference.Desc.K9 (lateOf)

/-! ## Flat programs that do not read the ledger -/

section
variable {α β : Type}

theorem flThen_inv {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {r : β × Fork × Tape}
    (h : Fl.andThen x f F t = some r) : ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  unfold Fl.andThen at h
  cases e : x F t with
  | none =>
    rw [e] at h
    exact nomatch h
  | some y =>
    obtain ⟨a, G, u⟩ := y
    rw [e] at h
    exact ⟨a, G, u, rfl, h⟩

theorem flThen_some (x : Fl α) (f : α → Fl β) (F G : Fork) (t u : Tape) (a : α)
    (h : x F t = some (a, G, u)) : Fl.andThen x f F t = f a G u := by
  unfold Fl.andThen
  rw [h]

/-- It turns neither ledger nor tape and does not read the ledger. -/
def Flat (x : Fl α) : Prop :=
  ∀ F t a G u, x F t = some (a, G, u) → G = F ∧ u = t ∧ ∀ F', x F' t = some (a, F', t)

theorem flat_ret (a : α) : Flat (Fl.ret a) := by
  intro F t b G u h
  have e : (a, F, t) = (b, G, u) := Option.some.inj h
  obtain ⟨rfl, e2⟩ := Prod.mk.inj e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
  exact ⟨rfl, rfl, fun _ => rfl⟩

theorem flat_must (b : Bool) : Flat (Fl.must b) := by
  intro F t a G u h
  cases b with
  | false => exact nomatch h
  | true =>
    have e : ((), F, t) = (a, G, u) := Option.some.inj h
    obtain ⟨rfl, e2⟩ := Prod.mk.inj e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
    exact ⟨rfl, rfl, fun _ => rfl⟩

theorem flat_need (o : Option α) : Flat (Fl.need o) := by
  intro F t a G u h
  cases o with
  | none => exact nomatch h
  | some v =>
    have e : (v, F, t) = (a, G, u) := Option.some.inj h
    obtain ⟨rfl, e2⟩ := Prod.mk.inj e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
    exact ⟨rfl, rfl, fun _ => rfl⟩

theorem flat_andThen {x : Fl α} {f : α → Fl β} (hx : Flat x) (hf : ∀ a, Flat (f a)) :
    Flat (Fl.andThen x f) := by
  intro F t b G u h
  obtain ⟨a, G1, u1, h1, h2⟩ := flThen_inv h
  obtain ⟨e1, e2, k1⟩ := hx F t a G1 u1 h1
  rw [e1, e2] at h2
  obtain ⟨e3, e4, k2⟩ := hf a F t b G u h2
  exact ⟨e3, e4, fun F' => (flThen_some x f F' F' t t a (k1 F')).trans (k2 F')⟩

theorem flat_foldlM {γ : Type} (f : β → γ → Fl β) (hf : ∀ b c, Flat (f b c)) :
    ∀ (l : List γ) (b : β), Flat (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact flat_ret b
  | c :: l, b => by
    rw [List.foldlM_cons]
    exact flat_andThen (hf b c) fun b' => flat_foldlM f hf l b'

end

theorem flat_planesAt (g : Forest.Heard) (lm e : ℕ) (r : ℕ → ℕ → Option Aff) :
    Flat (planesAtF g lm e fun e col => Fl.need (r e col)) := by
  unfold planesAtF
  exact flat_foldlM _ (fun _ col => flat_andThen (flat_need (r e col)) fun _ => flat_ret _) _ _

/-! ## The three programs at another ledger -/

theorem leavesRowOwn_at {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {t u : Tape} {lr : Aff}
    (h : leavesRowOwn p S0 kept F t = some (lr, G, u)) {F' G' : Fork}
    (hrun : F'.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) =
      some G') : leavesRowOwn p S0 kept F' t = some (lr, G', t) := by
  unfold leavesRowOwn at h ⊢
  have h' : Fl.andThen
      (Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size))
      (fun _ => Fl.andThen
        (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
        fun _ => Fl.ret (p.rowForm S0 kept)) F t = some (lr, G, u) := h
  obtain ⟨_, G1, u1, k1, k2⟩ := flThen_inv h'
  obtain ⟨e1, e2, m1⟩ := flat_must _ F t _ G1 u1 k1
  obtain ⟨_, G2, u2, _, k4⟩ := flThen_inv k2
  have e : (p.rowForm S0 kept, G2, u2) = (lr, G, u) := Option.some.inj k4
  have hlr : p.rowForm S0 kept = lr := (Prod.mk.inj e).1
  show Fl.andThen
      (Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size))
      (fun _ => Fl.andThen
        (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
        fun _ => Fl.ret (p.rowForm S0 kept)) F' t = some (lr, G', t)
  refine (flThen_some _ _ F' F' t t _ (m1 F')).trans ?_
  refine (flThen_some _ _ F' G' t t () ?_).trans ?_
  · show (F'.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)).map
      (fun G => ((), G, t)) = _
    rw [hrun]
    rfl
  · rw [← hlr]
    rfl

theorem planeClaimsOwn_at (g : Forest.Heard) (lm : ℕ) (r1 : ℕ → ℕ → Option Aff)
    (r2 : ℕ → Option Aff) {F G : Fork} {t u : Tape} {fs : Array Aff}
    (h : planeClaimsOwn g lm (fun e col => Fl.need (r1 e col)) (fun col => Fl.need (r2 col)) F t =
      some (fs, G, u)) {F' G' : Fork}
    (hrun : F'.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE)
      (subE zeroE oneE) = some G') :
    planeClaimsOwn g lm (fun e col => Fl.need (r1 e col)) (fun col => Fl.need (r2 col)) F' t =
      some (fs, G', t) := by
  unfold planeClaimsOwn at h ⊢
  obtain ⟨_, G1, u1, k1, h⟩ := flThen_inv (x := Fl.must (planesOk g.shape lm)) h
  obtain ⟨e1, e2, m1⟩ := flat_must _ F t _ G1 u1 k1
  rw [e1, e2] at h
  obtain ⟨at0, G2, u2, k2, h⟩ :=
    flThen_inv (x := planesAtF g lm 0 fun e col => Fl.need (r1 e col)) h
  obtain ⟨e3, e4, m2⟩ := flat_planesAt g lm 0 r1 F t at0 G2 u2 k2
  rw [e3, e4] at h
  obtain ⟨at1, G3, u3, k3, h⟩ :=
    flThen_inv (x := planesAtF g lm 1 fun e col => Fl.need (r1 e col)) h
  obtain ⟨e5, e6, m3⟩ := flat_planesAt g lm 1 r1 F t at1 G3 u3 k3
  rw [e5, e6] at h
  obtain ⟨count, G4, u4, k4, h⟩ := flThen_inv h
  obtain ⟨e7, e8, m4⟩ := flat_foldlM _
    (fun (f : Aff) col => flat_andThen (flat_need (r2 col)) fun x => flat_ret (f + x)) _ _ F t
    count G4 u4 k4
  rw [e7, e8] at h
  obtain ⟨lr, G5, u5, k5, h⟩ :=
    flThen_inv (x := leavesRowOwn g.leaves oneE (Aff.scale at0 g.leavesA)) h
  have e : (#[lr, Aff.slot g.sBit - at1, count], G5, u5) = (fs, G, u) := Option.some.inj h
  have hfs : #[lr, Aff.slot g.sBit - at1, count] = fs := (Prod.mk.inj e).1
  refine (flThen_some _ _ F' F' t t _ (m1 F')).trans ?_
  refine (flThen_some _ _ F' F' t t _ (m2 F')).trans ?_
  refine (flThen_some _ _ F' F' t t _ (m3 F')).trans ?_
  refine (flThen_some _ _ F' F' t t _ (m4 F')).trans ?_
  refine (flThen_some _ _ F' G' t t _ (leavesRowOwn_at k5 hrun)).trans ?_
  rw [← hfs]
  rfl

theorem joinF_at {g : Forest.Heard} {KF : Array Aff} {F G : Fork} {t u : Tape} {a : Aff}
    (h : joinF g KF F t = some (a, G, u)) (F' : Fork) :
    joinF g KF F' t = some (a, F'.paid g.owedJoin, t) := by
  unfold joinF at h ⊢
  obtain ⟨_, G1, u1, k1, h⟩ := flThen_inv
    (x := Fl.must (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size)) h
  obtain ⟨_, _, m1⟩ := flat_must _ F t _ G1 u1 k1
  obtain ⟨_, G2, u2, _, h⟩ := flThen_inv (x := joinAddedF g) h
  refine (flThen_some _ _ F' F' t t _ (m1 F')).trans ?_
  refine (flThen_some (joinAddedF g) _ F' (F'.paid g.owedJoin) t t () rfl).trans ?_
  have e := congrArg (fun y : Aff × Fork × Tape => y.1) (Option.some.inj h)
  exact congrArg (fun y : Aff => some (y, F'.paid g.owedJoin, t)) e

/-! ## The two runs -/

section
variable (seat : Seat S Claim) (hA : AtS2 seat) {s s' : S} {F G : Fork} (P : K3Pass s s' F G)
  (hh : seat.heard s' = seat.heard s)
include hA P hh

/-- **"join" answers behind a pass what it answered in front**, where the caller's keys answer
behind what they answered in front. -/
theorem join_runSame' (keys : S → Option (Array Aff))
    (hkeys : ∀ KF, keys s = some KF → keys s' = some KF) : RunSame (joinRun seat keys) s s' := by
  intro cl t F1 G1 hr hF1 hG1
  obtain rfl : F = F1 := Option.some.inj (P.front.symm.trans hF1)
  have hr0 := hr
  unfold joinRun at hr0
  rw [named_bind] at hr0
  obtain ⟨F2, e1, hr0⟩ := hr0
  obtain rfl : F = F2 := Option.some.inj (P.front.symm.trans ((hA.fork s).symm.trans e1))
  rw [named_bind] at hr0
  obtain ⟨g, e2, hr0⟩ := hr0
  rw [need_bind] at hr0
  obtain ⟨hun, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨KF, e3, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨⟨a, Gx, u⟩, e4, hr0⟩ := hr0
  have e5 : ([seat.claim a], seat.mark s Gx) = (cl, t) := Except.ok.inj hr0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  have c0 := joinF_at e4 F
  have hGx : Gx = F.paid g.owedJoin :=
    congrArg (fun y : Aff × Fork × Tape => y.2.1) (Option.some.inj (e4.symm.trans c0))
  have hr' : joinRun seat keys 0 s' =
      .ok ([seat.claim a], seat.mark s' (G.paid g.owedJoin)) := by
    unfold joinRun
    rw [named_bind]
    refine ⟨G, (hA.fork s').trans P.behind, ?_⟩
    rw [named_bind]
    refine ⟨g, hh.trans e2, ?_⟩
    rw [need_bind]
    refine ⟨P.owed _ hun, ?_⟩
    rw [named_bind]
    refine ⟨KF, hkeys KF e3, ?_⟩
    rw [named_bind]
    exact ⟨(a, G.paid g.owedJoin, []), joinF_at e4 G, rfl⟩
  have hG1' : G1 = F.paid g.owedJoin := by
    rw [hA.mark, fork_putFork s F _ P.front, hGx] at hG1
    exact (Option.some.inj hG1).symm
  refine ⟨_, G, G.paid g.owedJoin, hr', P.behind,
    by rw [hA.mark]; exact fork_putFork s' G _ P.behind, ?_, P.trees⟩
  rw [hG1', lateOf_same G (G.paid g.owedJoin) rfl, lateOf_same F (F.paid g.owedJoin) rfl]

/-- The same under the equation of the keys. -/
theorem join_runSame (keys : S → Option (Array Aff)) (hkeys : keys s' = keys s) :
    RunSame (joinRun seat keys) s s' :=
  join_runSame' seat hA P hh keys fun _ h => hkeys.trans h

/-- **"planes" answers behind a pass what it answered in front**, where the caller's readers answer
behind what they answered in front. -/
theorem planes_runSame' (lm : ℕ) (readers : Readers S)
    (hread : ∀ r, readers s = some r → readers s' = some r)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j) :
    RunSame (planesRun seat lm readers) s s' := by
  intro cl t F1 G1 hr hF1 hG1
  obtain rfl : F = F1 := Option.some.inj (P.front.symm.trans hF1)
  have hr0 := hr
  unfold planesRun at hr0
  rw [named_bind] at hr0
  obtain ⟨F2, e1, hr0⟩ := hr0
  obtain rfl : F = F2 := Option.some.inj (P.front.symm.trans ((hA.fork s).symm.trans e1))
  rw [named_bind] at hr0
  obtain ⟨g, e2, hr0⟩ := hr0
  rw [need_bind] at hr0
  obtain ⟨hun, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨r, e3, hr0⟩ := hr0
  dsimp only at hr0
  rw [named_bind] at hr0
  obtain ⟨⟨rows, Gx, u⟩, e4, hr0⟩ := hr0
  have e5 : (rows.toList.map seat.claim, seat.mark s Gx) = (cl, t) := Except.ok.inj hr0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  obtain ⟨fs, Ga, ua, k1, k2⟩ := flThen_inv
    (x := planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col)) fun col => Fl.need (r.2 col)) e4
  obtain ⟨_, Gb, ub, _, k4⟩ := flThen_inv (x := planesAddedF g) k2
  have hrows : fs = rows :=
    congrArg (fun y : Array Aff × Fork × Tape => y.1) (Option.some.inj k4)
  obtain ⟨w1, w2, w3⟩ := hwin g e2
  obtain ⟨H', hH'⟩ := own_write_returns (G := G) (g := g) P.sizedG
    ⟨Nat.le_trans w1 P.later.next, fun j h1 h2 hf =>
      w3 j h1 h2 (P.below j (Nat.lt_of_lt_of_le h2 w1) hf)⟩
    (by rw [P.later.ns]; exact w2)
  have c1 := planeClaimsOwn_at g lm r.1 r.2 k1 (F' := G) (G' := H') hH'
  have hr' : planesRun seat lm readers 0 s' =
      .ok (rows.toList.map seat.claim, seat.mark s' (H'.paid g.owedPlanes)) := by
    unfold planesRun
    rw [named_bind]
    refine ⟨G, (hA.fork s').trans P.behind, ?_⟩
    rw [named_bind]
    refine ⟨g, hh.trans e2, ?_⟩
    rw [need_bind]
    refine ⟨P.owed _ hun, ?_⟩
    rw [named_bind]
    refine ⟨r, hread r e3, ?_⟩
    dsimp only
    rw [named_bind]
    refine ⟨(rows, H'.paid g.owedPlanes, []), ?_, rfl⟩
    rw [← hrows]
    exact (flThen_some _ _ G H' [] [] fs c1).trans rfl
  obtain ⟨Gp, ep, lp⟩ := planes_late seat lm readers e1 P.sizedF e2 hr
  obtain ⟨Gq, eq, lq⟩ := planes_late seat lm readers ((hA.fork s').trans P.behind) P.sizedG
    (hh.trans e2) hr'
  have hG1' : G1 = Gp := by
    rw [ep, hA.mark, fork_putFork s F _ P.front] at hG1
    exact (Option.some.inj hG1).symm
  have hq : (seat.mark s' (H'.paid g.owedPlanes)).fork? = some Gq := by
    rw [eq, hA.mark]
    exact fork_putFork s' G _ P.behind
  refine ⟨_, G, Gq, hr', P.behind, hq, ?_, P.trees⟩
  rw [hG1']
  show lateG G Gq = lateG F Gp
  rw [lq, lp]

/-- The same under the equation of the readers, and with the room told through the next slot. -/
theorem planes_runSame (lm : ℕ) (readers : Readers S) (hread : readers s' = readers s)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧ F.next ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j) :
    RunSame (planesRun seat lm readers) s s' :=
  planes_runSame' seat hA P hh lm readers (fun _ h => hread.trans h) fun g hg =>
    ⟨(hwin g hg).1, Nat.le_trans (hwin g hg).1 (hwin g hg).2.1, (hwin g hg).2.2⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.planeClaimsOwn_at
#print axioms VerifiableInference.OnPublicFiles.joinF_at
#print axioms VerifiableInference.OnPublicFiles.join_runSame'
#print axioms VerifiableInference.OnPublicFiles.planes_runSame'
#print axioms VerifiableInference.OnPublicFiles.join_runSame
#print axioms VerifiableInference.OnPublicFiles.planes_runSame
