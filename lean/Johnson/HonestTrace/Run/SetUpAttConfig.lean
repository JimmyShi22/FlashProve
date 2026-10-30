-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpAttConfig.lean

Attention's "configO" (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) under other free numbers, another
layers' shape and other softmax shifts, one for each group. Its return is hypothesis p14 of the
library's "publicOfO_of_parts" (Johnson/AtFull/Public/Ledger.lean). One structure, one definition,
and theorems.

Main definitions:
* "SameForAtt P' P": nineteen fields of two scans are equal: the settings, sixteen numbers of the
  header, the lines callA, the tables' digests.
* "AlikePlans": two plans have the same seam, ns, own, size of the forest and S.Tt.

Main theorems:
* "group_same": under "SameForAtt", "Attention.group" gives the same at P' and P, whatever shape
  is set in the layers' layout.
* "group_carried": one group: from any one shift to any one shift in 4 to 12.
* "config_turn": where "configO o P y s mq" returns c, "configO" returns at P', at y with another
  shape and at other scales s' a c' with the same hCallsA, as many plans, each pair of plans with
  the same seam, ns, own and size of the forest, and the same list of (tl, Fp, Tp). At any hash o.
* "mapM_rel", "rel_len", "rel_get", "rel_map": on lists that are alike member by member.

Limits. "config_turn" asks: y.NGr * y.Lam ≤ 48; P.h.kFD = 16, P.h.Sx = 12, P.h.rx = 8, y.ldh = 7;
each group has one shift in s, and one shift in s' that lies in 4 to 12. Conditional: no scan at
which "configO" returns is shown here.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpAttPlan
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)
open Attention (Line Plan)
open VerifiableInference.PlanWritten (tableHeldO)
open VerifiableInference.PlanWritten.Attention (configO)

/-- **All that attention's configO reads of the parameter file as read** is the same in P' and P: the run's numbers, sixteen numbers of the header, the lines callA, the tables' digests. -/
structure SameForAtt (P' P : PolScan) : Prop where
  settings : P'.settings = P.settings
  Sx : P'.h.Sx = P.h.Sx
  lt : P'.h.lt = P.h.lt
  lB : P'.h.lB = P.h.lB
  H : P'.h.H = P.h.H
  Gk : P'.h.Gk = P.h.Gk
  ll : P'.h.ll = P.h.ll
  rx : P'.h.rx = P.h.rx
  kFD : P'.h.kFD = P.h.kFD
  lmS : P'.h.lmS = P.h.lmS
  la : P'.h.la = P.h.la
  lmbA : P'.h.lmbA = P.h.lmbA
  nmin : P'.h.nmin = P.h.nmin
  NAs : P'.h.NAs = P.h.NAs
  lmh : P'.h.lmh = P.h.lmh
  lmo : P'.h.lmo = P.h.lmo
  iotaA0 : P'.h.iotaA0 = P.h.iotaA0
  polCallsA : P'.polCallsA = P.polCallsA
  tblPol : P'.tblPol = P.tblPol

/-- A group's plan reads of P what SameForAtt names, and of the layers' layout not its shape. -/
theorem group_same {P' P : PolScan} (E : SameForAtt P' P) (y : Layer.Lay) (h' : Layer.Shape) (s : Layer.Scales)
    (mq : Nat → Nat) (lines : List Line) (g : Nat) :
    Attention.group P' { y with h := h' } s mq lines g = Attention.group P y s mq lines g := by
  unfold Attention.group Attention.fill Attention.inOf
  simp only [E.settings, E.Sx, E.lt, E.lB, E.H, E.Gk, E.ll, E.rx, E.kFD, E.lmS, E.la, E.lmbA, E.nmin, E.NAs, E.lmh, E.lmo,
    E.iotaA0]

/-! ### lists that are alike member by member -/

theorem mapM_rel {α β : Type} {f f' : α → Except String β} {R : β → β → Prop} :
    ∀ (l : List α) (r : List β), (∀ x ∈ l, ∀ b, f x = .ok b → ∃ b', f' x = .ok b' ∧ R b' b) →
      l.mapM f = .ok r → ∃ r', l.mapM f' = .ok r' ∧ List.Forall₂ R r' r
  | [], r, _, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: l, r, H, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := OnBytes.Road.L5.mapM_cons_ok h
    obtain ⟨b', hb', hR⟩ := H x (List.mem_cons_self ..) b hb
    obtain ⟨bs', hbs', hRs⟩ := mapM_rel l bs (fun a ha => H a (List.mem_cons_of_mem _ ha)) hbs
    refine ⟨b' :: bs', ?_, List.Forall₂.cons hR hRs⟩
    rw [List.mapM_cons, hb', hbs']
    rfl

theorem rel_len {β : Type} {R : β → β → Prop} : ∀ {r' r : List β}, List.Forall₂ R r' r → r'.length = r.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by rw [List.length_cons, List.length_cons, rel_len t]

theorem rel_get {β : Type} {R : β → β → Prop} : ∀ {r' r : List β}, List.Forall₂ R r' r →
    ∀ (g : Nat) (a a₀ : β), r'[g]? = some a → r[g]? = some a₀ → R a a₀
  | _, _, .nil, g, a, a₀, h1, _ => by simp at h1
  | _, _, .cons hd _, 0, a, a₀, h1, h2 => by
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    exact hd
  | _, _, .cons _ t, g + 1, a, a₀, h1, h2 => rel_get t g a a₀ (by simpa using h1) (by simpa using h2)

theorem rel_map {β γ : Type} {R : β → β → Prop} {f : β → γ} (hf : ∀ a b, R a b → f a = f b) :
    ∀ {r' r : List β}, List.Forall₂ R r' r → r'.map f = r.map f
  | _, _, .nil => rfl
  | _, _, .cons hd t => by rw [List.map_cons, List.map_cons, hf _ _ hd, rel_map hf t]

/-- What the steps behind read of a group's plan. -/
def AlikePlans (a a₀ : Plan) : Prop :=
  a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧ forestSize a.fs = forestSize a₀.fs ∧ a.S.Tt = a₀.S.Tt

/-- One group: from any one shift to any one shift in 4 to 12, under turned free numbers and a turned layers' shape. -/
theorem group_carried {P' P : PolScan} (E : SameForAtt P' P) {y : Layer.Lay} (h' : Layer.Shape) {s s' : Layer.Scales}
    {mq : Nat → Nat} {lines : List Line} {g : Nat} {X : Plan} (hg : g * y.Lam + y.Lam ≤ 48)
    (hk : P.h.kFD = 16) (hS : P.h.Sx = 12) (hr : P.h.rx = 8) (hd : y.ldh = 7)
    (one : ∃ v, ∀ lam, lam < y.Lam → s.klSh (g * y.Lam + lam) = v)
    (one' : ∃ v', 4 ≤ v' ∧ v' ≤ 12 ∧ ∀ lam, lam < y.Lam → s'.klSh (g * y.Lam + lam) = v')
    (h : Attention.group P y s mq lines g = .ok X) :
    ∃ X', Attention.group P' { y with h := h' } s' mq lines g = .ok X' ∧ AlikePlans X' X := by
  obtain ⟨v, hv⟩ := one
  obtain ⟨v', h4, h12, hv'⟩ := one'
  have a : ∀ (w : Nat) (lam : Nat), lam < y.Lam → (allWords w).klSh (g * y.Lam + lam) = w :=
    fun w lam hl => allWords_sh w (by omega)
  rw [group_congr (s' := allWords v) fun lam hl => (hv lam hl).trans (a v lam hl).symm] at h
  obtain ⟨X', hX', r⟩ := group_turn hg h hk hS hr hd h4 h12
  refine ⟨X', ?_, r⟩
  rw [group_same E, group_congr (s' := allWords v') fun lam hl => (hv' lam hl).trans (a v' lam hl).symm]
  exact hX'

/-- **STEP p14, CARRIED.** -/
theorem config_turn {o : Nat → ByteArray → ByteArray} {P' P : PolScan} (E : SameForAtt P' P) {y : Layer.Lay}
    (h' : Layer.Shape) {s s' : Layer.Scales} {mq : Nat → Nat} {c : Attention.Config}
    (h : configO o P y s mq = .ok c) (hN : y.NGr * y.Lam ≤ 48)
    (hk : P.h.kFD = 16) (hS : P.h.Sx = 12) (hr : P.h.rx = 8) (hd : y.ldh = 7)
    (one : ∀ g, g < y.NGr → ∃ v, ∀ lam, lam < y.Lam → s.klSh (g * y.Lam + lam) = v)
    (one' : ∀ g, g < y.NGr → ∃ v', 4 ≤ v' ∧ v' ≤ 12 ∧ ∀ lam, lam < y.Lam → s'.klSh (g * y.Lam + lam) = v') :
    ∃ c', configO o P' { y with h := h' } s' mq = .ok c' ∧ c'.hCallsA = c.hCallsA ∧ c'.plans.size = c.plans.size ∧
      (∀ (g : Nat) (a a₀ : Plan), c'.plans[g]? = some a → c.plans[g]? = some a₀ →
        a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧ forestSize a.fs = forestSize a₀.fs) ∧
      (c'.plans.map fun X => (⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩ : SubPlan)) =
        c.plans.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩ := by
  unfold configO at h ⊢
  dsimp only at h ⊢
  rw [E.polCallsA, E.Gk, E.lmh, E.lt, E.lmo, E.lmbA, E.lmS, E.NAs]
  obtain ⟨lines, a1, h⟩ := exc_bind h
  obtain ⟨_, a2, h⟩ := exc_bind h
  obtain ⟨_, a3, h⟩ := exc_bind h
  obtain ⟨plans, hM, h⟩ := exc_bind h
  obtain ⟨plans', hM', hR⟩ := mapM_rel (f' := Attention.group P' { y with h := h' } s' mq lines) (R := AlikePlans) _ _
    (fun g hg X hX => by
      have hg' : g < y.NGr := List.mem_range.1 hg
      have k : (g + 1) * y.Lam ≤ y.NGr * y.Lam := Nat.mul_le_mul_right _ hg'
      have k2 : g * y.Lam + y.Lam ≤ 48 := by
        rw [Nat.add_mul, Nat.one_mul] at k
        omega
      exact group_carried E h' k2 hk hS hr hd (one g hg') (one' g hg') hX) hM
  cases hR with
  | nil => cases h
  | @cons X' X r' r hd0 tl0 =>
    dsimp only at h
    obtain ⟨_, a4, h⟩ := exc_bind h
    obtain rfl := Except.ok.inj h
    have hR : List.Forall₂ AlikePlans (X' :: r') (X :: r) := List.Forall₂.cons hd0 tl0
    refine ⟨{ plans := (X' :: r').toArray, hCallsA := VerifiableInference.PlanWritten.Attention.callsDigestO o lines }, ?_, rfl, ?_, ?_, ?_⟩
    · refine (bind_ok a1).trans ?_
      refine (bind_ok a2).trans ?_
      refine (bind_ok a3).trans ?_
      refine (bind_ok hM').trans ?_
      dsimp only
      have a4' : tableHeldO o P' .exp X'.S.Tt = .ok () := by
        unfold tableHeldO PolScan.tableExpected at a4 ⊢
        rw [E.tblPol, hd0.2.2.2.2]
        exact a4
      refine (bind_ok a4').trans ?_
      rfl
    · show (X' :: r').toArray.size = (X :: r).toArray.size
      rw [List.size_toArray, List.size_toArray, rel_len hR]
    · intro g a a₀ h1 h2
      have q := rel_get hR g a a₀ (by simpa using h1) (by simpa using h2)
      exact ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩
    · show ((X' :: r').toArray.map fun X => (⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩ : SubPlan)) =
        (X :: r).toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩
      rw [List.map_toArray, List.map_toArray, rel_map (fun a b q => by rw [q.1]) hR]

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.group_same
#print axioms HonestTraceRun.SetUp.group_carried
#print axioms HonestTraceRun.SetUp.config_turn
#check @HonestTraceRun.SetUp.config_turn
