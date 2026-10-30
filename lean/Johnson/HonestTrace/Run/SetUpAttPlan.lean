-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpAttPlan.lean

Attention's plan and a group's plan under another single shift: what lies behind
"Attention.shapeHid". Theorems alone; no definition.

Main theorems (on OnBytes/Model/AttentionPlan.lean and OnBytes/Model/AttentionConfig.lean):
* "counts_call_turn", "counts_turn", "elems_turn": what the plan counts over the calls is the same
  under a map t of the calls that keeps their kinds, segments and pieces.
* "plan_turn": where "shapeHid" returns (S, fs) at cf and, at cf with other shifts, S with its
  calls under such a map and fs with other calls, "Attention.plan" returns at the other shifts
  the plan that it returns at cf, but for these two fields.
* "shifts_all", "expanded_all", "fill_turn": on "allWords"
  (Johnson/HonestTrace/Run/SetUpAttSmall.lean).
* "group_turn": where "Attention.group" returns X at "allWords v", it returns at "allWords v'" an
  X' with the same seam, ns, own, size of the forest and S.Tt.

Limits. "group_turn" asks: 4 ≤ v' ≤ 12; P.h.kFD = 16, P.h.Sx = 12, P.h.rx = 8, y.ldh = 7; and
g * y.Lam + y.Lam ≤ 48. It is stated at scales whose words are all one number. Conditional: no
group at which "Attention.group" returns is shown here. The file has two "local macro", "step"
and "jstep": tactics alone.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpAttHid
import Johnson.Road.Lane5AttPub
import Johnson.AtFull.Public.AttLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)
open Attention (ACall Cfg Shape Listed Table Seg Piece Line shape shapeHid layCall expandLine
  placePieces shTests tableOf rowKR rowKFD shdOf Counts In Plan plan)

local macro "step " k:ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             refine (bind_ok ha).trans ?_
             clear ha
             try dsimp only at $k:ident
             try dsimp only))

local macro "jstep " k:ident : tactic =>
  `(tactic| (obtain ⟨nc, $k:ident⟩ := OnBytes.Road.L5.jp_ok $k
             refine (if_neg nc).trans ?_
             clear nc
             refine (pure_bind _ _).trans ?_
             try dsimp only at $k:ident
             try dsimp only))

/-! ### what the plan counts over the calls reads their kinds, segments and pieces alone -/

section
variable {S : Shape} {c' : Cfg} {t : ACall → ACall}

theorem counts_call_turn (h1 : c'.lgk = S.cf.lgk) (h2 : c'.ldh = S.cf.ldh) (t1 : ∀ k, (t k).kind = k.kind)
    (t2 : ∀ k, (t k).segs = k.segs) (t3 : ∀ k, (t k).pcs = k.pcs) (x : Counts) (k : ACall) :
    Counts.call { S with cf := c', calls := S.calls.map t } x (t k) = Counts.call S x k := by
  unfold Attention.Counts.call Attention.Counts.plane Attention.Counts.scores Attention.ACall.holds Attention.ACall.npOf
    Attention.Shape.nvKF
  simp only [t1, t2, t3, h1, h2]

theorem counts_turn (h1 : c'.lgk = S.cf.lgk) (h2 : c'.ldh = S.cf.ldh) (t1 : ∀ k, (t k).kind = k.kind)
    (t2 : ∀ k, (t k).segs = k.segs) (t3 : ∀ k, (t k).pcs = k.pcs) :
    Counts.of { S with cf := c', calls := S.calls.map t } = Counts.of S := by
  unfold Attention.Counts.of
  show (S.calls.map t).foldl (Counts.call { S with cf := c', calls := S.calls.map t }) {} = _
  rw [Array.foldl_map]
  exact congrArg (fun f => S.calls.foldl f {}) (funext fun x => funext fun k => counts_call_turn h1 h2 t1 t2 t3 x k)

theorem elems_turn (h3 : c'.la = S.cf.la) (t1 : ∀ k, (t k).kind = k.kind) (t2 : ∀ k, (t k).segs = k.segs) :
    Shape.tableElems { S with cf := c', calls := S.calls.map t } = S.tableElems := by
  unfold Attention.Shape.tableElems
  simp only [Array.foldl_map, t1, t2, h3]

end

/-- **The plan behind a turned shapeHid**: the same plan, but for the shape and the lookup's record. -/
theorem plan_turn {settings : Settings} {i : In} {cf : Cfg} {sh' : Array Nat} {t : ACall → ACall}
    (t1 : ∀ k, (t k).kind = k.kind) (t2 : ∀ k, (t k).segs = k.segs) (t3 : ∀ k, (t k).pcs = k.pcs)
    {S : Shape} {fs : Forest.Shape} {C : Array Call} (hh : shapeHid settings.lidb cf = .ok (S, fs))
    (hh' : shapeHid settings.lidb { cf with sh := sh' } =
      .ok ({ S with cf := { cf with sh := sh' }, calls := S.calls.map t }, { fs with calls := C }))
    {X : Plan} (h : plan settings i cf = .ok X) :
    plan settings i { cf with sh := sh' } =
      .ok { X with S := { S with cf := { cf with sh := sh' }, calls := S.calls.map t }, fs := { fs with calls := C } } := by
  have ec := (OnBytes.Road.L5.shaped_of_hid hh).cfg
  subst ec
  have eC := counts_turn (S := S) (c' := { S.cf with sh := sh' }) (t := t) rfl rfl t1 t2 t3
  have eW := elems_turn (S := S) (c' := { S.cf with sh := sh' }) (t := t) rfl t1 t2
  unfold Attention.plan at h ⊢
  jstep h
  jstep h
  jstep h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl : (S, fs) = r := Except.ok.inj (hh.symm.trans hr)
  refine (bind_ok hh').trans ?_
  dsimp only at h ⊢
  rw [eC, eW, Array.size_map]
  jstep h
  step h
  jstep h
  jstep h
  step h
  obtain rfl := Except.ok.inj h
  rfl

/-! ### the configuration and the group -/

/-- At allWords v every layer's shift is v. -/
theorem shifts_all (v : Nat) {y : Layer.Lay} {g : Nat} (hg : g * y.Lam + y.Lam ≤ 48) :
    ((Array.range y.Lam).map fun lam => (allWords v).klSh (g * y.Lam + lam)) = (Array.range y.Lam).map fun _ => v :=
  Array.map_congr_left fun lam hl => allWords_sh v (by
    have k := Array.mem_range.1 hl
    omega)

/-- The number of expanded calls does not hang on which one shift a group has. -/
theorem expanded_all (lines : List Line) (n v v' : Nat) :
    Attention.expandedCalls lines ((Array.range n).map fun _ => v) =
      Attention.expandedCalls lines ((Array.range n).map fun _ => v') := by
  have e : ∀ w : Nat, ((Array.range n).map fun _ => w).toList.eraseDups.length = if n = 0 then 0 else 1 := by
    intro w
    have e0 : ((Array.range n).map fun _ => w).toList = List.replicate n w := by simp
    rw [e0]
    cases n with
    | zero => rfl
    | succ m =>
      rw [OnBytes.Road.L5.eraseDups_replicate]
      rfl
  unfold Attention.expandedCalls
  simp only [e]

theorem fill_turn {P : PolScan} {y : Layer.Lay} {lines : List Line} {g v : Nat} (v' : Nat) {cf : Cfg}
    (hg : g * y.Lam + y.Lam ≤ 48) (hf : Attention.fill P y (allWords v) lines g = .ok cf) :
    Attention.fill P y (allWords v') lines g = .ok { cf with sh := (Array.range y.Lam).map fun _ => v' } ∧
      cf.sh = (Array.range y.Lam).map fun _ => v := by
  unfold Attention.fill at hf ⊢
  dsimp only at hf ⊢
  rw [shifts_all v hg] at hf
  rw [shifts_all v' hg]
  obtain ⟨_, a1, hf⟩ := exc_bind hf
  obtain ⟨_, a2, hf⟩ := exc_bind hf
  obtain rfl := Except.ok.inj hf
  refine ⟨?_, rfl⟩
  refine (bind_ok a1).trans ?_
  rw [expanded_all lines y.Lam v' v]
  refine (bind_ok a2).trans ?_
  rfl

/-- **ATTENTION UNDER A TURNED SHIFT.** Where a group's plan is made with every shift v, it is made with every shift v'
in 4 to 12, and what the steps behind read of it has not turned. -/
theorem group_turn {P : PolScan} {y : Layer.Lay} {mq : Nat → Nat} {lines : List Attention.Line}
    {g v v' : Nat} {X : Attention.Plan} (hg : g * y.Lam + y.Lam ≤ 48)
    (h : Attention.group P y (allWords v) mq lines g = .ok X)
    (hk : P.h.kFD = 16) (hS : P.h.Sx = 12) (hr : P.h.rx = 8) (hd : y.ldh = 7)
    (h4 : 4 ≤ v') (h12 : v' ≤ 12) :
    ∃ X', Attention.group P y (allWords v') mq lines g = .ok X' ∧ X'.seam = X.seam ∧ X'.ns = X.ns ∧
      X'.own = X.own ∧ OnBytes.Model.forestSize X'.fs = OnBytes.Model.forestSize X.fs ∧ X'.S.Tt = X.S.Tt := by
  unfold Attention.group at h
  obtain ⟨cf, hf, h⟩ := exc_bind h
  obtain ⟨X0, hp, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, a1, h⟩ := exc_bind h
  obtain ⟨_, a2, h⟩ := exc_bind h
  obtain ⟨_, a3, h⟩ := exc_bind h
  obtain ⟨_, a4, h⟩ := exc_bind h
  obtain ⟨_, a5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  obtain ⟨hf', esh⟩ := fill_turn v' hg hf
  have hh := (OnBytes.Road.L5.plan_shape hp).1
  have Sh := OnBytes.Road.L5.shaped_of_hid hh
  obtain ⟨A, -, -, hA, -, -⟩ := OnBytes.Road.L5.hid_calls hh
  obtain ⟨-, -, -, -, hz⟩ := OnBytes.Road.L5.calls_of_shape hA
  have hLam : y.Lam = 2 ^ cf.ll := by
    rw [← hz, esh]
    simp
  have ef := OnBytes.Road.L5.fill_eq hf
  have ck : cf.kFD = 16 := by
    rw [ef]
    exact hk
  have cS : cf.S = 12 := by
    rw [ef]
    exact hS
  have cr : cf.rx = 8 := by
    rw [ef]
    exact hr
  have cd : cf.ldh = 7 := by
    rw [ef]
    exact hd
  have cT : cf.Ty = 2 ^ 18 := by
    rw [ef]
    rfl
  have eT : X0.S.Tt = OnBytes.Road.L5.refL.toArray := by
    have e := Sh.exp
    rw [cS, cr, OnBytes.Road.K4.Trial.AttLaws.expTable_W] at e
    exact (Option.some.inj e).symm
  have sz : X0.S.Tt.size = 2307 := by
    rw [eT, List.size_toArray]
    exact OnBytes.Road.L5.refL_length
  have hv : ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = v := by
    intro lam hl
    rw [esh, OnBytes.Road.Hd.getD_rangeMap _ _ _ (hLam ▸ hl)]
  have hh' := shapeHid_turn (M := 4096) (sh' := (Array.range y.Lam).map fun _ => v') (v := v) (v' := v') hh hv
    (by simp [hLam]) (fun lam hl => OnBytes.Road.Hd.getD_rangeMap _ _ _ (hLam ▸ hl))
    (by rw [sz, cd]; exact shTests_in_range ck cS cT h4 h12)
    (fun t => by rw [eT]; exact OnBytes.Road.K4.Trial.AttLaws.refL_le t)
    (by rw [sz, cd, ck]; exact kfdB_in_range h4 h12)
  have hp' := plan_turn (turnK_kind _ _ _ _) (turnK_segs _ _ _ _) (turnK_pcs _ _ _ _) hh hh' hp
  refine ⟨{ X0 with
      S := { X0.S with
        cf := { cf with sh := (Array.range y.Lam).map fun _ => v' }
        calls := X0.S.calls.map (turnK cf.kFD X0.S.Tt (2 ^ cf.ldh * clamp * clamp) v') }
      fs := { X0.fs with
        calls := (X0.S.calls.map (turnK cf.kFD X0.S.Tt (2 ^ cf.ldh * clamp * clamp) v')).map (·.call) } },
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  unfold Attention.group
  refine (bind_ok hf').trans ?_
  refine (bind_ok hp').trans ?_
  dsimp only
  refine (bind_ok a1).trans ?_
  refine (bind_ok a2).trans ?_
  refine (bind_ok a3).trans ?_
  refine (bind_ok a4).trans ?_
  rw [Sh.cfg] at a5
  refine (bind_ok a5).trans ?_
  rfl

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.counts_turn
#print axioms HonestTraceRun.SetUp.elems_turn
#print axioms HonestTraceRun.SetUp.plan_turn
#print axioms HonestTraceRun.SetUp.fill_turn
#print axioms HonestTraceRun.SetUp.group_turn
#check @HonestTraceRun.SetUp.group_turn
