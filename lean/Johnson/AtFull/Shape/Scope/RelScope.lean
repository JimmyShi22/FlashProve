-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/RelScope.lean: WHAT publicOfO RETURNS AT ANY FILES IN THE GOALS' SCOPE AND
AT THE STORED FULL-SIZE FILES MEET SameRead (Scope/Rel.lean). Theorems; nothing is evaluated.

* stripA_turn, group_strip, group_strip_carried: a group's plan at another single shift, under turned
  free numbers, is the plan but for what stripPlan lays: HonestTraceRun.SetUp.group_turn and
  group_carried (Johnson/HonestTrace/Run/SetUpAttPlan.lean, SetUpAttConfig.lean) with their whole
  conclusion in place of five fields; the walk of group_turn's proof, with plan_turn's record kept.
* **sameRead_in_scope**.

Limits. At the format's second hash function. The return at the stored files is a hypothesis, as in
public_in_scope, and so is the return at F. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.HonestTrace.Run.SetUpJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok)
open Attention (ACall Cfg Shape Line Plan tableOf rowKR rowKFD shdOf)
open VerifiableInference.PlanWritten (publicOfO publicSteps_of_O ConfigCut)
open Fo.Pub (midQ)
open HonestTraceRun.SetUp (turnK turnK_kind turnK_segs turnK_pcs shapeHid_turn plan_turn fill_turn
  allWords allWords_sh group_congr group_same SameForAtt SamePlans scanTurn layTurn pubTurn
  shTests_in_range kfdB_in_range mapM_rel rel_get rel_len read_of_scope scan_turn shape_turn_in_scope
  free_bounds public_in_scope pubOf_turn sameForAtt_turn shifts_of_read base_facts polLayout_turn
  owner_turn)

theorem stripA_turn (kFD : Nat) (Tt : Array Nat) (Sm v : Nat) (k : ACall) :
    stripA (turnK kFD Tt Sm v k) = stripA k := by
  unfold turnK
  split <;> rfl

/-- **A group's plan at another single shift is the plan but for what stripPlan lays.** -/
theorem group_strip {P : PolScan} {y : Layer.Lay} {mq : Nat → Nat} {lines : List Attention.Line}
    {g v v' : Nat} {X : Attention.Plan} (hg : g * y.Lam + y.Lam ≤ 48)
    (h : Attention.group P y (allWords v) mq lines g = .ok X)
    (hk : P.h.kFD = 16) (hS : P.h.Sx = 12) (hr : P.h.rx = 8) (hd : y.ldh = 7)
    (h4 : 4 ≤ v') (h12 : v' ≤ 12) :
    ∃ X', Attention.group P y (allWords v') mq lines g = .ok X' ∧ stripPlan X' = stripPlan X := by
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
  obtain ⟨A, -, -, hA, -, hFs⟩ := OnBytes.Road.L5.hid_calls hh
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
    ?_, ?_⟩
  · unfold Attention.group
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
  · have eA : (X0.S.calls.map (turnK cf.kFD X0.S.Tt (2 ^ cf.ldh * clamp * clamp) v')).map stripA =
        X0.S.calls.map stripA := by
      rw [Array.map_map]
      exact Array.map_congr_left fun k _ => stripA_turn _ _ _ _ k
    have eC : ((X0.S.calls.map (turnK cf.kFD X0.S.Tt (2 ^ cf.ldh * clamp * clamp) v')).map (·.call)).map stripCall =
        X0.fs.calls.map stripCall := by
      rw [hFs, Array.map_map, Array.map_map, Array.map_map]
      exact Array.map_congr_left fun k _ => congrArg ACall.call (stripA_turn _ _ _ _ k)
    unfold stripPlan stripS stripF
    dsimp only
    rw [eA, eC, Sh.cfg]

/-- The same under turned free numbers and any one shift of the group in front. -/
theorem group_strip_carried {P' P : PolScan} (E : SameForAtt P' P) {y : Layer.Lay} (h' : Layer.Shape)
    {s s' : Layer.Scales} {mq : Nat → Nat} {lines : List Line} {g : Nat} {X : Plan}
    (hg : g * y.Lam + y.Lam ≤ 48) (hk : P.h.kFD = 16) (hS : P.h.Sx = 12) (hr : P.h.rx = 8)
    (hd : y.ldh = 7) (one : ∃ v, ∀ lam, lam < y.Lam → s.klSh (g * y.Lam + lam) = v)
    (one' : ∃ v', 4 ≤ v' ∧ v' ≤ 12 ∧ ∀ lam, lam < y.Lam → s'.klSh (g * y.Lam + lam) = v')
    (h : Attention.group P y s mq lines g = .ok X) :
    ∃ X', Attention.group P' { y with h := h' } s' mq lines g = .ok X' ∧
      stripPlan X' = stripPlan X := by
  obtain ⟨v, hv⟩ := one
  obtain ⟨v', h4, h12, hv'⟩ := one'
  have a : ∀ (w : Nat) (lam : Nat), lam < y.Lam → (allWords w).klSh (g * y.Lam + lam) = w :=
    fun w lam hl => allWords_sh w (by omega)
  rw [group_congr (s' := allWords v) fun lam hl => (hv lam hl).trans (a v lam hl).symm] at h
  obtain ⟨X', hX', r⟩ := group_strip hg h hk hS hr hd h4 h12
  refine ⟨X', ?_, r⟩
  rw [group_same E, group_congr (s' := allWords v') fun lam hl => (hv' lam hl).trans (a v' lam hl).symm]
  exact hX'

/-- A member of the attention plans as the public part lays them: a plan of the list, with its seam
as it stands. -/
theorem zip_at {l : List Plan} {seen : Array SubPlan} {g : Nat} {a : Plan}
    (h : (l.toArray.zipWith
      (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen)[g]? = some a) :
    ∃ b, l[g]? = some b ∧ a = { b with seam := a.seam } := by
  rw [Array.getElem?_zipWith] at h
  cases hb : l.toArray[g]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hs : seen[g]? with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, by simpa using hb, rfl⟩

/-- **WHAT publicOfO RETURNS AT FILES IN SCOPE AND AT THE STORED FILES MEET SameRead.** -/
theorem sameRead_in_scope {X X₀ : Public} {F : VerifierAndGoals.PublicFiles}
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (hC : VerifierAndGoals.InScope F = true)
    (hX : publicOfO OnBytes.secondHashFunction F.pol F.KL (some F.lay) = .ok X) : SameRead X X₀ := by
  obtain ⟨pp, hR⟩ := read_of_scope hC
  have S₀ := publicSteps_of_O h₀
  have S := publicSteps_of_O hX
  obtain ⟨fLam, fNGr, fldh, fk, fS, fr, fT, fone⟩ := base_facts h₀
  obtain ⟨X', hX', SP⟩ := public_in_scope h₀ hC
  obtain rfl : X' = X := Except.ok.inj (hX'.symm.trans hX)
  have hP₀ : polScan VerifierAndGoals.storedPublicFiles.pol = .ok X₀.P := polLayout_scan S₀.layout
  have hP : polScan F.pol = .ok X'.P := polLayout_scan S.layout
  have hP' : polScan (VerifierAndGoals.policyFile (VerifierAndGoals.freeLinesOf pp)) = .ok X'.P := by
    rw [← OnBytes.Road.Hd.policy_of_scope hC hR]
    exact hP
  have eP : X'.P = scanTurn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp))
      (VerifierAndGoals.freeLinesOf pp) := scan_turn (v₀ := VerifierAndGoals.storedLines) hP' hP₀
  obtain ⟨b1, b2, -, -, -, -, -, -⟩ := free_bounds hR
  have hPt : polScan F.pol = .ok (scanTurn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp))
      (VerifierAndGoals.freeLinesOf pp)) := eP ▸ hP
  have p1 := polLayout_turn S₀.layout hPt (shape_turn_in_scope hC hR hPt hP₀) b1 b2
  have ey : X'.layers.y = layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp) :=
    congrArg Prod.snd (Except.ok.inj (S.layout.symm.trans p1))
  have erope : X'.layers.rope = X₀.layers.rope := by
    have a := S.rope
    rw [ey] at a
    have b : Layer.ropeOf (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h =
      Layer.ropeOf X₀.layers.y.h := rfl
    rw [b] at a
    exact Except.ok.inj (a.symm.trans S₀.rope)
  have eL : X'.layers = pubTurn X₀.layers (VerifierAndGoals.freeLinesOf pp) X'.layers.sc X₀.layers.rope := by
    have a := S.layers
    have b := pubOf_turn S₀.layers (VerifierAndGoals.freeLinesOf pp) X'.layers.sc X₀.layers.rope
    rw [ey, SP.wsLay, erope, eP] at a
    exact Except.ok.inj (a.symm.trans b)
  have f1 : flatP X'.P = flatP X₀.P := by
    rw [eP]
    rfl
  have f2 : flatLay X'.layers = flatLay X₀.layers := by
    rw [eL]
    rfl
  have f3 : flatH X'.hS = flatH X₀.hS := by
    rw [S.hS, S₀.hS, eP, ey]
    rfl
  have f4 : X'.owner = X₀.owner := by
    have a := S.owner
    rw [ey, SP.G, owner_turn] at a
    exact Except.ok.inj (a.symm.trans S₀.owner)
  have h4 := Johnson.Unfolds.ledger_h4 hC hR p1
  obtain ⟨A0, seen, k3, -, k7, -⟩ := S.attention
  obtain ⟨B0, seen₀, m3, -, m7, -⟩ := S₀.attention
  have c : ConfigCut X'.P X'.layers.y X'.layers.sc (midQ X'.layers.y) A0 := by
    rcases k3 with ⟨-, c⟩ | ⟨hp, -⟩
    · exact c
    · rw [ey, h4] at hp
      cases hp
  have c₀ : ConfigCut X₀.P X₀.layers.y X₀.layers.sc (midQ X₀.layers.y) B0 := by
    rcases m3 with ⟨-, c⟩ | ⟨hp, -⟩
    · exact c
    · have e : (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)).h.p4 = X₀.layers.y.h.p4 := rfl
      rw [e, hp] at h4
      cases h4
  obtain ⟨lines, ps, r1, -, -, q, -, rfl⟩ := c
  obtain ⟨lines₀, ps₀, r2, -, -, q₀, -, rfl⟩ := c₀
  have elines : lines = lines₀ := by
    rw [eP] at r1
    exact Except.ok.inj (r1.symm.trans r2)
  subst elines
  -- the scale file
  obtain ⟨P1, hP1, hshape⟩ := Meaning.Ret.shape_of_read hC hR
  obtain rfl : P1 = scanTurn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp))
      (VerifierAndGoals.freeLinesOf pp) := Except.ok.inj (hP1.symm.trans hPt)
  obtain ⟨q2, -, -⟩ := Meaning.Ret.scales_return hC hR
  obtain ⟨c1, -, -⟩ := Lk6.AtPlan.layout_sizes (Lk6.AtPlan.polLayout_layout p1)
  have esc : X'.layers.sc = Meaning.Ret.recOf F.KL := by
    have a := S.scales
    rw [ey, c1.trans hshape] at a
    exact Except.ok.inj (a.symm.trans q2)
  obtain ⟨ps', hM', hRel⟩ := mapM_rel
    (f' := Attention.group (scanTurn X₀.P (VerifierAndGoals.Lines.valuesAt (VerifierAndGoals.freeLinesOf pp))
      (VerifierAndGoals.freeLinesOf pp)) (layTurn X₀.layers.y (VerifierAndGoals.freeLinesOf pp)) X'.layers.sc
      (midQ X₀.layers.y) lines) (R := fun a b => stripPlan a = stripPlan b) _ _
    (fun g hg Xg hXg => by
      have hg' : g < X₀.layers.y.NGr := List.mem_range.1 hg
      have hg12 : g < 12 := by
        rw [fNGr] at hg'
        exact hg'
      have k2 : g * X₀.layers.y.Lam + X₀.layers.y.Lam ≤ 48 := by
        rw [fLam]
        omega
      refine group_strip_carried (sameForAtt_turn X₀.P _ _) _ k2 fk fS fr fldh
        ⟨X₀.layers.sc.klSh (g * 4 + 0), fun lam hl => ?_⟩
        ⟨(Meaning.Ret.recOf F.KL).klSh (g * 4), (shifts_of_read hC hR hg12 (l := 0) (by omega)).2.1,
          (shifts_of_read hC hR hg12 (l := 0) (by omega)).2.2, fun lam hl => ?_⟩ hXg
      · rw [fLam] at hl ⊢
        exact fone g hg12 lam hl
      · rw [fLam] at hl ⊢
        rw [esc]
        exact (shifts_of_read hC hR hg12 hl).1) q₀
  have eps : ps' = ps := by
    rw [ey, eP] at q
    exact Except.ok.inj (hM'.symm.trans q)
  subst eps
  have f5 : X'.A.map stripPlan = X₀.A.map stripPlan := by
    apply Array.ext
    · rw [Array.size_map, Array.size_map, SP.sizeA]
    · intro i h1 h2
      rw [Array.size_map] at h1 h2
      rw [Array.getElem_map, Array.getElem_map]
      have g1 : X'.A[i]? = some X'.A[i] := Array.getElem?_eq_getElem h1
      have g2 : X₀.A[i]? = some X₀.A[i] := Array.getElem?_eq_getElem h2
      generalize X'.A[i] = a at g1 ⊢
      generalize X₀.A[i] = a₀ at g2 ⊢
      obtain ⟨qs, -⟩ := SP.A i _ _ g1 g2
      rw [k7] at g1
      rw [m7] at g2
      obtain ⟨b, hb, eb⟩ := zip_at g1
      obtain ⟨b₀, hb₀, eb₀⟩ := zip_at g2
      have r : stripPlan b = stripPlan b₀ := rel_get hRel i b b₀ hb hb₀
      have e1 : stripPlan a = { stripPlan b with seam := a.seam } := by
        have t : stripPlan { b with seam := a.seam } = { stripPlan b with seam := a.seam } := rfl
        rw [← t, ← eb]
      have e2 : stripPlan a₀ = { stripPlan b₀ with seam := a₀.seam } := by
        have t : stripPlan { b₀ with seam := a₀.seam } = { stripPlan b₀ with seam := a₀.seam } := rfl
        rw [← t, ← eb₀]
      rw [e1, e2, r, qs]
  unfold SameRead flat
  rw [f1, f2, f3, SP.HLy, SP.G, f5, SP.H, f4]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.group_strip
#print axioms Johnson.AtFull.Shape.Scope.group_strip_carried
#print axioms Johnson.AtFull.Shape.Scope.zip_at
#print axioms Johnson.AtFull.Shape.Scope.sameRead_in_scope
