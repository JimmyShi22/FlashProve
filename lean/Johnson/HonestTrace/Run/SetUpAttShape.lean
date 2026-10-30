-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpAttShape.lean

Attention's shape under another single shift. Two definitions, and theorems (on
OnBytes/Model/AttentionShape.lean).

Main definitions:
* "reSh v'": a member of the expanded list of calls, with the shift v' where its table hangs on
  the shift.
* "turnK": a call with the shift v' and the table at v', where its kind is kr or kfd.

Main theorems:
* "shape_turn": where "Attention.shape cf" returns A and every layer's shift in cf is v, it returns
  at cf with the shifts sh', all of them v': A with that configuration and each call under "turnK".
  Asked: hz', sh' has 2 ^ cf.ll entries; ht, "shTests" passes at v'.
* "expand_turn", "listed_turn", "place_turn", "layCall_turn": the steps of "Attention.shape".
* "mapM_turn": a law on List.mapM in Except.

Limits. Conditional: no configuration at which "Attention.shape" returns is shown here. One shift
for all layers of the configuration, on either side. The file has one "local macro", "step": a
tactic alone.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpAttSmall
import Johnson.Road.Lane5AttLaid
import Johnson.LPFPol.HashReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)
open Attention (ACall Cfg Shape Listed Table Piece Line shape shapeHid layCall expandLine
  placePieces shTests tableOf rowKR rowKFD shdOf)

local macro "step " k:ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             refine (bind_ok ha).trans ?_
             clear ha
             try dsimp only at $k:ident
             try dsimp only))

/-- A member of the expanded call list with the shift v' where its table hangs on the shift. -/
def reSh (v' : Nat) (x : Listed) : Listed := (x.1, x.2.1, if x.2.1.bySh then v' else x.2.2.1, x.2.2.2)

/-- A call with the shift v' and the table at v', where its table hangs on the shift. -/
def turnK (kFD : Nat) (Tt : Array Nat) (Sm v' : Nat) (k : ACall) : ACall :=
  match k.kind with
  | .kr => { k with sh := v', call := { k.call with tau := tableOf 16 (rowKR v') } }
  | .kfd => { k with sh := v',
                     call := { k.call with tau := tableOf kFD (rowKFD Tt (shdOf Tt.size Sm v') v') } }
  | _ => k

theorem expand_turn (v v' : Nat) (l : Line) : expandLine [v'] l = (expandLine [v] l).map (reSh v') := by
  unfold Attention.expandLine reSh
  by_cases hb : l.kind.bySh = true
  · simp [hb]
  · simp [hb]

theorem listed_turn (v v' : Nat) (lines : List Line) :
    lines.flatMap (expandLine [v']) = (lines.flatMap (expandLine [v])).map (reSh v') := by
  rw [List.map_flatMap]
  exact congrArg (fun f => List.flatMap f lines) (funext fun l => expand_turn v v' l)

theorem mapM_turn {α β : Type} {f f' : α → Except String β} {g : α → α} {t : β → β} :
    ∀ (l : List α) (r : List β), (∀ x ∈ l, ∀ y, f x = .ok y → f' (g x) = .ok (t y)) →
      l.mapM f = .ok r → (l.map g).mapM f' = .ok (r.map t)
  | [], r, _, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | x :: l, r, H, h => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := OnBytes.Road.L5.mapM_cons_ok h
    rw [List.map_cons, List.mapM_cons, H x (List.mem_cons_self ..) y hy,
      mapM_turn l ys (fun a ha => H a (List.mem_cons_of_mem _ ha)) hys]
    rfl

section
variable {cf : Cfg} {sh' : Array Nat} {v v' HA : Nat}

theorem place_turn (hHA : 0 < HA) (hv : ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = v)
    (hv' : ∀ lam < 2 ^ cf.ll, sh'.getD lam 0 = v') (kind : Table) (sh : Nat)
    (hs : kind.bySh = true → sh = v) (segs : List Attention.Seg) :
    placePieces { cf with sh := sh' } HA kind (if kind.bySh then v' else sh) segs =
      placePieces cf HA kind sh segs := by
  have a : kind.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = sh :=
    fun hb lam hl => (hv lam hl).trans (hs hb).symm
  have a' : kind.bySh = true → ∀ lam < 2 ^ ({ cf with sh := sh' } : Cfg).ll,
      ({ cf with sh := sh' } : Cfg).sh.getD lam 0 = (if kind.bySh then v' else sh) :=
    fun hb lam hl => by
      rw [if_pos hb]
      exact hv' lam hl
  unfold Attention.placePieces
  simp only [OnBytes.Road.L5.listed_fam (cf := { cf with sh := sh' }) hHA a',
    OnBytes.Road.L5.listed_fam (cf := cf) hHA a]
  rfl

theorem layCall_turn (hHA : 0 < HA) (hv : ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = v)
    (hv' : ∀ lam < 2 ^ cf.ll, sh'.getD lam 0 = v') (Sm : Nat) (Tt : Array Nat) (x : Listed)
    (hs : x.2.1.bySh = true → x.2.2.1 = v) (k : ACall) (h : layCall cf HA Sm Tt x = .ok k) :
    layCall { cf with sh := sh' } HA Sm Tt (reSh v' x) = .ok (turnK cf.kFD Tt Sm v' k) := by
  obtain ⟨name, kind, sh, segs⟩ := x
  have e := place_turn hHA hv hv' kind sh hs segs
  unfold Attention.layCall at h ⊢
  unfold reSh
  dsimp only at h ⊢
  rw [e]
  obtain ⟨_, a1, h⟩ := exc_bind h
  refine (bind_ok a1).trans ?_
  obtain rfl := Except.ok.inj h
  cases kind <;> rfl

end

/-- **The shape under a turned single shift**, with its value. ht: the five tests on the new shift pass. -/
theorem shape_turn {cf : Cfg} {sh' : Array Nat} {v v' : Nat} {A : Shape} (k : shape cf = .ok A)
    (hv : ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = v) (hz' : sh'.size = 2 ^ cf.ll)
    (hv' : ∀ lam < 2 ^ cf.ll, sh'.getD lam 0 = v')
    (ht : shTests cf A.Tt.size (2 ^ cf.ldh * clamp * clamp) v' = .ok ()) :
    shape { cf with sh := sh' } = .ok { A with
      cf := { cf with sh := sh' }
      calls := A.calls.map (turnK cf.kFD A.Tt (2 ^ cf.ldh * clamp * clamp) v') } := by
  obtain ⟨-, hHA⟩ := OnBytes.Road.L5.tests_of_shape k
  obtain ⟨-, -, -, -, hz⟩ := OnBytes.Road.L5.calls_of_shape k
  have hexp := (OnBytes.Road.L5.shaped_of_shape k).exp
  have pos : 0 < 2 ^ cf.ll := Nat.two_pow_pos _
  have s1 : (cf.sh.toList.mergeSort fun a b => decide (a ≤ b)).eraseDups = [v] := by
    have q := OnBytes.Road.L5.shsOf_one hz fun l hl => (hv l hl).trans (hv 0 pos).symm
    unfold OnBytes.Road.L5.shsOf at q
    rw [q, hv 0 pos]
  have s2 : (sh'.toList.mergeSort fun a b => decide (a ≤ b)).eraseDups = [v'] := by
    have q := OnBytes.Road.L5.shsOf_one (cf := { cf with sh := sh' }) hz'
      fun l hl => (hv' l hl).trans (hv' 0 pos).symm
    unfold OnBytes.Road.L5.shsOf at q
    exact q.trans (by rw [show ({ cf with sh := sh' } : Cfg).sh.getD 0 0 = v' from hv' 0 pos])
  unfold Attention.shape at k ⊢
  dsimp only at k ⊢
  rw [s1] at k
  rw [s2]
  step k
  step k
  -- the number of shifts
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (refuseIf_no ?_)).trans ?_
  · rw [hz']
    simp
  step k
  step k
  obtain ⟨Tt, hT, k⟩ := exc_bind k
  refine (bind_ok hT).trans ?_
  dsimp only at k ⊢
  have eT : Tt = A.Tt := Option.some.inj ((OnBytes.Road.L5.orRefuse_ok hT).symm.trans hexp)
  rw [← eT] at ht
  clear eT hexp hT
  step k
  step k
  -- the five tests
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := PUnit.unit) (Meaning.Ret.forM_ok _ _ fun a ha => ?_)).trans ?_
  · obtain rfl := List.mem_singleton.1 ha
    exact (shTests_congr rfl rfl rfl _ _ _).trans ht
  try dsimp only at k
  try dsimp only
  step k
  step k
  step k
  step k
  -- the number of calls
  rw [listed_turn v v' cf.lines]
  obtain ⟨_, a14, k⟩ := exc_bind k
  refine (bind_ok (a := ()) ?_).trans ?_
  · rw [List.length_map]
    exact a14
  -- the calls
  obtain ⟨calls, hM, k⟩ := exc_bind k
  refine (bind_ok (mapM_turn _ _ (fun x hx y hy => layCall_turn hHA hv hv' _ _ x (fun hb => ?_) y hy)
    hM)).trans ?_
  · rcases OnBytes.Road.L5.listed_sh hx with ⟨-, q⟩ | ⟨q, -⟩
    · exact List.mem_singleton.1 q
    · rw [q] at hb
      cases hb
  obtain rfl := Except.ok.inj k
  rw [List.map_toArray]
  rfl

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.shape_turn
