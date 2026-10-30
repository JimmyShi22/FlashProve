-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpAttHid.lean

The lookup's forest and "Attention.shapeHid" (OnBytes/Model/AttentionShape.lean) under another
single shift. Theorems alone; no definition.

Main theorems:
* "forest_congr": where "Forest.shape cs lid" (OnBytes/Model/Forest.lean) returns h, it returns h
  with the calls cs' at calls cs' that have the same numbers n and k and pass "Forest.callAsk";
  and h.calls = cs.
* "turnK_kind", "turnK_segs", "turnK_pcs", "turnK_tot", "turnK_n", "turnK_k", "turnK_iota",
  "noTab_turn": what a call keeps under "turnK" (Johnson/HonestTrace/Run/SetUpAttShape.lean).
  "turnK_sh": what it gets: the shift v'; stated at the kind kfd alone.
* "asks_inv", "asks_of_forest", "noTab_of_ask", "pubAsk_calls", "forest_noAsk": on the tests on
  the calls.
* "shapeHid_turn": where "shapeHid lid cf" returns (S, fs) and every layer's shift in cf is v, it
  returns at cf with the shifts sh', all of them v': S and fs with each call under "turnK".

Limits. "shapeHid_turn" asks, and this file does not prove: hz', sh' has 2 ^ cf.ll entries; ht,
"shTests" passes at v'; hM, a bound M on the entries of S.Tt; hb, "kfdB" holds at M and v'.
Conditional: no configuration at which "shapeHid" returns is shown here. The file has two
"local macro", "step" and "jstep": tactics alone.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.HonestTrace.Run.SetUpAttShape
import Johnson.Unfolds.ShapeEq

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

/-- One test «if c then throw» that is the same, up to unfolding, in the hypothesis and in the goal. -/
local macro "jstep " k:ident : tactic =>
  `(tactic| (obtain ⟨nc, $k:ident⟩ := OnBytes.Road.L5.jp_ok $k
             refine (if_neg nc).trans ?_
             clear nc
             refine (pure_bind _ _).trans ?_
             try dsimp only at $k:ident
             try dsimp only))

/-! ### the forest reads of its calls their numbers n and k, and their number -/

theorem forest_noAsk {cs : Array Call} {lid : Nat} {h : Forest.Shape} (H : Forest.shape cs lid = .ok h) :
    Forest.shapeNoAsk cs lid = .ok h := by
  unfold Forest.shape at H
  obtain ⟨_, _, H⟩ := exc_bind H
  exact H

theorem forest_congr {cs cs' : Array Call} {lid : Nat} {h : Forest.Shape}
    (hn : cs'.map (·.n) = cs.map (·.n)) (hk : cs'.map (·.k) = cs.map (·.k))
    (ask : ∀ c ∈ cs'.toList, Forest.callAsk c = .ok ())
    (H : Forest.shape cs lid = .ok h) :
    Forest.shape cs' lid = .ok { h with calls := cs' } ∧ h.calls = cs := by
  have H' := forest_noAsk H
  have e1 : cs'.size = cs.size := by simpa using congrArg Array.size hn
  have e2 : ∀ m0 : Nat, cs'.foldl (fun m c => min m c.n) m0 = cs.foldl (fun m c => min m c.n) m0 := by
    intro m0
    have a : cs'.toList.map (·.n) = cs.toList.map (·.n) := by simpa using congrArg Array.toList hn
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    have b := congrArg (fun l : List Nat => l.foldl (fun m x => min m x) m0) a
    simpa [List.foldl_map] using b
  have e3 : ∀ m0 : Nat, cs'.foldl (fun m c => max m c.k) m0 = cs.foldl (fun m c => max m c.k) m0 := by
    intro m0
    have a : cs'.toList.map (·.k) = cs.toList.map (·.k) := by simpa using congrArg Array.toList hk
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    have b := congrArg (fun l : List Nat => l.foldl (fun m x => max m x) m0) a
    simpa [List.foldl_map] using b
  have e4 : ∀ d : Nat, (cs'.map fun c => c.n - d) = cs.map fun c => c.n - d := by
    intro d
    have a := congrArg (fun a : Array Nat => a.map (· - d)) hn
    simpa [Array.map_map, Function.comp_def] using a
  refine ⟨?_, ?_⟩
  · rw [Johnson.Unfolds.shape_eq cs' lid ask]
    unfold Forest.shapeNoAsk at H' ⊢
    dsimp only at H' ⊢
    rw [e2, e3, e4, e1]
    jstep H'
    jstep H'
    jstep H'
    jstep H'
    jstep H'
    obtain ⟨r, hr, H'⟩ := exc_bind H'
    refine (bind_ok hr).trans ?_
    obtain ⟨callOf, first, free⟩ := r
    dsimp only at H' ⊢
    jstep H'
    obtain rfl := Except.ok.inj H'
    rfl
  · unfold Forest.shapeNoAsk at H'
    dsimp only at H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain ⟨r, -, H'⟩ := exc_bind H'
    obtain ⟨callOf, first, free⟩ := r
    dsimp only at H'
    obtain ⟨-, H'⟩ := OnBytes.Road.L5.jp_ok H'
    obtain rfl := Except.ok.inj H'
    rfl

/-! ### what a turned call keeps -/

section
variable (kFD : Nat) (Tt : Array Nat) (Sm v' : Nat) (k : ACall)

theorem turnK_kind : (turnK kFD Tt Sm v' k).kind = k.kind := by
  unfold turnK
  split <;> rfl
theorem turnK_segs : (turnK kFD Tt Sm v' k).segs = k.segs := by
  unfold turnK
  split <;> rfl
theorem turnK_pcs : (turnK kFD Tt Sm v' k).pcs = k.pcs := by
  unfold turnK
  split <;> rfl
theorem turnK_tot : (turnK kFD Tt Sm v' k).tot = k.tot := by
  unfold turnK
  split <;> rfl
theorem turnK_n : (turnK kFD Tt Sm v' k).call.n = k.call.n := by
  unfold turnK
  split <;> rfl
theorem turnK_k : (turnK kFD Tt Sm v' k).call.k = k.call.k := by
  unfold turnK
  split <;> rfl

/-- Setting the number iota of a call and turning it can be done in either order. -/
theorem turnK_iota (i : Nat) :
    ({ turnK kFD Tt Sm v' k with call := { (turnK kFD Tt Sm v' k).call with iota := i } } : ACall) =
      turnK kFD Tt Sm v' { k with call := { k.call with iota := i } } := by
  unfold turnK
  cases hk : k.kind <;> simp only [hk]

end

/-! ### the tests on the calls -/

/-- Where the loop of tests has returned, callAsk has returned at every call. -/
theorem asks_inv : ∀ (l : List Call),
    (forIn l PUnit.unit fun c _ => (do
      Forest.callAsk c
      pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))) = .ok PUnit.unit →
    ∀ c ∈ l, Forest.callAsk c = .ok ()
  | [], _, c, hc => by cases hc
  | a :: l, h, c, hc => by
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := exc_bind h
    obtain ⟨u, hu, hr⟩ := exc_bind hr
    obtain rfl := Except.ok.inj hr
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact hu
    · exact asks_inv l h c hc'

theorem asks_of_forest {cs : Array Call} {lid : Nat} {h : Forest.Shape} (H : Forest.shape cs lid = .ok h) :
    ∀ c ∈ cs.toList, Forest.callAsk c = .ok () := by
  unfold Forest.shape at H
  obtain ⟨u, hu, -⟩ := exc_bind H
  rw [← Array.forIn_toList] at hu
  exact asks_inv _ hu

/-- The tests on the numbers are among callAsk's. -/
theorem noTab_of_ask {c : Call} (h : Forest.callAsk c = .ok ()) : Forest.callAskNoTab c = .ok () := by
  unfold Forest.callAsk at h
  unfold Forest.callAskNoTab
  obtain ⟨n1, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  have n1' : ¬ ((decide (c.k < 5) || decide (c.k > 16) || decide (c.fn > 2) || decide (c.t0 ≥ 2 ^ c.k) ||
      decide (c.n > 62)) = true) := by
    intro q
    exact n1 (by rw [Bool.or_eq_true]; exact Or.inl q)
  refine (if_neg n1').trans ?_
  exact h

theorem noTab_turn (kFD : Nat) (Tt : Array Nat) (Sm v' : Nat) (k : ACall) :
    Forest.callAskNoTab (turnK kFD Tt Sm v' k).call = Forest.callAskNoTab k.call := by
  unfold turnK
  split <;> rfl

theorem turnK_sh (kFD : Nat) (Tt : Array Nat) (Sm v' : Nat) (k : ACall) (hk : k.kind = .kfd) :
    (turnK kFD Tt Sm v' k).sh = v' := by
  unfold turnK
  rw [hk]

/-! ### shapeHid -/

theorem pubAsk_calls (h : Forest.Shape) (cs' : Array Call) (hs : cs'.size = h.calls.size) (pub : Array Nat) :
    Forest.pubAsk { h with calls := cs' } pub = Forest.pubAsk h pub := by
  unfold Forest.pubAsk
  dsimp only
  rw [hs]

theorem shapeHid_turn {lid M : Nat} {cf : Cfg} {sh' : Array Nat} {v v' : Nat} {S : Shape} {fs : Forest.Shape}
    (k : shapeHid lid cf = .ok (S, fs))
    (hv : ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = v) (hz' : sh'.size = 2 ^ cf.ll)
    (hv' : ∀ lam < 2 ^ cf.ll, sh'.getD lam 0 = v')
    (ht : shTests cf S.Tt.size (2 ^ cf.ldh * clamp * clamp) v' = .ok ())
    (hM : ∀ t, S.Tt.getD t 0 ≤ M)
    (hb : OnBytes.Road.K4.Trial.kfdB M (shdOf S.Tt.size (2 ^ cf.ldh * clamp * clamp) v') v' cf.kFD = true) :
    shapeHid lid { cf with sh := sh' } = .ok
      ({ S with cf := { cf with sh := sh' }, calls := S.calls.map (turnK cf.kFD S.Tt (2 ^ cf.ldh * clamp * clamp) v') },
       { fs with calls := (S.calls.map (turnK cf.kFD S.Tt (2 ^ cf.ldh * clamp * clamp) v')).map (·.call) }) := by
  have hS := (OnBytes.Road.L5.shaped_of_hid k).exp
  unfold Attention.shapeHid at k ⊢
  obtain ⟨A, hA, k⟩ := exc_bind k
  have eT : S.Tt = A.Tt := Option.some.inj (hS.symm.trans (OnBytes.Road.L5.shaped_of_shape hA).exp)
  rw [eT] at ht hM hb ⊢
  clear eT hS
  have hA' := shape_turn hA hv hz' hv' ht
  refine (bind_ok hA').trans ?_
  dsimp only at k ⊢
  obtain ⟨h, hF, k⟩ := exc_bind k
  generalize htK : turnK cf.kFD A.Tt (2 ^ cf.ldh * clamp * clamp) v' = tK at hA' ⊢
  have hn : ((A.calls.map tK).map (·.call)).map (·.n) = (A.calls.map (·.call)).map (·.n) := by
    rw [Array.map_map, Array.map_map, Array.map_map]
    refine Array.map_congr_left fun a _ => ?_
    rw [← htK]
    exact turnK_n _ _ _ _ a
  have hk : ((A.calls.map tK).map (·.call)).map (·.k) = (A.calls.map (·.call)).map (·.k) := by
    rw [Array.map_map, Array.map_map, Array.map_map]
    refine Array.map_congr_left fun a _ => ?_
    rw [← htK]
    exact turnK_k _ _ _ _ a
  have ask0 := asks_of_forest hF
  have ask : ∀ c ∈ ((A.calls.map tK).map (·.call)).toList, Forest.callAsk c = .ok () := by
    refine OnBytes.Road.K4.Trial.AttLaws.asks_of_shape hA' hM ?_
    rw [List.all_eq_true]
    intro k' hk'
    rw [Array.toList_map] at hk'
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk'
    have q0 : Forest.callAskNoTab k0.call = .ok () :=
      noTab_of_ask (ask0 _ (by rw [Array.toList_map]; exact List.mem_map.2 ⟨k0, hk0, rfl⟩))
    unfold OnBytes.Road.K4.Trial.askAt
    rw [Bool.and_eq_true]
    constructor
    · rw [← htK, noTab_turn, q0]
      rfl
    · rw [← htK, turnK_kind]
      by_cases c : k0.kind = .kfd
      · rw [if_pos c, turnK_sh _ _ _ _ _ c]
        exact hb
      · rw [if_neg c]
  obtain ⟨hF', hcalls⟩ := forest_congr hn hk ask hF
  refine (bind_ok hF').trans ?_
  dsimp only at k ⊢
  step k
  step k
  subst htK
  have e : ((A.calls.map (turnK cf.kFD A.Tt (2 ^ cf.ldh * clamp * clamp) v')).mapIdx fun q c =>
        ({ c with call := { c.call with iota := h.iota.getD q 0 } } : ACall)) =
      (A.calls.mapIdx fun q c => ({ c with call := { c.call with iota := h.iota.getD q 0 } } : ACall)).map
        (turnK cf.kFD A.Tt (2 ^ cf.ldh * clamp * clamp) v') := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_mapIdx, Array.getElem_map]
      exact turnK_iota _ _ _ _ _ _
  rw [e]
  obtain ⟨counted, hc, k⟩ := exc_bind k
  refine (bind_ok (a := counted) ?_).trans ?_
  · rw [Array.foldlM_map]
    · simp only [turnK_tot, turnK_n, Array.size_map]
      exact hc
    · rw [Array.size_map]
  dsimp only at k ⊢
  obtain ⟨_, hp, k⟩ := exc_bind k
  refine (bind_ok ((pubAsk_calls h _ (by rw [hcalls]; simp) _).trans hp)).trans ?_
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj k)
  rfl

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.forest_congr
#print axioms HonestTraceRun.SetUp.turnK_iota
#print axioms HonestTraceRun.SetUp.shapeHid_turn
