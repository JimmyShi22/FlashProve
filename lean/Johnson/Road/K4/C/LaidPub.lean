-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LaidPub.lean: CONDITIONAL: at a layout that the verifier returns, with the
library's lines of calls.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: THE HOST's SECOND COUNT
OF THE PADDING KEYS IS THE LAYOUT's OWN (the host: the sub-protocol that calls the lookup). The
layout counts the padding keys of each tree by its rule CallD.padding (Lay.pubOfCall, layoutLook,
OnBytes/Model/LayerLayout.lean): the field pub. At the join the count is made a second time, from
the marks of the segments' columns (weighedOf, laidOf, OnBytes/Model/LayerForms.lean; laidLayers,
Johnson/Desc/First/Look/Laid.lean), and compared. The library leaves open that the two are one
(Johnson/Road/FormsKeysPub.lean, «What is not claimed»). Statements and proofs.

  `foldlM_ok_some`   a loop that may refuse with a word, against a loop that may return nothing.
  `tree_lt`          a tree of a call is a tree of the lookup.
  `pub_stepL`        one column: the layout's step is the second count's.
  `laidOf_of_pub`    one call.
  `calls_laid`       all calls.
  **`laidLayers_of_layout`**   laidLayers P = some P.y.fo.pub.

Not shown here. That a layout with the library's lines of calls exists: no example is shown here;
the library's refPub_in_scope (Johnson/Road/K4/RefInScope.lean) gives the hypotheses at what
publicOf returns at public files in the goals' scope, for each group below twelve that has a plan;
its proof calls a statement under Johnson/Goal/. AT A LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE
LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE. The hypothesis on the sizes (Z) is no
condition: every shape meets it at its own sizes (the library's sized_dimOf,
Johnson/Road/FormsKeysFits.lean). Public data alone.
No property is claimed.
-/
import Johnson.Road.K4.C.ColsOfLayout
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysShape
import Johnson.Desc.First.Look.Laid
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model (refuseIf CallD)
open OnBytes.Model.Layer (Lay Env layout layoutLook)
open Inst.Model.FFSeg (Dim fams)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- A loop that may refuse with a word, against a loop that may return nothing: where each step of
the first that goes on is a step of the second, and a property I is kept. -/
theorem foldlM_ok_some {α β : Type} {f : β → α → Except String β} {g : β → α → Option β}
    (I : β → Prop) : ∀ (l : List α),
    (∀ a ∈ l, ∀ b b', I b → f b a = .ok b' → g b a = some b' ∧ I b') →
      ∀ b b', I b → l.foldlM f b = .ok b' → l.foldlM g b = some b' ∧ I b'
  | [], _, b, b', hb, h => by
    have e : b = b' := Except.ok.inj (show Except.ok b = Except.ok b' from h)
    subst e
    exact ⟨rfl, hb⟩
  | a :: l, H, b, b', hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b1, h1, h2⟩ := ok_of_bind h
    obtain ⟨g1, i1⟩ := H a List.mem_cons_self b b1 hb h1
    obtain ⟨r, i⟩ := foldlM_ok_some I l (fun a ha => H a (List.mem_cons_of_mem _ ha)) b1 b' i1 h2
    refine ⟨?_, i⟩
    rw [List.foldlM_cons, g1]
    exact r

/-- A tree of a call is a tree of the lookup. -/
theorem tree_lt {fo : Forest.Shape} (hok : FoNums.ok fo = true) {q b : ℕ} (hq : q < fo.NC)
    (hb : b < 2 ^ fo.iota.getD q 0) : fo.first.getD q 0 + b < fo.NT := by
  unfold FoNums.ok at hok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
  exact ((hok.1.1.1.1.1.2 q hq).2 b hb).1.1

/-- **One column**: where the layout's step goes on, the second count's step returns the same. m:
the column's mark. -/
theorem pub_stepL (P R m : Bool) (ix T n : ℕ) (nm : String) (pub pub' : Array ℕ)
    (hm : m = !P) (hix : P = true → R = false → ix < n) (hs : pub.size = n)
    (h : (if P = true then (do refuseIf R nm; pure (pub.modify ix (· + T))) else pure pub :
      Except String (Array ℕ)) = .ok pub') :
    (if m = true then some pub
      else if ix < pub.size then some (pub.modify ix (· + T)) else none) = some pub' ∧
      pub'.size = n := by
  subst hm
  by_cases hP : P = true
  · rw [if_pos hP] at h
    obtain ⟨hR, h⟩ := ok_of_refuse h
    have e : pub.modify ix (· + T) = pub' :=
      Except.ok.inj (show Except.ok (pub.modify ix (· + T)) = Except.ok pub' from h)
    subst e
    rw [hP, if_neg (by decide), if_pos (by rw [hs]; exact hix hP hR)]
    exact ⟨rfl, by rw [Array.size_modify]; exact hs⟩
  · rw [if_neg hP] at h
    have e : pub = pub' := Except.ok.inj (show Except.ok pub = Except.ok pub' from h)
    subst e
    have hP' : P = false := by simpa using hP
    rw [hP', if_pos (by decide)]
    exact ⟨rfl, hs⟩

/-- **One call**: where the layout's count of a call's padding keys goes on, the second count
returns the same. w: the call's marks. -/
theorem laidOf_of_pub {v : Env} {fo : Forest.Shape} {q : ℕ} {cd : CallD} {w : Array Bool} {n : ℕ}
    (hf : v.y.fo.first = fo.first) (hd : v.y.fo.dT = fo.dT) (hsz : w.size = v.y.Lam * cd.J)
    (hw : ∀ lam, lam < v.y.Lam → ∀ j, j < cd.J →
      w.getD (lam * cd.J + j) true = !cd.padding lam j)
    (hb : ∀ b, b < 2 ^ fo.iota.getD q 0 → fo.first.getD q 0 + b < n)
    {pub pub' : Array ℕ} (hs : pub.size = n) (h : v.y.pubOfCall fo q cd pub = .ok pub') :
    v.laidOf q w pub = some pub' ∧ pub'.size = n := by
  unfold Lay.pubOfCall at h
  unfold Env.laidOf
  dsimp only
  rw [hsz, hf, hd]
  refine foldlM_ok_some (fun p : Array ℕ => p.size = n) _ (fun x hx p p' hp hstep => ?_)
    pub pub' hs h
  have hx' := List.mem_range.mp hx
  have hJ : 0 < cd.J := by
    rcases Nat.eq_zero_or_pos cd.J with e | e
    · rw [e, Nat.mul_zero] at hx'
      exact absurd hx' (Nat.not_lt_zero _)
    · exact e
  have hlam : x / cd.J < v.y.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
  have hwx := hw _ hlam _ (Nat.mod_lt x hJ)
  rw [Nat.div_add_mod' x cd.J] at hwx
  exact pub_stepL (cd.padding (x / cd.J) (x % cd.J))
    (x / 2 ^ (fo.dT - v.y.h.lt) / 2 ^ fo.iota.getD q 0 != 0) (w.getD x true)
    (fo.first.getD q 0 + x / 2 ^ (fo.dT - v.y.h.lt)) v.y.T n "internal-forest-pub" p p' hwx
    (fun _ hR => hb _ (by
      have h0 : x / 2 ^ (fo.dT - v.y.h.lt) / 2 ^ fo.iota.getD q 0 = 0 := by simpa using hR
      by_contra hge
      have := Nat.div_pos (Nat.le_of_not_lt hge) (Nat.two_pow_pos (fo.iota.getD q 0))
      omega)) hp hstep

/-- **All calls.** k: the number of the list's first call. -/
theorem calls_laid {v : Env} {fo : Forest.Shape} {n : ℕ}
    (hf : v.y.fo.first = fo.first) (hd : v.y.fo.dT = fo.dT) : ∀ (l : List CallD) (k : ℕ),
    (∀ cd ∈ l, ∃ w, v.weighedOf cd = some w ∧ w.size = v.y.Lam * cd.J ∧
      ∀ lam, lam < v.y.Lam → ∀ j, j < cd.J → w.getD (lam * cd.J + j) true = !cd.padding lam j) →
    (∀ q, k ≤ q → q < k + l.length → ∀ b, b < 2 ^ fo.iota.getD q 0 →
      fo.first.getD q 0 + b < n) →
    ∀ pub pub' : Array ℕ, pub.size = n →
      (l.zipIdx k).foldlM (fun pub x => v.y.pubOfCall fo x.2 x.1 pub) pub = .ok pub' →
      ∃ ws, l.mapM v.weighedOf = some ws ∧
        (ws.zipIdx k).foldlM (fun laid x => v.laidOf x.2 x.1 laid) pub = some pub'
  | [], _, _, _, pub, pub', _, h => by
    have e : pub = pub' := Except.ok.inj (show Except.ok pub = Except.ok pub' from h)
    subst e
    exact ⟨[], rfl, rfl⟩
  | cd :: l, k, hW, hB, pub, pub', hs, h => by
    rw [List.zipIdx_cons, List.foldlM_cons] at h
    obtain ⟨p1, h1, h2⟩ := ok_of_bind h
    obtain ⟨w, hw, hsz, hm⟩ := hW cd List.mem_cons_self
    obtain ⟨g1, s1⟩ := laidOf_of_pub hf hd hsz hm
      (hB k (Nat.le_refl _) (by rw [List.length_cons]; omega)) hs h1
    obtain ⟨ws, hws, hfold⟩ := calls_laid hf hd l (k + 1)
      (fun c hc => hW c (List.mem_cons_of_mem _ hc))
      (fun q h1 h2 => hB q (by omega) (by rw [List.length_cons]; omega)) p1 pub' s1 h2
    refine ⟨w :: ws, ?_, ?_⟩
    · rw [List.mapM_cons, hw, hws]
      rfl
    · rw [List.zipIdx_cons, List.foldlM_cons, g1]
      exact hfold

/-- **THE HOST's SECOND COUNT OF THE PADDING KEYS IS THE LAYOUT's OWN.** CONDITIONAL: on the
layout's return, the switches, the sizes and the eight lines. -/
theorem laidLayers_of_layout {h : Layer.Shape} {pc : List (List String)} {P : Layer.Pub}
    (hy : layout h pc = .ok P.y) (S : Switches h) {D : Dim} (Z : Sized h D) (hN : LinesAre P.y) :
    laidLayers P = some P.y.fo.pub := by
  have A := admitted_of_layout hy S.p3
  have hok := _root_.Fo.Pay.shapeOf_ok (_root_.Fo.layout_shape hy)
  obtain ⟨h8, Hc⟩ := lines_calls hN
  obtain ⟨-, hNC, hcl⟩ := fo_of_layout hy
  have hy' := hy
  unfold layout at hy'
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy'
  obtain ⟨fo, pub, e, hp⟩ := look_pub h1
  have hp3 : P.y.h.p3 = true := by
    rw [A.shape]
    exact S.p3
  have hLam : P.y.Lam = 2 ^ P.y.h.ll := A.laid.Lam
  have h0 : 0 < P.y.Lam := by
    rw [hLam]
    exact Nat.two_pow_pos _
  have hL : P.y.Lam % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, P.y.h.ll = k + 1 := ⟨P.y.h.ll - 1, by have := A.laid.ll; omega⟩
    rw [hLam, hk, Nat.pow_succ]
    exact Nat.mul_mod_left _ _
  have hW : ∀ cd ∈ P.y.calls.toList, ∃ w,
      Env.weighedOf { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] } cd =
        some w ∧ w.size = P.y.Lam * cd.J ∧
      ∀ lam, lam < P.y.Lam → ∀ j, j < cd.J →
        w.getD (lam * cd.J + j) true = !cd.padding lam j := by
    intro cd hcd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcd
    have hk8 : k < 8 := by
      rw [← h8]
      simpa using hk
    obtain ⟨cd', e1, e2⟩ := Hc ⟨k, hk8⟩
    have ecd : P.y.calls.toList[k] = cd' := by
      have e3 : P.y.calls.toList[k]? = some cd' := by
        rw [Array.getElem?_toList]
        exact e1
      rw [List.getElem?_eq_getElem hk] at e3
      exact Option.some.inj e3
    rw [ecd]
    exact weighed_padding
      (v := { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] })
      (colsOK_of_layout hy S Z (Array.mem_of_getElem? e1) e2) hp3 hL h0
  have hB : ∀ q, 0 ≤ q → q < 0 + P.y.calls.toList.length → ∀ b, b < 2 ^ fo.iota.getD q 0 →
      fo.first.getD q 0 + b < fo.NT := by
    intro q _ hq b hb
    have hq' : q < P.y.fo.NC := by
      rw [hNC, hcl]
      simpa using hq
    rw [e] at hok hq'
    exact tree_lt hok hq' hb
  obtain ⟨ws, hws, hfold⟩ := calls_laid
    (v := { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] }) (fo := fo)
    (n := fo.NT) (by show P.y.fo.first = fo.first; rw [e]) (by show P.y.fo.dT = fo.dT; rw [e])
    P.y.calls.toList 0 hW hB (Forest.noPub fo) pub
    (by unfold Forest.noPub; rw [Array.size_replicate]) hp
  have en : Forest.noPub P.y.fo = Forest.noPub fo := by
    rw [e]
    rfl
  have eg : laidLayers P = ws.zipIdx.foldlM (fun laid x =>
      Env.laidOf { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] }
        x.2 x.1 laid) (Forest.noPub P.y.fo) := by
    unfold laidLayers
    dsimp only
    rw [Array.mapM_eq_mapM_toList, hws]
    rfl
  rw [eg, en, hfold, e]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.foldlM_ok_some
#print axioms OnBytes.Road.K4.C.tree_lt
#print axioms OnBytes.Road.K4.C.pub_stepL
#print axioms OnBytes.Road.K4.C.laidOf_of_pub
#print axioms OnBytes.Road.K4.C.calls_laid
#print axioms OnBytes.Road.K4.C.laidLayers_of_layout
