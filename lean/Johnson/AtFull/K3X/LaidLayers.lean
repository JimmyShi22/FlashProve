-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/LaidLayers.lean: at a layers' link the host's count of padding places is the
layout's own count. A general law on every layout that the verifier returns under the switches and
under hfit (below); nothing is evaluated.

Why. The lookup on the calls of a layers' link is handed two counts of padding keys, tree by tree.
One is the layout's field pub (Lay.pubOfCall, OnBytes/Model/LayerLayout.lean): it walks all columns
of a call and reads the marks in CallD.used. The other is the host's (laidLayers,
Johnson/Desc/First/Look/Laid.lean): it marks the columns that the call's segments list, layer by
layer (Env.weighedOf), and then walks all columns (Env.laidOf). At the full size a call has 131,072
pairs of a layer and a column, and each mark is a single write into an array. Lean's kernel holds an
array as a list, so either count was reckoned far too long for it there; neither was tried alone
in the kernel (Lean's evaluator, on a sheet not in this repository, found them equal at two links:
no proof); an earlier try at one test that holds this count among others ended at a cap on memory.
This law needs no run: both counts add the same number at the same tree for the same columns.

  `pair_all`: of a list whose members are pairwise related, any two members are one or related.
  `one_lister`: on a layer where the listed columns are all different, a column is listed by one
    segment alone.
  `padding_iff`: the layout's rule for a padding column (CallD.padding) says yes exactly at the
    columns that no segment which exists on the layer lists.
  `fold_tie`: two loops, one that may refuse with a name and one that may refuse without: if each
    step of the first that goes on is matched by the second, so is the whole.
  `laidOf_of_pubOfCall`: one call: where the layout's loop returns, the host's returns the same.
  `calls_tie`: all calls.
  **`laidLayers_eq_pub`**: laidLayers P = some P.y.fo.pub.

What is asked. That the layout is one that the function layout returns; the switches
(Johnson/Road/FormsKeysFits.lean); and hfit: the trees of each call lie among the lookup's trees.
The host tests that a tree's number is inside its array; the layout's loop tests only that the
column lies in one of the call's own trees: hfit joins the two. It is a statement on sixteen small
numbers of the layout.

Limits. Both counts are made next to the key forms, from the lists of columns, not from the forms: a
fault inside a form or in a list is not seen by either, and this law says nothing on it. THE LAW
ALSO SHOWS THAT THE LOOKUP's TEST "laid == pub" CANNOT REJECT AT A LAYERS' LINK at any layout that
the verifier's own function returns (under the switches and hfit): both counts come of one source,
the segments' lists of columns (CallD.used is filled from Seg.pos): so that test tests nothing
there. What the counts are as numbers is not said here. Nothing on soundness.

-/
import Johnson.Desc.First.Look.Laid
import Johnson.Goal.Meaning.WeighedScope
import Johnson.Road.FormsKeysPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model (Seg CallD markUsed refuseIf)
open OnBytes.Model.Layer (Env Lay Shape layout layoutBase layoutLook)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- Of a list whose members are pairwise related by a symmetric relation, any two members are one or
related. -/
theorem pair_all {α : Type} {R : α → α → Prop} (hsym : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a = b ∨ R a b
  | [], _, _, ha, _, _ => by cases ha
  | x :: l, h, a, ha, b, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ea | ha'
    · rcases List.mem_cons.mp hb with eb | hb'
      · exact Or.inl (ea.trans eb.symm)
      · exact Or.inr (ea ▸ h.1 b hb')
    · rcases List.mem_cons.mp hb with eb | hb'
      · exact Or.inr (hsym _ _ (eb ▸ h.1 a ha'))
      · exact pair_all hsym h.2 a ha' b hb'

/-- On a layer where the listed columns are all different, one segment alone lists a column. -/
theorem one_lister {v : Env} {c : CallD} {lam : Nat} (hn : (colsOn v c lam).Nodup) {s s' : Seg}
    (hs : s ∈ c.segs) (hs' : s' ∈ c.segs) (he : (s.moe && !v.isMoe lam) = false)
    (he' : (s'.moe && !v.isMoe lam) = false) {j : Nat} (hj : j ∈ s.pos.toList)
    (hj' : j ∈ s'.pos.toList) : s = s' := by
  unfold colsOn at hn
  have hp : c.segs.Pairwise (fun a b =>
      List.Disjoint (if a.moe && !v.isMoe lam then [] else a.pos.toList)
        (if b.moe && !v.isMoe lam then [] else b.pos.toList)) := (List.nodup_flatMap.mp hn).2
  rcases pair_all (fun _ _ h => List.Disjoint.symm h) hp s hs s' hs' with e | d
  · exact e
  · exfalso
    rw [he, he'] at d
    exact d hj hj'

/-- **The layout's rule for a padding column says yes exactly at the columns that no segment which
exists on the layer lists.** Asked: routed experts; the marks are made from the segments' lists; on
the group's last layer every segment exists and the listed columns are all different. -/
theorem padding_iff {v : Env} {c : CallD} (hp3 : v.y.h.p3 = true)
    (hused : c.used = c.segs.foldl markUsed (Array.replicate c.J 0))
    (hall : (colsOn v c (v.y.Lam - 1)).Nodup)
    (hlast : ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false) (lam : Nat) {j : Nat}
    (hj : j < c.J) : c.padding lam j = true ↔ j ∉ colsOn v c lam := by
  have hsz : j < (Array.replicate c.J 0).size := by rw [Array.size_replicate]; exact hj
  have h0 : (Array.replicate c.J 0).getD j 0 = 0 := by simp [Array.getD, hj]
  show (c.used.getD j 0 == 0 || (c.used.getD j 0 == 2 && lam % 2 == 0)) = true ↔ _
  by_cases hex : ∃ s ∈ c.segs, j ∈ s.pos.toList
  · obtain ⟨s, hs, hjs⟩ := hex
    have one : ∀ s' ∈ c.segs, j ∈ s'.pos.toList → s' = s := fun s' hs' hj' =>
      one_lister hall hs' hs (hlast s' hs') (hlast s hs) hj' hjs
    have hu : c.used.getD j 0 = markOf s := by
      rw [hused]
      exact (used_get (markOf s) j c.segs _ hsz fun s' hs' hj' => by rw [one s' hs' hj']).1
        ⟨s, hs, hjs⟩
    rw [hu]
    cases hm : s.moe with
    | false =>
      have hk : markOf s = 1 := by simp [markOf, hm]
      have hin : j ∈ colsOn v c lam := mem_colsOn.mpr ⟨s, hs, by rw [hm]; rfl, hjs⟩
      rw [hk]
      constructor
      · intro h
        simp at h
      · intro h
        exact absurd hin h
    | true =>
      have hk : markOf s = 2 := by simp [markOf, hm]
      rw [hk]
      rcases Nat.mod_two_eq_zero_or_one lam with hl | hl
      · constructor
        · intro _ hin
          obtain ⟨s', hs', he', hj'⟩ := mem_colsOn.mp hin
          rw [one s' hs' hj'] at he'
          simp [Env.isMoe, hp3, hl, hm] at he'
        · intro _
          simp [hl]
      · have hin : j ∈ colsOn v c lam :=
          mem_colsOn.mpr ⟨s, hs, by simp [Env.isMoe, hp3, hl], hjs⟩
        constructor
        · intro h
          simp [hl] at h
        · intro h
          exact absurd hin h
  · have hno : ∀ s ∈ c.segs, j ∉ s.pos.toList := fun s hs hjs => hex ⟨s, hs, hjs⟩
    have hu : c.used.getD j 0 = 0 := by
      rw [hused, (used_get 0 j c.segs _ hsz fun s hs hjs => absurd hjs (hno s hs)).2 hno, h0]
    rw [hu]
    constructor
    · intro _ hin
      obtain ⟨s, hs, -, hjs⟩ := mem_colsOn.mp hin
      exact hno s hs hjs
    · intro _
      rfl

/-- Two loops over one list, one in Except and one in Option: if each step of the first that goes on
from a state with the property Inv is matched by the second and keeps Inv, so is the whole loop. -/
theorem fold_tie {α β : Type} (f : β → α → Except String β) (g : β → α → Option β)
    (Inv : β → Prop) : ∀ (l : List α) (b b' : β),
      (∀ x ∈ l, ∀ b b', Inv b → f b x = .ok b' → g b x = some b' ∧ Inv b') → Inv b →
      l.foldlM f b = .ok b' → l.foldlM g b = some b' ∧ Inv b'
  | [], b, b', _, hb, h => by
    have e : b = b' := Except.ok.inj (h : Except.ok b = Except.ok b')
    subst e
    exact ⟨rfl, hb⟩
  | x :: l, b, b', H, hb, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨c, h1, h2⟩ := ok_of_bind h
    obtain ⟨g1, i1⟩ := H x (List.mem_cons_self ..) b c hb h1
    rw [List.foldlM_cons, g1]
    exact fold_tie f g Inv l c b' (fun y hy => H y (List.mem_cons_of_mem _ hy)) i1 h2

/-- **One call: where the layout's loop returns, the host's loop returns the same array.** -/
theorem laidOf_of_pubOfCall {v : Env} {c : CallD} {w : Array Bool} {q n : Nat}
    (hp3 : v.y.h.p3 = true) (hused : c.used = c.segs.foldl markUsed (Array.replicate c.J 0))
    (hw : v.weighedOf c = some w)
    (hlast : ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false)
    (hfit : v.y.fo.first.getD q 0 + 2 ^ v.y.fo.iota.getD q 0 ≤ n) {laid laid' : Array Nat}
    (hs : laid.size = n) (h : v.y.pubOfCall v.y.fo q c laid = .ok laid') :
    v.laidOf q w laid = some laid' ∧ laid'.size = n := by
  obtain ⟨hsz, H⟩ := weighedOf_spec hw hlast
  unfold Lay.pubOfCall at h
  unfold Env.laidOf
  rw [hsz]
  refine fold_tie _ _ (fun a => a.size = n) _ _ _ (fun x hx b b' hb hf => ?_) hs h
  have hx' : x < v.y.Lam * c.J := List.mem_range.mp hx
  have hJ : 0 < c.J := by
    rcases Nat.eq_zero_or_pos c.J with e | e
    · rw [e, Nat.mul_zero] at hx'
      omega
    · exact e
  have hlam : x / c.J < v.y.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
  have hj : x % c.J < c.J := Nat.mod_lt _ hJ
  have hxe : x / c.J * c.J + x % c.J = x := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x c.J
  have mj := (H (x / c.J) hlam).2.2 (x % c.J) hj
  rw [hxe] at mj
  have pj := padding_iff hp3 hused (H (v.y.Lam - 1)
    (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlam) Nat.one_pos)).2.1 hlast (x / c.J) hj
  dsimp only at hf ⊢
  by_cases hp : c.padding (x / c.J) (x % c.J) = true
  · have hw0 : w.getD x true = false := by
      cases e : w.getD x true with
      | false => rfl
      | true => exact absurd (mj.mp e) (pj.mp hp)
    rw [if_pos hp] at hf
    obtain ⟨hr, hv⟩ := ok_of_refuse hf
    have e : b.modify (v.y.fo.first.getD q 0 + x / 2 ^ (v.y.fo.dT - v.y.h.lt)) (· + v.y.T) = b' :=
      Except.ok.inj hv
    have hz : x / 2 ^ (v.y.fo.dT - v.y.h.lt) / 2 ^ v.y.fo.iota.getD q 0 = 0 := by simpa using hr
    have hlt : x / 2 ^ (v.y.fo.dT - v.y.h.lt) < 2 ^ v.y.fo.iota.getD q 0 := by
      by_contra hge
      have := Nat.div_pos (Nat.le_of_not_lt hge) (Nat.two_pow_pos (v.y.fo.iota.getD q 0))
      omega
    have ht : v.y.fo.first.getD q 0 + x / 2 ^ (v.y.fo.dT - v.y.h.lt) < b.size := by omega
    rw [hw0, if_neg (by simp), if_pos ht, e]
    refine ⟨rfl, ?_⟩
    rw [← e, Array.size_modify]
    exact hb
  · have hw1 : w.getD x true = true := mj.mpr (by
      by_contra hc
      exact hp (pj.mpr hc))
    rw [if_neg hp] at hf
    have e : b = b' := Except.ok.inj hf
    rw [hw1, if_pos rfl, e]
    exact ⟨rfl, e ▸ hb⟩

/-- **All calls**, from number k on. -/
theorem calls_tie (v : Env) (n : Nat) (hp3 : v.y.h.p3 = true) : ∀ (l : List CallD) (k : Nat)
    (laid laid' : Array Nat),
    (∀ c ∈ l, c.used = c.segs.foldl markUsed (Array.replicate c.J 0) ∧
      (∃ w, v.weighedOf c = some w) ∧
      ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false) →
    (∀ q, k ≤ q → q < k + l.length → v.y.fo.first.getD q 0 + 2 ^ v.y.fo.iota.getD q 0 ≤ n) →
    laid.size = n →
    (l.zipIdx k).foldlM (fun pub x => v.y.pubOfCall v.y.fo x.2 x.1 pub) laid = .ok laid' →
    ∃ ws, l.mapM v.weighedOf = some ws ∧
      (ws.zipIdx k).foldlM (fun laid x => v.laidOf x.2 x.1 laid) laid = some laid'
  | [], _, laid, laid', _, _, _, h => by
    have e : laid = laid' := Except.ok.inj (h : Except.ok laid = Except.ok laid')
    subst e
    exact ⟨[], rfl, rfl⟩
  | c :: l, k, laid, laid', H, hfit, hs, h => by
    rw [List.zipIdx_cons, List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := ok_of_bind h
    obtain ⟨hused, ⟨w, hw⟩, hlast⟩ := H c (List.mem_cons_self ..)
    obtain ⟨g1, s1⟩ := laidOf_of_pubOfCall hp3 hused hw hlast
      (hfit k (Nat.le_refl k) (by simp)) hs h1
    obtain ⟨ws, m1, f1⟩ := calls_tie v n hp3 l (k + 1) mid laid'
      (fun c' hc' => H c' (List.mem_cons_of_mem _ hc'))
      (fun q h3 h4 => hfit q (by omega) (by simp only [List.length_cons]; omega)) s1 h2
    refine ⟨w :: ws, ?_, ?_⟩
    · rw [List.mapM_cons, hw, m1]
      rfl
    · rw [List.zipIdx_cons, List.foldlM_cons]
      show (v.laidOf k w laid >>= fun s =>
        (ws.zipIdx (k + 1)).foldlM (fun laid x => v.laidOf x.2 x.1 laid) s) = some laid'
      rw [g1]
      exact f1

/-- The value at which laidLayers runs the program's two plain functions: they read the layout
alone. -/
def envOf (P : Layer.Pub) : Env :=
  { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] }

/-- **AT A LAYERS' LINK THE HOST's COUNT IS THE LAYOUT's OWN.** -/
theorem laidLayers_eq_pub {h : Shape} {pc : List (List String)} {P : Layer.Pub}
    (hy : layout h pc = .ok P.y) (S : Switches h)
    (hfit : ∀ q, q < P.y.calls.size →
      P.y.fo.first.getD q 0 + 2 ^ P.y.fo.iota.getD q 0 ≤ P.y.fo.NT) :
    laidLayers P = some P.y.fo.pub := by
  have hyv : layout h pc = .ok (envOf P).y := hy
  have A := admitted_of_layout hy S.p3
  have hp3 : (envOf P).y.h.p3 = true := by
    show P.y.h.p3 = true
    rw [A.shape]
    exact S.p3
  have hy' := hy
  unfold layout at hy'
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy'
  obtain ⟨fo, pub, e, hp⟩ := look_pub h1
  have hp' : (P.y.calls.toList.zipIdx).foldlM
      (fun pub x => P.y.pubOfCall P.y.fo x.2 x.1 pub) (Forest.noPub P.y.fo) = .ok P.y.fo.pub := by
    rw [e]
    exact hp
  obtain ⟨ws, m1, f1⟩ := calls_tie (envOf P) P.y.fo.NT hp3 P.y.calls.toList 0
    (Forest.noPub P.y.fo) P.y.fo.pub
    (fun c hc => by
      have hc' : c ∈ P.y.calls := Array.mem_def.mpr hc
      refine ⟨?_, Meaning.P34.weighed_of_layout hy S (envOf P) c hc', last_of_layout hyv S c⟩
      obtain ⟨cl, taken, -, -, h3⟩ := A.calls
      rw [h3] at hc'
      obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hc')
      rfl)
    (fun q _ h4 => hfit q (by simpa using h4))
    (by simp [Forest.noPub]) hp'
  show ((P.y.calls.mapM (envOf P).weighedOf).bind fun weighed =>
    weighed.toList.zipIdx.foldlM (fun laid x => (envOf P).laidOf x.2 x.1 laid)
      (Forest.noPub P.y.fo)) = some P.y.fo.pub
  rw [Array.mapM_eq_mapM_toList, m1]
  exact f1

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.pair_all
#print axioms Johnson.AtFull.K3X.one_lister
#print axioms Johnson.AtFull.K3X.padding_iff
#print axioms Johnson.AtFull.K3X.fold_tie
#print axioms Johnson.AtFull.K3X.laidOf_of_pubOfCall
#print axioms Johnson.AtFull.K3X.calls_tie
#print axioms Johnson.AtFull.K3X.laidLayers_eq_pub
