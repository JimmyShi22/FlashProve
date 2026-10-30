-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPub.lean: the number of padding keys of a tree of the lookup, the verifier's
against the library's.

The lookup of a layer sub-proof cuts the key vectors of its calls into trees of one size. Some keys
are padding: those of a column that no segment of the call takes, or whose segment does not exist on
the layer. The verifier counts the padding keys of each tree when it lays the sub-proof out
(Lay.pubOfCall and layoutLook in OnBytes/Model/LayerLayout.lean): the field pub. The library has its
own rule for a padding column (isPad), its own count (padCount) and a theorem on what that count is
(padCountEq), in Inst/Model/FF/Index.lean and IndexFacts.lean. This file sets the two side by side.

What is compared with what: the verifier's own functions on a layout that it returns, against the
library's own definitions. All statements are identities on public numbers of the layout: no
challenge, no message and no hidden value occurs.

Main theorems.
 (P) padding_isPad: for a call whose line is the library's, the verifier's rule CallD.padding
     (OnBytes/Model/Calls.lean) is isPad, on every layer and every column of the call. The
     verifier's rule reads marks that are written column by column (markUsed); used_get says what
     the writes leave; the library's famAtPos gives the way from a column back to its family.
 (F) pub_fold: what the two loops make: pub[θ] is the sum over the calls of pubOf: the number of
     tokens for each padding column of the call that lies in tree θ.
 (C) pub_card: pub[θ] = padCard D θ, the right side of the library's padCountEq to the letter: the
     number of the indices of tree θ whose column is padding on their layer. The library's Dim.OK is
     not asked.
 (E) pub_eq: where Dim.OK holds, pub[θ] = padCount D θ, by the library's padCountEq.
 (M) empty_eq: the keys in the trees that hold only padding; NT_of_layout: the number of trees.
Main definitions: markOf, pubOf, padCard.

What is asked. (P): layout returns; the switches; sizes that agree with the shape; the call's line
names the families of the library's call, in its order. (F): layout returns. (C), (E), (M): the
hypotheses of Dk_of_layout (Johnson/Road/FormsKeysShape.lean): beside those of (P), the library's
cap is the verifier's; there are eight calls; and, for each of the eight (H), call number cc has the
line of the library's call cc, and the verifier's least number of columns is at most the library's
number. With them the group's layers are the library's (Lam = 2^lL).

Where (C) and (E) part. Where a tree holds less than a layer, the library's padCount is an empty
sum, 0, while the tree may hold padding columns, which the verifier counts. (C) holds there; (E)
does not, and Dim.OK shuts the case out (its field whole).

What shows that the hypotheses can be met, and at which sizes. That they hold together, at a made-up
shape and at the lines of the full-size public example, is held by a run that is no part of this
library; nothing here shows it. The switches are theorems at both shapes. At the small public
example (H) fails for four calls (Johnson/Road/FormsKeysRunK.lean).

Who reads these numbers.
 - The verifier's pub: the lookup's public factor and the target of the counts' sum
   (OnBytes/Model/Look.lean) read its sums, by call and in all. Tree by tree only two tests read it:
   that a count is at most the size of a tree, and that it equals a second count made from the
   forms' marks. So (C) is finer than what the factor and the target read.
 - The library's padCount and padCountEq: in the library as it lies here, no file outside
   Inst/Model/FF/Index.lean and IndexFacts.lean names them. So (E) joins the verifier to a theorem
   that nothing else reads. Elsewhere the library has a lookup with a public count of padding for
   each tree (Alg/Lookup.lean; the field φ of Blocks.LkPar in Blocks/LookupRel.lean), which no file
   under Inst names: (C) would be the hypothesis φ = pub for whoever sets that record at the
   verifier's trees; nobody has.

What is not claimed. Nothing on the public factor itself, on the target of the counts' sum, or on
the verifier's map from a tree to its call. That the verifier's second count equals pub is not
shown. Nothing where the verifier's least number of columns bites. Nothing on soundness. By reading
the library's count of bad challenges (count_badAlpha_le in Alg/Lookup.lean: for one table and one
padding value, and for every public count with which the degrees fit), not by a theorem here, a
wrong count would cost an honest prover's acceptance, not the lookup's claim. The program does not
import this file.
-/
import Johnson.Road.FormsKeysKV
import Johnson.Road.FormsKeysLookT

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (refuseIf Seg CallD place markUsed topBit)
open OnBytes.Model.Layer (Lay Env layout layoutLook)
open Inst.Model.FFSeg (Dim Fam len pos call fams isExp isExpL present famAt isPad used lJ aC Dk eC
  trees firstTree NT sg callOf padCount)

/-! ## Which columns are marked as used -/

/-- Writing one value m at the indices of a list. The array keeps its size; an index of the list
that lies in the array then holds m; an index that is not in the list holds what it held. -/
theorem writes_get (m j : ℕ) : ∀ (l : List ℕ) (u : Array ℕ),
    (l.foldl (fun u p => u.setIfInBounds p m) u).size = u.size ∧
      (j ∈ l → j < u.size → (l.foldl (fun u p => u.setIfInBounds p m) u).getD j 0 = m) ∧
      (j ∉ l → (l.foldl (fun u p => u.setIfInBounds p m) u).getD j 0 = u.getD j 0)
  | [], _ => ⟨rfl, fun h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | p :: l, u => by
    obtain ⟨i1, i2, i3⟩ := writes_get m j l (u.setIfInBounds p m)
    rw [Array.size_setIfInBounds] at i1 i2
    refine ⟨i1, fun hm hj => ?_, fun hm => ?_⟩
    · by_cases hl : j ∈ l
      · exact i2 hl hj
      · have e : p = j := by
          rcases List.mem_cons.mp hm with e | e
          · exact e.symm
          · exact absurd e hl
        have r := i3 hl
        rw [e, getD_setN_self u hj] at r
        rw [e]
        exact r
    · have h1 : j ∉ l := fun k => hm (List.mem_cons_of_mem _ k)
      have h2 : p ≠ j := fun e => hm (e ▸ List.mem_cons_self)
      have r := i3 h1
      rw [getD_setN_ne u h2] at r
      exact r

/-- The mark that markUsed (OnBytes/Model/Calls.lean) writes for a segment: 2 if the segment exists
only on layers with routed experts, else 1. -/
def markOf (g : Seg) : ℕ := if g.moe then 2 else 1

/-- What markUsed leaves: the size; the segment's mark at each of its columns that lies in the
array; what stood there at every other index. -/
theorem markUsed_get (u : Array ℕ) (g : Seg) (j : ℕ) :
    (markUsed u g).size = u.size ∧
      (j ∈ g.pos.toList → j < u.size → (markUsed u g).getD j 0 = markOf g) ∧
      (j ∉ g.pos.toList → (markUsed u g).getD j 0 = u.getD j 0) := by
  unfold markUsed markOf
  rw [← Array.foldl_toList]
  exact writes_get _ j g.pos.toList u

/-- The marks of a list of segments, at an index j of the array, if all segments that list j have
one mark m: m if some segment lists j; what stood there if none does. -/
theorem used_get (m j : ℕ) : ∀ (segs : List Seg) (u : Array ℕ), j < u.size →
    (∀ s ∈ segs, j ∈ s.pos.toList → markOf s = m) →
    ((∃ s ∈ segs, j ∈ s.pos.toList) → (segs.foldl markUsed u).getD j 0 = m) ∧
      ((∀ s ∈ segs, j ∉ s.pos.toList) → (segs.foldl markUsed u).getD j 0 = u.getD j 0)
  | [], _, _, _ => ⟨fun ⟨_, hs, _⟩ => absurd hs List.not_mem_nil, fun _ => rfl⟩
  | g :: segs, u, hj, hm => by
    obtain ⟨a1, a2, a3⟩ := markUsed_get u g j
    obtain ⟨b1, b2⟩ := used_get m j segs (markUsed u g) (by rw [a1]; exact hj)
      fun s hs => hm s (List.mem_cons_of_mem _ hs)
    refine ⟨fun hex => ?_, fun hno => ?_⟩
    · by_cases hr : ∃ s ∈ segs, j ∈ s.pos.toList
      · exact b1 hr
      · have hr' : ∀ s ∈ segs, j ∉ s.pos.toList := fun s hs hjs => hr ⟨s, hs, hjs⟩
        have hg : j ∈ g.pos.toList := by
          obtain ⟨s, hs, hjs⟩ := hex
          rcases List.mem_cons.mp hs with e | e
          · exact e ▸ hjs
          · exact absurd hjs (hr' s e)
        have r := b2 hr'
        rw [a2 hg hj, hm g List.mem_cons_self hg] at r
        exact r
    · have r := b2 fun s hs => hno s (List.mem_cons_of_mem _ hs)
      rw [a3 (hno g List.mem_cons_self)] at r
      exact r

/-! ## (P) The verifier's rule for a padding column is the library's -/

/-- The verifier's rule for "column j holds padding on layer lam" is the library's isPad, for a call
whose marks are made from its segments' columns, whose segments hold the families of the library's
call cc, each with the library's length, layers and columns. fam: the family of each segment. -/
theorem padding_eq {cd : CallD} {D : Dim} {cc : Fin 8} (fam : Seg → Fam)
    (hused : cd.used = cd.segs.foldl markUsed (Array.replicate cd.J 0))
    (hfam : cd.segs.map fam = fams cc) (hmoe : ∀ s ∈ cd.segs, s.moe = isExp (fam s))
    (hsize : ∀ s ∈ cd.segs, s.pos.size = len D (fam s))
    (hpos : ∀ s ∈ cd.segs, ∀ x, x < len D (fam s) → s.pos.getD x 0 = pos D (fam s) x)
    (lam : ℕ) {j : ℕ} (hj : j < cd.J) : cd.padding lam j = isPad D cc lam j := by
  have hsz : j < (Array.replicate cd.J 0).size := by rw [Array.size_replicate]; exact hj
  have h0 : (Array.replicate cd.J 0).getD j 0 = 0 := by simp [Array.getD, hj]
  -- a segment that lists j gives the library's way back from the column
  have hF : ∀ s ∈ cd.segs, j ∈ s.pos.toList → ∃ x, famAt D cc j = some (fam s, x) := by
    intro s hs hm
    obtain ⟨x, hx, e⟩ := List.getElem_of_mem hm
    have hx' : x < s.pos.size := by simpa using hx
    have hxl : x < len D (fam s) := by rw [← hsize s hs]; exact hx'
    have hp : pos D (fam s) x = j := by
      rw [← hpos s hs x hxl, Array.getD, dif_pos hx']
      simpa using e
    have hc : call (fam s) = cc :=
      Inst.Model.FFSeg.IndexFacts.mem_fams_iff.mp (hfam ▸ List.mem_map_of_mem hs)
    exact ⟨x, (Inst.Model.FFSeg.IndexFacts.famAtPos D cc j (fam s) x).mpr ⟨hc, hxl, hp⟩⟩
  -- and the other way round
  have hG : ∀ s' x, famAt D cc j = some (s', x) → ∃ s ∈ cd.segs, fam s = s' ∧ j ∈ s.pos.toList := by
    intro s' x hf
    obtain ⟨hc, hxl, hp⟩ := (Inst.Model.FFSeg.IndexFacts.famAtPos D cc j s' x).mp hf
    have hmem : s' ∈ fams cc := Inst.Model.FFSeg.IndexFacts.mem_fams_iff.mpr hc
    rw [← hfam] at hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    refine ⟨s, hs, rfl, ?_⟩
    have hx' : x < s.pos.size := by rw [hsize s hs]; exact hxl
    have e := hpos s hs x hxl
    rw [hp, Array.getD, dif_pos hx'] at e
    rw [← e]
    simp
  show (cd.used.getD j 0 == 0 || (cd.used.getD j 0 == 2 && lam % 2 == 0)) = _
  cases hf : famAt D cc j with
  | none =>
    have hno : ∀ s ∈ cd.segs, j ∉ s.pos.toList := by
      intro s hs hm
      obtain ⟨x, e⟩ := hF s hs hm
      rw [hf] at e
      cases e
    have hu : cd.used.getD j 0 = 0 := by
      rw [hused, (used_get 0 j cd.segs _ hsz fun s hs hm => absurd hm (hno s hs)).2 hno, h0]
    have hI : isPad D cc lam j = true := by
      unfold isPad
      rw [hf]
    rw [hu, hI]
    rfl
  | some a =>
    obtain ⟨s', x⟩ := a
    obtain ⟨s, hs, rfl, hm⟩ := hG s' x hf
    have hmk : ∀ s2 ∈ cd.segs, j ∈ s2.pos.toList → markOf s2 = markOf s := by
      intro s2 h2 hm2
      obtain ⟨x2, e2⟩ := hF s2 h2 hm2
      rw [hf] at e2
      have e3 : fam s = fam s2 := congrArg Prod.fst (Option.some.inj e2)
      unfold markOf
      rw [hmoe s2 h2, hmoe s hs, e3]
    have hu : cd.used.getD j 0 = markOf s := by
      rw [hused]
      exact (used_get (markOf s) j cd.segs _ hsz hmk).1 ⟨s, hs, hm⟩
    have hI : isPad D cc lam j = !present (fam s) lam := by
      unfold isPad
      rw [hf]
    rw [hu, hI]
    unfold markOf present isExpL
    rw [hmoe s hs]
    cases isExp (fam s) <;> rcases Nat.mod_two_eq_zero_or_one lam with e | e <;> simp [e]

/-- (P) For a call of a layout that the verifier returns, whose line names the families of the
library's call cc in the library's order: the verifier's rule for a padding column is the library's
isPad, on every layer and every column of the call. Asked beside: the switches; sizes that agree
with the shape. The verifier's least number of columns is not asked to be the library's: where the
verifier's call has more columns, the further ones are padding by both rules. -/
theorem padding_isPad {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {D : Dim} (Z : Sized h D) {cd : CallD}
    (hcd : cd ∈ y.calls) {cc : Fin 8} (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (lam : ℕ) {j : ℕ} (hj : j < cd.J) : cd.padding lam j = isPad D cc lam j := by
  have A := admitted_of_layout hy S.p3
  have hseg : ∀ s ∈ cd.segs, s.n = len D (famS s) ∧ s.moe = isExp (famS s) ∧ s.pos.size = s.n := by
    intro s hs
    obtain ⟨fam, a1, a2, a3, a4, -⟩ := segs_of_layout hy S cd hcd s hs
    have e : famS s = fam := by
      unfold famS
      rw [a1, famOf_segName]
      rfl
    rw [e]
    exact ⟨a2.trans (Z.len_eq fam).symm, a3, a4⟩
  have hfam : cd.segs.map famS = fams cc := by
    have e1 : cd.segs.map famS = (cd.segs.map (·.name)).map fun n => (famOf n).getD .G := by
      rw [List.map_map]
      rfl
    rw [e1, hn, List.map_map]
    conv_rhs => rw [← List.map_id (fams cc)]
    refine List.map_congr_left fun s _ => ?_
    show (famOf (segName s)).getD .G = s
    rw [famOf_segName]
    rfl
  have hlt : ∀ s ∈ fams cc, len D s < 2 ^ (topBit + 1) := fun s _ => by
    rw [Z.len_eq s]
    exact len_lt A s
  obtain ⟨cl, taken, -, -, h3⟩ := A.calls
  rw [h3] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  exact padding_eq famS rfl hfam (fun s hs => (hseg s hs).2.1)
    (fun s hs => (hseg s hs).2.2.trans (hseg s hs).1)
    (pos_eq_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam (fun g hg => (hseg g hg).1) hlt) lam hj

/-! ## (F) What the two loops over the calls and their columns make -/

/-- A loop in which each step keeps the array's size n and adds A x θ at every index θ below n: the
whole loop keeps the size and adds the sum. -/
theorem loop_adds {α : Type} (g : α → Array ℕ → Except String (Array ℕ)) (A : α → ℕ → ℕ) (n : ℕ)
    (hg : ∀ x pub pub', pub.size = n → g x pub = .ok pub' →
      pub'.size = n ∧ ∀ θ, θ < n → pub'.getD θ 0 = pub.getD θ 0 + A x θ) :
    ∀ (l : List α) (pub pub' : Array ℕ), pub.size = n →
      l.foldlM (fun pub x => g x pub) pub = .ok pub' →
      pub'.size = n ∧ ∀ θ, θ < n → pub'.getD θ 0 = pub.getD θ 0 + (l.map fun x => A x θ).sum
  | [], pub, pub', hs, h => by
    have e : pub = pub' := Except.ok.inj (show Except.ok pub = Except.ok pub' from h)
    subst e
    exact ⟨hs, fun θ _ => by simp⟩
  | x :: l, pub, pub', hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨p1, h1, h2⟩ := ok_of_bind h
    obtain ⟨s1, e1⟩ := hg x pub p1 hs h1
    obtain ⟨s2, e2⟩ := loop_adds g A n hg l p1 pub' s1 h2
    refine ⟨s2, fun θ hθ => ?_⟩
    rw [e2 θ hθ, e1 θ hθ, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- One step of the inner loop: if P holds, a test, and T is added at the index ix. -/
theorem pub_step (P R : Bool) (ix T n : ℕ) (nm : String) (pub pub' : Array ℕ) (hs : pub.size = n)
    (h : (if P = true then (do refuseIf R nm; pure (pub.modify ix (· + T))) else pure pub :
      Except String (Array ℕ)) = .ok pub') :
    pub'.size = n ∧ ∀ θ, θ < n →
      pub'.getD θ 0 = pub.getD θ 0 + if P = true ∧ ix = θ then T else 0 := by
  by_cases hP : P = true
  · rw [if_pos hP] at h
    obtain ⟨-, h⟩ := ok_of_refuse h
    have e : pub.modify ix (· + T) = pub' :=
      Except.ok.inj (show Except.ok (pub.modify ix (· + T)) = Except.ok pub' from h)
    subst e
    refine ⟨by rw [Array.size_modify]; exact hs, fun θ hθ => ?_⟩
    by_cases e : ix = θ
    · have hi : ix < pub.size := by rw [e, hs]; exact hθ
      rw [getD_modify_add pub ix θ T hi, if_pos e, if_pos ⟨hP, e⟩]
    · have hθ' : θ < pub.size := by rw [hs]; exact hθ
      rw [if_neg fun k => e k.2, Nat.add_zero]
      simp [Array.getD, hθ', Array.getElem_modify, e]
  · rw [if_neg hP] at h
    have e : pub = pub' := Except.ok.inj (show Except.ok pub = Except.ok pub' from h)
    subst e
    exact ⟨hs, fun θ _ => by rw [if_neg fun k => hP k.1, Nat.add_zero]⟩

/-- What one call adds to the count of tree θ: the number of tokens for each padding column of the
call that lies in the tree. first, dT: the call's first tree and the depth of a tree. -/
def pubOf (y : Lay) (first dT : ℕ) (cd : CallD) (θ : ℕ) : ℕ :=
  ((List.range (y.Lam * cd.J)).map fun x =>
    if cd.padding (x / cd.J) (x % cd.J) = true ∧ first + x / 2 ^ (dT - y.h.lt) = θ then y.T
    else 0).sum

/-- The inner loop: pubOfCall keeps the size and adds pubOf. -/
theorem pubOfCall_adds (y : Lay) (fo : Model.Forest.Shape) (q : ℕ) (cd : CallD) (n : ℕ)
    (pub pub' : Array ℕ) (hs : pub.size = n) (h : y.pubOfCall fo q cd pub = .ok pub') :
    pub'.size = n ∧ ∀ θ, θ < n →
      pub'.getD θ 0 = pub.getD θ 0 + pubOf y (fo.first.getD q 0) fo.dT cd θ := by
  unfold Lay.pubOfCall at h
  exact loop_adds
    (fun x pub => if cd.padding (x / cd.J) (x % cd.J) = true then (do
        refuseIf (x / 2 ^ (fo.dT - y.h.lt) / 2 ^ fo.iota.getD q 0 != 0) "internal-forest-pub"
        pure (pub.modify (fo.first.getD q 0 + x / 2 ^ (fo.dT - y.h.lt)) (· + y.T)))
      else pure pub)
    (fun x θ => if cd.padding (x / cd.J) (x % cd.J) = true ∧
      fo.first.getD q 0 + x / 2 ^ (fo.dT - y.h.lt) = θ then y.T else 0) n
    (fun x pub pub' hs h => pub_step _ _ _ _ n _ pub pub' hs h) _ pub pub' hs h

/-- The second half of the layout fills the field pub by the loop over the calls. -/
theorem look_pub {y y' : Lay} (hy : layoutLook y = .ok y') :
    ∃ fo pub, y'.fo = { fo with pub := pub } ∧
      (y'.calls.toList.zipIdx).foldlM (fun pub x => y'.pubOfCall fo x.2 x.1 pub)
        (Model.Forest.noPub fo) = .ok pub := by
  unfold layoutLook at hy
  obtain ⟨u, hu, hy⟩ := ok_of_bind hy
  obtain ⟨fo, hfo, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨kbm, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, hpub, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  cases hy
  exact ⟨fo, pub, rfl, hpub⟩

/-- (F) The verifier's count of the padding keys of tree θ, for a layout that it returns: the sum
over the calls of what each adds. There is one count for each tree. -/
theorem pub_fold {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    y.fo.pub.size = y.fo.NT ∧ ∀ θ, θ < y.fo.NT → y.fo.pub.getD θ 0 =
      (y.calls.toList.zipIdx.map fun c => pubOf y (y.fo.first.getD c.2 0) y.fo.dT c.1 θ).sum := by
  unfold layout at hy
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy
  obtain ⟨fo, pub, e, hp⟩ := look_pub h1
  have hs : (Model.Forest.noPub fo).size = fo.NT := by
    unfold Model.Forest.noPub
    rw [Array.size_replicate]
  obtain ⟨s1, e1⟩ := loop_adds (fun (c : CallD × ℕ) pub => y.pubOfCall fo c.2 c.1 pub)
    (fun c θ => pubOf y (fo.first.getD c.2 0) fo.dT c.1 θ) fo.NT
    (fun c pub pub' hs h => pubOfCall_adds y fo c.2 c.1 fo.NT pub pub' hs h) _ _ pub hs hp
  rw [e]
  refine ⟨s1, fun θ hθ => ?_⟩
  have h0 : (Model.Forest.noPub fo).getD θ 0 = 0 := by
    unfold Model.Forest.noPub
    simp [Array.getD]
  have r := e1 θ hθ
  rw [h0, Nat.zero_add] at r
  exact r

#print axioms padding_eq
#print axioms padding_isPad
#print axioms pub_fold

/-! ## Counting by blocks -/

/-- The quotient of u M + v by M, for v below M. -/
theorem div_block {M v : ℕ} (u : ℕ) (hv : v < M) : (u * M + v) / M = u := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le v) hv),
    Nat.div_eq_of_lt hv, Nat.zero_add]

/-- Of the numbers below A M, those in block t, of M numbers: a sum of T over those that have the
property Q. -/
theorem sum_block (Q : ℕ → Bool) (T M : ℕ) {A t : ℕ} (ht : t < A) :
    ((List.range (A * M)).map fun x => if Q x = true ∧ x / M = t then T else 0).sum =
      ∑ x' ∈ range M, if Q (t * M + x') = true then T else 0 := by
  rw [list_range_sumM, Inst.Model.FFSeg.IndexFacts.sum_range_mul, Finset.sum_eq_single t]
  · refine sum_congr rfl fun v hv => ?_
    rw [div_block t (mem_range.mp hv)]
    by_cases hq : Q (t * M + v) = true
    · rw [if_pos ⟨hq, rfl⟩, if_pos hq]
    · rw [if_neg fun k => hq k.1, if_neg hq]
  · intro u _ hu
    refine sum_eq_zero fun v hv => ?_
    rw [div_block u (mem_range.mp hv), if_neg fun k => hu k.2]
  · intro k
    exact absurd (mem_range.mpr ht) k

/-- Of the M T numbers X, how many have the property Q at (t (M T) + X) / T: T for each x' below M
with Q at t M + x'. -/
theorem card_block (Q : ℕ → Bool) (T M t : ℕ) :
    ((range (M * T)).filter fun X => Q ((t * (M * T) + X) / T) = true).card =
      ∑ x' ∈ range M, if Q (t * M + x') = true then T else 0 := by
  rw [Finset.card_filter, Inst.Model.FFSeg.IndexFacts.sum_range_mul]
  refine sum_congr rfl fun x' _ => ?_
  have e : ∀ i ∈ range T, (if Q ((t * (M * T) + (x' * T + i)) / T) = true then 1 else 0) =
      if Q (t * M + x') = true then 1 else 0 := by
    intro i hi
    have a : t * (M * T) + (x' * T + i) = (t * M + x') * T + i := by ring
    rw [a, div_block _ (mem_range.mp hi)]
  rw [sum_congr rfl e]
  by_cases hq : Q (t * M + x') = true
  · simp [hq]
  · simp [hq]

/-- A sum over a list with its members' numbers, as a sum over the numbers. -/
theorem zipIdx_sum {α : Type} (d : α) (f : α × ℕ → ℕ) : ∀ (l : List α) (n : ℕ),
    ((l.zipIdx n).map f).sum = ∑ q ∈ range l.length, f (l.getD q d, n + q)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum d f l (n + 1), List.length_cons,
      Finset.sum_range_succ', Nat.add_comm]
    congr 1
    refine sum_congr rfl fun q _ => ?_
    have e : n + 1 + q = n + (q + 1) := by omega
    rw [e]
    rfl

/-! ## (C) The verifier's count is the number of padding indices of the tree -/

/-- The right side of the library's statement padCountEq (Inst/Model/FF/Index.lean), to the letter:
the number of the indices of tree θ whose column is padding on their layer. -/
def padCard (D : Dim) (θ : ℕ) : ℕ :=
  ((range (2 ^ Dk D)).filter fun X =>
    isPad D (callOf D θ)
      (((θ - firstTree D (callOf D θ)) * 2 ^ Dk D + X) / D.T / 2 ^ lJ D (callOf D θ))
      (((θ - firstTree D (callOf D θ)) * 2 ^ Dk D + X) / D.T % 2 ^ lJ D (callOf D θ))).card

/-- padCard, column by column: the number of positions for each padding column of the tree. Asked: a
tree holds at least the positions of one column. -/
theorem padCard_eq (D : Dim) (θ : ℕ) (hk : D.lT ≤ Dk D) :
    padCard D θ = ∑ x' ∈ range (2 ^ (Dk D - D.lT)),
      if isPad D (callOf D θ)
          (((θ - firstTree D (callOf D θ)) * 2 ^ (Dk D - D.lT) + x') / 2 ^ lJ D (callOf D θ))
          (((θ - firstTree D (callOf D θ)) * 2 ^ (Dk D - D.lT) + x') % 2 ^ lJ D (callOf D θ)) = true
      then D.T else 0 := by
  have e2 : 2 ^ Dk D = 2 ^ (Dk D - D.lT) * D.T := by
    have e3 : Dk D - D.lT + D.lT = Dk D := Nat.sub_add_cancel hk
    show 2 ^ Dk D = 2 ^ (Dk D - D.lT) * 2 ^ D.lT
    rw [← pow_add, e3]
  unfold padCard
  rw [e2]
  exact card_block (fun x => isPad D (callOf D θ) (x / 2 ^ lJ D (callOf D θ))
    (x % 2 ^ lJ D (callOf D θ))) D.T (2 ^ (Dk D - D.lT)) (θ - firstTree D (callOf D θ))

section Layout

variable {h : Model.Layer.Shape} {pc : List (List String)} {v : Env} {D : Dim}

/-- The verifier's number of trees is the library's. The hypotheses are those of Dk_of_layout
(Johnson/Road/FormsKeysShape.lean). -/
theorem NT_of_layout (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) : v.y.fo.NT = NT D := by
  have T := treesFit_of_layout hy S Z hc h8 H
  obtain ⟨s0, pub, hs0, e⟩ := shape_of_layout hy
  obtain ⟨-, hN, -, -⟩ := shape_numbers hs0
  have hsz : v.y.cl.size = 8 := by rw [(fo_of_layout hy).2.2, h8]
  rw [hsz] at hN
  have io : ∀ c : Fin 8, s0.iota.getD c.val 0 = eC D c := by
    intro c
    have r := T.iota c
    rw [e] at r
    exact r
  rw [e]
  show s0.NT = NT D
  rw [hN, Finset.sum_range]
  exact Finset.sum_congr rfl fun c _ => by rw [io c]; rfl

/-- What the call number cc of such a layout adds to the count of tree θ: nothing, if θ is no tree
of the library's call cc; else the number of tokens for each padding column of the tree. -/
theorem pubOf_call (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hcap : D.lT ≤ D.cap) {cc : Fin 8} {cd : CallD} (hcq : v.y.calls[cc.val]? = some cd)
    (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) (θ : ℕ) :
    pubOf v.y (firstTree D cc) (Dk D) cd θ =
      if firstTree D cc ≤ θ ∧ θ < firstTree D cc + trees D cc then
        ∑ x' ∈ range (2 ^ (Dk D - D.lT)),
          if isPad D cc (((θ - firstTree D cc) * 2 ^ (Dk D - D.lT) + x') / 2 ^ lJ D cc)
            (((θ - firstTree D cc) * 2 ^ (Dk D - D.lT) + x') % 2 ^ lJ D cc) = true then D.T else 0
      else 0 := by
  have A := admitted_of_layout hy S.p3
  have hcd : cd ∈ v.y.calls := Array.mem_of_getElem? hcq
  have hlJ : cd.lJ = lJ D cc := by
    rw [lJ_of_call hy S Z hcd hn]
    exact Nat.max_eq_left hfl
  have hJ : cd.J = 2 ^ lJ D cc := by
    obtain ⟨cl, taken, -, -, h3⟩ := A.calls
    have hcd' := hcd
    rw [h3] at hcd'
    obtain ⟨c0, -, e0⟩ := List.mem_map.mp (List.mem_toArray.mp hcd')
    rw [← hlJ, ← e0]
    rfl
  have hJ0 : 0 < 2 ^ lJ D cc := Nat.two_pow_pos _
  have hT : v.y.T = D.T := by
    rw [(laid2_of_layout hy).T, A.shape, ← Z.lT]
    rfl
  have hlt : v.y.h.lt = D.lT := by rw [A.shape, Z.lT]
  have hk := lT_le_Dk D hcap
  have hka := Inst.Model.FFSeg.IndexFacts.Dk_le D cc
  have haC : aC D cc = D.lL + lJ D cc + D.lT := rfl
  -- the columns of all layers are the call's trees times the columns of a tree
  have hN : v.y.Lam * cd.J = trees D cc * 2 ^ (Dk D - D.lT) := by
    rw [A.laid.Lam, A.shape, ← Z.lL, hJ, ← pow_add]
    show 2 ^ (D.lL + lJ D cc) = 2 ^ (aC D cc - Dk D) * 2 ^ (Dk D - D.lT)
    rw [← pow_add]
    congr 1
    omega
  unfold pubOf
  rw [hN, hT, hlt, hJ]
  have hpad : ∀ x, cd.padding (x / 2 ^ lJ D cc) (x % 2 ^ lJ D cc) =
      isPad D cc (x / 2 ^ lJ D cc) (x % 2 ^ lJ D cc) := fun x =>
    padding_isPad hy S Z hcd hn _ (by rw [hJ]; exact Nat.mod_lt _ hJ0)
  simp only [hpad]
  by_cases hb : firstTree D cc ≤ θ ∧ θ < firstTree D cc + trees D cc
  · rw [if_pos hb, ← sum_block (fun x => isPad D cc (x / 2 ^ lJ D cc) (x % 2 ^ lJ D cc)) D.T
      (2 ^ (Dk D - D.lT)) (A := trees D cc) (t := θ - firstTree D cc) (by omega)]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    have e : (firstTree D cc + x / 2 ^ (Dk D - D.lT) = θ) ↔
        (x / 2 ^ (Dk D - D.lT) = θ - firstTree D cc) := by omega
    simp only [e]
  · rw [if_neg hb]
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    refine if_neg fun k => hb ?_
    have hx' : x < trees D cc * 2 ^ (Dk D - D.lT) := List.mem_range.mp hx
    have hq : x / 2 ^ (Dk D - D.lT) < trees D cc :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
    obtain ⟨-, k2⟩ := k
    rw [← k2]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hq _⟩

/-- (C) THE VERIFIER'S COUNT OF THE PADDING KEYS OF A TREE IS THE NUMBER OF THE TREE'S PADDING
INDICES, in the library's own words: the right side of its statement padCountEq. For a layout with
eight calls, where call number cc has the line of the library's call cc and the verifier's least
number of columns does not bite; sizes that agree with the shape and have the verifier's cap: the
hypotheses of Dk_of_layout. The library's Dim.OK is not asked. -/
theorem pub_card (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    ∀ θ, θ < NT D → v.y.fo.pub.getD θ 0 = padCard D θ := by
  intro θ hθ
  have T := treesFit_of_layout hy S Z hc h8 H
  have hcap : D.lT ≤ D.cap := hcap_of_layout hy Z hc
  have hk := lT_le_Dk D hcap
  obtain ⟨b1, b2⟩ := Inst.Model.FFSeg.IndexFacts.callOf_spec D hθ
  rw [(pub_fold hy).2 θ (by rw [NT_of_layout hy S Z hc h8 H]; exact hθ),
    zipIdx_sum default _ v.y.calls.toList 0]
  have hlen : v.y.calls.toList.length = 8 := by simpa using h8
  rw [hlen, Finset.sum_range, Finset.sum_eq_single (callOf D θ)]
  · obtain ⟨cd, hcq, hn, hfl⟩ := H (callOf D θ)
    have hg : v.y.calls.toList.getD (callOf D θ).val default = cd := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hcq]
      rfl
    show pubOf v.y (v.y.fo.first.getD (0 + (callOf D θ).val) 0) v.y.fo.dT
      (v.y.calls.toList.getD (callOf D θ).val default) θ = _
    rw [hg, Nat.zero_add, T.first, T.dT, pubOf_call hy S Z hcap hcq hn hfl θ, if_pos ⟨b1, b2⟩,
      padCard_eq D θ hk]
  · intro cc _ hne
    obtain ⟨cd, hcq, hn, hfl⟩ := H cc
    have hg : v.y.calls.toList.getD cc.val default = cd := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hcq]
      rfl
    show pubOf v.y (v.y.fo.first.getD (0 + cc.val) 0) v.y.fo.dT
      (v.y.calls.toList.getD cc.val default) θ = 0
    rw [hg, Nat.zero_add, T.first, T.dT, pubOf_call hy S Z hcap hcq hn hfl θ, if_neg]
    intro k
    exact hne (Inst.Model.FFSeg.IndexFacts.callOf_eq D k.1 k.2).symm
  · intro k
    exact absurd (Finset.mem_univ _) k

/-- (E) Where the library's Dim.OK holds, the verifier's count is the library's padCount, by the
library's own theorem padCountEq. Of Dim.OK that theorem's proof reads that a tree holds whole
layers. Where a tree holds less than a layer, padCount is 0 and the verifier's count need not
be. -/
theorem pub_eq (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) (hD : D.OK) :
    ∀ θ, θ < NT D → v.y.fo.pub.getD θ 0 = padCount D θ := by
  intro θ hθ
  rw [pub_card hy S Z hc h8 H θ hθ, Inst.Model.FFSeg.IndexFacts.padCountEq D hD θ hθ]
  rfl

/-- (M) The keys in the trees that hold only padding: as many trees as the library's numbers leave
between the number of trees and the next power of two; none where the library's Dim.OK holds. -/
theorem empty_eq (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    v.y.fo.emptyKeys = (2 ^ sg D - NT D) * 2 ^ Dk D ∧ (D.OK → v.y.fo.emptyKeys = 0) := by
  have T := treesFit_of_layout hy S Z hc h8 H
  have e : v.y.fo.emptyKeys = (2 ^ sg D - NT D) * 2 ^ Dk D := by
    unfold Model.Forest.Shape.emptyKeys
    rw [T.rK, T.dT, NT_of_layout hy S Z hc h8 H]
  refine ⟨e, fun hD => ?_⟩
  rw [e, hD.full, Nat.sub_self, Nat.zero_mul]

end Layout

#print axioms sum_block
#print axioms card_block
#print axioms padCard_eq
#print axioms NT_of_layout
#print axioms pubOf_call
#print axioms pub_card
#print axioms pub_eq
#print axioms empty_eq

end OnBytes.Road
