-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OwnKinds.lean: IN THE GOALS' SCOPE AN ENTRY OF THE 25 LISTS WHOSE LABEL NAMES THE ENTRY
ITSELF IS A MATRIX THAT ITS OWN SUB-PROOF COMMITS TO (TMat.kind = 0). Statements and proofs.

  bordersOf_kinds · planG_kinds · plan_kinds · kind_tails   the layers' lists: the walks of the library's bordersOf_labels, planG_labels, plan_labels (Johnson/Road/HeadDict.lean) and labA_tails (Johnson/Road/FormsKeysDictA.lean), at the field kind
  kind_even · kind_odd · kind_head   the kinds in scope: a group's list: 1 at entry 8 of a later group, else 0 · attention's four first entries: 0 · the head's seven first entries: 0
  **kind_own**       the label names the entry itself ⟹ kind 0

What is not claimed. The full size alone. No soundness.

-/
import Johnson.Goal.Meaning.HidOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace IM.Own

open OnBytes OnBytes.Road OnBytes.Road.L5 Meaning
open OnBytes.Model (TMat T2Foreign Settings)
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx tailsOf bordersOf planG plansFrom plansG Pub HPlan2 Scales)

theorem getD_of_map {α β : Type} (f : α → β) {a b : Array α} (h : a.map f = b.map f) (n : ℕ)
    (d : α) : f (a.getD n d) = f (b.getD n d) := by
  have k0 := congrArg (fun z : Array β => z[n]?) h
  have k : (a[n]?).map f = (b[n]?).map f := by simpa using k0
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases ha : a[n]? with
  | none =>
    cases hb : b[n]? with
    | none => rfl
    | some y =>
      rw [ha, hb] at k
      cases k
  | some x =>
    cases hb : b[n]? with
    | none =>
      rw [ha, hb] at k
      cases k
    | some y =>
      rw [ha, hb] at k
      exact Option.some.inj k

/-- bordersOf keeps the matrices' order, number and kinds. -/
theorem bordersOf_kinds {y : Lay} {ms : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign} (h : bordersOf y ms = .ok r) :
    (r.1.map fun M => M.kind) = ms.map fun M => M.kind := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := (Except.ok.inj h).symm
  subst e
  have H : ∀ (l : List (TMat × ℕ))
      (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
      ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
        if (x.1.kind == 0 && (x.2 == (Model.Layer.matIx y).iXO ||
            (y.h.p4 && x.2 == (Model.Layer.matIx y).iQA))) = true then
          (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
        else if (x.1.kind == 1) = true then
          (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
           s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                          wp := x.1.wp }, s.2.2.2)
        else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)) s).1.toList.map
          fun M => M.kind) =
        (s.1.toList.map fun M => M.kind) ++ l.map fun x => x.1.kind := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, ih]
      split_ifs <;> simp
  have h1 := H ms.toList.zipIdx (#[], #[], #[], 0)
  apply Array.ext'
  rw [Array.toList_map, Array.toList_map]
  refine Eq.trans h1 ?_
  have h2 : (ms.toList.zipIdx.map fun x => x.1.kind) =
      (ms.toList.zipIdx.map (·.1)).map fun M => M.kind := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]
  simp

theorem planG_kinds {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) :
    (hp.tl.mats.map fun M => M.kind) = (P.tails.getD g {}).mats.map fun M => M.kind := by
  obtain ⟨b, hb, e⟩ := Hd.planG_mats h
  rw [e]
  exact bordersOf_kinds hb

theorem plan_kinds {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) (g : ℕ) (hp : HPlan2) (hg : G[g]? = some hp) :
    (hp.tl.mats.map fun M => M.kind) = ((tailsOf y).getD g {}).mats.map fun M => M.kind := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
  rw [Nat.zero_add] at hO
  exact planG_kinds hO

/-- The kinds that the verifier's plan gives. -/
theorem kind_tails (y : Lay) {g n : ℕ} (hg : g < y.NGr)
    (hn : n < y.parts.getD 0 0 + y.parts.getD 1 0 + 5) :
    (((tailsOf y).getD g {}).mats.getD n {}).kind =
      if n = (matIx y).iXI ∧ g ≠ 0 then 1 else 0 := by
  have hb : ((n == (matIx y).iXI && g != 0) = true) ↔ (n = (matIx y).iXI ∧ g ≠ 0) := by simp
  unfold tailsOf
  dsimp only
  rw [range_map_at _ _ _ hg]
  dsimp only
  rw [zipIdx_map_at _ _ _ (by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
    omega)]
  dsimp only
  by_cases h1 : n = (matIx y).iXI ∧ g ≠ 0
  · rw [if_pos h1, if_pos (hb.mpr h1)]
  · rw [if_neg h1, if_neg fun h => h1 (hb.mp h)]

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

theorem kind_even (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {a : ℕ} (ha : a < 9) :
    ((matsAt X (2 * g)).getD a {}).kind = if a = 8 ∧ g ≠ 0 then 1 else 0 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨-, -, i8⟩ := ix_of_core h C
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨P, e⟩ := planG_there h C hg
  rw [matsAt_even hg e, getD_of_map (fun M : TMat => M.kind) (plan_kinds hP hG g P e) a {},
    kind_tails X.y (by rw [B.groups]; exact hg) (by rw [p0, p1]; exact ha), i8]

theorem kind_odd (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {a : ℕ} (ha : a < 4) : ((matsAt X (2 * g + 1)).getD a {}).kind = 0 := by
  obtain ⟨i, -, n1, e⟩ := matsAt_att_gid h C hg
  rw [e]
  unfold Attention.matrices
  dsimp only
  rw [n1]
  have c : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases c with rfl | rfl | rfl | rfl <;>
    simp [fixed, Attention.ownMatrix, List.range_succ, Array.getD_eq_getD_getElem?]

theorem kind_head (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {a : ℕ} (ha : a < 7) :
    ((matsAt X 24).getD a {}).kind = 0 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  have em : X.H.tl.mats = Model.Head.matsH X.hS X.HLy (Model.Verify.borderOf X.y) (1 + X.y.NGr)
      stream.aId := by
    rw [e]
    exact hm
  rw [matsAt_head, em]
  unfold Model.Head.matsH
  rw [hN]
  have c : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **In scope: an entry whose label names the entry itself is of kind 0.** -/
theorem kind_own (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ}
    (hk : k < 25) (ha : a < (matsAt X k).size) (ho : ownerK (labAt X k a) = k) :
    ((matsAt X k).getD a {}).kind = 0 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨i6, i7, i8⟩ := ix_of_core h C
  by_cases h24 : k = 24
  · subst h24
    rw [size_head h C] at ha
    by_cases e : a = 7
    · subst e
      exfalso
      have L : labAt X 24 7 = (1 + 11) * 256 + 7 := by
        rw [lab_head h C ha]
        unfold Hd.labH labA
        rw [hN, B.groups, i7, i8, if_pos rfl, if_neg (by omega)]
      obtain ⟨o1, -⟩ := owner_of (1 + 11) 7 (by norm_num)
      rw [L, o1, linkOf_group (by norm_num)] at ho
      omega
    · exact kind_head h C (by omega)
  · by_cases hev : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_even h C hg] at ha
      by_cases e : a = 8 ∧ g ≠ 0
      · exfalso
        have L : labAt X (2 * g) a = (1 + (g - 1)) * 256 + 7 := by
          rw [lab_even h C hg ha]
          unfold labA
          rw [i7, i8, if_pos e, show 1 + (g - 1) = g by omega]
        obtain ⟨o1, -⟩ := owner_of (1 + (g - 1)) 7 (by norm_num)
        rw [L, o1, linkOf_group (by omega)] at ho
        omega
      · rw [kind_even h C hg ha, if_neg e]
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_odd h C hg] at ha
      obtain ⟨i, -, n1, -⟩ := matsAt_att_gid h C hg
      by_cases e : a = 4
      · subst e
        exfalso
        obtain ⟨M, a1, -, -, a4⟩ := entryA h C hg
        rw [n1] at a1
        have L : labAt X (2 * g + 1) 4 = (1 + g) * 256 + 6 := by
          unfold labAt
          rw [getD_of a1, a4]
          unfold labA
          rw [i6, i8, if_neg (by omega)]
        obtain ⟨o1, -⟩ := owner_of (1 + g) 6 (by norm_num)
        rw [L, o1, linkOf_group hg] at ho
        omega
      · exact kind_odd h C hg (by omega)

end Core

end IM.Own

#print axioms IM.Own.kind_even
#print axioms IM.Own.kind_odd
#print axioms IM.Own.kind_head
#print axioms IM.Own.kind_own
