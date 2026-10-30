-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MadeAtPlans.lean: THE SMALLNESS TEST: THE RECORD OF EVERY SMALLNESS TEST IN WHAT
Verify.publicOf RETURNS IS, BUT FOR TWO LISTS OF PLACES, WHAT THE ROUTINE THAT LAYS THE ARRAYS
(addTreesF, OnBytes/Model/Tail.lean) RETURNED ON WHAT THE ROUTINE OF SHAPES (shapeF) RETURNED; SO
THERE THE SHAPES FIT THE MATRICES AND EVERY MATRIX HAS A ROW OF CELLS. Definitions, statements and
proofs. On the routines that make a plan alone: no state, no prover. Lemmas; none of the library's
goals.

Why. The planners' routines behind addTreesF (ownerIs, borderMeans, attentionOwnerPlace, ownerHeld)
write the two lists plOwn and plFor alone.
  `SameL a b`   b is a but for these two lists; `SameL.refl`, `SameL.trans`, `borderMeans_sameL`,
      `ownerIs_sameL`, `ownerPlace_sameL`, `owners_sameL`, `ownerHeld_sameL`
  **`Made tlc`**   tlc is, but for the two lists, addTreesF's return on shapeF's return
  `planG_made`, `planA_made`, `planH2_made`, **`public_made`**   at the three planners' returns; at
      all records of the three kinds of plans in what Verify.publicOf returns
  **`shapeF_pos`**   shapeF's return holds the list of matrices that it was handed; each has a row
      of cells; without a matrix there is no column
  **`sizesB tl`**   with code: each shape has its matrix's numbers of rows of cells and of columns;
      each matrix has a row of cells; without a matrix there is no column
  **`made_sizes`**   `Made tlc` gives `sizesB tlc`
By: the walks of Johnson/P1K8R/UnitsAtPlan.lean and UnitsAtPlans.lean · addTreesF_fits
(OnBytes/Tie/Pv/Tail/EndSame.lean) · piecesF_sameC and the walk of shapeF_cols
(Johnson/Desc/First/Look/ColsAt.lean).
Limits. Nothing on two matrices' arrays. Nothing on a record that a later routine of a run has
turned.

-/
import Johnson.P1K8R.UnitsAtPlans
import Johnson.Desc.First.Look.ColsAt
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open _root_.Fo (pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan

/-- b is a but for the two lists of places. -/
def SameL (a b : HTailF2) : Prop := ({ b with plFor := a.plFor, plOwn := a.plOwn } : HTailF2) = a

theorem SameL.refl (a : HTailF2) : SameL a a := rfl

theorem SameL.trans {a b c : HTailF2} (h : SameL a b) (k : SameL b c) : SameL a c := by
  unfold SameL at h k ⊢
  have e : ({ c with plFor := a.plFor, plOwn := a.plOwn } : HTailF2) =
      { ({ c with plFor := b.plFor, plOwn := b.plOwn } : HTailF2) with
        plFor := a.plFor, plOwn := a.plOwn } := rfl
  rw [e, k]
  exact h

theorem ownerIs_sameL (a : HTailF2) (no : Nat) : SameL a (a.ownerIs no) := rfl

theorem borderMeans_sameL {a b : HTailF2} {iF ownerNo index : Nat}
    (e : a.borderMeans iF ownerNo index = .ok b) : SameL a b := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      rfl

theorem ownerPlace_sameL {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : SameL X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_sameL h1

/-- What the loop keeps. -/
def SameLKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ SameL s0.tl s.tl

theorem ownerPlaces_sameL (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), SameLKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → SameLKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_sameL G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨s0, e0, a0.trans (ownerPlace_sameL h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_sameL {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : SameLKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_sameL G A _ A r (fun i s hi => ⟨s, hi, SameL.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, SameL.refl _⟩

theorem ownerHeld_sameL {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameL tl tl' := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_sameL hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- But for the two lists: what addTreesF returned on what shapeF returned. -/
def Made (tlc : HTailF2) : Prop :=
  ∃ (tl₀ tl tl' : HTailF2) (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign)
    (hasU : Array Bool) (tau : Nat) (F G : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat), tl₀.shapeF m txOf f hasU tau = .ok tl ∧
    tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T') ∧ SameL tl' tlc

theorem made_of {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    {tlc : HTailF2} (hr : SameL tl' tlc) : Made tlc :=
  ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩

theorem planG_made (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Made hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact made_of hS hA (ownerIs_sameL tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact made_of hS hA ((ownerIs_sameL tl1 g).trans (borderMeans_sameL hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_made (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameL P.seam.tl tlc) : Made tlc := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact made_of hS hA hr

theorem planH2_made (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : Made hp.tl := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact made_of hS hA (ownerHeld_sameL hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_made (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : Made hp.tl :=
  planG_made X.layers g _ hp (public_G h g hp hg)

theorem public_H_made (h : Verify.publicOf pol KL layout = .ok X) : Made X.H.tl := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k := planH2_made _ _ _ _ _ _ _ H0 h0
  rw [e]
  exact k

theorem public_A_made (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : Made a.seam.tl := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameL k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show Made s.tl
    rw [f3] at f2
    exact planA_made _ _ _ a0 m2 s.tl f2
  · simp at e1

/-- **At the record of every smallness test in what publicOf returns.** -/
theorem public_made (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → Made hp.tl) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → Made a.seam.tl) ∧ Made X.H.tl :=
  ⟨public_G_made h, public_A_made h, public_H_made h⟩

end

/-- **What shapeF's return holds of the matrices.** -/
theorem shapeF_pos {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.mats = m ∧ tl'.NM = m.size ∧ (∀ mu, mu < m.size → 0 < (m.getD mu {}).m) ∧
      (m.size = 0 → tl'.mz = 0) := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := OnBytes.Road.ok_of_jp h
  obtain ⟨_, h⟩ := OnBytes.Road.ok_of_jp h
  obtain ⟨r1, h1, h⟩ := OnBytes.Road.ok_of_bind h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := OnBytes.Road.ok_of_jp h
  obtain ⟨r2, h2, h⟩ := OnBytes.Road.ok_of_bind h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := OnBytes.Road.ok_of_bind h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := OnBytes.Road.ok_of_jp h
  obtain ⟨_, h⟩ := OnBytes.Road.ok_of_jp h
  have hC := piecesF_sameC h
  clear h h2 h1
  have K3 := OnBytes.Road.forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      (∀ mu ∈ pre, 0 < (m.getD mu {}).m) ∧ (pre = [] → s.2.1 = 0))
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      have i1 : ∀ mu ∈ pre, 0 < (m.getD mu {}).m := hI.1
      dsimp only at hs
      obtain ⟨hm, hs⟩ := OnBytes.Road.ok_of_jp hs
      obtain ⟨_, hs⟩ := OnBytes.Road.ok_of_jp hs
      have keep : (∀ mu ∈ pre ++ [a], 0 < (m.getD mu {}).m) ∧
          (pre ++ [a] = [] → mz' + (m.getD a {}).m = 0) := by
        refine ⟨fun mu hmu => ?_, fun e0 => absurd e0 (by simp)⟩
        rcases List.mem_append.1 hmu with h1 | h1
        · exact i1 mu h1
        · obtain rfl := List.mem_singleton.1 h1
          exact Nat.pos_of_ne_zero fun e0 => hm (by rw [e0]; rfl)
      split at hs
      · split at hs
        · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
        · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
      · split at hs
        · split at hs
          · simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl ⟨fun _ hj => absurd hj List.not_mem_nil, fun _ => rfl⟩ h3
  obtain ⟨k1, k2⟩ : (∀ mu ∈ List.range m.size, 0 < (m.getD mu {}).m) ∧
      (List.range m.size = [] → mz = 0) := K3
  refine ⟨hC.mats, hC.NM, fun mu hmu => k1 mu (List.mem_range.2 hmu), fun h0 => ?_⟩
  rw [hC.mz]
  exact k2 (by rw [h0]; rfl)

/-- The shapes fit the matrices; each matrix has a row of cells; no matrix, no column. -/
def sizesB (tl : HTailF2) : Bool :=
  ((List.range tl.NM).all fun mu =>
    (tl.shp.getD mu {}).m == (tl.mats.getD mu {}).m &&
      (tl.shp.getD mu {}).k == (tl.mats.getD mu {}).k && decide (0 < (tl.mats.getD mu {}).m)) &&
    (tl.NM != 0 || tl.mz == 0)

/-- **At every record that is made so.** -/
theorem made_sizes {tlc : HTailF2} (M : Made tlc) : sizesB tlc = true := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  obtain ⟨p1, p2, p3, p4⟩ := shapeF_pos hs
  obtain ⟨hF, -, hE⟩ := OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine ha
  have eM : tl'.mats = tl.mats := by rw [hE]
  have eN : tl'.NM = tl.NM := by rw [hE]
  have eZ : tl'.mz = tl.mz := by rw [hE]
  have cS : tlc.shp = tl'.shp := congrArg (·.shp) hr
  have cM : tlc.mats = tl'.mats := congrArg (·.mats) hr
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  have cZ : tlc.mz = tl'.mz := congrArg (·.mz) hr
  unfold sizesB
  rw [cS, cM, cN, cZ]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨fun mu hmu => ⟨⟨(hF mu hmu).1, (hF mu hmu).2⟩, ?_⟩, ?_⟩
  · rw [eM, p1]
    exact p3 mu (by rw [← p2, ← eN]; exact hmu)
  · by_cases h0 : tl'.NM = 0
    · right
      rw [eZ]
      exact p4 (by rw [← p2, ← eN]; exact h0)
    · exact Or.inl h0

end P1K8

#print axioms P1K8.owners_sameL
#print axioms P1K8.ownerHeld_sameL
#print axioms P1K8.planG_made
#print axioms P1K8.planA_made
#print axioms P1K8.planH2_made
#print axioms P1K8.public_made
#print axioms P1K8.shapeF_pos
#print axioms P1K8.made_sizes
