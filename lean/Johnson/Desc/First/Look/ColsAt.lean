-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/ColsAt.lean: in the parameters of every approximate range proof (the
library's smallness test) in what `Verify.publicOf` returns, the matrices lie one behind the other:
`DgP.colsTest tl = true` (OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean). Statements and proofs.
NO SOUNDNESS IS CLAIMED.

Why. colsTest is the one public premise of kind K3's item on the digits. No test of the IOP as
written in Lean asks it; in the library it is a premise wherever it is used.

How. `HTailF2.shapeF` (OnBytes/Model/Tail.lean) lays off and mz in one loop over the matrices: "off
:= off.push mz; mz := mz + M.m". With sumM m j := the sum of the first j matrices' rows of cells,
the loop keeps: off has as many entries as matrices are passed; mz = sumM of that number; entry j of
off is sumM m j. colsTest's two clauses follow. The walk through the loop is that of
`Meaning.Plan.shapeF_gt` (Johnson/Goal/Meaning/PlanPort.lean). Behind shapeF no step of the three
planners writes off, mz, NM or mats: the walk is that of OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean
and of FoZMade.lean | FoZPublic.lean beneath it, with `SameC` in the place of `SameP`.

Main names (namespace Fo.ZPlan):
  `ColsP off mz NM mats`, `colsTest_iff`: colsTest's two clauses as a proposition on four fields.
  `SameC a b`: b has a's off, mz, NM and mats.
  `shapeF_cols`: what shapeF returns passes colsTest.
  `planG_cols`, `planA_cols`, `planH2_cols`: at the three planners' returns.
  **`public_cols`**: from Verify.publicOf pol KL layout = .ok X: at hp.tl for every member hp of
    X.G, at a.seam.tl for every member a of X.A, and at X.H.tl.
(namespace VerifiableInference.Desc.First.Look):
  `ColsAll X`: public_cols' conclusion, as a premise with a name.
  **`cols_at`**: under it: tlAt X i = some tl → DgP.colsTest tl = true, at every segment.

OBJECT: Verify.publicOf and the three planners beneath it (what they return).
USER: Johnson/Desc/First/Look/K3DigitsOfAt.lean, Johnson/P5J/K8OwnSizesAt.lean,
  Johnson/HB/LLHARD/Q38E/TiesAtHead.lean.
LETTERS: pol, KL, layout, X; i, tl.
Compiled with the whole library.



Limits. The parameters are the planners'. Nothing is said of the tl with which a run goes on.
Nor is it claimed that publicOf returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import OnBytes.Tie.Pv.Lookup.Digits.PortCols
import Johnson.Road.FormsKeysForest
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Tie.Pv.Tail.Port Fo.Pub
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open Fo.BatRows (bindE_ok ite_ok)

/-! ### the test as a proposition on four fields -/

/-- colsTest's two clauses. -/
def ColsP (off : Array Nat) (mz NM : Nat) (mats : Array TMat) : Prop :=
  (∀ mu < NM, off.getD mu 0 + (mats.getD mu {}).m =
    if mu + 1 < NM then off.getD (mu + 1) 0 else mz) ∧ off.getD 0 0 = 0

theorem colsTest_iff (tl : HTailF2) :
    DgP.colsTest tl = true ↔ ColsP tl.off tl.mz tl.NM tl.mats := by
  unfold DgP.colsTest
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact Iff.rfl

/-- b has the four fields of a that colsTest reads. -/
structure SameC (a b : HTailF2) : Prop where
  off : b.off = a.off
  mz : b.mz = a.mz
  NM : b.NM = a.NM
  mats : b.mats = a.mats

theorem SameC.refl (a : HTailF2) : SameC a a := ⟨rfl, rfl, rfl, rfl⟩

theorem SameC.trans {a b c : HTailF2} (h : SameC a b) (k : SameC b c) : SameC a c :=
  ⟨k.off.trans h.off, k.mz.trans h.mz, k.NM.trans h.NM, k.mats.trans h.mats⟩

theorem SameC.cols {a b : HTailF2} (k : SameC a b) (h : DgP.colsTest a = true) :
    DgP.colsTest b = true := by
  rw [colsTest_iff] at h ⊢
  rw [k.off, k.mz, k.NM, k.mats]
  exact h

/-! ### the loop of shapeF -/

/-- The rows of cells of the first j matrices. -/
def sumM (m : Array TMat) (j : Nat) : Nat := ((List.range j).map fun i => (m.getD i {}).m).sum

theorem sumM_zero (m : Array TMat) : sumM m 0 = 0 := rfl

theorem sumM_succ (m : Array TMat) (j : Nat) : sumM m (j + 1) = sumM m j + (m.getD j {}).m := by
  unfold sumM
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- In a cut of List.range n the member behind the front part is the front part's length. -/
theorem range_cut {n a : Nat} {pre rest : List Nat} (e : List.range n = pre ++ a :: rest) :
    a = pre.length := by
  have hl : pre.length < n := by
    have h := congrArg List.length e
    simp at h
    omega
  have h1 : (List.range n)[pre.length]? = some a := by
    rw [e]
    simp
  have h2 : (List.range n)[pre.length]? = some pre.length := by
    simp [hl]
  rw [h2] at h1
  exact (Option.some.inj h1).symm

theorem getD_push_lt (xs : Array Nat) (x j : Nat) (h : j < xs.size) :
    (xs.push x).getD j 0 = xs.getD j 0 := by
  have hne : j ≠ xs.size := Nat.ne_of_lt h
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hne]

theorem getD_push_eq (xs : Array Nat) (x : Nat) : (xs.push x).getD xs.size 0 = x := by
  simp [Array.getD_eq_getD_getElem?]

/-- From the loop's invariant at its end: the two clauses. -/
theorem colsP_of_sums {off : Array Nat} {mz : Nat} {m : Array TMat} (hs : off.size = m.size)
    (hz : mz = sumM m m.size) (ho : ∀ j < m.size, off.getD j 0 = sumM m j) :
    ColsP off mz m.size m := by
  refine ⟨fun mu hmu => ?_, ?_⟩
  · rw [ho mu hmu, ← sumM_succ]
    by_cases h1 : mu + 1 < m.size
    · rw [if_pos h1, ho _ h1]
    · rw [if_neg h1, hz]
      have e : mu + 1 = m.size := by omega
      rw [e]
  · by_cases h0 : 0 < m.size
    · rw [ho 0 h0]
      rfl
    · have e : off.size = 0 := by omega
      have e' : off = #[] := Array.eq_empty_of_size_eq_zero e
      rw [e']
      rfl

/-- The maker of the two calls leaves the four fields. -/
theorem piecesF_sameC {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') : SameC tl tl' := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨f9, _, h⟩ := bindX h
  obtain ⟨pub, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **What shapeF returns passes colsTest.** -/
theorem shapeF_cols {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') : DgP.colsTest tl' = true := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r1, h1, h⟩ := ok_of_bind h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨r2, h2, h⟩ := ok_of_bind h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := ok_of_bind h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  refine (piecesF_sameC h).cols ((colsTest_iff _).2 ?_)
  clear h h2 h1
  have K3 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      s.2.2.2.2.1.size = pre.length ∧ s.2.1 = sumM m pre.length ∧
        ∀ j < pre.length, s.2.2.2.2.1.getD j 0 = sumM m j)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      obtain ⟨i1, i2, i3⟩ : off'.size = pre.length ∧ mz' = sumM m pre.length ∧
        ∀ j < pre.length, off'.getD j 0 = sumM m j := hI
      have ha : a = pre.length := range_cut e
      have keep : (off'.push mz').size = (pre ++ [a]).length ∧
          mz' + (m.getD a {}).m = sumM m (pre ++ [a]).length ∧
          ∀ j < (pre ++ [a]).length, (off'.push mz').getD j 0 = sumM m j := by
        have hl : (pre ++ [a]).length = pre.length + 1 := by simp
        rw [hl]
        refine ⟨by simp [i1], ?_, fun j hj => ?_⟩
        · rw [sumM_succ, ← ha, i2, ha]
        · by_cases hlt : j < pre.length
          · rw [getD_push_lt off' mz' j (by omega)]
            exact i3 j hlt
          · have ej : j = off'.size := by omega
            rw [ej, getD_push_eq, i2, i1]
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
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
    (List.range m.size) [] _ _ rfl ⟨rfl, rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩ h3
  obtain ⟨k1, k2, k3⟩ : off.size = (List.range m.size).length ∧
      mz = sumM m (List.range m.size).length ∧
      ∀ j < (List.range m.size).length, off.getD j 0 = sumM m j := K3
  rw [List.length_range] at k1 k2 k3
  exact colsP_of_sums k1 k2 k3

/-! ### the plans' later steps -/

theorem addTreesF_sameC {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    SameC tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ownerIs_sameC (tl : HTailF2) (no : Nat) : SameC tl (tl.ownerIs no) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem borderMeans_sameC {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : SameC tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem ownerHeld_sameC {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameC tl tl' := by
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
    exact borderMeans_sameC hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- Behind shapeF and addTreesF, and whatever leaves the four fields. -/
theorem cols_made {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    {tlc : HTailF2} (hr : SameC tl' tlc) : DgP.colsTest tlc = true :=
  ((addTreesF_sameC ha).trans hr).cols (shapeF_cols hs)

/-! ### the three plans -/

theorem planG_cols (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : DgP.colsTest hp.tl = true := by
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
    exact cols_made hS hA (ownerIs_sameC tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact cols_made hS hA ((ownerIs_sameC tl1 g).trans (borderMeans_sameC hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_cols (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    DgP.colsTest P.seam.tl = true := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hasU, hS⟩ := seamShape_cut h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact cols_made hS hA (SameC.refl _)

theorem planH2_cols (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : DgP.colsTest hp.tl = true := by
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
    exact cols_made hS hA (ownerHeld_sameC hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ### the owners' loop over the attention plans -/

theorem ownerPlace_sameC {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : SameC X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_sameC h1

/-- What the loop keeps. -/
def SameCKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s →
    ∃ s0, A[i]? = some s0 ∧ SameC s0.tl s.tl

theorem ownerPlaces_sameC (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), SameCKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → SameCKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_sameC G A l out1 r ?_ h
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
        exact ⟨s0, e0, a0.trans (ownerPlace_sameC h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_sameC {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : SameCKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_sameC G A _ A r (fun i s hi => ⟨s, hi, SameC.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, SameC.refl _⟩

/-! ### the members of X -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_cols (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : DgP.colsTest hp.tl = true :=
  planG_cols X.layers g _ hp (public_G h g hp hg)

theorem public_H_cols (h : Verify.publicOf pol KL layout = .ok X) :
    DgP.colsTest X.H.tl = true := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_cols _ _ _ _ _ _ _ H0 h0

theorem public_A_cols (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : DgP.colsTest a.seam.tl = true := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameC k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show DgP.colsTest s.tl = true
    rw [f3] at f2
    exact f2.cols (planA_cols _ _ _ a0 m2)
  · simp at e1

/-- **In the parameters of every approximate range proof in what publicOf returns the matrices lie
one behind the other.** -/
theorem public_cols (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → DgP.colsTest hp.tl = true) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → DgP.colsTest a.seam.tl = true) ∧
    DgP.colsTest X.H.tl = true :=
  ⟨public_G_cols h, public_A_cols h, public_H_cols h⟩

end

end Fo.ZPlan

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- colsTest at the parameters of every approximate range proof in the public parameters. -/
def ColsAll (X : Verify.Public) : Prop :=
  (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → DgP.colsTest hp.tl = true) ∧
  (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → DgP.colsTest a.seam.tl = true) ∧
  DgP.colsTest X.H.tl = true

/-- It holds at whatever publicOf returns. -/
theorem colsAll_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : ColsAll X :=
  _root_.Fo.ZPlan.public_cols h

/-- **At every segment: what tlAt returns passes colsTest.** -/
theorem cols_at {X : Verify.Public} (Z : ColsAll X) {i : ℕ} {tl : HTailF2}
    (h : tlAt X i = some tl) : DgP.colsTest tl = true := by
  unfold tlAt at h
  cases hH : (i == (if X.p4 then 2 else 1) * X.NGr) with
  | true =>
    simp only [hH, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    exact Z.2.2
  | false =>
    cases hE : (i % (if X.p4 then 2 else 1) == 0) with
    | true =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.1 _ hp hg
    | false =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨a, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.2.1 _ a hg

end VerifiableInference.Desc.First.Look

#print axioms Fo.ZPlan.shapeF_cols
#print axioms Fo.ZPlan.public_cols
#print axioms VerifiableInference.Desc.First.Look.cols_at
