-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OwnLaid.lean: WHICH ARRAY OF A SUB-PROOF's LIST BEARS WHICH OF ITS OWN MATRICES, AND
WITH WHICH ROWS AND COLUMNS: from the success of the two library routines that lay them:
HTailF2.shapeF and HTailF2.addTreesF (OnBytes/Model/Tail.lean). General: no scope, no plan.
Statements and proofs.

  piecesF_own       shapeF's last act keeps pkMat and pxMat
  shapeF_own        (G1) what shapeF returns: the list of matrices and its length; every matrix of kind 0 stands in pkMat or in pxMat; ix.PK and ix.TX have the sizes of pkMat and pxMat
  t2AddP_at         the array that t2AddP adds: its number, its rows ((m + 2) / 3) and its columns (k)
  Sym G t M         array number t of G is there with the rows and columns of the matrix M's symbols · Sym.keep
  addTreesF_sym     (G2) behind addTreesF: at every i below pkMat's size the array ix.PK[i] has the rows and columns of matrix pkMat[i]; the like at ix.TX and pxMat
  OwnLaid tl Fp     every matrix of kind 0 of tl's list has an array of Fp, at one index of (ix.PK, pkMat) or of (ix.TX, pxMat), with its rows and columns
  ownLaid_made      shapeF, then addTreesF on what it returned: OwnLaid

The walks are those of the library's shapeF_ix (OnBytes/Tie/Pv/Lookup/Ends/FoShapeF.lean) and of our addTreesF_u3 (Johnson/Goal/Meaning/PlanPort.lean).
What is not claimed. That either routine returns anywhere. Nothing on a matrix of kind 1. No soundness.

-/
import Johnson.Goal.Meaning.PlanPort
import OnBytes.Model.Fit.ShapeFCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM.Own

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- shapeF's last act keeps the two lists of own matrices. -/
theorem piecesF_own {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    tl'.pkMat = tl.pkMat ∧ tl'.pxMat = tl.pxMat := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨f9, _, h⟩ := ok_of_bind h
  obtain ⟨pub, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- **(G1) What shapeF says of the sub-proof's own matrices.** -/
theorem shapeF_own {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.mats = m ∧ tl'.NM = m.size ∧ tl'.ix.PK.size = tl'.pkMat.size ∧
      tl'.ix.TX.size = tl'.pxMat.size ∧
      ∀ mu < m.size, (m.getD mu {}).kind = 0 →
        mu ∈ tl'.pkMat.toList ∨ mu ∈ tl'.pxMat.toList := by
  have hm := (shapeF_caps h).1
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
  obtain ⟨e1, -, e3, -⟩ := Fo.piecesF_keys h
  obtain ⟨p1, p2⟩ := piecesF_own h
  refine ⟨hm, e3, ?_, ?_, ?_⟩
  · rw [e1, p1]
    simp
  · rw [e1, p2]
    simp
  rw [p1, p2]
  clear h e1 e3 p1 p2 h2 h3 hm
  have K1 := forIn_keeps _ (List.range m.size)
    (fun pre (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) =>
      ∀ mu ∈ pre, ((m.getD mu {}).kind == 0) = true →
        mu ∈ s.2.1.toList ∨ mu ∈ s.2.2.toList)
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨k, pk, px⟩ := s
      dsimp only at hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i i hi
          obtain ⟨_, hs⟩ := ok_of_jp hs
          refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
          rcases List.mem_append.1 hmu with hm | hm
          · rcases hI mu hm hkm with q | q
            · exact Or.inl q
            · exact Or.inr (by simp [q])
          · have : mu = a := by simpa using hm
            subst this
            exact Or.inr (by simp)
        · rename_i hi
          refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
          rcases List.mem_append.1 hmu with hm | hm
          · rcases hI mu hm hkm with q | q
            · exact Or.inl (by simp [q])
            · exact Or.inr q
          · have : mu = a := by simpa using hm
            subst this
            exact Or.inl (by simp)
      · rename_i hk
        refine ⟨_, (Except.ok.inj hs).symm, fun mu hmu hkm => ?_⟩
        rcases List.mem_append.1 hmu with hm | hm
        · exact hI mu hm hkm
        · have : mu = a := by simpa using hm
          subst this
          exact absurd hkm hk)
    (List.range m.size) [] _ _ rfl (fun _ h => by cases h) h1
  intro mu hmu hk
  exact K1 mu (List.mem_range.2 hmu) (by rw [hk]; rfl)

/-- The array that t2AddP adds. -/
theorem t2AddP_at {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) :
    got = F.trees.size ∧ F'.trees.size = F.trees.size + 1 ∧
      (F'.trees.getD got {}).R = (m + 2) / 3 ∧ (F'.trees.getD got {}).K = k := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      obtain ⟨e2, _⟩ := Prod.mk.inj e2
      subst e1 e2
      refine ⟨rfl, by simp, ?_, ?_⟩
      · show ((F.trees.push _).getD F.trees.size {}).R = _
        rw [getD_push_last]
        rfl
      · show ((F.trees.push _).getD F.trees.size {}).K = _
        rw [getD_push_last]
        rfl

/-- Array number t of G is there, with the rows and columns of the matrix M's symbols. -/
def Sym (G : Fork) (t : Nat) (M : TMat) : Prop :=
  t < G.trees.size ∧ (G.trees.getD t {}).R = (M.m + 2) / 3 ∧ (G.trees.getD t {}).K = M.k

theorem Sym.keep {F G : Fork} (h : Ext F G) {t : Nat} {M : TMat} (k : Sym F t M) : Sym G t M :=
  ⟨Nat.lt_of_lt_of_le k.1 h.1, by rw [h.2 t k.1]; exact k.2.1, by rw [h.2 t k.1]; exact k.2.2⟩

/-- **(G2) Behind addTreesF each own matrix's array has the rows and columns of its symbols.** -/
theorem addTreesF_sym {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (∀ i < tl.pkMat.size, ∃ t, tl.ix.PK[i]? = some t ∧
      Sym G t (tl.mats.getD (tl.pkMat.getD i 0) {})) ∧
    (∀ i < tl.pxMat.size, ∃ t, tl.ix.TX[i]? = some t ∧
      Sym G t (tl.mats.getD (tl.pxMat.getD i 0) {})) := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨-, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, -⟩ := Prod.mk.inj e2
  subst e2
  have K2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun pre (s : MProd Fork Tail2) => ∀ i ∈ pre, ∃ t, tl.ix.PK[i]? = some t ∧
      Sym s.1 t (tl.mats.getD (tl.pkMat.getD i 0) {}))
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨hg, hs⟩ := ok_of_jp hs
      refine ⟨_, (Except.ok.inj hs).symm, fun i hi => ?_⟩
      obtain ⟨g1, g2, g3, g4⟩ := t2AddP_at hP
      rcases List.mem_append.1 hi with hi | hi
      · obtain ⟨t, et, S⟩ := hI i hi
        exact ⟨t, et, S.keep (t2AddP_ok hP)⟩
      · have : i = a := by simpa using hi
        subst this
        have eg : some got = tl.ix.PK[i]? := by simpa using hg
        exact ⟨got, eg.symm, by show got < F'.trees.size; omega, g3, g4⟩)
    (List.range tl.pkMat.size) [] _ _ rfl (fun _ h => by cases h) h2
  have K3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun pre (s : MProd Fork Tail2) => Ext F2 s.1 ∧ ∀ i ∈ pre, ∃ t, tl.ix.TX[i]? = some t ∧
      Sym s.1 t (tl.mats.getD (tl.pxMat.getD i 0) {}))
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨hg, hs⟩ := ok_of_jp hs
      refine ⟨_, (Except.ok.inj hs).symm, hI.1.trans (t2AddP_ok hP), fun i hi => ?_⟩
      obtain ⟨g1, g2, g3, g4⟩ := t2AddP_at hP
      rcases List.mem_append.1 hi with hi | hi
      · obtain ⟨t, et, S⟩ := hI.2 i hi
        exact ⟨t, et, S.keep (t2AddP_ok hP)⟩
      · have : i = a := by simpa using hi
        subst this
        have eg : some got = tl.ix.TX[i]? := by simpa using hg
        exact ⟨got, eg.symm, by show got < F'.trees.size; omega, g3, g4⟩)
    (List.range tl.pxMat.size) [] _ _ rfl ⟨Ext.refl F2, fun _ h => by cases h⟩ h3
  have E4 : Ext FB F4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => Ext FB s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    (List.range tl.ft.size) [] _ _ rfl (Ext.refl FB) h4
  have E34 : Ext F3 F4 := ((t2AddN_ok hZ).2.1.trans (t2AddN_ok hB).2.1).trans E4
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨t, et, S⟩ := K2 i (List.mem_range.2 hi)
    exact ⟨t, et, S.keep (K3.1.trans E34)⟩
  · obtain ⟨t, et, S⟩ := K3.2 i (List.mem_range.2 hi)
    exact ⟨t, et, S.keep E34⟩

/-- What addTreesF leaves of the record's fields that speak of the own matrices. -/
theorem addTreesF_own {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    tl'.mats = tl.mats ∧ tl'.NM = tl.NM ∧ tl'.pkMat = tl.pkMat ∧ tl'.pxMat = tl.pxMat ∧
      tl'.ix = tl.ix := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  subst e1
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Every matrix of kind 0 of tl's list has an array of Fp, at one index of (ix.PK, pkMat) or of
(ix.TX, pxMat), with the rows and columns of its symbols.** -/
def OwnLaid (tl : HTailF2) (Fp : Fork) : Prop :=
  ∀ mu < tl.NM, (tl.mats.getD mu {}).kind = 0 → ∃ i t : Nat,
    ((tl.pkMat[i]? = some mu ∧ tl.ix.PK[i]? = some t) ∨
      (tl.pxMat[i]? = some mu ∧ tl.ix.TX[i]? = some t)) ∧ Sym Fp t (tl.mats.getD mu {})

/-- **shapeF, then addTreesF on what it returned: OwnLaid.** -/
theorem ownLaid_made {tl0 tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat} {F G : Fork} {T T' : Tail2}
    {nU aTX : Array Nat} {hb hbLine : Nat} (hs : tl0.shapeF m txOf f hasU tau = .ok tl)
    (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) : OwnLaid tl' G := by
  obtain ⟨s1, s2, -, -, s5⟩ := shapeF_own hs
  obtain ⟨a1, a2, a3, a4, a5⟩ := addTreesF_own ha
  obtain ⟨k, x⟩ := addTreesF_sym ha
  intro mu hmu hk
  rw [a1, a3, a4, a5]
  rw [a2, s2] at hmu
  rw [a1, s1] at hk
  rcases s5 mu hmu hk with q | q
  · obtain ⟨i, hi, e⟩ := List.getElem_of_mem q
    have hi' : i < tl.pkMat.size := by simpa using hi
    obtain ⟨t, et, S⟩ := k i hi'
    have eg : tl.pkMat.getD i 0 = mu := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
      simpa using e
    rw [eg] at S
    refine ⟨i, t, Or.inl ⟨?_, et⟩, S⟩
    rw [Array.getElem?_eq_getElem hi']
    simpa using e
  · obtain ⟨i, hi, e⟩ := List.getElem_of_mem q
    have hi' : i < tl.pxMat.size := by simpa using hi
    obtain ⟨t, et, S⟩ := x i hi'
    have eg : tl.pxMat.getD i 0 = mu := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
      simpa using e
    rw [eg] at S
    refine ⟨i, t, Or.inr ⟨?_, et⟩, S⟩
    rw [Array.getElem?_eq_getElem hi']
    simpa using e

end IM.Own

#print axioms IM.Own.shapeF_own
#print axioms IM.Own.addTreesF_sym
#print axioms IM.Own.ownLaid_made
