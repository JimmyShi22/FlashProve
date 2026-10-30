-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean: the arrays ZZ and BZ in the state that the routine which
lays the arrays leaves.

HTailF2.addTreesF adds the arrays of a sub-proof's smallness test to the state's list, each behind
the last: among them ZZ, with tau rows and 2 * zzBlocks + 2 virtual rows, and BZ, with 32 rows and 3
virtual rows. It refuses unless each array gets the number that the record tl holds for it.

 - Ext F G: G's list of arrays begins with F's.
 - t2AddN_ok: one array is pushed; its number is the list's old length; it has the rows and virtual
   rows asked for. t2AddP_ok says less: the list that t2AddP leaves begins with the old one (Ext).
 - addTreesF_rows: if addTreesF returns (tl', G, T'): tl' has tl's numbers of arrays, blocks, pieces
   and matrices; G has ZZ's virtual rows below 2 * zzBlocks + 2 and BZ's virtual rows 0, 1, 2; BZ
   has 32 rows.
 - SameRec tl tl': two records agree in what CoefOK reads: the arrays' numbers, the blocks, the two
   calls with their pieces, the matrices' arrays and number. CoefOK.of_same.
 - coefOK_behind: from the success of shapeF and of addTreesF, run on the record that shapeF
   returns: CoefOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean) at every record tlc with SameRec
   from the record that addTreesF returns, in every state Fc with Frame
   (OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean) from the state that addTreesF leaves.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that SameRec and Frame hold from what addTreesF returns to the record and the
state on which coefficientsF is run.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeF

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

private theorem ok_bind2 {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ok_jp2 {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

private theorem forIn_keeps2 {α σ : Type} (f : α → σ → Except String (ForInStep σ))
    (I : σ → Prop)
    (step : ∀ a s s', I s → f a s = .ok s' → ∃ t, s' = .yield t ∧ I t) :
    ∀ (l : List α) (s r : σ), I s → forIn l s f = .ok r → I r
  | [], s, r, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [← hr]
    exact hI
  | a :: l, s, r, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := ok_bind2 h
    obtain ⟨t, rfl, hI'⟩ := step a s s' hI hs
    exact forIn_keeps2 f I step l t r hI' h

/-- G's list of arrays begins with F's. -/
def Ext (F G : Fork) : Prop :=
  F.trees.size ≤ G.trees.size ∧ ∀ t < F.trees.size, G.trees.getD t {} = F.trees.getD t {}

theorem Ext.refl (F : Fork) : Ext F F := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {F G H : Fork} (h1 : Ext F G) (h2 : Ext G H) : Ext F H :=
  ⟨Nat.le_trans h1.1 h2.1, fun t ht =>
    (h2.2 t (Nat.lt_of_lt_of_le ht h1.1)).trans (h1.2 t ht)⟩

theorem ext_push (F : Fork) (X : HTree) : Ext F { F with trees := F.trees.push X } := by
  refine ⟨by simp, fun t ht => ?_⟩
  simp [Array.getD, Array.getElem_push, ht, Nat.lt_succ_of_lt ht]

theorem getD_push_last (F : Fork) (X : HTree) :
    (F.trees.push X).getD F.trees.size {} = X := by
  simp [Array.getD]

theorem t2AddN_ok {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    got = F.trees.size ∧ Ext F F' ∧ F'.trees.size = F.trees.size + 1 ∧
      (F'.trees.getD got {}).R = R ∧ (F'.trees.getD got {}).rows.size = nv := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e1 e2
    refine ⟨rfl, ext_push F _, by simp, ?_, ?_⟩
    · show ((F.trees.push _).getD F.trees.size {}).R = R
      rw [getD_push_last]
    · show ((F.trees.push _).getD F.trees.size {}).rows.size = nv
      rw [getD_push_last]
      simp

theorem t2AddP_ok {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) : Ext F F' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨e2, _⟩ := Prod.mk.inj e2
      subst e2
      exact ext_push F _

/-- The arrays ZZ and BZ behind the routine that lays the arrays. -/
theorem addTreesF_rows {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (tl'.ix = tl.ix ∧ tl'.blocks = tl.blocks ∧ tl'.z1 = tl.z1 ∧ tl'.z2 = tl.z2 ∧
      tl'.gtTree = tl.gtTree ∧ tl'.NM = tl.NM) ∧
    (∀ i < 2 * tl.zzBlocks + 2, HasRow G tl.ix.ZZ i) ∧
    (∀ i < 3, HasRow G tl.ix.BZ i) ∧ (G.trees.getD tl.ix.BZ {}).R = 32 := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_jp2 h
  obtain ⟨_, h⟩ := ok_jp2 h
  obtain ⟨_, h⟩ := ok_jp2 h
  obtain ⟨_, h⟩ := ok_jp2 h
  obtain ⟨⟨F1, T1⟩, _, h⟩ := ok_bind2 h
  obtain ⟨⟨F2, T2⟩, _, h⟩ := ok_bind2 h
  obtain ⟨⟨F3, T3⟩, _, h⟩ := ok_bind2 h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_bind2 h
  obtain ⟨gZ, h⟩ := ok_jp2 h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_bind2 h
  obtain ⟨gB, h⟩ := ok_jp2 h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_bind2 h
  obtain ⟨_, h⟩ := ok_jp2 h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e1 e2
  have K4 : Ext FB F4 := forIn_keeps2 _ (fun s : MProd Fork Tail2 => Ext FB s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_bind2 hs
      obtain ⟨_, hs⟩ := ok_jp2 hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl FB) h4
  obtain ⟨z1, z2, z3, z4, z5⟩ := t2AddN_ok hZ
  obtain ⟨b1, b2, b3, b4, b5⟩ := t2AddN_ok hB
  have gZ' : gotZ = tl.ix.ZZ := by simpa using gZ
  have gB' : gotB = tl.ix.BZ := by simpa using gB
  subst gZ' gB'
  have lZ : tl.ix.ZZ < FZ.trees.size := by omega
  have lB : tl.ix.BZ < FB.trees.size := by omega
  have tZ : F4.trees.getD tl.ix.ZZ {} = FZ.trees.getD tl.ix.ZZ {} :=
    (K4.2 _ (Nat.lt_of_lt_of_le lZ b2.1)).trans (b2.2 _ lZ)
  have tB : F4.trees.getD tl.ix.BZ {} = FB.trees.getD tl.ix.BZ {} := K4.2 _ lB
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun i hi => ⟨?_, ?_⟩, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le lZ b2.1) K4.1
  · rw [tZ, z5]
    exact hi
  · exact Nat.lt_of_lt_of_le lB K4.1
  · rw [tB, b5]
    exact hi
  · rw [tB, b4]

/-- Two records of the smallness test agree in what CoefOK reads. -/
structure SameRec (tl tl' : HTailF2) : Prop where
  ix : tl'.ix = tl.ix
  blocks : tl'.blocks = tl.blocks
  z1 : tl'.z1 = tl.z1
  z2 : tl'.z2 = tl.z2
  gtTree : tl'.gtTree = tl.gtTree
  NM : tl'.NM = tl.NM

theorem SameRec.refl (tl : HTailF2) : SameRec tl tl := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameRec.trans {a b c : HTailF2} (h1 : SameRec a b) (h2 : SameRec b c) : SameRec a c :=
  ⟨h2.ix.trans h1.ix, h2.blocks.trans h1.blocks, h2.z1.trans h1.z1, h2.z2.trans h1.z2,
    h2.gtTree.trans h1.gtTree, h2.NM.trans h1.NM⟩

theorem CoefOK.of_same {tl tl' : HTailF2} {Fc : Fork} (T : CoefOK tl Fc) (h : SameRec tl tl') :
    CoefOK tl' Fc := by
  have hp : allPieces tl' = allPieces tl := by
    unfold allPieces HTailF2.zOf
    rw [h.z1, h.z2]
  have hr : tl'.zzRowReads = tl.zzRowReads := by
    unfold HTailF2.zzRowReads HTailF2.zzBlocks
    rw [h.blocks]
  have ht : tl'.zzRowTies = tl.zzRowTies := by
    unfold HTailF2.zzRowTies HTailF2.zzBlocks
    rw [h.blocks]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.ix]; exact T.bz
  · rw [h.ix]; exact T.bzR
  · rw [h.ix, h.gtTree, h.NM]; exact T.mats
  · rw [hp]; exact T.apart
  · rw [hp, hr, ht, h.ix, h.gtTree, h.NM]; exact T.piece

/-- CoefOK at every record that agrees with the one that addTreesF returns in what CoefOK reads, in
every state with as many arrays, rows and virtual rows (Frame) as the one that addTreesF leaves. -/
theorem coefOK_behind {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (hs : tl₀.shapeF m txOf f hasU tau = .ok tl) {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (hr : SameRec tl' tlc) (Fc : Fork) (hF : Frame G Fc) : CoefOK tlc Fc := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, r1, r2, r3⟩ := addTreesF_rows ha
  have T0 : CoefOK tl Fc := coefOK_of_shape hs Fc ((hF.2 _).1.trans r3)
    ⟨hF.hasRow (r2 0 (by omega)), hF.hasRow (r2 1 (by omega)), hF.hasRow (r2 2 (by omega))⟩
    fun i hi => hF.hasRow (r1 i (by omega))
  exact T0.of_same ((⟨a1, a2, a3, a4, a5, a6⟩ : SameRec tl tl').trans hr)

end Fo
