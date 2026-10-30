-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsArray.lean: the array of reads in the head's planned ledger has one row,
and as many columns as the plan's vector of reads is long, in every public part that the verifier's
function publicOf returns.

What the file holds.
  addTreesF_third  behind the routine that lays a smallness test's arrays (HTailF2.addTreesF): the
                   array under the number that the record holds for its third vector, U3, is there,
                   with nU[2] columns and one row.
  planH2_array     so in what the head's planner returns: array 0 of its ledger Fp is there, with
                   nU[2] columns and one row; and nU[2] is the planner's readsLength.
  public_array     **publicOf pol KL layout = .ok X gives: 0 < X.H.Fp.trees.size; array 0 has
                   X.H.nU.getD 2 0 columns and one row.**
Why. The head's seat names an entry of a read by its place pos in that vector, as row pos / K and
column pos % K of the array. With one row, the entry is in the array just if pos < K.

A RELATED LEMMA. Johnson/Goal/Meaning/PlanPort.lean (Meaning.Plan.addTreesF_u3) shows the first two
clauses of addTreesF_third: the array is there, with nU[2] columns;
and carries them to the LAYERS' plans (planG_K3, public_G_K3).
What is added here: the third clause, one row,
which wants the same walk of the routine;
and the HEAD's plan.

On what it rests. OnBytes/Tie/Pv/Lookup/Ends/FoLayCols.lean shows the like for the arrays ZZ and BZ
(addTreesF_cols); the walk of the routine here is that proof's, with the first loop's three turns
taken one by one. Ext, t2AddN_ok, t2AddP_ok: OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean. That the
number is 0: Johnson/Desc/Kinds/Law/ReadsNamed.lean. That publicOf trims the ledger without turning
an array's rows or columns is read off Fork.trimL's text here (trim_same).

What it does not give. Nothing on soundness. It speaks of the PLANNED ledger: that a run's later
ledgers keep the array's rows and columns is not shown here. Nothing on where each named table of
reads ends. That publicOf returns is a premise.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLayCols
import Johnson.Desc.Kinds.Law.ReadsNamed

set_option autoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.ReadsArray

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok)

theorem addTreesF_third {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine k : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (hU : tl.ix.U.getD 2 none = some k) :
    k < G.trees.size ∧ (G.trees.getD k {}).K = nU.getD 2 0 ∧ (G.trees.getD k {}).R = 1 := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := bindX h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := bindX h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := bindX h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e1 e2
  -- the first loop: three turns
  rw [show List.range 3 = [0, 1, 2] from rfl, List.forIn_cons] at h1
  obtain ⟨s0, hs0, h1⟩ := bindX h1
  have Y0 : ∃ t0, s0 = ForInStep.yield t0 := by
    split at hs0
    · obtain ⟨⟨got, F', T''⟩, _, hs0⟩ := bindX hs0
      obtain ⟨_, hs0⟩ := jpX hs0
      exact ⟨_, (Except.ok.inj hs0).symm⟩
    · exact ⟨_, (Except.ok.inj hs0).symm⟩
  obtain ⟨t0, rfl⟩ := Y0
  replace h1 : forIn [1, 2] t0 _ = Except.ok (⟨F1, T1⟩ : MProd Fork Tail2) := h1
  rw [List.forIn_cons] at h1
  obtain ⟨s1, hs1, h1⟩ := bindX h1
  have Y1 : ∃ t1, s1 = ForInStep.yield t1 := by
    split at hs1
    · obtain ⟨⟨got, F', T''⟩, _, hs1⟩ := bindX hs1
      obtain ⟨_, hs1⟩ := jpX hs1
      exact ⟨_, (Except.ok.inj hs1).symm⟩
    · exact ⟨_, (Except.ok.inj hs1).symm⟩
  obtain ⟨t1, rfl⟩ := Y1
  replace h1 : forIn [2] t1 _ = Except.ok (⟨F1, T1⟩ : MProd Fork Tail2) := h1
  rw [List.forIn_cons] at h1
  obtain ⟨s2, hs2, h1⟩ := bindX h1
  have Y2 : ∃ t2 : MProd Fork Tail2, s2 = ForInStep.yield t2 ∧ k < t2.1.trees.size ∧
      (t2.1.trees.getD k {}).K = nU.getD 2 0 ∧ (t2.1.trees.getD k {}).R = 1 := by
    split at hs2
    · rename_i want heq
      rw [hU] at heq
      obtain rfl := Option.some.inj heq
      obtain ⟨⟨got, F', T''⟩, hP, hsb⟩ := bindX hs2
      obtain ⟨hg, hsc⟩ := jpX hsb
      have hg' : got = k := by simpa using hg
      obtain ⟨a1, a2, a3, a4, a5⟩ := t2AddN_ok hP
      have hK := t2AddN_K hP
      rw [hg'] at a4 hK
      refine ⟨⟨F', T''⟩, (Except.ok.inj hsc).symm, ?_, hK, a4⟩
      show k < F'.trees.size
      omega
    · rename_i hx
      exact absurd hU (hx k)
  obtain ⟨t2, rfl, p1, p2, p3⟩ := Y2
  replace h1 : forIn [] t2 _ = Except.ok (⟨F1, T1⟩ : MProd Fork Tail2) := h1
  rw [List.forIn_nil] at h1
  obtain rfl : t2 = ⟨F1, T1⟩ := Except.ok.inj h1
  -- what follows pushes arrays behind
  have K2 : Ext F1 F2 := forInX _ (fun s : MProd Fork Tail2 => Ext F1 s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl F1) h2
  have K3 : Ext F2 F3 := forInX _ (fun s : MProd Fork Tail2 => Ext F2 s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl F2) h3
  have K4 : Ext FB F4 := forInX _ (fun s : MProd Fork Tail2 => Ext FB s.1)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindX hs
      obtain ⟨_, hs⟩ := jpX hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩)
    _ _ _ (Ext.refl FB) h4
  have KA : Ext F1 F4 :=
    ((((K2.trans K3).trans (t2AddN_ok hZ).2.1).trans (t2AddN_ok hB).2.1).trans K4)
  refine ⟨Nat.lt_of_lt_of_le p1 KA.1, ?_, ?_⟩
  · rw [KA.2 k p1]; exact p2
  · rw [KA.2 k p1]; exact p3

/-- The trimming turns no array's number of rows or of columns, nor the number of arrays. -/
theorem trim_same (F : Fork) (t : Nat) :
    F.trimL.trees.size = F.trees.size ∧ (F.trimL.trees.getD t {}).K = (F.trees.getD t {}).K ∧
      (F.trimL.trees.getD t {}).R = (F.trees.getD t {}).R := by
  unfold Fork.trimL
  refine ⟨by simp, ?_, ?_⟩ <;>
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases F.trees[t]? with
    | none => rfl
    | some X => rfl

theorem planH2_array (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    0 < hp.Fp.trees.size ∧ (hp.Fp.trees.getD 0 {}).K = hp.nU.getD 2 0 ∧
      (hp.Fp.trees.getD 0 {}).R = 1 ∧ hp.nU.getD 2 0 = Head.readsLength h L b := by
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
    obtain ⟨a1, a2, a3⟩ := addTreesF_third hA (ReadsNamed.shapeF_third hS)
    exact ⟨a1, a2, a3, rfl⟩
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **The array of reads in the public part's planned ledger.** -/
theorem public_array (h : Verify.publicOf pol KL layout = .ok X) :
    0 < X.H.Fp.trees.size ∧ (X.H.Fp.trees.getD 0 {}).K = X.H.nU.getD 2 0 ∧
      (X.H.Fp.trees.getD 0 {}).R = 1 ∧
      X.H.nU.getD 2 0 = Head.readsLength X.hS X.HLy (Verify.borderOf X.layers.y) := by
  obtain ⟨H0, h0, e⟩ := public_H h
  obtain ⟨a1, a2, a3, a4⟩ := planH2_array _ _ _ _ _ _ _ H0 h0
  obtain ⟨t1, t2, t3⟩ := trim_same H0.Fp 0
  rw [e]
  exact ⟨by show 0 < H0.Fp.trimL.trees.size; rw [t1]; exact a1,
    by show (H0.Fp.trimL.trees.getD 0 {}).K = H0.nU.getD 2 0; rw [t2]; exact a2,
    by show (H0.Fp.trimL.trees.getD 0 {}).R = 1; rw [t3]; exact a3, a4⟩

end VerifiableInference.Desc.Kinds.Head.Law.ReadsArray

#print axioms VerifiableInference.Desc.Kinds.Head.Law.ReadsArray.addTreesF_third
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ReadsArray.planH2_array
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ReadsArray.public_array
