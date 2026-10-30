-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontThin.lean

What it is. A second text of five declarations that stand in FrontPlainB.lean (thin_batT) and
FrontPubB.lean (core_spent, core_withGroup, frontPubB, frontPub_of_B) in this folder: the code to
the sign, in another namespace; frontPubB's docstring is worded anew. Why: these two files import
OneFitsB.lean and JobOne.lean, which are on a job of one sending and on that sending's coins; the
five declarations use nothing of these.
Here the five import ShapeAll.lean and one other file.

What it proves. The clause pub of FrontAsks (ShapeAll.lean) follows from one test with code on the
thin shape of the verifier's state in front (frontPubB). The clause speaks of the statement with the
group's test begun, the fresh table spent as a mask and the next stage's group added; the shape of
that statement is what three functions on shapes return (batThin, spendS, newGroupS).

Names.
  thin_batT   the thin shape of the state with the group's test begun is what batThin returns.
  core_spent, core_withGroup   where spendS and newGroupS return at a statement's shape, they return
      the shape of the statement written out.
  frontPubB   the test.
  frontPub_of_B   the test is true at the state's thin shape: then the clause pub holds.

Limits. That the test is true is shown at no parameters here. The case in which the first fold's
fresh table has come earlier, alone. Nothing on values. Steps of the verifier's: nothing is shown of
any prover. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll
import Johnson.Desc.K12.Honest.Shape.TestCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Thin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.Sh (ThinSh thinSh batThin readPubB)

/-- **The thin shape of the state with the group's test begun.** -/
theorem thin_batT (p : P12) (t : T12) (G : Group) (row : GroupRow) (aB : ThinSh)
    (hp : t.pass = .nothing) (he : p.early = true) (hG : t.st.groups[t.g]? = some G)
    (h : batThin p (thinSh t) = some aB) : thinSh (batT t G row) = aB := by
  unfold batThin at h
  have e0 : (thinSh t).pass = .nothing := by
    show ProofFile.Honest.Sh.thinPass t.pass = _
    rw [hp]
    rfl
  rw [e0] at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    have hy' : beginRunS (shD (H2K.Out.dT t [])) t.g = some y := hy
    obtain ⟨x, hx⟩ := beginRun_returns (H2K.Out.dT t []) t.g y hy'
    have c := beginRun_carries (H2K.Out.dT t []) x.2 t.g x.1 hx
    obtain rfl := Option.some.inj (hy'.symm.trans c)
    unfold VerifiableInference.Desc.Ground.beginRunP at hx
    split at hx
    · have hG' : (H2K.Out.dT t []).st.groups[t.g]? = some G := hG
      rw [hG'] at hx
      obtain rfl := Option.some.inj hx
      rw [he]
      show thinSh (batT t G row) = ⟨coreSh ⟨begun t.st t.g G, t.book, t.roots⟩, t.g,
        .claim (Own.layoutOf t.st G), t.mask⟩
      rw [layoutOf_own hG]
      rfl
    · cases hx
  · cases h

/-- Where the spending returns on shapes, it returns the shape of the statement written out. -/
theorem core_spent (S : Statement) (B : TreeBook) (r id : ℕ) (y : CoreSh)
    (h : spendS (coreSh ⟨S, B, r⟩) id = some y) : y = coreSh ⟨spent S id, B, r⟩ := by
  have h' : spendS (shD (⟨S, B, r, [], ()⟩ : H2K.Out.DS)) id = some y := h
  obtain ⟨d', hd⟩ := spend_returns _ id y h'
  have c := spend_carries _ d' id hd
  obtain rfl := Option.some.inj (h'.symm.trans c)
  unfold VerifiableInference.Desc.Ground.spendAsMaskP at hd
  split at hd
  · obtain rfl := Option.some.inj hd
    rfl
  · cases hd

/-- The like for one more group. -/
theorem core_withGroup (S : Statement) (B : TreeBook) (r a b : ℕ) (z : ℕ × CoreSh)
    (h : newGroupS (coreSh ⟨S, B, r⟩) a b = some z) :
    z.2 = coreSh ⟨Ground.withGroup S a b, B, r⟩ := by
  have h' : newGroupS (shD (⟨S, B, r, [], ()⟩ : H2K.Out.DS)) a b = some z := h
  obtain ⟨x, hx⟩ := newGroup_returns _ a b z h'
  have c := newGroup_carries _ x.2 a b x.1 hx
  obtain rfl := Option.some.inj (h'.symm.trans c)
  unfold VerifiableInference.Desc.Ground.newGroupP at hx
  split at hx
  · obtain rfl := Option.some.inj hx
    rfl
  · cases hx

/-- **The test for the clause pub**, on the parameters and the thin shape in front. -/
def frontPubB (p : P12) (a₀ : ThinSh) : Bool :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass, aB.mask with
    | .claim L, some id =>
      match spendS aB.core id with
      | some c2 =>
        match newGroupS c2 (lettersOf p (stA p) (stN p)).n.code
            (lettersOf p (stA p) (stN p)).n.maskCode with
        | some z => readPubB z.2
            (frontSingle L (lettersOf p (stA p) (stN p)).i (stA p).k (stA p).h id) (stA p).C.a
        | none => false
      | none => false
    | _, _ => false
  | none => false

/-- **The test's "true" gives the clause "pub".** -/
theorem frontPub_of_B (p : P12) (t : T12) (hp : t.pass = .nothing) (he : p.early = true)
    (h : frontPubB p (thinSh t) = true) (G : Group) (id : ℕ) (hG : t.st.groups[t.g]? = some G)
    (hm : t.mask = some id) :
    readPubB (coreSh ⟨Ground.withGroup (spent (begun t.st t.g G) id)
        (lettersOf p (stA p) (stN p)).n.code (lettersOf p (stA p) (stN p)).n.maskCode,
        t.book, t.roots⟩)
      (frontSingle (layoutOf t.st G) (lettersOf p (stA p) (stN p)).i (stA p).k (stA p).h id)
      (stA p).C.a = true := by
  unfold frontPubB at h
  split at h
  · rename_i aB hB
    obtain rfl := thin_batT p t G {} aB hp he hG hB
    split at h
    · rename_i L id' hL hid
      have eL : L = layoutOf t.st G := by
        have k : (thinSh (batT t G {})).pass = .claim (layoutOf t.st G) := rfl
        rw [hL] at k
        injection k
      have eI : id' = id := by
        have k : (thinSh (batT t G {})).mask = t.mask := rfl
        rw [hid, hm] at k
        exact Option.some.inj k
      subst eL eI
      split at h
      · rename_i c2 h2
        have h2' : spendS (coreSh ⟨begun t.st t.g G, t.book, t.roots⟩) id' = some c2 := h2
        obtain rfl := core_spent _ _ _ _ _ h2'
        split at h
        · rename_i z hz
          rw [core_withGroup _ _ _ _ _ z hz] at h
          exact h
        · cases h
      · cases h
    · cases h
  · cases h

end ProofFile.Honest.K12.Thin

#print axioms ProofFile.Honest.K12.Thin.thin_batT
#print axioms ProofFile.Honest.K12.Thin.core_spent
#print axioms ProofFile.Honest.K12.Thin.core_withGroup
#print axioms ProofFile.Honest.K12.Thin.frontPubB
#print axioms ProofFile.Honest.K12.Thin.frontPub_of_B
