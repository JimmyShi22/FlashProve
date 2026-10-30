-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/FrontPubOwn.lean

THE CLAUSE pub OF `FrontAsksO` FROM ONE TEST ON THE THIN SHAPE, WHERE THE FIRST FOLD SENDS ITS OWN TABLE: the twin of
`frontPubB`, `frontPub_of_B` (FrontThin.lean in the folder above), which are false here by the mask.

  `enteredCore`, `enteredCore_eq`   what the entering of the fold's own table does, on shapes; it is the shape of
                 `withOwn`, `ownBook`
  `foldF`, `pubOwnAt`, `pubOwnAt_yes`   the spending, the next group and `readPubB`, at a shape
  `frontPubOwnB`, `frontPubOwn_of_B`   the test, and that its yes gives the clause

Limits. That the test is true is not shown here. Steps of the verifier's: nothing of any prover. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.ShapeAsksOwn
import Johnson.Desc.ProofFile.Honest.K12.FrontThin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.Sh (ThinSh thinSh batThin readPubB)
open ProofFile.Honest.K12.Thin (thin_batT core_spent core_withGroup)

/-- **The entering of the fold's own table, on shapes.** -/
def enteredCore (firstTree : ℕ) (a : CoreSh) (F : FoldShape) : CoreSh :=
  { st := { a.st with oracles := a.st.oracles ++ [orcSh { shape := (foldMaskNotice F).shape }] }
    book := { trees := a.book.trees ++
                [treeSh (ownTree firstTree a.roots a.st.oracles.length a.st.codes F)]
              place := a.book.place ++ [(a.book.trees.length, 0)] }
    roots := a.roots + 1 }

/-- It is the shape of what the entering leaves. -/
theorem enteredCore_eq (firstTree : ℕ) (S : Statement) (B : TreeBook) (r : ℕ) (F : FoldShape) :
    enteredCore firstTree (coreSh ⟨S, B, r⟩) F =
      coreSh ⟨withOwn S F, ownBook firstTree S B r F, r + 1⟩ := by
  simp [enteredCore, coreSh, stSh, bookSh, withOwn, ownBook, Array.toList_push, List.map_append]

/-- The fold's shape at the first stage, at a layout. -/
def foldF (p : P12) (L : GroupLayout) : FoldShape :=
  ioppFoldShape ⟨(lettersOf p (stA p) (stN p)).i.1, (lettersOf p (stA p) (stN p)).i.2, (stA p).k,
    (stA p).h⟩ L

/-- Spend the new message, make the next group, test the public part. -/
def pubOwnAt (p : P12) (L : GroupLayout) (id : ℕ) (c : CoreSh) : Bool :=
  match spendS c id with
  | some c2 =>
    match newGroupS c2 (lettersOf p (stA p) (stN p)).n.code
        (lettersOf p (stA p) (stN p)).n.maskCode with
    | some z => readPubB z.2
        (frontSingle L (lettersOf p (stA p) (stN p)).i (stA p).k (stA p).h id) (stA p).C.a
    | none => false
  | none => false

theorem pubOwnAt_yes (p : P12) (L : GroupLayout) (id : ℕ) (S : Statement) (B : TreeBook) (r : ℕ)
    (h : pubOwnAt p L id (coreSh ⟨S, B, r⟩) = true) :
    readPubB (coreSh ⟨Ground.withGroup (spent S id) (lettersOf p (stA p) (stN p)).n.code
        (lettersOf p (stA p) (stN p)).n.maskCode, B, r⟩)
      (frontSingle L (lettersOf p (stA p) (stN p)).i (stA p).k (stA p).h id) (stA p).C.a = true := by
  unfold pubOwnAt at h
  split at h
  · rename_i c2 h2
    obtain rfl := core_spent _ _ _ _ _ h2
    split at h
    · rename_i z hz
      rw [core_withGroup _ _ _ _ _ z hz] at h
      exact h
    · cases h
  · cases h

/-- **The test for the clause pub.** -/
def frontPubOwnB (p : P12) (a₀ : ThinSh) : Bool :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass with
    | .claim L => pubOwnAt p L aB.core.st.oracles.length
        (enteredCore p.nums.firstTree aB.core (foldF p L))
    | _ => false
  | none => false

/-- **The test's "true" gives the clause pub.** -/
theorem frontPubOwn_of_B (p : P12) (t : T12) (hp : t.pass = .nothing) (he : p.early = true)
    (h : frontPubOwnB p (thinSh t) = true) (G : Group) (hG : t.st.groups[t.g]? = some G) :
    readPubB (coreSh ⟨Ground.withGroup (spent (withOwn (begun t.st t.g G) (foldF p (layoutOf t.st G)))
          (begun t.st t.g G).oracles.size)
        (lettersOf p (stA p) (stN p)).n.code (lettersOf p (stA p) (stN p)).n.maskCode,
      ownBook p.nums.firstTree (begun t.st t.g G) t.book t.roots (foldF p (layoutOf t.st G)),
      t.roots + 1⟩)
      (frontSingle (layoutOf t.st G) (lettersOf p (stA p) (stN p)).i (stA p).k (stA p).h
        (begun t.st t.g G).oracles.size) (stA p).C.a = true := by
  unfold frontPubOwnB at h
  split at h
  · rename_i aB hB
    obtain rfl := thin_batT p t G {} aB hp he hG hB
    split at h
    · rename_i L hL
      have eL : L = layoutOf t.st G := by
        have k : (thinSh (batT t G {})).pass = .claim (layoutOf t.st G) := rfl
        rw [hL] at k
        injection k
      subst eL
      have hl : (coreSh ⟨begun t.st t.g G, t.book, t.roots⟩).st.oracles.length =
          (begun t.st t.g G).oracles.size := by
        simp [coreSh, stSh]
      have h' : pubOwnAt p (layoutOf t.st G)
          (coreSh ⟨begun t.st t.g G, t.book, t.roots⟩).st.oracles.length
          (enteredCore p.nums.firstTree (coreSh ⟨begun t.st t.g G, t.book, t.roots⟩)
            (foldF p (layoutOf t.st G))) = true := h
      rw [hl, enteredCore_eq] at h'
      exact pubOwnAt_yes _ _ _ _ _ _ h'
    · cases h
  · cases h

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.enteredCore
#print axioms ProofFile.Honest.K12.Own.enteredCore_eq
#print axioms ProofFile.Honest.K12.Own.foldF
#print axioms ProofFile.Honest.K12.Own.pubOwnAt
#print axioms ProofFile.Honest.K12.Own.pubOwnAt_yes
#print axioms ProofFile.Honest.K12.Own.frontPubOwnB
#print axioms ProofFile.Honest.K12.Own.frontPubOwn_of_B
