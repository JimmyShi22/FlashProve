-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainTop.lean: the written link's refusal, in the form in which a proof goes through
the rounds block by block.

OnBytes/Slice/Unfold.lean shows that the written protocol refuses whenever a test of work fails or
the entry file's decision says no at the whole view, the view that shows every column. This file
brings that to the predicate "the prover has lost" (Iop/Rbr.lean: `Doomed`), and it says what tests
of work and columns are on a transcript that is joined from parts by the library's `Tr.app`.

The shape of a joined list of rounds and the two shapes joined are equal by induction only. So the
laws on a joined transcript are stated for any transcript τ' of the joined list with a proof that τ'
and `Tr.app τ b` are the same, across the two types. At lists of rounds that are written out both
types are the same by evaluation, and the proof is `HEq.rfl`.

Main definitions.
 `NoAt`      a test of work fails, or the decision says no at the whole view.
 `treeCol`   the columns of the tree that one written message sends, as a function of the position.
Main theorems.
 `doomed_accept`   if the prover has lost towards `NoAt`, it has lost towards the written
                   protocol's no.
 `noAt_of_pass`, `noAt_of_dec`   the two ways to `NoAt`.
 `pass_app`, `colAtS_app_lt`, `colAtS_app_ge`   tests of work and columns of a joined transcript.
 `whole_tree`      the whole view shows, of the tree that a given round sends, that round's columns,
                   whatever is sent before and after it.
Not claimed. Nothing on soundness: no block of the proximity test is looked at.
-/
import OnBytes.Slice.Unfold

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

/-! ## From the written protocol's no to the whole view -/

section
variable (P : Fmt.M3.Par) (ds : List PQ.RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str)

/-- A test of work fails, or the decision says no at the whole view. The batched row is taken at the
whole view of the empty transcript: it depends on the stored tables alone. -/
def NoAt (τ : Tr (PQ.uL (ckP .two) ds)) : Prop :=
  (PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) &&
    Fmt.M3.decBy Fmt.M1.blocks P (whole ds a y τ) (Fmt.M3.batchLit P (whole [] a y ()))) = false

/-- A failed test of work gives `NoAt`. -/
theorem noAt_of_pass (τ : Tr (PQ.uL (ckP .two) ds))
    (h : PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = false) : NoAt P ds a y τ := by
  unfold NoAt
  rw [h, Bool.false_and]

/-- A no of the decision at the whole view gives `NoAt`. -/
theorem noAt_of_dec (τ : Tr (PQ.uL (ckP .two) ds))
    (h : Fmt.M3.decBy Fmt.M1.blocks P (whole ds a y τ) (Fmt.M3.batchLit P (whole [] a y ())) =
      false) : NoAt P ds a y τ := by
  unfold NoAt
  rw [h, Bool.and_false]

/-- Where `NoAt` holds the written protocol refuses. -/
theorem refuses_of_noAt (xs : List PQ.XO) (τ : Tr (PQ.uL (ckP .two) ds))
    (m0 : (PQ.s0 (ckP .two)).up.Msg) (c0 : (PQ.s0 (ckP .two)).up.Chal) (h : NoAt P ds a y τ) :
    (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs (Fmt.M3.dec P)).up.loc.accept () y (m0, c0, τ) = false := by
  refine refuses_of_whole ds a xs y τ P m0 c0 ?_
  rw [batchLit_whole]
  exact h

/-- If the prover has lost towards `NoAt`, it has lost towards the written protocol's no. emb is
any map from transcripts of the shape t to transcripts of all rounds. -/
theorem doomed_accept (xs : List PQ.XO) (m0 : (PQ.s0 (ckP .two)).up.Msg)
    (c0 : (PQ.s0 (ckP .two)).up.Chal) (t : Shape) (ε : Err t)
    (emb : Tr t → Tr (PQ.uL (ckP .two) ds)) (h : Doomed t ε fun b => NoAt P ds a y (emb b)) :
    Doomed t ε fun b =>
      (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs (Fmt.M3.dec P)).up.loc.accept () y (m0, c0, emb b) = false :=
  Doomed.mono t ε (fun b hb => refuses_of_noAt P ds a y xs (emb b) m0 c0 hb) h

end

/-! ## Joined transcripts -/

section
variable (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁)) (b : Tr (PQ.uL (ckP .two) ds₂))
  (τ' : Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂))) (h : HEq τ' (Tr.app τ b))
include h

/-- A transcript that is the library's joined transcript is `joinT`. -/
theorem eq_joinT : τ' = joinT ds₁ ds₂ τ b := eq_of_heq (h.trans (joinT_heq ds₁ ds₂ τ b).symm)

/-- All tests of work of a joined transcript pass if and only if they pass in both parts. -/
theorem pass_app :
    PQ.passSL (ckP .two) (ds₁ ++ ds₂) (PQ.rhoSL (ckP .two) (ds₁ ++ ds₂) τ') =
      (PQ.passSL (ckP .two) ds₁ (PQ.rhoSL (ckP .two) ds₁ τ) &&
        PQ.passSL (ckP .two) ds₂ (PQ.rhoSL (ckP .two) ds₂ b)) := by
  rw [eq_joinT ds₁ ds₂ τ b τ' h]
  exact pass_joinT ds₁ ds₂ τ b

/-- A tree of the first part does not depend on the second part. -/
theorem colAtS_app_lt (n x : ℕ) (hn : n < nTrees ds₁) :
    PQ.colAtS (ckP .two) (ds₁ ++ ds₂) τ' n x = PQ.colAtS (ckP .two) ds₁ τ n x := by
  rw [eq_joinT ds₁ ds₂ τ b τ' h]
  exact colAtS_join_lt ds₁ ds₂ τ b n x hn

/-- The trees of the second part follow those of the first. -/
theorem colAtS_app_ge (n x : ℕ) :
    PQ.colAtS (ckP .two) (ds₁ ++ ds₂) τ' (nTrees ds₁ + n) x = PQ.colAtS (ckP .two) ds₂ b n x := by
  rw [eq_joinT ds₁ ds₂ τ b τ' h]
  exact colAtS_join_ge ds₁ ds₂ τ b n x

end

/-! ## The columns of one round's tree -/

/-- The columns of the tree that the written message m of the round d sends. -/
def treeCol (d : PQ.RD) (m : (wRound d).Msg) (x : ℕ) : Option (List UInt64) :=
  if x < PQ.posN d.tree then some (colW d m.1 x) else none

/-- A column of a round's tree is the column of the written oracle. -/
theorem treeCol_some (d : PQ.RD) (m : (wRound d).Msg) (x : ℕ) (w : List UInt64)
    (h : treeCol d m x = some w) : w = colW d m.1 x := by
  unfold treeCol at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- The whole view shows, of the tree that the round d sends, that round's columns. The rounds
before d send n trees; what is sent before and after d does not matter. -/
theorem whole_tree (pre rest : List PQ.RD) (d : PQ.RD) (hd : d.tree.isSome = true) (n : ℕ)
    (hn : nTrees pre = n) (a : ℕ) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str)
    (τp : Tr (PQ.uL (ckP .two) pre)) (m : (wRound d).Msg) (c : (wRound d).Chal)
    (τr : Tr (PQ.uL (ckP .two) rest)) (τ' : Tr (PQ.uL (ckP .two) (pre ++ d :: rest)))
    (h : HEq τ' (Tr.app (t := PQ.uL (ckP .two) (d :: rest)) τp (m, c, τr))) (x : ℕ) :
    Fmt.M1.colAt (whole (pre ++ d :: rest) a y τ').own n x = treeCol d m x := by
  have h0 := colAtS_app_ge pre (d :: rest) τp (m, c, τr) τ' h 0 x
  rw [Nat.add_zero, hn] at h0
  rw [whole_own, h0, colAtS_here d rest m c τr hd x]
  rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.refuses_of_noAt
#print axioms OnBytes.Slice.doomed_accept
#print axioms OnBytes.Slice.pass_app
#print axioms OnBytes.Slice.colAtS_app_lt
#print axioms OnBytes.Slice.colAtS_app_ge
#print axioms OnBytes.Slice.whole_tree
