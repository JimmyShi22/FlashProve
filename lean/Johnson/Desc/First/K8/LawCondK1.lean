-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawCondK1.lean: THE SMALLNESS TEST: ITS TWO TESTS ON THE VERIFIER'S STATE
(Johnson/Desc/First/K8/Cond.lean: lay7B, onThirdB) BEHIND A YES OF THE BLOCK AT THE PLACE OF THE
SENDING OF THE READS. NO SOUNDNESS IS CLAIMED.

The block at that place is two blocks joined by Block.andThen: K1's own (K1.laterAt) and, behind it,
a step without a round (ProofFile.orLoud … (ProofFile.readsQuietAt G l X piece),
Johnson/Desc/ProofFile/Lots/Makers.lean; joined in Johnson/Desc/ProofFile/Lot/K1.lean: blocks, and
Lots/PureLots.lean: k1Pure). K1's own half leaves the smallness test's part of the state (S.tl?:
K1.laterAt_tl) and the tables as the claims take them (S.funs?: K1.laterAt_funs, here). What
the two tests say behind the block comes from the step behind K1's half.

  funsThirdB s (Johnson/Desc/First/K8/CondFuns.lean): a test with code: the tables as the claims
    take them (S.funs?) are there in s, and every one lies on the third vector of reads.
  funsThirdB_of, funsThirdB_iff: what its yes says: to the letter
    what Johnson/Road/K4/FunsTree.lean's funs_tree_atS concludes behind a yes of the block of a
    layers' link's own rounds (that file is not imported here).
  K1.putLink_funs, putFork_funs, commitAtS_funs, laterAt_funs: K1's block of a later moment leaves
    S.funs?.
  layers_makes, head_makes, att_makes: behind a yes of each of the three texts of the step.
  quiet_arms: a yes of ProofFile.orLoud … (ProofFile.readsQuietAt G l X piece) is a yes of one of the three
    texts, with its parameters named; the block that refuses has no yes.
  joined_makes_layers, _head, _att: the step joined behind ANY block k that leaves what is read: at
    a layers' link S.funs?, at the head's nothing, at an attention link S.tl?.
  joined_kind: under hX a yes is there at the kinds 0, 1 and 2 alone: at another kind the block
    refuses.
  **k1Reads_makes_layers**: k := K1.laterAt …; X is the link number l as built, of kind 0: the plan
    hp of its group of layers is there; lay7B hp.tl s' = true; and onThirdB s' = funsThirdB s, s THE
    STATE IN FRONT OF THE WHOLE BLOCK.
  **k1Reads_makes_head**: of kind 2: lay7B G.W.H.tl s' = true and onThirdB s' = true.
  **k1Reads_makes_att**: of kind 1: onThirdB s' = true, and lay7B tlP s' = lay7B tlP s at every tlP:
    the first test is kept here, not made.
Statements and proofs.
Limits. AT A LAYERS' LINK onThirdB IS NOT MADE OUT OF NOTHING: it is yes behind the block exactly
where funsThirdB is yes in front of it: that is owed by the block in front (the link's own rounds).
THAT hp.tl (hp the plan G.W.G[X.g]) OR G.W.H.tl IS THE VALUE AT WHICH A FILLING OF THE TABLE OF
JOINTS ASKS lay7B IS NOT SAID HERE; Stages.LinkH has a field tl of its own: nothing is said of it.
onThirdB is Johnson/Desc/First/K8/Cond.lean's: it asks that the list is closed.
The letters of K1's half (q, gp, lk, pr, mo, reads), the names and the piece stand under "for all":
that the lot's block at a place is of this form is not said here. A block that refuses makes every
statement here true emptily: that a yes exists at any value is shown nowhere here. Of completeness's
kind: no error term. Nothing on soundness; nothing on hiding; nothing on what an honest prover
reaches.

-/
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Desc.First.K8.LawCondAtt
import Johnson.Desc.First.K8.CondFuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## K1's block of a later moment leaves the tables as the claims take them -/

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

theorem putLink_funs (s : S) (L : LinkCtx) : (s.putLink L).funs? = s.funs? := by
  unfold S.putLink
  split <;> (try split) <;> simp_all [S.funs?]

theorem putFork_funs (s : S) (F : Fork) : (s.putFork F).funs? = s.funs? := by
  unfold S.putFork
  split <;> (try split) <;> simp_all [S.funs?]

theorem commitAtS_funs (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.funs? = s.funs? := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, _, rfl⟩ := VerifiableInference.Desc.mapOk h
    exact ((putFork_funs _ _).trans (putLink_funs _ _)).trans rfl
  · cases h

theorem laterAt_funs (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (laterAt q gp link piece moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.funs? = s.funs? :=
  commitAtS_funs _ _ _ _ s s' rs gs h

end VerifiableInference.Desc.K1

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model
open VerifiableInference.Desc.K8 (ReadsQuiet.layers ReadsQuiet.head ReadsQuiet.PG ReadsQuiet.PH)

/-! ## The tests, read off the readings -/

theorem funsThirdB_of (s : S) (f : Array HFun) (h : s.funs? = some f) :
    funsThirdB s = f.toList.all fun Fn => Fn.tree == 2 := by
  unfold funsThirdB
  rw [h]
  show (some (f.toList.all fun Fn => Fn.tree == 2) == some true) = _
  cases f.toList.all (fun Fn => Fn.tree == 2) <;> rfl

/-- What its yes says. -/
theorem funsThirdB_iff (s : S) :
    funsThirdB s = true ↔ ∃ f, s.funs? = some f ∧ ∀ Fn ∈ f, Fn.tree = 2 := by
  constructor
  · intro h
    cases hf : s.funs? with
    | none =>
      unfold funsThirdB at h
      rw [hf] at h
      exact nomatch h
    | some f =>
      rw [funsThirdB_of s f hf] at h
      exact ⟨f, rfl, fun Fn hFn => beq_iff_eq.1 (List.all_eq_true.1 h Fn (Array.mem_def.1 hFn))⟩
  · rintro ⟨f, hf, h⟩
    rw [funsThirdB_of s f hf]
    exact List.all_eq_true.2 fun Fn hFn => beq_iff_eq.2 (h Fn (Array.mem_def.2 hFn))

/-- The second test, where the smallness test's part of the state is known and its list is
closed. -/
theorem onThirdB_of (s : S) (tl : HTailF2) (h : s.tl? = some tl) (hc : tl.funClosed = true) :
    onThirdB s = tl.funs.toList.all fun Fn => Fn.tree == 2 := by
  unfold onThirdB onThird closedNow
  rw [h]
  show ((some (tl.funs.toList.all fun Fn => Fn.tree == 2) == some true) &&
    (some tl.funClosed == some true)) = _
  rw [hc]
  cases tl.funs.toList.all (fun Fn => Fn.tree == 2) <;> rfl

/-- The first test, where that part is tlP but for the list and its mark. -/
theorem lay7B_of (tlP : HTailF2) (c : Bool) (f : Array HFun) (s : S)
    (h : s.tl? = some { tlP with funClosed := c, funs := f }) : lay7B tlP s = true := by
  unfold lay7B
  rw [h]
  simp

/-! ## Behind a yes of each of the three texts -/

/-- At a layers' link. -/
theorem layers_makes (P : ReadsQuiet.PG) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ReadsQuiet.layers P).decide s rs gs = .ok s') :
    lay7B P.tl s' = true ∧ onThirdB s' = funsThirdB s := by
  obtain ⟨a, own, ha, ho, ht⟩ := layers_lays_tl P h
  have hf : s.funs? = some own.funs := by simp [S.funs?, ha, ho]
  exact ⟨lay7B_of _ _ _ _ ht, (onThirdB_of _ _ ht rfl).trans (funsThirdB_of _ _ hf).symm⟩

/-- At the head's link. -/
theorem head_makes (P : ReadsQuiet.PH) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    lay7B P.hp.tl s' = true ∧ onThirdB s' = true := by
  obtain ⟨cov, x, t, ht, hf⟩ := head_lays_tl P h
  refine ⟨lay7B_of _ _ _ _ hf, (onThirdB_of _ _ hf rfl).trans ?_⟩
  exact List.all_eq_true.2 fun Fn hFn => beq_iff_eq.2 (tables_tree ht Fn hFn)

/-- At an attention link: the second is made, the first is kept. -/
theorem att_makes (A : Attention.Plan) {s s' : S} (h : Att.readsAtSO A s = .ok s') :
    onThirdB s' = true ∧ ∀ tlP, lay7B tlP s' = lay7B tlP s := by
  obtain ⟨tl, funs, h1, h2, h3⟩ := attO_yes_tree A s s' h
  refine ⟨(onThirdB_of _ _ h2 rfl).trans ?_, fun tlP => ?_⟩
  · exact List.all_eq_true.2 fun Fn hFn => beq_iff_eq.2 (h3 Fn hFn)
  · unfold lay7B
    rw [h1, h2]

/-! ## The step as the lot joins it -/

private theorem some_of_ite {α : Type} {c : Prop} [Decidable c] {x : Option α} {q : α}
    (h : (if c then x else none) = some q) : x = some q := by
  split at h
  · exact h
  · exact nomatch h

/-- **A yes of the step as the lot joins it is a yes of one of the three texts**, with its
parameters. -/
theorem quiet_arms (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (piece : Nat) (n : String)
    (a : Place) (w : String) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece)).decide s rs gs = .ok s') :
    (X.kind = 1 ∧ ∃ A, G.W.A[X.g]? = some A ∧ Att.readsAtSO A s = .ok s') ∨
    (X.kind ≠ 1 ∧ ∃ Y, G.built[l]? = some Y ∧
      ((Y.kind = 0 ∧ ∃ hp, G.W.G[Y.g]? = some hp ∧
          (ReadsQuiet.layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩).decide s rs gs = .ok s') ∨
        (Y.kind = 2 ∧
          (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩).decide s rs gs =
            .ok s'))) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none =>
    rw [hq] at h
    have h' : (Except.error ("no block could be made for this place: " ++ w) : Except String S) =
        .ok s' := h
    exact nomatch h'
  | some q =>
    rw [hq] at h
    replace h : q.decide s rs gs = .ok s' := h
    unfold ProofFile.readsQuietAt at hq
    split at hq
    · rename_i hk
      replace hq := some_of_ite hq
      unfold Att.readsAtO at hq
      obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hq
      exact Or.inl ⟨by simpa using hk, A, hA, h⟩
    · rename_i hk
      replace hq := some_of_ite hq
      unfold VerifiableInference.Desc.K8.ReadsQuiet.blockAt at hq
      obtain ⟨k, hk2, hq⟩ := Option.bind_eq_some_iff.1 hq
      have hk3 : (G.built[l]?).map (fun Y => (Y.kind, Y.g)) = some k := by simpa using hk2
      obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hk3
      dsimp only at hq
      refine Or.inr ⟨by simpa using hk, Y, hY, ?_⟩
      split at hq
      · rename_i h0
        obtain ⟨hp, hhp, rfl⟩ := Option.map_eq_some_iff.1 hq
        exact Or.inl ⟨by simpa using h0, hp, hhp, h⟩
      · split at hq
        · rename_i h2
          obtain rfl := Option.some.inj hq
          exact Or.inr ⟨by simpa using h2, h⟩
        · exact nomatch hq

/-! ## The step joined behind a block -/

/-- Where two blocks joined by Block.andThen go on, the first went on, and the second at the
state that it returned. -/
private theorem joined_yes {nm : String} {k z : Block S Unit} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (Block.andThen nm k z).decide s rs gs = .ok s') :
    ∃ m, k.decide s (rs.take k.rounds.length) (gs.take k.openings) = .ok m ∧
      z.decide m (rs.drop k.rounds.length) (gs.drop k.openings) = .ok s' :=
  bindOk (x := k.decide s (rs.take k.rounds.length) (gs.take k.openings)) h

section
variable (k : Block S Unit) (nm : String) (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH)
  (piece : Nat) (n : String) (a : Place) (w : String) {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}

/-- Under hX a yes is there at the kinds 0, 1 and 2 alone. -/
theorem joined_kind (hX : G.built[l]? = some X)
    (h : (Block.andThen nm k (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs =
      .ok s') :
    X.kind = 0 ∨ X.kind = 1 ∨ X.kind = 2 := by
  obtain ⟨m, _, H⟩ := joined_yes h
  rcases quiet_arms G l X piece n a w H with ⟨h1, _⟩ | ⟨_, Y, hY, hL | hH⟩
  · exact Or.inr (Or.inl h1)
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    exact Or.inl hL.1
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    exact Or.inr (Or.inr hH.1)

/-- A layers' link: k any block that leaves the tables as the claims take them. -/
theorem joined_makes_layers (hk : k.Leaves S.funs?) (hX : G.built[l]? = some X) (h0 : X.kind = 0)
    (h : (Block.andThen nm k (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs =
      .ok s') :
    ∃ hp, G.W.G[X.g]? = some hp ∧ lay7B hp.tl s' = true ∧ onThirdB s' = funsThirdB s := by
  obtain ⟨m, hm, H⟩ := joined_yes h
  have e : funsThirdB m = funsThirdB s := by
    unfold funsThirdB
    rw [hk _ _ _ _ hm]
  rcases quiet_arms G l X piece n a w H with ⟨h1, _⟩ | ⟨_, Y, hY, hL | hH⟩
  · omega
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    obtain ⟨_, hp, hhp, hd⟩ := hL
    exact ⟨hp, hhp, (layers_makes _ hd).1, (layers_makes _ hd).2.trans e⟩
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    have := hH.1
    omega

/-- The head's link: k any block. -/
theorem joined_makes_head (hX : G.built[l]? = some X) (h2 : X.kind = 2)
    (h : (Block.andThen nm k (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs =
      .ok s') :
    lay7B G.W.H.tl s' = true ∧ onThirdB s' = true := by
  obtain ⟨m, _, H⟩ := joined_yes h
  rcases quiet_arms G l X piece n a w H with ⟨h1, _⟩ | ⟨_, Y, hY, hL | hH⟩
  · omega
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    have := hL.1
    omega
  · exact head_makes _ hH.2

/-- An attention link: k any block that leaves the smallness test's part of the state. -/
theorem joined_makes_att (hk : k.Leaves S.tl?) (h1 : X.kind = 1)
    (h : (Block.andThen nm k (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs =
      .ok s') :
    onThirdB s' = true ∧ ∀ tlP, lay7B tlP s' = lay7B tlP s := by
  obtain ⟨m, hm, H⟩ := joined_yes h
  rcases quiet_arms G l X piece n a w H with ⟨_, A, _, hd⟩ | ⟨hn, _⟩
  · refine ⟨(att_makes A hd).1, fun tlP => ((att_makes A hd).2 tlP).trans ?_⟩
    unfold lay7B
    rw [hk _ _ _ _ hm]
  · exact absurd h1 hn

end

/-! ## The whole block at the place of the sending of the reads -/

section
variable (q : Params.First) (gp : _root_.Desc.Plain.GPar) (lk pr mo : Nat)
  (reads : Option (List Nat)) (nm : String) (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH)
  (piece : Nat) (n : String) (a : Place) (w : String) {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}

/-- **A layers' link.** -/
theorem k1Reads_makes_layers (hX : G.built[l]? = some X) (h0 : X.kind = 0)
    (h : (Block.andThen nm (VerifiableInference.Desc.K1.laterAt q gp lk pr mo reads)
      (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs = .ok s') :
    ∃ hp, G.W.G[X.g]? = some hp ∧ lay7B hp.tl s' = true ∧ onThirdB s' = funsThirdB s :=
  joined_makes_layers _ nm G l X piece n a w
    (fun s rs gs m hm => VerifiableInference.Desc.K1.laterAt_funs q gp lk pr mo reads s m rs gs hm)
    hX h0 h

/-- **The head's link.** -/
theorem k1Reads_makes_head (hX : G.built[l]? = some X) (h2 : X.kind = 2)
    (h : (Block.andThen nm (VerifiableInference.Desc.K1.laterAt q gp lk pr mo reads)
      (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs = .ok s') :
    lay7B G.W.H.tl s' = true ∧ onThirdB s' = true :=
  joined_makes_head _ nm G l X piece n a w hX h2 h

/-- **An attention link.** -/
theorem k1Reads_makes_att (h1 : X.kind = 1)
    (h : (Block.andThen nm (VerifiableInference.Desc.K1.laterAt q gp lk pr mo reads)
      (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs = .ok s') :
    onThirdB s' = true ∧ ∀ tlP, lay7B tlP s' = lay7B tlP s :=
  joined_makes_att _ nm G l X piece n a w
    (fun s rs gs m hm =>
      (VerifiableInference.Desc.K1.laterAt_tl q gp lk pr mo reads s m rs gs hm).1)
    h1 h

end

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.K1.laterAt_funs
#print axioms VerifiableInference.Desc.First.K8.Ready.funsThirdB_iff
#print axioms VerifiableInference.Desc.First.K8.Ready.layers_makes
#print axioms VerifiableInference.Desc.First.K8.Ready.head_makes
#print axioms VerifiableInference.Desc.First.K8.Ready.att_makes
#print axioms VerifiableInference.Desc.First.K8.Ready.quiet_arms
#print axioms VerifiableInference.Desc.First.K8.Ready.joined_kind
#print axioms VerifiableInference.Desc.First.K8.Ready.joined_makes_layers
#print axioms VerifiableInference.Desc.First.K8.Ready.joined_makes_head
#print axioms VerifiableInference.Desc.First.K8.Ready.joined_makes_att
#print axioms VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_layers
#print axioms VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_head
#print axioms VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_att
