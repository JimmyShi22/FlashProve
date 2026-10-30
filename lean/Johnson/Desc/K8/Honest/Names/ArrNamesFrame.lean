-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesFrame.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE FRAME's OWN STEPS (THE MAKERS THAT LAY A LINK's LEDGER), THE REPLY (K7) AND THE MERGE (K11).
MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksFrame.lean, WITH AN ARRAY's NAME
(`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration
of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names
the looks, or leans on one that does, under a new name; the others are called where they lie: that
file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are
named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (9): laid_keeps → laid_keepsN · cleared_keeps → cleared_keepsN · keeps_laid →
keeps_laidN · openAtt_makes → openAtt_makesN · openLay_makes → openLay_makesN · openLayZero_makes →
openLayZero_makesN · k7_steps → k7_stepsN · mergeHear_looks → mergeHear_arrNames · k11_steps →
k11_stepsN.
CALLED WHERE THEY LIE (4): fork_none_between · steps_quiet · laid_between · named_some.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (1): steps_andThen.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksFrame
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesAre
import Johnson.Desc.K8.Honest.Names.FlArrNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero layFront openAtt openLay
  openLayZero clearWith)
open Johnson.Desc.First.ForkMerge (mergeHear headMergeDecide headClaimMergeKind)

theorem laid_keepsN (shOf : ℕ → List String) {l : ℕ} {s t : S} (h : layFront l s = .ok t) :
    KeepsArrNames shOf s t := by
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok h).1]
  exact keeps_reflN shOf s

theorem cleared_keepsN (shOf : ℕ → List String) {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : Johnson.Desc.First.Walk.RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : KeepsArrNames shOf s t := by
  obtain ⟨_, _, _, _, _, _, _, _, hb, _⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  exact keeps_noneN shOf (fork_none_between hb)

/-- **Behind the step the open ledger is the one laid off arrays with the link's names.** -/
theorem keeps_laidN (shOf : ℕ → List String) {s t : S} (F0 : Fork) (ns : ℕ) (L : LinkCtx)
    (hf : t.fork? = some (emptySlots (weightsAtZero F0) ns)) (hl : t.link? = some L)
    (hsh : shOf L.link = F0.trees.toList.map treeName) : KeepsArrNames shOf s t := by
  refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inl ?_
  rw [← Option.some.inj (hf.symm.trans hG), ← Option.some.inj (hl.symm.trans hL'), hsh]
  exact arrNames_laid F0 ns

/-- **«Opened» at an attention link.** -/
theorem openAtt_makesN (shOf : ℕ → List String) {P : Johnson.Desc.First.Walk.AttPar} {s t : S}
    (h : openAtt P s = .ok t) (hsh : shOf P.l = P.X.Fp.trees.toList.map treeName) :
    KeepsArrNames shOf s t := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok h
  exact keeps_laidN shOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at a layers' link.** -/
theorem openLay_makesN (shOf : ℕ → List String) {P : Johnson.Desc.First.Walk.LayPar} {s t : S}
    (h : openLay P s = .ok t) (hsh : shOf P.l = P.X.Fp.trees.toList.map treeName) :
    KeepsArrNames shOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok h
  exact keeps_laidN shOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at the first link.** -/
theorem openLayZero_makesN (shOf : ℕ → List String) {P : Johnson.Desc.First.Walk.LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} (h : openLayZero P fvs kCol s = .ok t)
    (hsh : shOf 0 = P.X.Fp.trees.toList.map treeName) : KeepsArrNames shOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok h
  exact keeps_laidN shOf P.X.Fp P.ns _ h6 h5 hsh

/-- **K7: the reply**, at any seat whose laying leaves the two readings. -/
theorem k7_stepsN {Cl : Type} (shOf : ℕ → List String) (L : Kinds.Reply.Seat S)
    (hL : ∀ s x, (L.setReply s x).fork? = s.fork? ∧ (L.setReply s x).link? = s.link?)
    (link piece V : ℕ) : (Kinds.Reply.kind (Cl := Cl) L link piece V).Steps
        (KeepsArrNames shOf) := by
  intro s rs gs s' h
  obtain ⟨_, x, _, _, _, rfl⟩ := Kinds.Head.Law.k7_ok h
  exact keeps_sameN shOf (hL s x).1 (by rw [(hL s x).2])

/-- The merge's hearing leaves the names. -/
theorem mergeHear_arrNames {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, G, u)) :
    FlL.SameArrNames F G := by
  unfold mergeHear at h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨⟨rho, F1, t1⟩, e1, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨v, F2, t2⟩, e2, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨p, F3, t3⟩, e3, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨rm, p4⟩, F4, t4⟩, e4, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨sFv, p5⟩, F5, t5⟩, e5, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨fvp, F6, t6⟩, e6, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain rfl : F6 = G := congrArg (·.2.1) (Except.ok.inj h)
  exact (((((FlL.StaysN.same (named_some e1)).trans (FlL.StaysN.same (named_some e2))).trans
    (FlL.StaysN.same (named_some e3))).trans (FlL.StaysN.same (named_some e4))).trans
    (FlL.StaysN.same (named_some e5))).trans (FlL.StaysN.same (named_some e6))

/-- **K11: the merge of the claims on the weights.** -/
theorem k11_stepsN (shOf : ℕ → List String) (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    (headClaimMergeKind P).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  have h' : headMergeDecide P s rs = .ok s' := h
  unfold headMergeDecide at h'
  split at h'
  · rename_i a ha
    obtain ⟨_, ho, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨claim, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨⟨wo, F, t'⟩, hm, h'⟩ := K9L.ok_bind h'
    dsimp only at h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain rfl := Except.ok.inj h'
    refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, ha, hop]
    · simp [S.link?, ha, hop]
    · have e : some a.L = some L' := by simpa [S.link?, hop] using hL'
      exact congrArg (·.link) (Option.some.inj e)
    · have e : some ({ F with planClaimsF := P.nLin } : Fork) = some G' := by
        simpa [S.fork?, hop] using hG
      rw [← Option.some.inj e]
      exact (mergeHear_arrNames hm : F.trees.map treeName = a.F.trees.map treeName)
  · exact nomatch h'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laid_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.cleared_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_laidN
#print axioms VerifiableInference.Desc.LinkJoin.openAtt_makesN
#print axioms VerifiableInference.Desc.LinkJoin.openLay_makesN
#print axioms VerifiableInference.Desc.LinkJoin.openLayZero_makesN
#print axioms VerifiableInference.Desc.LinkJoin.k7_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.mergeHear_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.k11_stepsN
