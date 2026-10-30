-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesEnds.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE REST OF THE SEAT's MAKERS: THE FIRST SENDING, THE REPLY, K2's PLACES, THE READS' STEPS. MADE BY
PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksEnds.lean, WITH AN ARRAY's NAME
(`treeName`, Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration
of that file that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names
the looks, or leans on one that does, under a new name; the others are called where they lie: that
file is imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are
named here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (9): k1First_whole → k1First_wholeN · k7Of_whole → k7Of_wholeN · k2_whole →
k2_wholeN · headFront_keeps → headFront_keepsN · headOpen_makes → headOpen_makesN · finFront_keeps →
finFront_keepsN · finBehind_keeps → finBehind_keepsN · readsBlockAt_whole → readsBlockAt_wholeN ·
readsQuietAt_whole → readsQuietAt_wholeN.
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
import Johnson.Desc.First.Link.Law.LooksEnds
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesFrame
import Johnson.Desc.K8.Honest.Names.ArrNamesK2
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9L (ok_bind)
open VerifiableInference.Desc.First.K2

section
variable (shOf : ℕ → List String)

/-- K1's first sending. -/
theorem k1First_wholeN {Cl : Type} (q : Params.First) (gp : _) :
    Whole (KeepsArrNames shOf) (K1.firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨⟨c, d⟩, _, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_sameN shOf rfl rfl

/-- K7 as the seat lays it. -/
theorem k7Of_wholeN (W : Verify.Public) (l : ℕ) :
    Whole (KeepsArrNames shOf) (Kinds.Reply.blockOf W l) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' := h
  unfold Kinds.Reply.blockOf Kinds.Reply.blockAt Kinds.Reply.entered at h'
  dsimp only at h'
  split at h'
  · split at h'
    · exact nomatch h'
    · exact k7_stepsN shOf Kinds.Reply.seatAt (fun _ _ => ⟨rfl, rfl⟩) l 1 W.hS.V s rs gs s' h'
  · exact nomatch h'

theorem k2_wholeN (p : P2) : Whole (KeepsArrNames shOf) (codeSwitchKind p : Block S Unit) :=
  ⟨k2_stepsN shOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- «H.0.front»: the head's link is entered, not opened. -/
theorem headFront_keepsN (tl : HTailF2) : Fn (KeepsArrNames shOf) (headFrontQ tl) := by
  intro s s' h
  unfold headFrontQ at h
  split at h
  · exact nomatch h
  · rename_i hb
    split at h
    · exact nomatch h
    · obtain ⟨x, _, h⟩ := Keeps.ebind_ok h
      obtain ⟨s₁, h1, h⟩ := Keeps.ebind_ok h
      have hB : s.atBetween = true := by simpa using hb
      have e1 : s.enterHead tl = s₁ := ((S.unmarked_ok _ _).1 h1).1
      unfold S.enterHead at e1
      rw [if_pos hB] at e1
      rw [← e1] at h
      dsimp only at h
      rw [← Except.ok.inj h]
      exact keeps_noneN shOf rfl

/-- **«H.1.quiet»: THE HEAD's LINK's MAKER.** -/
theorem headOpen_makesN (P : HeadPar) (hsh : shOf P.l = P.X.Fp.trees.toList.map treeName) :
    Fn (KeepsArrNames shOf) (headOpenQ P) := by
  intro s s' h
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P s s').1 h
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P s s' h
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hlink : s'.link? = some L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  exact keeps_laidN shOf { trees := P.X.Fp.trees } P.hp.ns L (headOpenQ_fork h) hlink
    (by rw [hL]; exact hsh)

/-- The finish's front: no link is open behind. -/
theorem finFront_keepsN : Fn (KeepsArrNames shOf) finishFrontQ := by
  intro s s' h
  unfold finishFrontQ at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · obtain ⟨s₁, _, h⟩ := Keeps.ebind_ok h
        split at h
        · rw [← Except.ok.inj h]
          exact keeps_noneN shOf rfl
        · exact nomatch h
      · exact nomatch h
      · exact nomatch h

theorem finBehind_keepsN : Fn (KeepsArrNames shOf) finishBehindQ := by
  intro s s' h
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Keeps.emap_ok h
    exact keeps_noneN shOf rfl
  · exact nomatch h

theorem readsBlockAt_wholeN {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole (KeepsArrNames shOf) b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_wholeN shOf _
  · split at h
    · cases h
      exact readsHead_wholeN shOf _
    · cases h

/-- The step behind the reads' sending, as the lots make it. -/
theorem readsQuietAt_wholeN {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) :
    Whole (KeepsArrNames shOf) b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_wholeN shOf h
    | exact readsBlockAt_wholeN shOf h
    | cases h

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k1First_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k7Of_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.k2_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.headFront_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.headOpen_makesN
#print axioms VerifiableInference.Desc.LinkJoin.finFront_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.finBehind_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.readsBlockAt_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.readsQuietAt_wholeN
