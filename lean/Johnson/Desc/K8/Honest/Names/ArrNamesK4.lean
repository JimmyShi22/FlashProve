-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesK4.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
KIND K4's SHARE: ITS HEARING AND ITS DECISION. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksK4.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
ITS FORM, AS ITS SOURCE's: 27 INSTANCES OF THE CLASS `StaysN` (27 of them unnamed) · ONE LOCAL
MACRO, "staysN" (the library's "stays" is global; this one is laid anew in each file that spends
it).
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (2): hearFl_looks → hearFl_arrNames · k4_steps → k4_stepsN.
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
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.K8.Honest.Names.FlArrNames
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4

variable {α : Type}

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysN" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysN.bind ?_ ?_
    | intro _
    | split)

instance (x : Option α) : StaysN (engFl.get x) := inferInstanceAs (StaysN (Fl.need x))
instance (b : Bool) : StaysN (engFl.must b) := inferInstanceAs (StaysN (Fl.must b))
instance (n : String) (b : Bool) : StaysN (engFl.mustAs n b) := inferInstanceAs (StaysN (Fl.must b))
instance (n : String) (b : Bool) : StaysN (engFl.check n b) := inferInstanceAs (StaysN (Fl.must b))
instance : StaysN engFl.fork := inferInstanceAs (StaysN (Fl.ask some))
instance (j : Nat) : StaysN (engFl.shown j) := inferInstanceAs (StaysN (Fl.shown j))
instance (a : Aff) : StaysN (engFl.lin a) := inferInstanceAs (StaysN (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : StaysN (engFl.point r n) :=
  inferInstanceAs (StaysN (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : StaysN (engFl.claimsIn n) := inferInstanceAs (StaysN (Fl.claimsIn n))
instance (n : Nat) : StaysN (engFl.batch n) := inferInstanceAs (StaysN (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysN (engFl.levelIn mu rho C order) := inferInstanceAs (StaysN (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : StaysN (engFl.tscIn P lt n d) :=
  inferInstanceAs (StaysN (Fl.tscIn P lt n d))

instance (C : Aff) : StaysN (engFl.pscBegin C) := inferInstanceAs (StaysN (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : StaysN (engFl.roundIn f p z d) :=
  inferInstanceAs (StaysN (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : StaysN (engFl.pscEnds p d n) :=
  inferInstanceAs (StaysN (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : StaysN (engFl.pscRow p s k) :=
  inferInstanceAs (StaysN (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : StaysN (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (StaysN (flatForkEnd lay cl sv))

instance (p : Psc) (S0 : E) : StaysN (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : StaysN (shownRun engFl first n) := by
  unfold shownRun
  exact stays_mapM_arrayN (fun _ => inferInstance) _

instance (st : Stack) : StaysN (plainRounds engFl st) := by
  unfold plainRounds
  refine StaysN.bind (stays_foldlMN (fun s z => ?_) _ _) fun x => ?_
  · staysN
  · staysN

instance (g : Forest.Heard) (laid : Array Nat) : StaysN (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : StaysN (hearNorms engFl P g fo) := by
  unfold hearNorms; staysN

instance (P : Pub) (H : Heard) : StaysN (hearTerms engFl P H) := by
  unfold hearTerms; staysN

instance (v : Env) (H : Heard) (om : Array E) : StaysN (joinStart engFl v H om) := by
  unfold joinStart; staysN

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    StaysN (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; staysN

instance (P : Pub) (H : Heard) (K : HeardStack) : StaysN (hearGated engFl P H K) := by
  unfold hearGated; staysN

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : StaysN (hear engFl P hp g fo) := by
  unfold hear; staysN

/-- **Wherever HEAR returns, its ledger has the names of the one that it was handed.** -/
theorem hearFl_arrNames {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameArrNames F G := by
  have i : StaysN (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_stepsN (shOf : ℕ → List String) (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  obtain ⟨x, h0, h1⟩ := K9L.ok_bind h
  obtain ⟨y, h2, rfl⟩ := Keeps.emap_ok h1
  have hx : part? s = some x := by
    cases e : part? s with
    | none =>
      rw [e] at h0
      exact nomatch h0
    | some z =>
      rw [e] at h0
      exact congrArg some (Except.ok.inj h0)
  unfold part? at hx
  split at hx
  · rename_i a ha
    obtain rfl := Option.some.inj hx
    have h3 : hearAt seatOwn p (a, if s.noneWaits then none else s.rowsOwed, s.tokv) rs = .ok y :=
        h2
    unfold hearAt at h3
    obtain ⟨_, _, h3⟩ := K9L.ok_bind h3
    obtain ⟨_, _, h3⟩ := K9L.ok_bind h3
    obtain ⟨_, _, h3⟩ := K9L.ok_bind h3
    obtain ⟨fo, _, h3⟩ := K9L.ok_bind h3
    split at h3
    · rename_i o F hh
      obtain rfl := Except.ok.inj h3
      refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg (·.link) (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlL.hearFl_arrNames hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.FlL.hearFl_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.k4_stepsN
