-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrK4.lean: K4, THE FEED-FORWARD LAYERS' OWN ROUNDS: an accepting decision is `KeepsTr`.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.ProofFile.Honest.K9.TrWalk
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.ProofFile.Honest.K9.TrFl
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.BlockKeeps
import OnBytes.Desc.First.K4.HearGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlT
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4

variable {α : Type}

/-! ### The engine's fields -/

instance (x : Option α) : StaysT (engFl.get x) := inferInstanceAs (StaysT (Fl.need x))
instance (b : Bool) : StaysT (engFl.must b) := inferInstanceAs (StaysT (Fl.must b))
instance (n : String) (b : Bool) : StaysT (engFl.mustAs n b) := inferInstanceAs (StaysT (Fl.must b))
instance (n : String) (b : Bool) : StaysT (engFl.check n b) := inferInstanceAs (StaysT (Fl.must b))
instance : StaysT engFl.fork := inferInstanceAs (StaysT (Fl.ask some))
instance (j : Nat) : StaysT (engFl.shown j) := inferInstanceAs (StaysT (Fl.shown j))

instance (r : RoundName) (n : Nat) : StaysT (engFl.point r n) :=
  inferInstanceAs (StaysT (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : StaysT (engFl.claimsIn n) := inferInstanceAs (StaysT (Fl.claimsIn n))
instance (n : Nat) : StaysT (engFl.batch n) := inferInstanceAs (StaysT (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysT (engFl.levelIn mu rho C order) := inferInstanceAs (StaysT (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : StaysT (engFl.tscIn P lt n d) :=
  inferInstanceAs (StaysT (Fl.tscIn P lt n d))

instance (C : Aff) : StaysT (engFl.pscBegin C) := inferInstanceAs (StaysT (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : StaysT (engFl.roundIn f p z d) :=
  inferInstanceAs (StaysT (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : StaysT (engFl.pscEnds p d n) :=
  inferInstanceAs (StaysT (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : StaysT (engFl.pscRow p s k) :=
  inferInstanceAs (StaysT (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : StaysT (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (StaysT (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : StaysT (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : StaysT (shownRun engFl first n) := by
  unfold shownRun
  exact stays_mapM_arrayT (fun _ => inferInstance) _

instance (st : Stack) : StaysT (plainRounds engFl st) := by
  unfold plainRounds
  refine StaysT.bind (stays_foldlMT (fun s z => ?_) _ _) fun x => ?_
  · staysT
  · staysT

instance (g : Forest.Heard) (laid : Array Nat) : StaysT (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : StaysT (hearNorms engFl P g fo) := by
  unfold hearNorms; staysT

instance (P : Pub) (H : Heard) : StaysT (hearTerms engFl P H) := by
  unfold hearTerms; staysT

instance (v : Env) (H : Heard) (om : Array E) : StaysT (joinStart engFl v H om) := by
  unfold joinStart; staysT

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    StaysT (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; staysT

instance (P : Pub) (H : Heard) (K : HeardStack) : StaysT (hearGated engFl P H K) := by
  unfold hearGated; staysT

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : StaysT (hear engFl P hp g fo) := by
  unfold hear; staysT

/-- **Wherever HEAR returns, its ledger has the reading of the one that it was handed.** -/
theorem hearFl_tr {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameTr F G := by
  have i : StaysT (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlT

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_stepsT (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps (KeepsTr) := by
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
      refine keeps_of_casesT fun G' L' hG hL' => ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg lnk (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlT.hearFl_tr hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.FlT.hearFl_tr
#print axioms VerifiableInference.Desc.LinkJoin.k4_stepsT
