-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrK4.lean: K4, THE FEED-FORWARD LAYERS' OWN ROUNDS: an accepting decision is `KeepsCr`.

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.ProofFile.Honest.K9.CrWalk
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.ProofFile.Honest.K9.CrFl
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.BlockKeeps
import OnBytes.Desc.First.K4.HearGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlC
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4

variable {α : Type}

/-! ### The engine's fields -/

instance (x : Option α) : StaysC (engFl.get x) := inferInstanceAs (StaysC (Fl.need x))
instance (b : Bool) : StaysC (engFl.must b) := inferInstanceAs (StaysC (Fl.must b))
instance (n : String) (b : Bool) : StaysC (engFl.mustAs n b) := inferInstanceAs (StaysC (Fl.must b))
instance (n : String) (b : Bool) : StaysC (engFl.check n b) := inferInstanceAs (StaysC (Fl.must b))
instance : StaysC engFl.fork := inferInstanceAs (StaysC (Fl.ask some))
instance (j : Nat) : StaysC (engFl.shown j) := inferInstanceAs (StaysC (Fl.shown j))

instance (r : RoundName) (n : Nat) : StaysC (engFl.point r n) :=
  inferInstanceAs (StaysC (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : StaysC (engFl.claimsIn n) := inferInstanceAs (StaysC (Fl.claimsIn n))
instance (n : Nat) : StaysC (engFl.batch n) := inferInstanceAs (StaysC (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysC (engFl.levelIn mu rho C order) := inferInstanceAs (StaysC (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : StaysC (engFl.tscIn P lt n d) :=
  inferInstanceAs (StaysC (Fl.tscIn P lt n d))

instance (C : Aff) : StaysC (engFl.pscBegin C) := inferInstanceAs (StaysC (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : StaysC (engFl.roundIn f p z d) :=
  inferInstanceAs (StaysC (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : StaysC (engFl.pscEnds p d n) :=
  inferInstanceAs (StaysC (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : StaysC (engFl.pscRow p s k) :=
  inferInstanceAs (StaysC (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : StaysC (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (StaysC (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : StaysC (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : StaysC (shownRun engFl first n) := by
  unfold shownRun
  exact stays_mapM_arrayC (fun _ => inferInstance) _

instance (st : Stack) : StaysC (plainRounds engFl st) := by
  unfold plainRounds
  refine StaysC.bind (stays_foldlMC (fun s z => ?_) _ _) fun x => ?_
  · staysC
  · staysC

instance (g : Forest.Heard) (laid : Array Nat) : StaysC (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : StaysC (hearNorms engFl P g fo) := by
  unfold hearNorms; staysC

instance (P : Pub) (H : Heard) : StaysC (hearTerms engFl P H) := by
  unfold hearTerms; staysC

instance (v : Env) (H : Heard) (om : Array E) : StaysC (joinStart engFl v H om) := by
  unfold joinStart; staysC

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    StaysC (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; staysC

instance (P : Pub) (H : Heard) (K : HeardStack) : StaysC (hearGated engFl P H K) := by
  unfold hearGated; staysC

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : StaysC (hear engFl P hp g fo) := by
  unfold hear; staysC

/-- **Wherever HEAR returns, its ledger has the reading of the one that it was handed.** -/
theorem hearFl_cr {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameCr F G := by
  have i : StaysC (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlC

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_stepsC (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps (KeepsCr) := by
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
      refine keeps_of_casesC fun G' L' hG hL' => ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg lnk (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlC.hearFl_cr hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.FlC.hearFl_cr
#print axioms VerifiableInference.Desc.LinkJoin.k4_stepsC
