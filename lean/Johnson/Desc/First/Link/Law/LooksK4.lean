-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksK4.lean: THE FEED-FORWARD LAYERS' OWN ROUNDS (kind K4) HAND ON «THE
LEDGER's ARRAYS HAVE THE PLAN's SHAPES»: K4's share of the walk of
Johnson/Desc/First/Link/Law/LooksWalk.lean. Instances and theorems. No text already in the library turns.

How. IT IS OnBytes/Desc/First/K4/HearGrows.lean, INSTANCE FOR INSTANCE, with the class `Stays`
(Johnson/Desc/First/Link/Law/FlLooks.lean) in the place of `Grows` (made from that file's text by
program).
  `hearFl_looks`: wherever K4's hearing (`hearFl`, OnBytes/Desc/First/K4/Plain.lean) returns, its
    ledger has the looks of the one that it was handed.
  `k4_steps`: **(K4.blockAtS p).Steps (KeepsLooks shOf)**: the decision lays that ledger, what was
    heard and "nothing is owed" into the layers' own part: the link's context is not touched.
Limits. THE DECISION ALONE: nothing on this sub-protocol's runs of claims (the batching's runs'
share). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.BlockKeeps
import OnBytes.Desc.First.K4.HearGrows

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

/-! ### The engine's fields -/

instance (x : Option α) : Stays (engFl.get x) := inferInstanceAs (Stays (Fl.need x))
instance (b : Bool) : Stays (engFl.must b) := inferInstanceAs (Stays (Fl.must b))
instance (n : String) (b : Bool) : Stays (engFl.mustAs n b) := inferInstanceAs (Stays (Fl.must b))
instance (n : String) (b : Bool) : Stays (engFl.check n b) := inferInstanceAs (Stays (Fl.must b))
instance : Stays engFl.fork := inferInstanceAs (Stays (Fl.ask some))
instance (j : Nat) : Stays (engFl.shown j) := inferInstanceAs (Stays (Fl.shown j))
instance (a : Aff) : Stays (engFl.lin a) := inferInstanceAs (Stays (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : Stays (engFl.point r n) :=
  inferInstanceAs (Stays (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : Stays (engFl.claimsIn n) := inferInstanceAs (Stays (Fl.claimsIn n))
instance (n : Nat) : Stays (engFl.batch n) := inferInstanceAs (Stays (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Stays (engFl.levelIn mu rho C order) := inferInstanceAs (Stays (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : Stays (engFl.tscIn P lt n d) :=
  inferInstanceAs (Stays (Fl.tscIn P lt n d))

instance (C : Aff) : Stays (engFl.pscBegin C) := inferInstanceAs (Stays (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : Stays (engFl.roundIn f p z d) :=
  inferInstanceAs (Stays (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : Stays (engFl.pscEnds p d n) :=
  inferInstanceAs (Stays (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : Stays (engFl.pscRow p s k) :=
  inferInstanceAs (Stays (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : Stays (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (Stays (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : Stays (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : Stays (shownRun engFl first n) := by
  unfold shownRun
  exact stays_mapM_array (fun _ => inferInstance) _

instance (st : Stack) : Stays (plainRounds engFl st) := by
  unfold plainRounds
  refine Stays.bind (stays_foldlM (fun s z => ?_) _ _) fun x => ?_
  · stays
  · stays

instance (g : Forest.Heard) (laid : Array Nat) : Stays (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : Stays (hearNorms engFl P g fo) := by
  unfold hearNorms; stays

instance (P : Pub) (H : Heard) : Stays (hearTerms engFl P H) := by
  unfold hearTerms; stays

instance (v : Env) (H : Heard) (om : Array E) : Stays (joinStart engFl v H om) := by
  unfold joinStart; stays

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    Stays (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; stays

instance (P : Pub) (H : Heard) (K : HeardStack) : Stays (hearGated engFl P H K) := by
  unfold hearGated; stays

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : Stays (hear engFl P hp g fo) := by
  unfold hear; stays

/-- **Wherever HEAR returns, its ledger has the looks of the one that it was handed.** -/
theorem hearFl_looks {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameLooks F G := by
  have i : Stays (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_steps (shOf : ℕ → List Look) (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps (KeepsLooks shOf) := by
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
      refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg (·.link) (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlL.hearFl_looks hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.FlL.hearFl_looks
#print axioms VerifiableInference.Desc.LinkJoin.k4_steps
