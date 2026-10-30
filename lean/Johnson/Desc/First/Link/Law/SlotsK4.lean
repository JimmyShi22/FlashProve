-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsK4.lean: K4.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksK4.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.SlotsWalk
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.Link.Law.FlSlots
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.BlockKeeps
import OnBytes.Desc.First.K4.HearGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlS
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4

variable {α : Type}

/-! ### The engine's fields -/

instance (x : Option α) : StaysS (engFl.get x) := inferInstanceAs (StaysS (Fl.need x))
instance (b : Bool) : StaysS (engFl.must b) := inferInstanceAs (StaysS (Fl.must b))
instance (n : String) (b : Bool) : StaysS (engFl.mustAs n b) := inferInstanceAs (StaysS (Fl.must b))
instance (n : String) (b : Bool) : StaysS (engFl.check n b) := inferInstanceAs (StaysS (Fl.must b))
instance : StaysS engFl.fork := inferInstanceAs (StaysS (Fl.ask some))
instance (j : Nat) : StaysS (engFl.shown j) := inferInstanceAs (StaysS (Fl.shown j))
instance (a : Aff) : StaysS (engFl.lin a) := inferInstanceAs (StaysS (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : StaysS (engFl.point r n) :=
  inferInstanceAs (StaysS (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : StaysS (engFl.claimsIn n) := inferInstanceAs (StaysS (Fl.claimsIn n))
instance (n : Nat) : StaysS (engFl.batch n) := inferInstanceAs (StaysS (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysS (engFl.levelIn mu rho C order) := inferInstanceAs (StaysS (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : StaysS (engFl.tscIn P lt n d) :=
  inferInstanceAs (StaysS (Fl.tscIn P lt n d))

instance (C : Aff) : StaysS (engFl.pscBegin C) := inferInstanceAs (StaysS (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : StaysS (engFl.roundIn f p z d) :=
  inferInstanceAs (StaysS (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : StaysS (engFl.pscEnds p d n) :=
  inferInstanceAs (StaysS (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : StaysS (engFl.pscRow p s k) :=
  inferInstanceAs (StaysS (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : StaysS (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (StaysS (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : StaysS (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : StaysS (shownRun engFl first n) := by
  unfold shownRun
  exact stays_mapM_arrayS (fun _ => inferInstance) _

instance (st : Stack) : StaysS (plainRounds engFl st) := by
  unfold plainRounds
  refine StaysS.bind (stays_foldlMS (fun s z => ?_) _ _) fun x => ?_
  · staysS
  · staysS

instance (g : Forest.Heard) (laid : Array Nat) : StaysS (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : StaysS (hearNorms engFl P g fo) := by
  unfold hearNorms; staysS

instance (P : Pub) (H : Heard) : StaysS (hearTerms engFl P H) := by
  unfold hearTerms; staysS

instance (v : Env) (H : Heard) (om : Array E) : StaysS (joinStart engFl v H om) := by
  unfold joinStart; staysS

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    StaysS (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; staysS

instance (P : Pub) (H : Heard) (K : HeardStack) : StaysS (hearGated engFl P H K) := by
  unfold hearGated; staysS

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : StaysS (hear engFl P hp g fo) := by
  unfold hear; staysS

/-- **Wherever HEAR returns, its ledger has the two numbers of the one that it was handed.** -/
theorem hearFl_slots {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameSlots F G := by
  have i : StaysS (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlS

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_stepsS (nsOf : ℕ → ℕ × ℕ) (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps (KeepsSlots nsOf) := by
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
      refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg (·.link) (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlS.hearFl_slots hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin
