-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroK4.lean: ITS FORM FIRST: 27 INSTANCES OF THE CLASS `StaysZ`
(Johnson/P1K8R/ZeroFl.lean) AND NO OTHER, ONE LOCAL MACRO ("staysZ"): AS
Johnson/Desc/First/Link/Law/LooksK4.lean HAS THEM FOR THE CLASS Stays. THE FEED-FORWARD LAYERS' OWN
ROUNDS (K4): THE DECISION STEPS IN `KeepsZero`. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksK4.lean, WITH THE ROWS' FIRST COLUMNS (`l0s`,
Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE OF
KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under a
new name; the others are called where they lie. None of the library's goals. No prover stands in it;
nothing on completeness, soundness or hiding.

  `hearFl_l0s`   wherever K4's hearing returns, its ledger has the first columns of the one that it
      was handed
  **`k4_kz`**   K4's decision steps in `KeepsZero`
Limits. THE DECISION ALONE: nothing on K4's runs of claims (Johnson/P1K8R/ZeroRuns.lean has these).
Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroFl
import Johnson.Desc.First.Link.Law.LooksK4

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
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

variable {α : Type}

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysZ" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysZ.bind ?_ ?_
    | intro _
    | split)

/-! ### The engine's fields -/

instance (x : Option α) : StaysZ (engFl.get x) := inferInstanceAs (StaysZ (Fl.need x))
instance (b : Bool) : StaysZ (engFl.must b) := inferInstanceAs (StaysZ (Fl.must b))
instance (n : String) (b : Bool) : StaysZ (engFl.mustAs n b) := inferInstanceAs (StaysZ (Fl.must b))
instance (n : String) (b : Bool) : StaysZ (engFl.check n b) := inferInstanceAs (StaysZ (Fl.must b))
instance : StaysZ engFl.fork := inferInstanceAs (StaysZ (Fl.ask some))
instance (j : Nat) : StaysZ (engFl.shown j) := inferInstanceAs (StaysZ (Fl.shown j))
instance (a : Aff) : StaysZ (engFl.lin a) := inferInstanceAs (StaysZ (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : StaysZ (engFl.point r n) :=
  inferInstanceAs (StaysZ (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : StaysZ (engFl.claimsIn n) := inferInstanceAs (StaysZ (Fl.claimsIn n))
instance (n : Nat) : StaysZ (engFl.batch n) := inferInstanceAs (StaysZ (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysZ (engFl.levelIn mu rho C order) := inferInstanceAs (StaysZ (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : StaysZ (engFl.tscIn P lt n d) :=
  inferInstanceAs (StaysZ (Fl.tscIn P lt n d))

instance (C : Aff) : StaysZ (engFl.pscBegin C) := inferInstanceAs (StaysZ (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : StaysZ (engFl.roundIn f p z d) :=
  inferInstanceAs (StaysZ (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : StaysZ (engFl.pscEnds p d n) :=
  inferInstanceAs (StaysZ (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : StaysZ (engFl.pscRow p s k) :=
  inferInstanceAs (StaysZ (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : StaysZ (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (StaysZ (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : StaysZ (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : StaysZ (shownRun engFl first n) := by
  unfold shownRun
  exact staysZ_mapM_array (fun _ => inferInstance) _

instance (st : Stack) : StaysZ (plainRounds engFl st) := by
  unfold plainRounds
  refine StaysZ.bind (staysZ_foldlM (fun s z => ?_) _ _) fun x => ?_
  · staysZ
  · staysZ

instance (g : Forest.Heard) (laid : Array Nat) : StaysZ (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : StaysZ (hearNorms engFl P g fo) := by
  unfold hearNorms; staysZ

instance (P : Pub) (H : Heard) : StaysZ (hearTerms engFl P H) := by
  unfold hearTerms; staysZ

instance (v : Env) (H : Heard) (om : Array E) : StaysZ (joinStart engFl v H om) := by
  unfold joinStart; staysZ

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    StaysZ (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; staysZ

instance (P : Pub) (H : Heard) (K : HeardStack) : StaysZ (hearGated engFl P H K) := by
  unfold hearGated; staysZ

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : StaysZ (hear engFl P hp g fo) := by
  unfold hear; staysZ

/-- **Wherever HEAR returns, its ledger has the first columns of the one that it was handed.** -/
theorem hearFl_l0s {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameL0 F G := by
  have i : StaysZ (hear engFl P hp g fo) := inferInstance
  exact i.same h

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart hearAt)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- **K4: the feed-forward layers' own rounds.** -/
theorem k4_kz (p : OnBytes.Desc.First.K4.Par) :
    (blockAtS p).Steps KeepsZero := by
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
      refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
      · unfold S.fork?
        rw [ha]
      · unfold S.link?
        rw [ha]
      · exact congrArg (·.link) (Option.some.inj hL')
      · rw [← Option.some.inj hG]
        exact FlL.hearFl_l0s hh
    · exact nomatch h3
    · exact nomatch h3
  · exact nomatch hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.FlL.hearFl_l0s
#print axioms VerifiableInference.Desc.LinkJoin.k4_kz
