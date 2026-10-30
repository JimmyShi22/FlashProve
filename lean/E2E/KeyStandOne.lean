-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandOne.lean: the key's shared thread at its first two borders, at a letter `Said`, and with no
`ready`. It is no `run` of the frame.

Why. `Thr` reads no `Ready` and no `Prover`. `enters₂_of` spends `ready` for one field alone. So the start
can be had at a prover that has only some of its halves in place.

Main names.
  `startK`: the state in which the run begins.
  `thr_start`: the thread at border 0, at the description's start.
  `pair_zero`: the pair at border 0.
  `pair_one`: the pair at border 1: nothing has been heard.

Premises that stay. `hS`, `hN`: on the letter `Said`, at the start state `startAt K o`; `o` is what a letter may
hand at the start. `hI`: the one open item at the start. `hK`, `hE`, `hC`, `hbare`: as at `stands_key`
(E2E/KeySharedQuiet.lean). `hV`: something is said of this input.

What stays open. Up to border 1 nothing is played, sent or heard: alone, this says nothing of any
words. A thread at a later border is what is meant.

NOT IN FRONT OF A LAW OVER COINS: `thr_start`, `pair_zero`, `pair_one` bear this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `Said` under `hS` is a letter for a predicate, of the
first kind, through `k`, and `o` is no coin. `Vd` under `hV` is a letter for a predicate, of the first kind,
through `inK w₀ rc x`. `hN` is bound over all coins and by itself picks none; `hK`, `hE` name no coin. They stand
at a run's coins `k`, and `hI` ties `Mg₀`, of the first kind; `hs`, `scope` read public files. None of these is the term that the
committer makes. None: the bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeySharedQuiet
import E2E.KeyStandStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyStandOne
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS sharedPlaces)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey lettersKey threadKey sits_two start_key)
open AtPublicFiles.KeySharedQuiet (CellsAlone over_key quiet_key owes_front ridesPast_front fits_key)
open AtPublicFiles.KeyStandStep (step_pair)
open AtPublicFiles.KeyThread (plays_quiet₂ behind₂ exchange_of_nil steps_quiet_none stop_quiet_none)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (o : Option (List OpenedColumn))
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- The state in which the run begins. -/
def startK (_ : Coins Bk) (v : Common W₀ Rc TableKey) (_ : List Fmt.Drawn) :
    Mid (Common W₀ Rc TableKey) X₀ :=
  startShared (keyProver K) v

/-- **The state in which the chain's run begins, at a field `o`**: what a letter may hand at the start. -/
abbrev startAt (o : Option (List OpenedColumn)) (v : Common W₀ Rc TableKey) : Mid (Common W₀ Rc TableKey) X₀ :=
  { startShared (keyProver K) v with opened := o }

/-- The input at this instance. -/
abbrev inK : Common W₀ Rc TableKey := ⟨w₀, rc, x.key⟩

/-- The tables at hand at the start. -/
abbrev envK : Env := envOf ((keyProver K).storedWords w₀ rc) (fun _ _ => none) []

/-- **The thread at its first border.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem thr_start (k : Coins Bk) (hV : Vd (inK w₀ rc x))
    (hI : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).Items
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).opened 0) k
      ((descriptionFromSource Xs Nr Pl).start₂ x) (startAt K o (inK w₀ rc x)) (envK K w₀ rc)) :
    Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) 0 k ((descriptionFromSource Xs Nr Pl).start₂ x)
      (startAt K o (inK w₀ rc x)) (envK K w₀ rc) := by
  unfold Thr
  refine ⟨⟨fun i p => rfl, fun σ hσ => ?_⟩, ?_, ?_, hI, ?_, trivial, rfl, hV⟩
  · have hh : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).hand 0 = [] := rfl
    rw [hh] at hσ
    cases hσ
  · rfl
  · refine ⟨?_, OnBytes.Means.InOrder.start _⟩
    show (form2 (parKey Xs Pl) (fun _ _ => true) 0 ((descriptionFromSource Xs Nr Pl).start₂ x) &&
      (!decide ((sharedPlaces true).length ≤ 0) || true)) = true
    have hn : ¬(2 ≤ 0 ∧ 0 ≤ 9) := by omega
    unfold form2
    rw [if_neg hn]
    simp
  · unfold Thread.Made
    refine ⟨rfl, ?_, rfl, fun _ _ => rfl, (descriptionFromSource Xs Nr Pl).start₂ x, [], ?_, rfl, rfl⟩
    · show ([] : List Fmt.Drawn) = Thread.locOf _ []
      unfold Thread.locOf
      simp
    · exact start_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) x

/-- **The pair at border 0.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem pair_zero (k : Coins Bk) (hV : Vd (inK w₀ rc x))
    (hI : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).Items
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).opened 0) k
      ((descriptionFromSource Xs Nr Pl).start₂ x) (startAt K o (inK w₀ rc x)) (envK K w₀ rc))
    (hS : Said 0 k (startAt K o (inK w₀ rc x))) :
    ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x))
      Said 0 k
      ((descriptionFromSource Xs Nr Pl).start₂ x) (startAt K o (inK w₀ rc x)) (envK K w₀ rc) :=
  ⟨thr_start Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd o w₀ rc x k hV hI, hS⟩

/-- **The pair at border 1: nothing has been heard.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem pair_one {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (k : Coins Bk) (hV : Vd (inK w₀ rc x))
    (hI : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).Items
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).opened 0) k
      ((descriptionFromSource Xs Nr Pl).start₂ x) (startAt K o (inK w₀ rc x)) (envK K w₀ rc))
    (hK : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hC : ∀ v, CellsAlone (Mg₀ v))
    (hbare : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).bs[0]? = some blk →
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).hs.find? fun g =>
        g.place == blk.place) = none)
    (hS : Said 0 k (startAt K o (inK w₀ rc x)))
    (hN : SaidNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) Said 0) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x))
        Said 1 k s m E ∧
      m.st.heard = [] := by
  have hO := over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)
  have hfit := fits_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) hs.named.plan
  have hb : ∃ b₀, (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).bs[0]? = some b₀ ∧
      b₀.rounds = [] ∧ b₀.oracles = [] := by
    rw [hO.bs]
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨b₀, e₀, hr₀, ho₀⟩ := hb
  have hf := hbare b₀ e₀
  have hd : drawsFit b₀.rounds [] = true := by
    rw [hr₀]
    rfl
  obtain ⟨s, m, E, hT, hh, -, -⟩ := step_pair _ Said (n := 12) (b := 0) (l := [])
    (fun _ _ _ => none) hfit (by decide) e₀ hN
    (playsS_of _ Said (plays_quiet₂ scope hs.named _ hO.bs 0 (by decide)))
    (acceptedS_of _ Said (AtPublicFiles.AtFiles.accepted_front₂ Xs Nr Pl _ (fall := fun _ _ _ => none) hO.bs))
    (behindS_of _ Said (behind₂ Xs Nr Pl hs scope hO
      (quiet_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) hK) 0 (by decide)))
    (exchangeS_of _ Said (exchange_of_nil _ (owes_front Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x))))
    (ridesPastS_of _ Said (ridesPast_front Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x) hE hC))
    (made_next _ hfit (by rw [hO.bs]; exact (planOk_all hs.named.plan).2.1) 0)
    (pair_zero Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd Said o w₀ rc x k hV hI hS) hd
    (stop_quiet_none hf _ _) (steps_quiet_none hr₀ ho₀ hf) rfl
  exact ⟨s, m, E, hT, hh⟩

end

end AtPublicFiles.KeyStandOne

#print axioms AtPublicFiles.KeyStandOne.thr_start
#print axioms AtPublicFiles.KeyStandOne.pair_zero
#print axioms AtPublicFiles.KeyStandOne.pair_one
