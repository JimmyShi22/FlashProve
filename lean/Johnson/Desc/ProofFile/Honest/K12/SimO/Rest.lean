-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at a proximity test whose first fold sends its own table: the second part.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Rest.lean: THE FRAME's SENTENCE exact AT THE SECOND MEMBER OF A PROXIMITY TEST WHOSE FIRST FOLD SENDS ITS OWN FRESH TABLE. The library's law at that member (`exact_rest_trees`, Sim/TreesExact.lean) holds of nothing there: its invariant of the later stages is `BodyInv` at `PlanAll`, whose `PlanFrom` asks `ownMask = false`. This file takes the law one step below it: `core_own_trees` (Sim/TreesLaw.lean), which asks only that the last claim is true, `EndOkT`, at the place itself, and names neither arm of the first fold.

  `AskedOwn`          `AskedT` (Sim/TreesExact.lean) with its clause `behind` turned to `endOk`: the last claim. Every other clause is `AskedT`'s, to the letter
  `exact_rest_own`    **`ExactMember` at `restMember J Js`, at every On and bud that give `AskedOwn`**
  `some_rest_own`     both sides of that sentence are some, at every coin: no «none = none»

Limits. CONDITIONAL ON `AskedOwn`, which no file shows at a run; SimO/Free.lean draws it from a condition at the stand. The first member is not here (Sim/FirstPubOwnAtHead.lean has it). Nothing here says that the sides of a description have these parts. No property of the protocol is claimed: nothing on completeness, soundness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody qNext oNext)
open ProofFile.Honest.Small (ExactMember)

attribute [local instance] csNonempty

variable {S Cl V W X Pb : Type}

/-! ## The sentence -/

/-- **What is asked**: `AskedT` (Sim/TreesExact.lean) with its clause on the later stages turned to the last claim. -/
structure AskedOwn (J : TestJob W X) (Js : SimJob Pb) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (s next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  play : PlayTies J s next (nx' :: rest') m (drawnAll J m ds) ds
  count : restLen J.p.nums.stages = 2 + lenFrom next (nx' :: rest')
  endOk : ∀ c : ℕ → GE, EndOkT J.p s next (nx' :: rest') (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
    (carriedCoins J mem).hide (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))
    (drawnAll J m ds) c
  groups : aGroups s 1 (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))
      (drawnAll J m ds) = aGroups s 1 (Js.trees₀ front) (drawnAll J m ds)
  fits : FitsBody (drawnAll J m ds) (next :: nx' :: rest') s 1
  low : ∀ st ∈ next :: nx' :: rest', st.h ≤ st.k
  asks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr (drawnAll J m ds) (next :: nx' :: rest') s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  same : partEntry J mem m = Js.entry pb front

section At
variable {J : TestJob W X} {Js : SimJob Pb} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
  {front : Before} {ds : List Fmt.Drawn} {asks : List (List (List ℕ))}
  {s next nx' : Fmt.M1.Stage} {rest' : List Fmt.M1.Stage}

/-- The state behind the first fold, in the law's letters. -/
theorem entry_eq_own (A : AskedOwn J Js pb mem m front ds asks s next nx' rest') :
    partEntry J mem m =
      entryOf J.p s (laidS J.p) (J.recB m.st.input (restFront J m) (drawnAll J m ds 0))
        (rowsAt J mem m) (hideW (carriedCoins J mem).hide) (drawnAll J m ds) := by
  have hs : J.s₀ = s := by
    unfold TestJob.s₀
    rw [A.play.stages]
    rfl
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [A.play.stages]; rfl
  have h0 : drawnAll J m ds 0 = heardIn J m 0 := by
    unfold drawnAll
    rw [if_pos (by omega)]
  unfold partEntry entryOf
  simp only
  rw [hs, h0, A.play.laid]
  refine congrArg _ ?_
  exact aFold_congr _ _ _ _ _ _ _ _ fun n hn' => by
    unfold drawnAll
    rw [if_pos (by rw [hn, A.play.k]; omega)]

/-- **What the simulator yields.** -/
theorem tells_rest_own (A : AskedOwn J Js pb mem m front ds asks s next nx' rest')
    (c : Cs (restSim Js).takes) :
    (restSim Js).tell pb front ds asks c =
      some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
        (carriedCoins J mem).hide (Js.trees₀ front) (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e) := by
  have hst : Js.stages = s :: next :: nx' :: rest' := by
    unfold SimJob.stages
    rw [A.place, A.play.stages]
  have hl : Js.laid = laidOf J.p := by
    rw [← A.play.laid]
    unfold SimJob.laid TestJob.laid
    rw [A.place]
  have hD : (fun i => if i < firstLen Js.stages then
      ((lastSeen front (firstLen Js.stages)).map (·.drawn)).getD i noDraw
      else ds.getD (i - firstLen Js.stages) noDraw) = drawnAll J m ds := by
    have e : Js.stages = J.p.nums.stages := by rw [hst, A.play.stages]
    funext i
    rw [e, A.heard]
    rfl
  have hdep : ∀ i, Js.depthAt i = depthAt J i := fun i => by
    unfold SimJob.depthAt depthAt
    rw [A.own, A.place]
  unfold restSim
  simp only [hD]
  unfold restZeroText
  simp only [hst, Option.map_some]
  have hlen : ∀ x : ℕ → GE, (zeroText Js.p s next (nx' :: rest') (Js.laid.drop 1)
      (Js.entry pb front) (Js.trees₀ front) x (drawnAll J m ds)).rs.length =
      restLen J.p.nums.stages := fun x => by
    rw [A.count]
    simp only [zeroText, zeroTextK, restText, List.length_set, List.length_append, length_stages,
      aSwitch, List.length_cons, List.length_nil]
  rw [hlen]
  unfold zeroOwnT
  rw [← entry_eq_own A, A.same, A.place, hl]
  have e2 : firstLen (s :: next :: nx' :: rest') = firstLen J.p.nums.stages := by
    rw [A.play.stages]
  simp only [hdep, e2]
  rfl

end At

/-- **The frame's sentence at the second member**, where the first fold sends its own table, at every On and bud that give what is asked. -/
theorem exact_rest_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop)
    (hA : ∀ (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) m front ds asks,
      On (restMember J Js) ca m front → m.seen = front.seen →
      drawsFit ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      bud 1 ds asks →
      front.holds chain firstTree ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      ∃ s next nx' rest', AskedOwn J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks
        s next nx' rest') :
    ExactMember φ σ chain firstTree On bud (restMember J Js) := by
  intro ca m front ds asks hOn hseen hfit hbud hholds _
  obtain ⟨s, next, nx', rest', A⟩ := hA ca m front ds asks hOn hseen hfit hbud hholds
  have hlaw := core_own_trees J.p s next nx' rest' (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
    (carriedCoins J (stretches _ ca)).hide
    (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
    (Js.trees₀ front) (drawnAll J m ds)
    (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks A.fits A.low
    A.groups (fun c => A.endOk (stretchOf c).e) A.asks
  have hd : (⟨0, dueRest J.p.nums.stages⟩ : Due) = ⟨0, dueFrom s (next :: nx' :: rest')⟩ := by
    rw [A.play.stages]
    rfl
  have hd' : (restSim Js).takes = ⟨0, dueFrom s (next :: nx' :: rest')⟩ := by
    show (⟨0, dueRest Js.stages⟩ : Due) = _
    unfold SimJob.stages
    rw [A.place, A.play.stages]
    rfl
  -- the left side
  have hL : (fun c : Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends =>
      σ.shows φ (restMember J Js) (c.1, c.2, ca) m ds asks) =
      (fun c : Cs ⟨0, dueRest J.p.nums.stages⟩ => some (realOwnT J.p s next (nx' :: rest')
        (laidS J.p) (J.recB m.st.input (restFront J m) (drawnAll J m ds 0))
        (rowsAt J (stretches _ ca) m) (carriedCoins J (stretches _ ca)).hide
        (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
        (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e)) ∘ Prod.fst := by
    funext c
    rw [shows_rest φ σ J Js s next (nx' :: rest') m (drawnAll J m ds) ds A.play (c.1, c.2, ca)
      asks]
    show some (shownFrom (restOf J m.st.input (restFront J m) (restCoins J (c.1, c.2, ca))
      (drawnAll J m ds) s next (nx' :: rest')) _ _ asks) =
      some (realOwnT _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    unfold restOf realOwnT
    rw [A.play.laid]
    rfl
  have hR : (fun c : Cs (restMember J Js : Member V W X Pb).sim.takes =>
      (restMember J Js : Member V W X Pb).tells φ c m.st.input front ds asks) =
      fun c : Cs (restSim Js).takes => some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
        (carriedCoins J (stretches _ ca)).hide (Js.trees₀ front) (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e) := funext fun c => tells_rest_own A c
  rw [hL, hR]
  refine (PMF.map_comp Prod.fst _ _).symm.trans ?_
  haveI : Nonempty (CsAll (restMember J Js : Member V W X Pb).part.spends) := ⟨default⟩
  haveI : Nonempty (Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends) := ⟨(default, default)⟩
  have hfst : (Prob.unif (Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends)).map Prod.fst =
      Prob.unif (Cs ⟨0, dueRest J.p.nums.stages⟩) := Prob.map_fst_unif
  refine (congrArg (PMF.map _) hfst).trans ?_
  have h2 := congrArg (PMF.map some) hlaw
  rw [PMF.map_comp, PMF.map_comp] at h2
  exact (map_stretch hd fun x => some (realOwnT J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
      (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks x)).trans
    (h2.trans (map_stretch hd' fun x => some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide (Js.trees₀ front) (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
      x)).symm)

/-! ## 2 At a written On that reads the part's own challenges in one clause -/


/-- **Both sides of `exact` at the second member are some**, at every coin, where what is asked holds. -/
theorem some_rest_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) (m : Mid W X) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List ℕ))) (s next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (A : AskedOwn J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks s next nx' rest') :
    (∀ c : Cs (restMember J Js : Member V W X Pb).part.takes ×
        CsAll (restMember J Js : Member V W X Pb).part.spends,
      ∃ v, σ.shows φ (restMember J Js) (c.1, c.2, ca) m ds asks = some v) ∧
    ∀ c : Cs (restMember J Js : Member V W X Pb).sim.takes,
      ∃ v, (restMember J Js : Member V W X Pb).tells φ c m.st.input front ds asks = some v :=
  ⟨fun c => ⟨_, shows_rest φ σ J Js s next (nx' :: rest') m (drawnAll J m ds) ds A.play (c.1, c.2, ca) asks⟩,
    fun c => ⟨_, tells_rest_own A c⟩⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.some_rest_own
#print axioms ProofFile.Honest.K12.AskedOwn
#print axioms ProofFile.Honest.K12.exact_rest_own
