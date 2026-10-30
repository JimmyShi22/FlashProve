-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Exact.lean: the frame's own sentence `exact` at a proximity
test's second member (`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean; the member and
its simulator's form: `restMember`, Sim/Row.lean; `restSim`, Sim/Sims.lean), at every `On` and `bud`
that give what is listed in `Asked`. It is stated at a state on entry that is made of the plan's
public part, not shown to be the verifier's. Conditional: whether an `On` that a chain's run meets
gives `Asked` is not shown; no property is claimed. General in the face φ (`Face`), the side σ, the
two jobs J and Js, the numbers chain and firstTree, `On` and `bud`. Sim/ExactPlan.lean calls
`exact_rest`. A definition, a structure and four theorems.

What it is. On the left: what the part shows, played alone by the frame's own play. On the right:
what the written simulator yields, of the public part of the input, of what is shown in front, of
the challenges, of the positions and of coins of its own. The two have one law.

Terms. A path that begins with K12/ is under Johnson/Desc/ProofFile/Honest/, one that begins with
Sim/ under Johnson/Desc/ProofFile/Honest/K12/. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean
with Side.lean in the same folder. Its sentence `exact` is a field of its structure `Good`, and
`ExactMember` is that field's text at one member. A side (`Side`) has a sub-protocol and a list of
the prover's parts (`Part`), each paired with a term of type `Sim`: the part's simulator's form. A
member (`Member`) is one part with its number in the list, its declared rounds and that term. `On`
and `bud` are parameters of `Good`: a condition at a part's start, and which positions may be read
at given challenges. What a part shows, played alone, is `Side.shows`; what its simulator yields is
`Member.tells`. A law is a distribution (`PMF`). A job J (`TestJob`, K12/Test.lean) is what a caller
supplies for its test, and Js (`SimJob`, Sim/Sims.lean) what it supplies for the simulators. The
place `J.p` (`P12`) holds the test's numbers, among them its list of stages (`Fmt.M1.Stage`). In
"facts on the plan" the plan is these numbers, the declared rounds that follow from them (`laidOf`),
and the jobs' fields on who sends the first fold's fresh table. The text is the Lean function that
computes the test's rounds (`testAll`, K12/Test.lean; from the first switch on `restText`,
Sim/Text.lean). The first part has the round "BAT" and the first fold's rounds (`firstLen`), the
second part all the others (`restLen`): the switches from each stage to the next, the later folds
and the base case. A reading round is a round whose challenge samples positions. In front of,
behind: before, after. The front (`Before`) is what a part's simulator is given of the run before
its part. Where the run stands is m (`Mid`), the state of a chain's run between two rounds. The
carried coins are the bound variable ca of `ExactMember`, of type `CsAll u.part.carries`; mem is
`stretches _ ca` (K12/Coins.lean), the same by number. A family of the part's coins is a function c
: ℕ → GE. pb is the public part of the input, ds the list of the second part's own challenges, asks
the positions. To be handed: to get as an argument.

  `exact_rest`: the statement: `ExactMember φ σ chain firstTree On bud (restMember J Js)`, under the
    hypothesis hA below; at a state on entry that is made of the plan's public part, not shown to be
    the verifier's
  `Asked`: a structure: what is asked, at carried coins, where the run stands, what is shown in
    front, the part's challenges and the positions. Its fields are listed under "Hypotheses"
  `drawnAll J m ds`: a definition: the test's challenges by number: the first part's as the state
    has heard them, then the second part's own
  `tells_rest`: what the simulator yields. Under `Asked`, at every c,
    `(restSim Js).tell pb front ds asks c` is `some` of `zeroOwn` (Sim/CoreOwn.lean) at colF and at
    `(stretchOf c).e`
  `entry_eq`: under `Asked`, `partEntry J mem m` (Sim/Row.lean) is `entryOf` (Sim/CoreLaw.lean) at
    the arguments at which `exact_rest` calls `core_inv`
  `map_stretch`: coins typed at two counts that are one. Where d = d' (`Due`), `Prob.unif (Cs d)`
    and `Prob.unif (Cs d')`, each mapped by `fun c => F (stretchOf c).e`, are equal

By what. Left: `shows_rest` (Sim/Shows.lean). Between: `core_inv` (Sim/ClaimBody.lean). Right: by
unfolding the simulator's text. Step by step: `exact_rest` takes `Asked` from hA. By `shows_rest` at
the field `play`, and by the fields `tree` and `play.laid`, the left side is `realOwn`
(Sim/CoreOwn.lean) composed with `Prod.fst` on `Cs takes × CsAll spends`; `Prob.map_fst_unif`
(Prob/Count.lean) rewrites `Prob.unif` of that product, mapped by `Prod.fst`, to `Prob.unif` of the
first factor. By `tells_rest` the right side is `zeroOwn`. `core_inv`, called at the fields `fits`,
`low`, `cols`, `behind` and `asks`, is the equation of `realOwn` and `zeroOwn` over `OwnCs`
(Sim/CoreOwn.lean), and `map_stretch` rewrites the two counts in the types to that of `OwnCs`.
`entry_eq` is by `aFold_congr` (Johnson/Desc/K12/Honest/Causal.lean). `tells_rest` unfolds
`restSim`, `restZeroText` and `zeroOwn`, and uses `entry_eq`, the fields `same`, `listed`, `place`,
`own`, `heard`, `count` and `play`, and `length_stages` (K12/TermLen.lean).

Hypotheses. `exact_rest` has one, hA: at every ca, m, front, ds and asks that meet
`On (restMember J Js) ca m front`, `m.seen = front.seen`, `drawsFit` and `front.holds` at the
member's rounds and ds, and `bud 1 ds asks`, there are s, next, nx', rest', colR and colF at which
`Asked J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks` holds. These are the hypotheses of
`ExactMember` at this member, whose number is 1, but for the one on `stopAt`, which the proof does
not use. What `Asked` holds, and how far it is from what a run gives.
  `same`: the verifier's state behind the first fold as the part's text makes it is the simulator's.
    Whole states are compared. By reading, no theorem: an honest run cannot meet this clause at the
    proof file's main test (why: Sim/Row.lean's head). In Lean:
    `partEntry J mem m = Js.entry pb front`
  `behind`: the invariant of the later stages holds behind the first switch, at every family of the
    part's coins and at the part's own challenges ds. `On` is not handed ds. From what it follows:
    `behind_of_coreB` (Sim/AllRest.lean), `behind_of_plan` (Sim/PlanLaw.lean); at an `On` no clause
    of which speaks of ds: Sim/ExactFree.lean. In Lean: `BehindFirst` (Sim/ClaimBody.lean), which
    unfolds to `BodyInv` (Johnson/Prover/Link/BodyInv.lean) from the second stage on
  `tree`, `listed`, `cols`: one tree in front, of the first stage's depth; the columns that the
    front lists are its own at the positions that the first reading round samples. In Lean:
    `J.trees₀` returns one tree, with the columns colR; `Js.trees₀ front` returns one tree, with the
    columns colF; colR and colF agree at the positions of `openedAt`
    (Johnson/LinkSim/AtText/SpecStage.lean)
  `asks`: the positions asked lie among those that the next reading round samples: narrower than
    `budRest` (Sim/Row.lean). That it gives `budRest` is by reading: no theorem. In Lean: of the
    first tree of the part's round number i, every position asked is in `openedTr`
    (Sim/CoreText.lean)
  `play`, `fits`, `low`, `count`, `place`, `own`, `heard`: public facts on the plan, on the
    challenges' form, and on where the run stands. One by one:
  `play`: `PlayTies` (Sim/Shows.lean) at `drawnAll J m ds` and ds; its field `stages` says that the
    place's stages are `s :: next :: nx' :: rest'`
  `fits`: `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean) from the first stage on, at
    `drawnAll J m ds`
  `low`: h ≤ k at every stage after the first
  `count`: `restLen` of the place's stages is 2 + `lenFrom next (nx' :: rest')` (K12/TermLen.lean)
  `place`: `Js.p = J.p`
  `own`: `Js.own = J.fresh.isNone`
  `heard`: the challenges of the last `firstLen` rounds that the front shows (`lastSeen`,
    Sim/Sims.lean) are the last `firstLen` that the state m has heard (`m.st.lately`)

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state function `J.rec₀` (K12/Test.lean) is a field of the free parameter J,
  and no field of `Asked` compares it with a verifier's state: `same` compares `partEntry J mem m`,
  which is computed from it, with `Js.entry pb front`, which is computed from `Js.rec₀`. "The
  verifier's state" in these comments names a value of type `T12` that is computed so.
- Conditional, as the first paragraph says. The limits at the fields `same`, `behind` and `asks`,
  and "one tree in front", are under "Hypotheses".
- It is shown at no job that is played: this file proves hA at no job.
- `Asked` has no value that meets it in the library. The library builds it in one place, inside the
  proof of `exact_plan` (Sim/ExactPlan.lean), from `OnPlan`, and it builds `OnPlan` from `OnFree`
  only (`onPlan_of_free`, Sim/ExactFree.lean). The statements that conclude `OnFree` take three of
  its clauses as premises (the limits of Sim/ExactFree.lean name them): by reading the files that
  name it.
- `behind` cannot be met at a place whose numbers say that the first fold sends its own table:
  `BehindFirst` is `BodyInv` at `PlanAll J.p` (Johnson/Prover/Link/BodyCloseB.lean), and `PlanAll`
  has the clause `PlanFrom` (Johnson/Prover/Link/FormStepPlan.lean), which asks
  `p.nums.ownMask = false`. At such a place no value meets `Asked`: hA can hold only where its own
  five conditions are never met together, and then `exact_rest` says nothing.
- It speaks of the parts of `proverSideOfProximityTest` (K12/Parts.lean), not of the guarded halves (`lightHalf`,
  K12/PartsBy.lean; `lightHalfOf`, K12/PartsByJob.lean).
- What the parts send is `testAll` (K12/Test.lean), cut into parts in K12/Parts.lean, over the
  random values of K12/Coins.lean. How far `testAll` is tied to the library's `bodyAll` is said in
  Test.lean's limits.
- Three stages or more, by the field `play`.
- An honest verifier; fixed challenges; one part.
- σ is a free parameter, and `restMember J Js` is the member as written out: that a side made by
  `testSide` (Sim/Row.lean) has it among its members is not shown here (`Spec.members`,
  Sim/Spec.lean: a definition; `members_of_seat`, Sim/ExactSide.lean: a theorem under hypotheses of
  its own, and not `Spec.members`).
- At the level of oracle messages: no root, salt or hash.
- Nothing on the first member, on `fresh`, on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Shows
import Johnson.Desc.ProofFile.Honest.K12.Sim.ClaimBody
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody openedAt)
open ProofFile.Honest.Small (ExactMember)

attribute [local instance] csNonempty

variable {S Cl V W X Pb : Type}

/-- The test's challenges by number: the first part's as the state has heard them, then the second
part's own. -/
def drawnAll (J : TestJob W X) (m : Mid W X) (ds : List Fmt.Drawn) (i : ℕ) : Fmt.Drawn :=
  if i < firstLen J.p.nums.stages then heardIn J m i
  else ds.getD (i - firstLen J.p.nums.stages) noDraw

/-- What is asked, at carried coins, where the run stands, what is shown in front, the part's
challenges and the positions. pb: the public part of the input. mem: the carried coins by number. s,
next, nx', rest': the place's stages. colR, colF: the columns of the one tree in front, as
`J.trees₀` and as `Js.trees₀` give them. The fields are described in this file's head, under
"Hypotheses". -/
structure Asked (J : TestJob W X) (Js : SimJob Pb) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (s next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage) (colR colF : ℕ → List UInt64) :
    Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  play : PlayTies J s next (nx' :: rest') m (drawnAll J m ds) ds
  count : restLen J.p.nums.stages = 2 + lenFrom next (nx' :: rest')
  behind : ∀ c : ℕ → GE, BehindFirst J.p s next (nx' :: rest') (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
    (carriedCoins J mem).hide colR (drawnAll J m ds) c
  tree : J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m) = [((sgOf s).C.a, colR)]
  listed : Js.trees₀ front = [((sgOf s).C.a, colF)]
  cols : ∀ x ∈ Fmt.listOf (openedAt (drawnAll J m ds) (next :: nx' :: rest') s 1), colR x = colF x
  fits : FitsBody (drawnAll J m ds) (next :: nx' :: rest') s 1
  low : ∀ st ∈ next :: nx' :: rest', st.h ≤ st.k
  asks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr (drawnAll J m ds) (next :: nx' :: rest') s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  same : partEntry J mem m = Js.entry pb front

/-- Coins typed at two counts that are one. Where d = d', `Prob.unif (Cs d)` and
`Prob.unif (Cs d')`, each mapped by `fun c => F (stretchOf c).e`, are equal. -/
theorem map_stretch {d d' : Due} (h : d = d') {α : Type} (F : (ℕ → GE) → α) :
    (Prob.unif (Cs d)).map (fun c => F (stretchOf c).e) =
      (Prob.unif (Cs d')).map fun c => F (stretchOf c).e := by
  subst h
  rfl

section At
variable {J : TestJob W X} {Js : SimJob Pb} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
  {front : Before} {ds : List Fmt.Drawn} {asks : List (List (List ℕ))}
  {s next nx' : Fmt.M1.Stage} {rest' : List Fmt.M1.Stage} {colR colF : ℕ → List UInt64}

/-- Under `Asked`, `partEntry J mem m` (Sim/Row.lean), the state behind the first fold, is `entryOf`
(Sim/CoreLaw.lean) at the arguments at which `exact_rest` calls `core_inv`. -/
theorem entry_eq (A : Asked J Js pb mem m front ds asks s next nx' rest' colR colF) :
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

/-- What the simulator yields. Under `Asked`, at every c, it is `some` of `zeroOwn`
(Sim/CoreOwn.lean) at colF and at `(stretchOf c).e`. -/
theorem tells_rest (A : Asked J Js pb mem m front ds asks s next nx' rest' colR colF)
    (c : Cs (restSim Js).takes) :
    (restSim Js).tell pb front ds asks c =
      some (zeroOwn J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
        (carriedCoins J mem).hide colF (drawnAll J m ds)
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
  unfold zeroOwn
  rw [← entry_eq A, A.same, A.listed, A.place, hl]
  have e2 : firstLen (s :: next :: nx' :: rest') = firstLen J.p.nums.stages := by
    rw [A.play.stages]
  simp only [hdep, e2]
  rfl

end At

/-- **The frame's sentence at the second member**, at every On and bud that give what is asked. It
is stated at a state on entry that is made of the plan's public part, not shown to be the
verifier's. -/
theorem exact_rest (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop)
    (hA : ∀ (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) m front ds asks,
      On (restMember J Js) ca m front → m.seen = front.seen →
      drawsFit ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      bud 1 ds asks →
      front.holds chain firstTree ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      ∃ s next nx' rest' colR colF, Asked J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks
        s next nx' rest' colR colF) :
    ExactMember φ σ chain firstTree On bud (restMember J Js) := by
  intro ca m front ds asks hOn hseen hfit hbud hholds _
  obtain ⟨s, next, nx', rest', colR, colF, A⟩ :=
    hA ca m front ds asks hOn hseen hfit hbud hholds
  have hlaw := core_inv J.p s next (nx' :: rest') (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
    (carriedCoins J (stretches _ ca)).hide colR colF (drawnAll J m ds)
    (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks A.fits A.low
    A.cols (fun c => A.behind (stretchOf c).e) A.asks
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
      (fun c : Cs ⟨0, dueRest J.p.nums.stages⟩ => some (realOwn J.p s next (nx' :: rest')
        (laidS J.p) (J.recB m.st.input (restFront J m) (drawnAll J m ds 0))
        (rowsAt J (stretches _ ca) m) (carriedCoins J (stretches _ ca)).hide colR (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e)) ∘ Prod.fst := by
    funext c
    rw [shows_rest φ σ J Js s next (nx' :: rest') m (drawnAll J m ds) ds A.play (c.1, c.2, ca)
      asks]
    show some (shownFrom (restOf J m.st.input (restFront J m) (restCoins J (c.1, c.2, ca))
      (drawnAll J m ds) s next (nx' :: rest')) _ _ asks) =
      some (realOwn _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    unfold restOf realOwn
    have ht : J.trees₀ m.st.input (restFront J m) (restCoins J (c.1, c.2, ca)).mem
        (J.first m.st.input (restFront J m) (restCoins J (c.1, c.2, ca))) =
        [((sgOf s).C.a, colR)] := A.tree
    rw [ht, A.play.laid]
    rfl
  have hR : (fun c : Cs (restMember J Js : Member V W X Pb).sim.takes =>
      (restMember J Js : Member V W X Pb).tells φ c m.st.input front ds asks) =
      fun c : Cs (restSim Js).takes => some (zeroOwn J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
        (carriedCoins J (stretches _ ca)).hide colF (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e) := funext fun c => tells_rest A c
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
  exact (map_stretch hd fun x => some (realOwn J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide colR (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks x)).trans
    (h2.trans (map_stretch hd' fun x => some (zeroOwn J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide colF (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
      x)).symm)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.map_stretch
#print axioms ProofFile.Honest.K12.entry_eq
#print axioms ProofFile.Honest.K12.tells_rest
#print axioms ProofFile.Honest.K12.exact_rest
#print axioms ProofFile.Honest.K12.drawnAll
#print axioms ProofFile.Honest.K12.Asked
