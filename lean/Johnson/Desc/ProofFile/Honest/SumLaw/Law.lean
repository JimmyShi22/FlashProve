-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Law.lean: THE LAW OF THE MASKED SUMCHECK's HONEST PART, FOR
EVERY CALL OF THE VERIFIER's FIRST TEXT: the proofs of four of the seven statements of
Honest/SumLaw/Statement.lean: `SumSays`, `SumHeard`, `SumClaim`, `SumLeft`. Statements with their
proofs. How. The part's rounds are written out (Honest/SumLaw/Out.lean); the verifier's reader
accepts them (Reads.lean); its fold over them ends at a walk plus eps times the summand's last
claim, and the walk is its own form on the hiding polynomial's coefficients (Walk.lean). The
ledger's side is the library's: `hear_spec`, `hear_returns_iff`, `row_value`, `ledger_own`,
`heard_lenK`, `hidingAt_val` (Johnson/Desc/Part/).
Main names:
  `draws_length`, `rounds_eq`, `epsOf_cons`, `varsOf_cons`: the challenges and the rounds.
  `claim_reads`: the last running claim, in the verifier's own form (`hidingAt`).
  `heard_spec`: what `hear` hands back on the part's rounds. `heard_target`: the target that it
    hands back is the public part of the claimed sum.
  `sumSays`, `sumHeard`, `sumClaim`, `sumLeft`: **the four.**

Limits. Those of Honest/SumLaw/Statement.lean. Nothing on soundness or on any property of a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Reads
import Johnson.Desc.ProofFile.Honest.SumLaw.Statement
import Johnson.Desc.Part.MaskedSumRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open OnBytes.Desc.First.P1 (hid psiProd)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-! ## The challenges and the rounds -/

/-- Challenges that pass `drawsOk` are as many as the part's moves. -/
theorem draws_length (name endName : String) (J : SumJob W X) (t : State W X) (seen : Seen)
    {ds : List Fmt.Drawn} (h : drawsOk (J.callAt t.input (frontOf t seen)) ds = true) :
    ds.length = (sumGs name endName J).length := by
  obtain ⟨d0, dv, dl, rfl, _, hv, _, hl⟩ := drawsOk_spec h
  rw [sumGs_length name endName J t.input (frontOf t seen), List.length_cons, List.length_append,
      hv]
  have hends : (J.callAt t.input (frontOf t seen)).ends = J.shape.ends := rfl
  rw [hends] at hl
  cases he : J.shape.ends with
  | none =>
    rw [he] at hl
    have hn : dl = [] := List.map_eq_nil_iff.1 hl
    rw [hn, List.length_nil, Option.isSome_none, if_neg Bool.false_ne_true]
    omega
  | some e =>
    rw [he] at hl
    have hn : dl.length = 1 := by
      have := congrArg List.length hl
      rw [List.length_map] at this
      exact this
    rw [hn, Option.isSome_some, if_pos rfl]
    omega

/-- The rounds of the part, played alone, are `sumOut`. -/
theorem rounds_eq {name endName : String} {J : SumJob W X} {c : SumCoins name endName J}
    {t : State W X} {seen : Seen} {ds : List Fmt.Drawn} {rounds : List Fmt.RoundView}
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds) :
    rounds = sumOut J c t seen ds := by
  rw [alone_sumPart name endName J c t seen ds (draws_length name endName J t seen hd)] at ha
  exact (Option.some.inj ha).symm

/-- The first challenge's element. -/
theorem epsOf_cons (d0 : Fmt.Drawn) (ds : List Fmt.Drawn) : epsOf (d0 :: ds) = elemOf d0 := rfl

/-- The variables' challenges' elements. -/
theorem varsOf_cons (k : Call) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hv : dv.length = k.all.length) : varsOf k (d0 :: (dv ++ dl)) = dv.map elemOf := by
  show ((dv ++ dl).map elemOf).take k.all.length = _
  rw [List.map_append, ← hv, ← List.length_map (f := elemOf) (as := dv), List.take_left]

/-! ## The last running claim -/

/-- **The last running claim, in the verifier's own form.** -/
theorem claim_reads {name endName : String} (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (d0 : Fmt.Drawn) (dv : List Fmt.Drawn)
    (hs : shapeOk (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length) (T : E) (σ cf : GE)
    (hS : SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
      (jobPoly J t.input (frontOf t seen) (endRun c)) [] (dv.map elemOf) σ cf) :
    Reading.gl.val (after (J.callAt t.input (frontOf t seen)).all (readOf J c t seen d0 dv).rounds
        (addE (readOf J c t seen d0 dv).mu (mulE (readOf J c t seen d0 dv).eps T))) =
      dotFrom Reading.gl (hidingCoin c)
          (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 +
        Reading.gl.val (elemOf d0) * cf +
        Reading.gl.val (elemOf d0) * (Reading.gl.val T - σ) *
          Reading.gl.val
            (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).2 := by
  have h2 := all_two hs
  have hfst := sharesOf_fst J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)
  have key := after_reads Reading.gl canon canon_gl (elemOf d0)
    (jobPoly J t.input (frontOf t seen) (endRun c))
    (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
    (dv.map elemOf)
    (addE (canon (tailSum (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all
      (firstRun c)))) (mulE (elemOf d0) T))
    (Reading.gl.val (elemOf d0) * (Reading.gl.val T - σ)) σ cf
    (wOf_sizes _ _ h2)
    (by
      rw [Reading.gl.add, Reading.gl.mul, canon_gl, Reading.gl.zero]
      ring)
    (by rw [hfst]; exact hS)
  rw [hfst] at key
  have hw := walk_hiding Reading.gl (J.callAt t.input (frontOf t seen)).all
    ((firstRun c).drop J.shape.lead) (dv.map elemOf)
    (Reading.gl.val zeroE + Reading.gl.val (elemOf d0) * (Reading.gl.val T - σ)) (hidingCoin c)
    (by rw [List.length_map, hv]) (fun j => by rw [getD_drop]; rfl)
  show Reading.gl.val (after _ (sentRounds canon (elemOf d0) _ _ zeroE [] (dv.map elemOf))
    (addE (canon _) (mulE (elemOf d0) T))) = _
  rw [key]
  show walkK Reading.gl ((J.callAt t.input (frontOf t seen)).all.zip
    (wOf (J.callAt t.input (frontOf t seen)).all ((firstRun c).drop J.shape.lead))) _ _ + _ = _
  rw [hw, Reading.gl.zero]
  ring

/-- **What `hear` hands back on the part's rounds**: its first component, h. T is the field `target`
of h. Two things are not said here. That T is the public part of the claimed sum: `heard_target`,
below. And anything on G, the ledger that is handed back. -/
theorem heard_spec {name endName : String} {J : SumJob W X} {c : SumCoins name endName J}
    {t : State W X} {seen : Seen} {ds : List Fmt.Drawn} {rounds : List Fmt.RoundView} {C : Aff}
    {F G : Fork} {h : Heard} (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds)
    (hh : hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G)) :
    ∃ (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn) (T : E), ds = d0 :: (dv ++ dl) ∧
      dv.length = (J.callAt t.input (frontOf t seen)).all.length ∧
      shapeOk (J.callAt t.input (frontOf t seen)) = true ∧
      readAll (J.callAt t.input (frontOf t seen)) rounds = some (readOf J c t seen d0 dv) ∧
      h = { start := C, target := T, eps := elemOf d0,
            claim := after (J.callAt t.input (frontOf t seen)).all (readOf J c t seen d0 dv).rounds
              (addE (readOf J c t seen d0 dv).mu (mulE (readOf J c t seen d0 dv).eps T)),
            first := F.next, vars := (J.callAt t.input (frontOf t seen)).all, r := dv.map elemOf,
            sEnd := F.next + ownSlots (J.callAt t.input (frontOf t seen)).all } := by
  obtain ⟨hs, T, R, _, hR, he, _⟩ := hear_spec hh
  obtain ⟨d0, dv, dl, rfl, h0, hv, h1, hl⟩ := drawsOk_spec hd
  have hr := rounds_eq hd ha
  have hread := readAll_sumOut J c t seen d0 dv dl hs h0 hv h1 hl
  rw [← hr, hR] at hread
  have hRR : R = readOf J c t seen d0 dv := Option.some.inj hread
  refine ⟨d0, dv, dl, T, rfl, hv, hs, by rw [hR, hRR], ?_⟩
  rw [he, hRR]
  have hc : (readOf J c t seen d0 dv).rounds.map (·.2) = dv.map elemOf :=
    sentRounds_chal canon _ _ _ _ _ _ (by rw [sharesOf_length, List.length_map, hv])
  rw [hc]
  rfl

/-- **The target that `hear` hands back is the public part of the claimed sum, at F, the ledger that
`hear` is given.** General in the call and the rounds. With the equation on h in `heard_spec` it
says of that statement's T: `F.publicPart C = some T`. Kin: the library's `heard_front`
(Johnson/Desc/Part/MaskedSumJoint.lean) has this as its second conjunct, from the same premise; that
file is not imported here. -/
theorem heard_target {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) : F.publicPart C = some h.target := by
  obtain ⟨_, T, R, hT, _, he, _⟩ := hear_spec hh
  rw [he]
  exact hT

/-! ## The four -/

/-- Played alone, all moves of the part answer: the proof of `SumSays`. -/
theorem sumSays : SumSays := by
  intro V W X name endName J c t seen ds hd
  exact ⟨_, alone_sumPart name endName J c t seen ds (draws_length name endName J t seen hd)⟩

/-- The verifier's `hear` accepts the part's rounds at a ready ledger: the proof of `SumHeard`. -/
theorem sumHeard : SumHeard := by
  intro V W X name endName J c t seen ds rounds C F hs hd ha hL
  obtain ⟨d0, dv, dl, rfl, h0, hv, h1, hl⟩ := drawsOk_spec hd
  have hr := rounds_eq hd ha
  have hread := readAll_sumOut J c t seen d0 dv dl hs h0 hv h1 hl
  rw [← hr] at hread
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
    ((hear_returns_iff hL rounds).2 ⟨hs, by rw [hread]; rfl⟩)
  exact ⟨y.1, y.2, hy⟩

/-- **What the last running claim reads as: the proof of `SumClaim`.** -/
theorem sumClaim : SumClaim := by
  intro V W X name endName J c t seen ds rounds C F G h hd ha hh
  obtain ⟨d0, dv, dl, T, rfl, hv, hs, _, rfl⟩ := heard_spec hd ha hh
  refine ⟨rfl, (varsOf_cons _ d0 dv dl hv).symm, fun σ cf hS => ?_⟩
  have hc := claim_reads J c t seen d0 dv hs hv T σ cf hS
  have hlens : Lens (J.callAt t.input (frontOf t seen)).all (readOf J c t seen d0 dv).rounds := by
    have := sentRounds_lens canon (elemOf d0) (jobPoly J t.input (frontOf t seen) (endRun c))
      (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
      (dv.map elemOf) (fun x hx => (wOf_sizes _ _ (all_two hs) x hx).1)
      (by rw [sharesOf_length, List.length_map, hv])
    rw [sharesOf_fst] at this
    exact this
  have hch : (readOf J c t seen d0 dv).rounds.map (·.2) = dv.map elemOf :=
    sentRounds_chal canon _ _ _ _ _ _ (by rw [sharesOf_length, List.length_map, hv])
  obtain ⟨hu1, hu2⟩ := hidingAt_val Reading.gl
    ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf)) (hidingCoin c)
  have e1 := zip_wt Reading.gl _ _ hlens
  have e2 := zip_val Reading.gl _ _ hlens
  rw [hch] at e1 e2
  rw [e1, e2] at hu1 hu2
  show Reading.gl.val (after _ _ _) = _
  rw [hc, hu1, hu2]

/-- What the claim that `row` leaves is worth on the hidden values: the proof of `SumLeft`. -/
theorem sumLeft : SumLeft := by
  intro V W X name endName J c t seen ds rounds C F G F' G' H h S0 kept f mask entry cf hd ha hh
    hF' hr hl hm hS
  have hown := ledger_own Reading.gl mask entry hh hF' hr hl
  obtain ⟨_, _, hlen⟩ := heard_lenK hh
  have hval := row_value Reading.gl (H.worldOf Reading.gl mask entry) hr
  obtain ⟨d0, dv, dl, T, rfl, hv, hs, _, rfl⟩ := heard_spec hd ha hh
  have hc := claim_reads J c t seen d0 dv hs hv T _ cf hS
  have hdot : dotFrom Reading.gl (fun i => (H.worldOf Reading.gl mask entry).slot (F.next + i))
      (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 =
      dotFrom Reading.gl (hidingCoin c)
        (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 :=
    dotFrom_congr Reading.gl _ _ _ fun i hi => by
      have hi' : i < ownSlots (J.callAt t.input (frontOf t seen)).all := by
        rw [← hlen]
        exact hi
      rw [← hm i hi']
      exact hown i hi'
  rw [hval]
  show dotFrom Reading.gl (fun i => (H.worldOf Reading.gl mask entry).slot (F.next + i))
      (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 +
      Reading.gl.val (elemOf d0) *
        Reading.gl.val (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).2 *
        (Reading.gl.val T - C.value Reading.gl (H.worldOf Reading.gl mask entry)) +
      Reading.gl.val (elemOf d0) * kept.value Reading.gl (H.worldOf Reading.gl mask entry) -
      (Reading.gl.val (after _ _ _) - Reading.gl.val (elemOf d0) * Reading.gl.val S0) = _
  rw [hdot, hc]
  show _ = Reading.gl.val (elemOf d0) * _
  ring

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.draws_length
#print axioms ProofFile.Honest.SumLaw.rounds_eq
#print axioms ProofFile.Honest.SumLaw.epsOf_cons
#print axioms ProofFile.Honest.SumLaw.varsOf_cons
#print axioms ProofFile.Honest.SumLaw.claim_reads
#print axioms ProofFile.Honest.SumLaw.heard_spec
#print axioms ProofFile.Honest.SumLaw.heard_target
#print axioms ProofFile.Honest.SumLaw.sumSays
#print axioms ProofFile.Honest.SumLaw.sumHeard
#print axioms ProofFile.Honest.SumLaw.sumClaim
#print axioms ProofFile.Honest.SumLaw.sumLeft
