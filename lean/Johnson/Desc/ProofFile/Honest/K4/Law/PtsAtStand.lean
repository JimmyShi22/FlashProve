-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsAtStand.lean: CONDITIONAL.

Not shown here. No property is claimed. THAT THE PREMISES CAN BE MET: no example is known. THAT A
MAKER RETURNS, that a cube's sizes fit, that the embedding's claim is there: these are taken as
hypotheses and handed through. Equations between machine words: nothing on what a sampled value is
used for. No statement here calls `K4Seated.fits`: they hold at shapes that do not fit too. Nothing
on soundness, on completeness or on any other property.

What is here: "the sampled values are the verifier's", at a stand (`K4Stand`, Law/SlotsTrue.lean):
behind the step of the member of the layers' own rounds (the sub-protocol K4) on what the honest row
has played. Other files say it of a return of the verifier's hearing, in the form of the library's
`LedG` (Johnson/Road/K4/OwnLedgersG.lean), on a tape that has sampled what the challenges hold
(`DrawnIs`, Law/PtsNorms.lean): Law/PtsHear.lean, Law/PtsAt.lean; Law/W/AtOfLed.lean fills three
structures of hypotheses from it. HERE THESE PREMISES ARE SHOWN AT A STAND (`stand_led`), and the
four structures that the statements on the honest words take as hypotheses are filled there: three
by calls, one (`PtsAre`) field by field. Statements with their proofs.

THE PREMISES: `K4Stand`; and, where a statement reads a field of `ptsOf`
(Johnson/Desc/K4/Honest/Front.lean), `Thr`, the thread's own proposition on a stand
(Honest/Thread/Thr.lean), for one number: as many challenges have been heard in front of the member
as the public data count; in `stackAt_at` besides `K4LookTieAt` (Law/ScriptAt.lean), of which one
field is read: the lookup's point.

  `stand_drawn`   the tape of the played rounds has sampled what the challenges hold
  `k4_moves_merge`, `stand_reach`   the member's challenges reach the merge's first round
  `StandLed`, `stand_led`   **`LedG` at a stand**, at what the step has heard of the lookup, with
      `DrawnIs`, the challenges' reach, the group and the layout beside it, as one structure
  `jobSquares_cube`, `jobRows_cube`, `claimEnv_layout`   the two norms' jobs' cubes: variables,
      order, sizes; the layout in the list of weight claims' environment is the public data's
  `stand_zx`   the lookup's point, as the honest side's reader of the lookup makes it, is the one
      that the step has heard
  `ptsAre_at`   **`PtsAre`** (Law/W/RightNorms.lean), whole
  `gatedAt_at`, `embAt_at`, `stackAt_at`   **`GatedAt`**, **`EmbAt`** (Law/W/RightGated.lean; the
      second in the first group of layers), **`StackAt`** (Law/W/RightStack.lean): calls of
      `gatedAt_of_led`, `embAt_of_led`, `stackAt_of_led`

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightNorms
import Johnson.Desc.ProofFile.Honest.K4.Law.W.AtOfLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Fork Level Tsc orderDefault orderRange WsClaim)
open OnBytes.Model.Layer (Own ClaimEnv downFrom)
open OnBytes.K.Kc (Tape paired)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (Par entries seatS k0 hear engFl hear_parts)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4 (LedG own_ledG)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.K4.W (PtsAre GatedAt EmbAt StackAt pts4 pts5 pts6 ptsE gatedAt_of_led embAt_of_led
  stackAt_of_led)

/-! ## 1 The premises of the statements on a hearing's return, at a stand -/

/-- **The tape of the played rounds has sampled what the challenges hold.** -/
theorem stand_drawn {W Z : Type} {l : List (Step W Z)} {ds : List Fmt.Drawn} {m : Mid W Z}
    {y : List Played × Mid W Z} (hy : play l ds [] m = .ok y) (es : List Fmt.Entry) :
    DrawnIs (paired (roundsOf y.1) es) ds := by
  intro n d hd
  have q := played_drawn hy n
  rw [hd] at q
  rw [paired_drawn]
  cases hr : (roundsOf y.1)[n]? with
  | none =>
    rw [hr] at q
    cases q
  | some r =>
    rw [hr] at q
    obtain rfl : r.drawn = d := Option.some.inj q
    rfl

/-- The rounds in front of the merge's part. -/
theorem k4_moves_merge (Q : K4Pub) :
    movesTo (k4RowIn Q) (k0 Q.g + 15) = rE Q.P Q.hp Q.g + 1 := by
  have m15 := k4_moves_at Q 15
  rw [k4Tail_moves] at m15
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at m15
  unfold rE rJ6 rJ5 rJ4 rJ3 rJ2 rowsRound
  omega

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **The member's challenges reach the merge's first round.** -/
theorem stand_reach
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    k4StartAt Q 6 ≤ ds.length := by
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  have h := sum_rounds_there Pl (k0 Q.g + 15) _ _ _ (k4RowIn_at Q 15) ⟨1, 1⟩ rfl
  rw [k4_moves_merge, ← (k4StartAt_eq Q).2.2.2.2.2.2] at h
  omega

/-- **What the statements on a hearing's return ask, at a stand**: the library's `LedG` at what the
step has heard, of the lookup too, on a tape t; t has sampled what the member's challenges hold;
these reach the merge's first round; the group and the layout that were heard are the public data's.
hd2, tT: the second gated level and the second token sumcheck as they were heard. It is a
definition. -/
structure StandLed (Q : K4Pub) (tk : Array Nat) (o : Own) (ds : List Fmt.Drawn) (hd2 : Level)
    (tT : Tsc) : Prop where
  led : ∃ (F G : Fork) (t u : Tape) (H1 : OnBytes.Model.Layer.Heard)
    (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : Tape),
    LedG { Q.P with tokv := tk } Q.hp Q.g o.H.fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5 ∧ DrawnIs t ds
  reach : k4StartAt Q 6 ≤ ds.length
  group : o.v.g = Q.g
  layout : o.v.y = Q.P.y

/-- **A stand gives it.** -/
theorem stand_led
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ∃ hd2 tT, StandLed Q s.tokv o ds hd2 tT := by
  obtain ⟨a, a₀, fo, _, ha0, haF, _, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have hSd : Sized a.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  have h' : hear engFl { Q.P with tokv := s.tokv } Q.hp Q.g fo a.F
      (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) = some (o, A.F, []) := hh
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hSd h'
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  obtain ⟨_, hy1, _, hg1, _⟩ := hear_parts h'
  obtain rfl : o.H.fo = fo := led_fo L
  exact ⟨hd2, tT, ⟨_, _, _, _, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L,
    stand_drawn hy _⟩, stand_reach Z, hg1, hy1⟩

/-! ## 2 The norms' two jobs' cubes -/

/-- The squares' job's cube: its variables and their order. -/
theorem jobSquares_cube {Q : K4Pub} {w : K4In} {q : Pts} {J : Job}
    (h : jobSquares Q w q = some J) :
    J.cube.n = Q.P.rd.muV ∧ J.cube.order = orderDefault Q.P.rd.muV := by
  unfold jobSquares at h
  simp only at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · cases h

/-- The row products' job's cube: its sizes fit; its variables and their order. -/
theorem jobRows_cube {Q : K4Pub} {w : K4In} {q : Pts} {J : Job} (h : jobRows Q w q = some J) :
    J.cube.fits = true ∧ J.cube.n = Q.P.y.h.lt ∧ J.cube.order = orderDefault Q.P.y.h.lt := by
  rw [jobRows_eq] at h
  obtain ⟨ms, _, h2⟩ := Option.bind_eq_some_iff.1 h
  split at h2
  · rename_i hf
    obtain rfl := Option.some.inj h2
    exact ⟨hf, rfl, rfl⟩
  · cases h2

/-! ## 3 The four structures -/

/-- **THE SAMPLED VALUES THAT THE NORMS' MAKERS READ ARE THOSE THAT THE STEP HAS HEARD**: `PtsAre`,
whole, at every small input w. CONDITIONAL on the stand and on `Thr` there. -/
theorem ptsAre_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (w : K4In) : PtsAre Q w m.st.heard ds o := by
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    _⟩ := stand_led Z
  have hh : m.st.heard.length = Q.r0 := k4_heard_front Z.seat hT
  obtain ⟨e0, e1, e2, _, _, _, _⟩ := k4StartAt_eq Q
  obtain ⟨l1, l2, _, _, _, _⟩ := stand_lens Z
  have s6 : k4StartAt Q 1 ≤ k4StartAt Q 6 ∧ k4StartAt Q 2 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  have hl1 : k4StartAt Q 1 ≤ ds.length := Nat.le_trans s6.1 hr
  have hl2 : k4StartAt Q 2 ≤ ds.length := Nat.le_trans s6.2 hr
  have hk0 : 0 < k0 Q.g := by
    rcases k0_cases Q.g with ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] <;> omega
  refine
    { PV0 := at_PV w _ L ds hD hl1 hh _ hk0
      gp := at_gp w _ L ds hD hl1 hh _ (by unfold rJ1; omega)
      r6 := fun J hJ => ?_
      PV1 := at_PV w _ L ds hD hl1 hh _ (by unfold rowsRound; omega)
      rtV := fun J hJ => ?_
      PV2 := at_PV w _ L ds hD hl1 hh _ (by unfold rJ2; omega)
      omV := at_omV w _ L ds hD hl1 hh _ (by rw [e1])
      fo := ?_ }
  · obtain ⟨c1, c2⟩ := jobSquares_cube hJ
    rw [pointOf_levelR, c1, c2, led_r6 L ds hD hl1, e0]
    rfl
  · obtain ⟨c0, c1, c2⟩ := jobRows_cube hJ
    rw [OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_default J.cube c0 (by rw [c2, c1]) _
      (by rw [c1]; exact l2), led_rtV L ds hD hl2, e1]
    rfl
  · rw [pts_fo_val, pts_fo_val, ← hh, List.take_left, List.take_left]

/-- **THE TWO GATED LEVELS' CHALLENGES, LAID AS POINTS, ARE THOSE THAT THE STEP HAS HEARD**:
`GatedAt`: its two lengths and its two points; that the tables are there and the cubes' sizes fit is
handed through. CONDITIONAL on the stand. -/
theorem gatedAt_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (w : K4In) {tb1 tb2 : Tab × Tab} (t1 : gatedTabs Q w = some tb1)
    (t2 : gatedTabs2 Q w = some tb2)
    (fit1 : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (pts5 Q w m.st.heard ds).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (pts5 Q w m.st.heard ds)) tb1).cube.fits = true)
    (fit2 : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((pts6 Q w m.st.heard ds).rhoM ++ downFrom (pts6 Q w m.st.heard ds).rs Q.P.y.lfe ++
        (pts6 Q w m.st.heard ds).rt) tb2).cube.fits = true) :
    GatedAt Q w m.st.heard ds o tb1 tb2 := by
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    _⟩ := stand_led Z
  exact gatedAt_of_led L hD hr t1 t2 fit1 fit2

/-- The layout in the environment of the list of weight claims is the public data's. -/
theorem claimEnv_layout {Q : K4Pub} {q : Pts} {ce : ClaimEnv} (env : claimEnvOf Q q = some ce) :
    ce.v.y = Q.P.y := by
  unfold claimEnvOf at env
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 env
  unfold OnBytes.Desc.First.K4.Honest.envOf at hv
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hv
  obtain ⟨_, _, _, _, hv⟩ := hv
  obtain rfl := Option.some.inj hv
  rfl

/-- **THE EMBEDDING's TWO POINTS ARE THOSE THAT THE STEP HAS HEARD**, in the first group of layers:
`EmbAt`: its group, its layout and its two points; that the claim is there is handed through.
CONDITIONAL on the stand and on `Thr` there. -/
theorem embAt_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hg : (Q.g == 0) = true) (w : K4In) {ce : ClaimEnv} {cl : WsClaim}
    (env : claimEnvOf Q (ptsE Q w m.st.heard ds) = some ce)
    (claim : ce.claimE (ptsE Q w m.st.heard ds).ZE (ptsE Q w m.st.heard ds).tkh Q.P.V w.tokv =
      some cl) : EmbAt Q w m.st.heard ds o ce cl := by
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, hgo,
    hyo⟩ := stand_led Z
  have h3 : 3 ≤ ds.length := by
    have h6 : 3 ≤ k4StartAt Q 6 := by
      simp only [k4StartAt]
      omega
    omega
  exact embAt_of_led L hD h3 hg (k4_heard_front Z.seat hT) env claim hgo
    ((claimEnv_layout env).trans hyo.symm)

/-- **The lookup's point, as the honest side's reader of the lookup makes it, is the one that the
step has heard.** CONDITIONAL on the stand and on the tie at it. -/
theorem stand_zx
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hLk : K4LookTieAt look Q s m) : (look Q m.st.heard).zx = o.H.fo.zx := by
  obtain ⟨g, _, h2, hz, _, _⟩ := hLk
  have h := stand_look Z
  rw [h2] at h
  obtain rfl := Option.some.inj h
  exact hz

/-- **THE BATCHED SUMCHECK's CHALLENGES AND THE POINTS THAT ITS JOB READS ARE THOSE THAT THE STEP
HAS HEARD**: `StackAt`, at the small input that the row reads; that the job's data and its end
values are there is handed through. CONDITIONAL on the stand, on `Thr` and on `K4LookTieAt` there.
-/
theorem stackAt_at
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) {seen : Seen} {SD : StackData}
    {e : List OnBytes.E}
    (data : stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds)
      (k4SentAt seen.rounds (k4TermsEnds Q)) = some SD)
    (ends : SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e) :
    StackAt Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds seen o SD e := by
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    hyo⟩ := stand_led Z
  have s6 : k4StartAt Q 4 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  exact stackAt_of_led L hD (Nat.le_trans s6 hr) (k4_heard_front Z.seat hT) (stand_zx Z hLk) data
    ends hyo

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stand_drawn
#print axioms ProofFile.Honest.K4.k4_moves_merge
#print axioms ProofFile.Honest.K4.stand_reach
#print axioms ProofFile.Honest.K4.stand_led
#print axioms ProofFile.Honest.K4.jobSquares_cube
#print axioms ProofFile.Honest.K4.jobRows_cube
#print axioms ProofFile.Honest.K4.ptsAre_at
#print axioms ProofFile.Honest.K4.gatedAt_at
#print axioms ProofFile.Honest.K4.claimEnv_layout
#print axioms ProofFile.Honest.K4.embAt_at
#print axioms ProofFile.Honest.K4.stand_zx
#print axioms ProofFile.Honest.K4.stackAt_at
