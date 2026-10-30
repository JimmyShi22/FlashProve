-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatStack.lean: CONDITIONAL.

What is here. The batched sumcheck of the feed-forward layers' rounds: the verifier's flat text
(`hearStack`, OnBytes/Desc/First/K4/Hear.lean) against the part's text of the masked sumcheck
(`hear`, Johnson/Desc/Part/MaskedSum.lean), and what the sumcheck's own claim is worth on the honest
part's rounds.

What is shown. Where both texts return on the same rounds, the flat text's state has the letters of
what `hear` hands back; the values that the flat text lays under the end slots are the last round's
scalars, and are what the library calls `stackVals`; the verifier's challenges by bit are the
state's first challenges reversed. With the masked sumcheck's law: the own claim (`HeardStack.rowS`)
is worth the sumcheck's first challenge (the tape's second: the batching round stands first) times
(the verifier's summand on the values that it was shown, less the job's summand on the end values as
sent). Statements and proofs.

  `stack_sameLetters`   the two texts
  `stack_start`, `stack_ready`   the start form is made; the ledger is ready for the part's text:
     the window is laid inside the flat text
  `stack_worth`   **the own claim's worth**
  `stack_zero`   **it is 0** where the verifier's summand on the shown values reads as the job's on
     the sent ones

Limits. At the reading `Reading.gl` from § 2 on. THE START IS A PREMISE (hσ: the start form is worth
the reading of the cube's total): it holds the lookup's join and the second token sumcheck's form.
FIVE PREMISES ON THE JOB beside that it fits its call: its degree in the further variable is 2
(hdY); at as many challenges as the cube has variables it has as many end values as the call says
(hn); along the masked line its summand is a polynomial of that degree (hP); it reads its values
through the reading (hA); on the true end values its summand is the cube's (hE). None of the five is
shown here: StackCube.lean has the first four of the honest job from its fitting the call, and hE
with Johnson/Road/K4/C/StackTrue.lean. THAT THE VERIFIER's TWO NUMBERS ARE THE HONEST SIDE's ON THE
SAME VALUES IS A PREMISE OF `stack_zero` (hfin): it asks that the panels, the challenges and the two
weights of the two sides be one. The job is a free letter: that it is the row's is not said here. No
example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatWindow
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Desc.First.K4.StackEnded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE mulE addE)
open OnBytes.Model (Reading Aff Fork World powers)
open OnBytes.Model.Layer (HeardStack)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.P1 (plainWs endP_spec tapeEps filledA_of_publicPart walk_length)
open OnBytes.Desc.First.K4 (engFl hearStack hearStack_tape)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-! ## 1 The two texts -/

/-- **Where both texts return on the same rounds.** C: the start form. t: the tape, the batching
round first. p: the flat text's state; the own claim is p's form on the verifier's summand. vals:
the values that the flat text lays under the end slots, from K.sA0 on, at the last challenge beta:
they are the library's `stackVals`. The verifier's challenges by bit are p's first lamS challenges
reversed; p's first challenge is the one that the tape's second round has sampled. Where `hear`
returns on the tape's rounds, p has the letters of what it hands back, and
the last round's scalars are vals. -/
theorem stack_sameLetters {P : OnBytes.Model.Layer.Pub} {v : OnBytes.Model.Layer.Env}
    {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ}
    {F G G' : Fork} {t u : Tape} {K : HeardStack}
    (hF : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) (vs : List Var)
    (hk : vs.map Var.weight = plainWs lamS) {rounds : List Fmt.RoundView} {h : Heard} :
    ∃ (C : Aff) (p : OnBytes.Model.Psc) (vals : Array E) (G1 : Fork) (beta : E),
      OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps t) 2) F (t.drop 1) =
        some (C, F, t.drop 1) ∧
      K.rowS = p.rowForm (mulE K.fin.As K.fin.Bs) {} ∧
      vals.size = 2 + (1 + P.y.LamM) + NCLp ∧
      vals.toList = OnBytes.Desc.First.K4.stackVals lamS t ∧
      ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork).hideRun
        K.sA0 vals beta = some G1 ∧
      K.rs.toList = (p.r.toList.take lamS).reverse ∧
      p.eps = tapeEps (t.drop 1) ∧
      G1.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧
      (hear C ⟨0, vs, some ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩⟩ F rounds = some (h, G') →
        TapeIs (t.drop 1) rounds →
        SameLetters p h ∧
          ∃ rv, rounds.getLast? = some rv ∧ scalars rv.vals = some vals.toList) := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, hrs, _, hC, hTp,
    hms, hyy, hp, a1, _, _, hKrs, _, _, _, _, hvs, hrun, hrow, hwin⟩ := hearStack_tape hF
  have ex : tapeEps t = x := by
    rw [ht]
    rfl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } ms y
  rw [← hp] at e1 e2 e3 e4 e5 e6 e7
  have hml : (ms.map (·.2.2)).length = lamS := by
    have e := congrArg List.length a1
    rw [List.length_map, plainWs, List.length_replicate] at e
    rw [List.length_map]
    exact e
  have hv : vals.toList = OnBytes.Desc.First.K4.stackVals lamS t := by
    unfold OnBytes.Desc.First.K4.stackVals
    rw [ht, ← hrs]
    show _ = OnBytes.Desc.First.P1.sentOf ((_ :: _ :: (rs ++ _ :: _ :: u)).drop (rs.length + 3))
    rw [show rs.length + 3 = (rs.length + 2) + 1 from rfl, List.drop_succ_cons,
      OnBytes.Desc.First.P1.drop_second]
    rfl
  have hr' : K.rs.toList = (p.r.toList.take lamS).reverse := by
    rw [hKrs, e2, List.map_append]
    show _ = (([] ++ (ms.map (fun m : OnBytes.Desc.First.P1.Rnd => m.2.2) ++
      [y].map (fun m : OnBytes.Desc.First.P1.Rnd => m.2.2))).take lamS).reverse
    rw [List.nil_append, ← hml, List.take_left]
  have hpe : p.eps = tapeEps (t.drop 1) := by
    rw [e6, ht]
    rfl
  refine ⟨C, p, vals, G1, beta, by rw [ex]; exact hC, hrow, hvs, hv, hrun, hr', hpe, hwin,
    fun hh hT => ?_⟩
  have ht1 : t.drop 1 = ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, w1, [] ++ [mu0], [eps]⟩ ::
      (rs ++ ⟨some OnBytes.Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
        ⟨some OnBytes.Model.RoundName.pscValues.name, 0, wV, vals.toList, []⟩ :: u) := by
    rw [ht]
    rfl
  rw [hms] at a1
  exact sameLetters_of_tape (front := []) (dY := 2) (n := 2 + (1 + P.y.LamM) + NCLp) ht1
    (by rw [plainWs, List.length_replicate, hrs]) a1
    (by rw [e1, hms, hyy, List.map_append, a1]; rfl)
    (by rw [e2, hms, hyy]; rfl) (by rw [e3, hms, hyy]) e5 e6 e4 e7 hTp vs hk hh hT

/-- The start form is made. -/
theorem stack_start {P : OnBytes.Model.Layer.Pub} {v : OnBytes.Model.Layer.Env}
    {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ}
    {F G : Fork} {t u : Tape} {K : HeardStack}
    (hF : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ C, OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps t) 2) F (t.drop 1) =
      some (C, F, t.drop 1) := by
  obtain ⟨x, _, _, _, _, _, _, _, _, _, _, C, _, _, _, _, ht, _, _, hC, _⟩ := hearStack_tape hF
  have ex : tapeEps t = x := by
    rw [ht]
    rfl
  exact ⟨C, by rw [ex]; exact hC⟩

/-- **The ledger is ready for the part's text**: the flat text lays the sumcheck's own slots itself,
behind the end values: that this laying returns says that they were free. -/
theorem stack_ready {P : OnBytes.Model.Layer.Pub} {v : OnBytes.Model.Layer.Env}
    {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ}
    {F G : Fork} {t u : Tape} {K : HeardStack}
    (hF : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) (hS : Sized F) (vs : List Var)
    (hk : vs.map Var.weight = plainWs lamS) {C : Aff}
    (hC : OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps t) 2) F (t.drop 1) =
      some (C, F, t.drop 1)) :
    LedgerReady C ⟨0, vs, some ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩⟩ F := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C', G1, ms, y, p, ht, hrs, _, hC',
    hTp, hms, hyy, hp, a1, hheld, _, _, hsA, _, _, _, hvs, hrun, _, hwin⟩ := hearStack_tape hF
  have ex : tapeEps t = x := by
    rw [ht]
    rfl
  have eC : C' = C := by
    rw [ex, hC'] at hC
    exact (congrArg Prod.fst (Option.some.inj hC))
  rw [eC] at hTp hp
  obtain ⟨e1, e2, _, _, _, _, e7⟩ := endP_spec
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } ms y
  rw [← hp] at e1 e2 e7
  have hvl : vs.length = lamS := by
    have e := congrArg List.length hk
    rw [List.length_map, plainWs, List.length_replicate] at e
    exact e
  have hd : ∀ v ∈ vs, v.d = 3 := weights_d vs _ hk (by
    intro w hw
    rw [List.eq_of_mem_replicate hw]
    rfl)
  have hown : ownSlots (Call.all ⟨0, vs, some ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩⟩) =
      1 + 2 * lamS + 2 := by
    show ownSlots (vs ++ [Var.point zeroE (2 + 1)]) = _
    rw [own_count vs hd 2, hvl]
  have hm1 : (ms ++ [y]).map (·.1) = plainWs lamS ++ [OnBytes.Psc.Weight.atZero 3] := by
    rw [List.map_append, a1, hyy]
    rfl
  have hwl : p.walk.1.length = 1 + 2 * lamS + 2 := by
    rw [walk_length (ms := ms ++ [y]) (by simp) (by rw [e1, hm1]; rfl) (by rw [e2]; rfl) hheld,
      hm1, OnBytes.Psc.hidingEntries, List.map_append, List.sum_append, plainWs, plain_sum]
    rfl
  have hF' : Sized ({ F with
      next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork) := hS
  obtain ⟨_, hS1, hin, hout⟩ := OnBytes.PscRun.hideRun_ok _ G1 K.sA0 vals beta hF' hrun
  refine ⟨hS, filledA_of_publicPart hTp, ?_, ?_⟩
  · have b := (hin (2 + (1 + P.y.LamM) + NCLp - 1) (by omega)).1
    have b' : K.sA0 + (2 + (1 + P.y.LamM) + NCLp - 1) < F.ns := b
    rw [hown]
    show F.next + (1 + 2 * lamS + 2) + (2 + (1 + P.y.LamM) + NCLp) ≤ F.ns
    omega
  · intro j h1 h2
    rw [hown] at h2
    have h2' : j < F.next + (1 + 2 * lamS + 2) + (2 + (1 + P.y.LamM) + NCLp) := h2
    by_cases hj : j < K.sA0
    · intro hf
      have hfG : Filled G1 j := (hout j (Or.inl hj)).2.2.mpr hf
      have c' := ((OnBytes.PscRun.hideRun_ok G1 G _ _ _ hS1 hwin).2.2.1 (j - F.next)
        (by rw [Array.size_replicate, hwl]; omega)).2.1
      rw [e7, show F.next + (j - F.next) = j by omega] at c'
      exact c' hfG
    · have c' := (hin (j - K.sA0) (by omega)).2.1
      rw [show K.sA0 + (j - K.sA0) = j by omega] at c'
      exact c'

/-! ## 2 The own claim on the honest part's rounds -/

/-- **What the batched sumcheck's own claim is worth on the honest part's rounds**: the sumcheck's
first challenge times (the verifier's summand on the values that it was shown, less the job's
summand on the last round's scalars). job: the maker of the part's job, a free letter. tp: the
tape, the batching round first. -/
theorem stack_worth (name endName : String) {P : OnBytes.Model.Layer.Pub}
    {v : OnBytes.Model.Layer.Env} {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ}
    (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job))
    (st : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (F : Fork) (Wd : World GE) {G : Fork} {tp u : Tape} {K : HeardStack}
    (hd : drawsOk ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
      st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName
      (k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job)) c st seen ds =
        some rounds)
    (hs : ∀ i, i < ownSlots ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp))
      job).callAt st.input (frontOf st seen)).all → Wd.slot (F.next + i) = hidingCoin c i)
    (j : Job) (hj : job st.input (frontOf st seen) = some j)
    (hfit : k4JobFits (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) j = true)
    (hF : hearStack engFl P v H lamS NCLp F tp = some (K, G, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds)
    (hσ : ∀ C, OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps tp) 2) F (tp.drop 1) =
      some (C, F, tp.drop 1) → C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hdY : j.dY = 2)
    (hn : ∀ rs, rs.length = j.cube.n → (j.ends rs).length = 2 + (1 + P.y.LamM) + NCLp)
    (hP : ∀ rs, PolyOn j.dY fun y => j.atEnds rs (maskedEnds (j.ends rs) (endRun c) y))
    (hA : ∀ rs, ReadsAlike (j.atEnds rs))
    (hE : ∀ rs, rs.length = j.cube.n →
      Reading.gl.val (j.atEnds rs (j.ends rs)) = Reading.gl.val (j.cube.summandAt rs)) :
    ∃ (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv ∧
      scalars rv.vals = some s ∧ s = OnBytes.Desc.First.K4.stackVals lamS tp ∧
      K.rs.toList = ((varsOf
        ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
          st.input (frontOf st seen)) ds).take lamS).reverse ∧
      K.rowS.value Reading.gl Wd = Reading.gl.val (tapeEps (tp.drop 1)) *
        (Reading.gl.val (mulE K.fin.As K.fin.Bs) - Reading.gl.val (j.atEnds
          ((varsOf ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
            st.input (frontOf st seen)) ds).take j.cube.n) s)) := by
  have hk : ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt st.input
      (frontOf st seen)).vs.map Var.weight = plainWs lamS := by
    show (withPoints (List.replicate lamS (Var.plain 3)) _).map Var.weight = _
    rw [wp_replicate_plain, List.map_replicate]
    rfl
  obtain ⟨C0, hC0⟩ := stack_start hF
  obtain ⟨h, G', hh, hf⟩ := k4_hears (V := V) name endName
    (k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job) c st seen ds rounds C0 F
    (shapeOk_plain lamS (by norm_num) (by omega)) hd ha (stack_ready hF hS _ hk hC0)
  obtain ⟨C, p, vals, G1, beta, hC, hrow, _, hv, _, hKr, hpe, _, htie⟩ :=
    stack_sameLetters (rounds := rounds) (h := h) (G' := G') hF _ hk
  have eC : C = C0 := by
    rw [hC0] at hC
    exact (congrArg Prod.fst (Option.some.inj hC)).symm
  rw [eC] at htie
  obtain ⟨hSL, rv, b1, b2⟩ := htie hh hT
  have hr : h.r = varsOf ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
      st.input (frontOf st seen)) ds :=
    (sumClaim V W X name endName _ c st seen ds rounds C0 F G' h hd ha hh).2.1
  have hlen : (h.r.take j.cube.n).length = j.cube.n := by
    rw [hr, List.length_take, vars_length _ job st.input (frontOf st seen) j
      ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩ ds hd (jobFits_parts hfit) rfl]
    omega
  obtain ⟨r, s, c1, c2, _, c4⟩ := k4_sent_summand (V := V) name endName
    (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job c st seen ds rounds j
    ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩ hd ha hj (jobFits_parts hfit) rfl
    (hn _ (by rw [← hr]; exact hlen)) (hA _)
  have er : rv = r := Option.some.inj (b1.symm.trans c1)
  have es : s = vals.toList := by
    rw [er] at b2
    exact Option.some.inj (c2.symm.trans b2)
  refine ⟨r, s, c1, c2, by rw [es, hv], by rw [hKr, hSL.r, hr], ?_⟩
  rw [hrow, flatRowTie GE Reading.gl Wd p h _ _ hSL,
    k4_rowForm_worth (V := V) name endName (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job c
      st seen ds rounds C0 F G' h _ {} Wd j ⟨2, 2 + (1 + P.y.LamM) + NCLp⟩ hd ha hh
      (by rw [hf]; exact hs) (hσ C0 hC0) hj (jobFits_parts hfit) rfl (by rw [hdY]; norm_num)
      (hn _ hlen) (hP _) (hA _) (hE _ hlen),
    hr, c4, Aff.value_empty, ← hSL.eps, hpe]
  ring

/-- **The own claim is worth 0**, where the verifier's summand on the values that it was shown reads
as the job's summand on the values as sent. -/
theorem stack_zero (name endName : String) {P : OnBytes.Model.Layer.Pub}
    {v : OnBytes.Model.Layer.Env} {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ}
    (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job))
    (st : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (F : Fork) (Wd : World GE) {G : Fork} {tp u : Tape} {K : HeardStack}
    (hd : drawsOk ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
      st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName
      (k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job)) c st seen ds =
        some rounds)
    (hs : ∀ i, i < ownSlots ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp))
      job).callAt st.input (frontOf st seen)).all → Wd.slot (F.next + i) = hidingCoin c i)
    (j : Job) (hj : job st.input (frontOf st seen) = some j)
    (hfit : k4JobFits (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) j = true)
    (hF : hearStack engFl P v H lamS NCLp F tp = some (K, G, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds)
    (hσ : ∀ C, OnBytes.Desc.First.K4.joinStart engFl v H (powers (tapeEps tp) 2) F (tp.drop 1) =
      some (C, F, tp.drop 1) → C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hdY : j.dY = 2)
    (hn : ∀ rs, rs.length = j.cube.n → (j.ends rs).length = 2 + (1 + P.y.LamM) + NCLp)
    (hP : ∀ rs, PolyOn j.dY fun y => j.atEnds rs (maskedEnds (j.ends rs) (endRun c) y))
    (hA : ∀ rs, ReadsAlike (j.atEnds rs))
    (hE : ∀ rs, rs.length = j.cube.n →
      Reading.gl.val (j.atEnds rs (j.ends rs)) = Reading.gl.val (j.cube.summandAt rs))
    (hfin : ∀ (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv → scalars rv.vals = some s →
      Reading.gl.val (mulE K.fin.As K.fin.Bs) = Reading.gl.val (j.atEnds
        ((varsOf ((k4SumJob (k4PlainShape lamS 2 (2 + (1 + P.y.LamM) + NCLp)) job).callAt
          st.input (frontOf st seen)) ds).take j.cube.n) s)) :
    K.rowS.value Reading.gl Wd = 0 := by
  obtain ⟨rv, s, c1, c2, _, _, hw⟩ := stack_worth (V := V) name endName job c st seen ds rounds
    F Wd hd ha hs j hj hfit hF hS hT hσ hdY hn hP hA hE
  rw [hw, hfin rv s c1 c2, sub_self, mul_zero]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_sameLetters
#print axioms ProofFile.Honest.K4.stack_start
#print axioms ProofFile.Honest.K4.stack_ready
#print axioms ProofFile.Honest.K4.stack_worth
#print axioms ProofFile.Honest.K4.stack_zero
