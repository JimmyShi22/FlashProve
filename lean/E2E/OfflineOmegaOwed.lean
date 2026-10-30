-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaOwed.lean: WHAT IS OWED AT A RUN AT THE ROW OF THE KEY FILE's TEST ON G_omega (⟨2, –, 10⟩): `Lettered.owedAt`
(Johnson/Desc/ProofFile/Honest/Rule.lean) at the offline rows (`offlineRows`, E2E/OfflineSides.lean), over parts whose
half at the place is `proverSideOfTestOnOmega` (the pair behind the guard), at the written book, where the row's condition at a part follows
from: columns are handed, and `OnEntryOwn` (Johnson/Desc/ProofFile/Honest/K12/SimO/Entry.lean) at the written codes.

PAID HERE, at the run's own carried block, state and front: that columns are handed (both parts) · the five clauses le,
leS, heardFit, heard, fold (E2E/OfflineOmegaFive.lean) · of the clause asks all but its sentence on hidden data
(E2E/OfflineOmegaLeft.lean).

FOUR NAMED PREMISES STAY, each at the run's own values, each with the tie of the carried block and the state kept:
  `SayAtRun`     (E2E/OfflineSayAtRun.lean) the rows that the test takes in hold at the members' words: hidden data
  `DoorAtRun`    the clause door: the job's state on entry is the simulators' job's, made of the front
  `FirstTreesAtRun`   the clause trees: the trees that the first round of positions opens have the declared depths, and what the
                 front lists of them is theirs
  hbud           the row's letter on positions, in the text of the field `bud₂` of `BudDebts`
                 (Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean): on the lists' cut and the challenges alone

  `orRefused_ok`, `carriedAt_behindGuard`, `guarded_row_members`, `opened_at_shared_row`   four general lemmas
  `omega_row_form`      the row's parts, its sub-protocol's rounds, its stages
  `omega_on_at_run`     the condition at every member of the row, at a run's own values
  `omega_owed_at_rows`  `owedAt` at the row

Limits. Conditional on the four. The first three read the input or the carried coins: no later law may take them as
hypotheses on a run and then speak of the coins as drawn anew. The state that stands in (`OnEntryOwn`'s r') is the job's own.
That a run returns, or calls a part, is not shown here. At the written sizes. Nothing on any property.
-/
import E2E.OfflineOmegaLeft
import E2E.OfflineSayAtRun
import E2E.OfflineGuardLaws
import Johnson.Desc.ProofFile.Honest.K12.SimO.Entry
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (plainMany)
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St blocks)
open H2K.Member (codesKeyFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega)
open AtPublicFiles.KeyValueHolds (place_p12At)
open VerifierAndGoals (PublicFiles InScope)

/-! ## The two clauses that stay, as named sentences at one run -/

section Named
variable {W X Pb : Type}

/-- **The clause door at one run, at the called second part.** pub: the public field of an input. front: the run's
front at the part. -/
def DoorAtRun (J : TestJob W X) (Js : SimJob Pb) (pub : W → Pb) (a : Place) (called : Addr → Bool)
    (mid : Addr → Except Refusal (Option (Mid W X))) (front : Before) : Prop :=
  called ⟨a, 1⟩ = true → ∀ m : Mid W X, mid ⟨a, 1⟩ = .ok (some m) →
    J.rec₀ m.st.input (restFront J m) = Js.rec₀ (pub m.st.input) (front.cut (firstLen J.p.nums.stages))

/-- **The clause trees at one run, at the called second part.** V: as in `SayAtRun`. os: the trees that the part's
first round of positions is declared to open. -/
def FirstTreesAtRun (V : Type) (J : TestJob W X) (os : List (Fmt.Shape × Fmt.TreeSource)) {Bk : ProverCoinCounts}
    (k : Coins Bk) (chain : ℕ) (a : Place) (called : Addr → Bool)
    (mid : Addr → Except Refusal (Option (Mid W X))) (front : Before) : Prop :=
  called ⟨a, 1⟩ = true → ∀ (m : Mid W X) (ca : CsAll (restPart J : Part V W X).carries),
    mid ⟨a, 1⟩ = .ok (some m) → carriedAt Bk k chain ⟨a, 1⟩ (restPart J : Part V W X) = .ok ca →
    (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (K12.rowsAt J (stretches _ ca) m)).map (·.1) =
        os.map (·.1.a) ∧
      ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
        (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (K12.rowsAt J (stretches _ ca) m))[i]? =
          some T →
        ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
          ∀ q ∈ cols, q.2 = T.2 q.1

/-- Where `orRefused` returns a state, the walk has returned that state. -/
theorem orRefused_ok {e : Except Refusal (Option (Mid W X))} {m : Mid W X}
    (h : orRefused e = .ok m) : e = .ok (some m) := by
  cases e with
  | error _ => cases h
  | ok o =>
    cases o with
    | none => cases h
    | some m' =>
      have e' : m' = m := Except.ok.inj h
      rw [e']

/-- What the book carries to a part behind the guard it carries to the part. -/
theorem carriedAt_behindGuard {V : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (chain : ℕ) (a : Addr) (p : Part V W X)
    {ca : CsAll p.carries} (h : carriedAt Bk k chain a p.needsField = .ok ca) :
    carriedAt Bk k chain a p = .ok ca := by
  unfold carriedAt at h ⊢
  rw [lendPart_behindGuard] at h
  exact h

end Named

/-! ## Two general lemmas on a row of the shared chain -/

section General
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {r : RunC F}

/-- **The two members of a row that holds a proximity test's pair behind the guard.** -/
theorem guarded_row_members (plan : F.planOk = true) (book : Bk.word F = none)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    {σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hσ : L.side F.shared.blocksInOrder = some σ)
    (J : TestJob (Common W₀ Rc Ky) X₀)
    (hparts : L.row.map (·.1) = [(firstPart J).needsField, (restPart J).needsField])
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest) :
    ∃ s0 s1, σ.members = [⟨0, J.laid.take (firstLen J.p.nums.stages), (firstPart J).needsField, s0⟩,
      ⟨1, J.laid.drop (firstLen J.p.nums.stages), (restPart J).needsField, s1⟩] := by
  have hrowσ : σ.row = L.row := OnBytes.SendSim.Seat.row_of_seated hσ
  obtain ⟨s0, s1, hrow⟩ := two_of_map hparts
  obtain ⟨⟨hsum, hor⟩, -⟩ := shared_stands plan book hR L hL σ hσ
  have e0 : (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length =
      firstLen J.p.nums.stages := (needsField_length _).trans (Light.first_moves_len J)
  have e1 : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length =
      restLen J.p.nums.stages := by
    rw [needsField_length, rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hlen : J.laid.length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    rw [← hlaid, List.length_zip, hor, Nat.min_self, ← hsum, hrowσ, hrow]
    simp [e0, e1]
  have ht : (J.laid.drop (firstLen J.p.nums.stages)).take (restLen J.p.nums.stages) =
      J.laid.drop (firstLen J.p.nums.stages) :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  refine ⟨s0, s1, ?_⟩
  unfold Side.members
  rw [hrowσ, hrow, hlaid]
  show [_, _] = _
  simp only [e0, e1, ht, Nat.zero_add]

/-- **At a called part of the shared chain columns are handed.** -/
theorem opened_at_shared_row (plan : F.planOk = true) (book : Bk.word F = none)
    (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    {σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hσ : L.side F.shared.blocksInOrder = some σ)
    {u : Member Empty (Common W₀ Rc Ky) X₀ Ky} (hu : u ∈ σ.members)
    (hc : r.called ⟨L.place, u.number⟩ = true) {m : Mid (Common W₀ Rc Ky) X₀}
    (hm : orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m) :
    ∃ cs, m.opened = some cs := by
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  have hbp : σ.block.place = L.place := side_place hσ
  obtain ⟨-, hst⟩ := shared_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, A⟩, -⟩ := hst u hu
  obtain ⟨m', -, cs, hm', hop, -, -⟩ := Sim2.called_columns plan hR h σ u pre t _ A (by rw [hbp]; exact hc)
  rw [hbp] at hm'
  have e : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans (orRefused_ok hm)))
  exact ⟨cs, e ▸ hop⟩

end General

/-! ## The row at the key file -/

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The row's parts, its sub-protocol's declared rounds, its stages.** -/
theorem omega_row_form (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk) (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU.place = foldedTestPlace) (A : SendPub) (pU pO : P12)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      (L.On = (c.shared omegaTestPlace).atPart ∧ L.bud = (c.shared omegaTestPlace).positions ∧
        L.row.map (·.1) = [(firstPart (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest).needsField,
          (restPart (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest).needsField]) ∧
      (∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → σ.block.rounds.zip σ.block.oracles =
        (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest.laid) ∧
      ∃ s next rest, (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest.p.nums.stages =
        s :: next :: rest := by
  subst hpO
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  intro L hL hp
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO]
    exact place_p12At _ _
  obtain ⟨s, next, rest, P, -⟩ := omega_public (X₀ := Unit) A pU bs weights rand
    (jobKO (X := Unit) A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand).toRun.toTest.rec₀
  refine ⟨?_, fun σ hσ => omega_laid A pU bs weights rand _ hs scope
    (OnBytes.SendSim.Seat.block_of_seated hσ) ((side_place hσ).trans hp), s, next, rest, P.stages⟩
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
  obtain rfl := half_at_omegaTest K hsp hU hOp hg hp
  refine ⟨?_, ?_, ?_⟩
  · show (c.shared K.onOmega.place).atPart = _
    rw [hOp]
  · show (c.shared K.onOmega.place).positions = _
    rw [hOp]
  · show (partsBeside K.onOmega.parts _).map (·.1) = _
    rw [partsBeside_parts, hO]
    rfl

/-- **THE CONDITION AT EVERY MEMBER OF THE ROW, AT A RUN's OWN VALUES**: columns are handed, and `OnEntryOwn` at the
written codes: from the three named sentences at that run. os: the list that the second part's first round of
positions opens. -/
theorem omega_on_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64))
    (say : SayAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest
      (plainMany (jobKO (X := Unit) A pU pO bs weights rand)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ))
    (door : DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩))
    (trees : FirstTreesAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest os k 1
      omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      (∃ cs, m.opened = some cs) ∧
        OnEntryOwn Face.shared (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js codesKeyFull 1 os u
          ca m (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  intro L hL hp σ hσ u hu hc ca m hca hm
  have plan := hs.named.plan
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  refine ⟨opened_at_shared_row plan book h hL hσ hu hc hm, fun hn => ?_⟩
  have five := omega_five_at_run_own hs scope hK hB K hsp hU A hA pU pO hpO bs weights rand hO S c H Js due h
    st L hL hp σ hσ u hu hn hc ca m hca hm
  have left := omega_left_at_run hs scope hK hB K hsp hU A hA pU pO hpU hpO bs hb weights rand hO S c H Js
    due h L hL hp σ hσ u hu hn hc ca m hca hm
  obtain ⟨⟨-, -, hparts⟩, hlaid, s, next, rest, hst⟩ :=
    omega_row_form hs scope K hsp hU A pU pO hpO bs weights rand hO S c L hL hp
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  obtain ⟨s0, s1, hmem⟩ := guarded_row_members plan book hR hL hσ _ hparts (hlaid σ hσ) s next rest hst
  rw [hmem] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact absurd (show (0 : ℕ) = 1 from hn) (by decide)
  rw [hp] at hc hca hm five ⊢
  have hm' := orRefused_ok hm
  have hca' := carriedAt_behindGuard k 1 ⟨omegaTestPlace, 1⟩
    (restPart (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest) (ca := ca) hca
  obtain ⟨Dp, cc, Rw, h3, hS, hD⟩ := left (say hc m ca hm' hca')
  refine ⟨(jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest.rec₀, fun _ _ => rfl, ?_⟩
  exact { le := five.le, leS := five.leS, heardFit := five.heardFit, heard := five.heard,
          door := door hc m hm', fold := five.fold, trees := trees hc m ca hm' hca',
          asks := ⟨Dp, cc, Rw, h3.trans hos.symm, hS, hD⟩ }

/-- **`owedAt` AT THE ROW OF THE TEST ON G_omega**, where the row's condition at a part follows from the condition above.
hbud: the row's letter on positions, in the text of `BudDebts.bud₂`. -/
theorem omega_owed_at_rows (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3)
    (hOn : ∀ u ca m front, ((∃ cs, m.opened = some cs) ∧
      OnEntryOwn Face.shared (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js codesKeyFull 1 os u ca
        m front) → (c.shared omegaTestPlace).atPart u ca m front)
    (hbud : ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (keyFileDescription Xs N Pl).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (keyFileDescription Xs N Pl) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (keyFileDescription Xs N Pl) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take n).map (·.2.length)).sum))
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64))
    (say : SayAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest
      (plainMany (jobKO (X := Unit) A pU pO bs weights rand)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ))
    (door : DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩))
    (trees : FirstTreesAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest os k 1
      omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ a)) r.run st r.called := by
  intro L hL hp
  have plan := hs.named.plan
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  obtain ⟨⟨eOn, -, -⟩, -, -⟩ := omega_row_form hs scope K hsp hU A pU pO hpO bs weights rand hO S c L hL hp
  refine owedAt_shared_at plan book h hL st (fun σ hσ u hu hc ca m hca hm => ?_) fun σ hσ u hu => ?_
  · rw [eOn]
    exact hOn _ _ _ _ (omega_on_at_run hs scope hK hB K hsp hU A hA pU pO hpU hpO bs hb weights rand hO S c H
      Js os hos due h st say door trees L hL hp σ hσ u hu hc ca m hca hm)
  · obtain ⟨-, ⟨pre, t, hcut, e1, e2⟩, -⟩ := shared_part_at_run plan book h hL hσ hu
    rw [e1, e2]
    exact hbud L hL hp σ hσ u hu pre t _ hcut rfl ρ due

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.orRefused_ok
#print axioms AtPublicFiles.OfflineRows.carriedAt_behindGuard
#print axioms AtPublicFiles.OfflineRows.guarded_row_members
#print axioms AtPublicFiles.OfflineRows.opened_at_shared_row
#print axioms AtPublicFiles.OfflineRows.omega_row_form
#print axioms AtPublicFiles.OfflineRows.omega_on_at_run
#print axioms AtPublicFiles.OfflineRows.omega_owed_at_rows
