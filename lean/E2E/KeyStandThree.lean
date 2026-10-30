-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandThree.lean: the key's shared thread at border 3: behind «LIN point» and «send o_u», at a
letter `Said`, with the half that sends real words. It is no `run` of the frame: see
E2E/KeyStandPlayed.lean.

Why. This is the first border of the thread at which a half has sent something: o_u, its tree and its
sample row. The thread's item there says that the state holds o_u's sample constraints and that they
hold of the honest words.

Main names.
  `halves_key`: the kind's halves are among the key prover's, at the key's `Others`.
  `next_pair`: one step at a member of the eight, from `K14Asks`.
  `first_sampled_full`, `first_sampled`: the first message of «send o_u» has sample rows, at the written
    value.
  `TieU`, `PlayedSends`, `word_at`: the tie of the tables to the words, at one family of rows `rowsU`, with
    the step made at «send o_u» kept.
  `pair_three`: the pair at border 3; the state holds at least one sample row of o_u; and the first round
    that the step returned shows `treeTables` of the honest rows, of which the witness's words are the
    tables. THE TAIL of a row is in the code word and in no word: it stands in `rowsU`.

Premises that stay: `hS`, `hSN` on the letter `Said`, at the start's field `o`; those of `pair_one`
(E2E/KeyStandOne.lean) and of `asks_key` (E2E/KeyAsksKey.lean), and two lists of challenges that fit: `hd₁`, `hd₂`.

What stays open. `lengthsOk` is not stated. The job of the test on G_u is not written: `rowsR` against
`rowsU`, and the carried coins, are open. THE MEMBER: no term of `K` is laid here and the premises are not
shown met together.
That the words of the item are the tables that the half sent is not said by the item: the library
says so (Honest/K14/Thread2.lean). At `fits`, the lists are letters. No proximity test; nothing of the
first chain, W, the door or the last chain.

NOT IN FRONT OF A LAW OVER COINS: `next_pair` and `pair_three` bear this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `Said` under `hS` is a letter for a predicate, of the
first kind, through `k`, and `o` is no coin. `Vd` under `hV` is a letter for a predicate, of the first kind,
through `inK w₀ rc x`. `hSN`, and `hN` at `next_pair`, are bound over all coins and by themselves pick none;
`tt` stands under no premise; `hKp`, `hE` name no coin. They stand at a run's coins `k`, and the pair ties the thread's letters, of the first kind; `F` is of that kind where the input is made of the
committer's coins; `hs`, `scope` read public files. None of these is the term that the committer makes.
None: the bar is flat. `halves_key` names no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyAsksKey
import E2E.KeyStandOne
import E2E.KeyHalfSteps
import E2E.KeyNoStop
import E2E.KeyRowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyStandThree
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi sharedTests keyAsProof descriptionFromSource Claim)
open _root_.Desc.K14 (St blocks blocksOr)
open _root_.Desc.K14.Honest (Eight withU_zero shapeAt_of_get)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub k14_stated k14_sends_stated of_atFull full_two pointPlace
  foldedPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared randK14)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey othersKey threadKey plan_key)
open AtPublicFiles.KeySharedQuiet (CellsAlone over_key fits_key)
open AtPublicFiles.KeyAsksKey (tableKey asks_key own_in sends_in)
open AtPublicFiles.KeyStandOne (startAt inK envK pair_one)
open AtPublicFiles.KeyStandStep (step_pair)
open AtPublicFiles.KeyHalfSteps (steps_half full_point full_folded)
open AtPublicFiles.Stops (NoStop chainStopAt_none)

/-- **The tables that a half sent and the words of a witness, at one family of honest rows**: the first
round that was played shows the code words of the rows, and the witness's words at the sending's
numbers are their tables. The tail of a row is in a code word and in no word. THE FIRST HALF CARRIES
IT: the played tables are made of the part's own rows, and `rowsAgree_u` and `sentTables_tie` hold them
against `rowsU`. The second half is what the thread's witness is defined to be. -/
def TieU {Wt : Type} (Q : _root_.Desc.K14.P14) (sentU : Array OnBytes.OracleNotice) (ℓ : WitLens Wt)
    (H : _root_.Desc.K14.Honest.Inputs) (key : TableKey) (r1 : Fmt.RoundView) (ps : List Played) (wit : Wt) : Prop :=
  (ps.head?.map (·.tables)) = some ((K1.treeTables (_root_.Desc.K14.Law.parU Q sentU)
      (_root_.Desc.K14.Honest.rowsU Q (_root_.Desc.K14.first Q.codes key) r1 H)).map some) ∧
    ∀ o part i, o < (_root_.Desc.K14.Law.parU Q sentU).sent.size →
      ℓ.get wit o part i =
        (_root_.Desc.K14.Honest.rowsU Q (_root_.Desc.K14.first Q.codes key) r1 H o).word
          (Johnson.Prover.Send.shapeAt (_root_.Desc.K14.Law.parU Q sentU) o) part i

/-- **The run's step at «send o_u», kept**: the pair stands at border 2, the member's move there
returned the rounds `y.1`, the stand and tables are what that move leaves, and of those rounds the
sentence `tie` holds. So `tie` speaks of what the frame's `play` returned. -/
def PlayedSends {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (k : Coins Bk) (ds : List Fmt.Drawn)
    (m : Mid W X) (E : Env) (tie : List Played → Prop) : Prop :=
  ∃ (s₂ : S) (m₂ : Mid W X) (E₂ : Env) (blk : Block S Cl) (y : List Played × Mid W X)
    (cols : List VerifiableInference.Desc.OpenedColumn),
    ThrS T Said 2 k s₂ m₂ E₂ ∧ T.bs[2]? = some blk ∧ T.Moved blk k m₂ E₂ ds y cols ∧
      m = y.2.took cols ∧ E = E₂.add y.1 ∧ tie y.1

/-- One draw at one round. -/
theorem one_draw {r : Fmt.DeclaredRound} {ds : List Fmt.Drawn} (h : drawsFit [r] ds = true) :
    ∃ d, ds = [d] ∧ d.elems.length = r.entry.drawE := by
  cases ds with
  | nil => simp [drawsFit] at h
  | cons d t =>
    cases t with
    | nil =>
      refine ⟨d, rfl, ?_⟩
      simp only [drawsFit, Bool.and_true, drawFit, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1.1.1.1.1.1
    | cons _ _ => simp [drawsFit] at h

/-- The first member's one round draws the point: at the written value, by Lean's kernel. -/
theorem point_closed : ((blocksOr QK).head?.map fun b => b.rounds.map (·.entry.drawE)) =
    some [QK.par.S.kCol] := by
  decide +kernel

/-- So at a value that is the written one. -/
theorem blocks_point (Q : _root_.Desc.K14.P14) (e : Q = QK)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ rd, b1.rounds = [rd] ∧ rd.entry.drawE = Q.par.S.kCol := by
  subst e
  have h := point_closed
  have eb : blocksOr QK = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hb]
    rfl
  rw [eb] at h
  simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h
  cases hr : b1.rounds with
  | nil => rw [hr] at h; simp at h
  | cons rd t =>
    rw [hr] at h
    simp only [List.map_cons, List.cons.injEq] at h
    cases t with
    | nil => exact ⟨rd, rfl, h.1⟩
    | cons _ _ => simp at h

/-- **The words of the thread's witness at a number of the first sending.** -/
theorem word_at {Bk : ProverCoinCounts} {W₀ Rc Wt : Type} (Q : _root_.Desc.K14.P14) (sentU : Array OnBytes.OracleNotice)
    (ℓ : WitLens Wt) (holds : Coins Bk → Common W₀ Rc TableKey → _root_.Desc.K14.Honest.Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) {o : Nat} {part : OnBytes.Part} {i : Nat}
    (ho : o < (_root_.Desc.K14.Law.parU Q sentU).sent.size) (h2 : sentU.size = 2) :
    ℓ.get (witL ℓ Q sentU holds rest k w h) o part i =
      (_root_.Desc.K14.Honest.rowsU Q (_root_.Desc.K14.first Q.codes w.key) (firstRv h) (holds k w) o).word
        (Johnson.Prover.Send.shapeAt (_root_.Desc.K14.Law.parU Q sentU) o) part i := by
  rw [get_witL]
  have ho' : o < sentU.size := by
    have e := _root_.Desc.K14.Law.parK1_sent Q 2 "o_u and the first mask" sentU
    rw [show (_root_.Desc.K14.Law.parU Q sentU).sent = sentU from e] at ho
    exact ho
  show (if 0 + 2 ≤ o ∧ o < 0 + 2 + (_root_.Desc.K14.Law.parO Q).sent.size then _ else
    if 0 ≤ o ∧ o < 0 + (_root_.Desc.K14.Law.parU Q sentU).sent.size then _ else _) = _
  rw [_root_.Desc.K14.Law.parK1_sent, _root_.Desc.K14.Law.parK1_sent]
  have h2' : ¬ (0 + 2 ≤ o ∧ o < 0 + 2 + (_root_.Desc.K14.withOmega Q.S).size) := by omega
  have h1 : 0 ≤ o ∧ o < 0 + sentU.size := by omega
  rw [if_neg h2', if_pos h1]
  rfl

/-- The first message of «send o_u» is sampled, at the written value. By Lean's kernel. -/
theorem first_sampled_full :
    ((((_root_.Desc.K14.withU QK.S).getD #[])[0]?).map (·.shape.answers)).getD 0 ≠ 0 := by
  decide +kernel

/-- So at a value that is the written one. -/
theorem first_sampled (Q : _root_.Desc.K14.P14) (e : Q = QK) (sU : Array OnBytes.OracleNotice)
    (hU : sU = (_root_.Desc.K14.withU Q.S).getD #[]) :
    ∃ n, (_root_.Desc.K14.Law.parU Q sU).sent[0]? = some n ∧ n.shape.answers ≠ 0 := by
  subst e
  subst hU
  have h := first_sampled_full
  rw [_root_.Desc.K14.Law.parU, _root_.Desc.K14.Law.parK1_sent]
  cases hn : ((_root_.Desc.K14.withU QK.S).getD #[])[0]? with
  | none =>
    rw [hn] at h
    exact absurd rfl h
  | some n =>
    rw [hn] at h
    exact ⟨n, rfl, h⟩

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (o : Option (List OpenedColumn))
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- The kind's halves are among the key prover's. -/
theorem halves_key (hlin : K.lin = planData (parKey Xs Pl))
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K.onU.place, K.onOmega.place].Nodup) (w : Common W₀ Rc TableKey) :
    HalvesIn (parKey Xs Pl)
      (othersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w)
      (planData (parKey Xs Pl)) K.weights := by
  refine ⟨rfl, ?_, ?_⟩
  · show ((keyProver K).shared.map (·.place)).Nodup
    rw [keyProver_shared K hsp]
    exact hap
  · intro h hh
    rw [← hlin] at hh
    exact own_in K hsp h hh

/-- **One step at a member of the eight.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem next_pair {layO : OnBytes.TreeLay}
    (h : K14Asks ℓ (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x))
      (parKey Xs Pl) (sentKey Xs Pl) layO (keyAsProof Xs.chains) (sharedTests Pl)
      VerifiableInference.Desc.K12.Seat.last (planData (parKey Xs Pl)) K.weights (randKey K))
    {b : Nat} (h1 : 1 ≤ b) (h8 : b ≤ 8) {blk : Block St Claim} {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} {ds : List Fmt.Drawn} {l : List (Step _ X₀)}
    (hfit : (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).fits 12 = true)
    (hN : SaidNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) Said b)
    (hM : MadeNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) b)
    (hblk : (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[b]? = some blk)
    (hA : ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x))
      Said b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hstop : chainStopAt ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m.st.input) [blk] (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs m.loc ds = none)
    (hsteps : chainSteps (keyBook K₀) ((keyBook K₀).rowsOf (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).chain)
      (k.look (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).chain)
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m.st.input) [blk] (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs = .ok l) :
    ∃ (s' : St) (m' : Mid (Common W₀ Rc TableKey) X₀) (E' : Env),
      ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x))
        Said (b + 1) k s' m' E' ∧
      m'.st.heard = m.st.heard ++ ds ∧ (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).keeps b s s' ∧
      ∃ (y : List Played × Mid (Common W₀ Rc TableKey) X₀) (cols : List VerifiableInference.Desc.OpenedColumn),
        (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).Moved blk k m E ds y cols ∧ m' = y.2.took cols ∧ E' = E.add y.1 := by
  obtain ⟨hP, -, hX, hR, hAc⟩ := k14_asks h (fun _ _ _ => none) b h1 h8
  have hB := k14_behind h (cs := [])
    (fun _ _ _ => ⟨fun _ _ hc => absurd hc List.not_mem_nil, fun _ => trivial⟩)
    b h1 h8 (fun _ hy => absurd hy List.not_mem_nil) (fun _ hy => absurd hy List.not_mem_nil)
  exact step_pair _ Said (n := 12) (fun _ _ _ => none) hfit (by omega) hblk hN
    (playsS_of _ Said hP) (acceptedS_of _ Said hAc) (behindS_of _ Said hB) (exchangeS_of _ Said hX)
    (ridesPastS_of _ Said hR) hM hA hd hstop hsteps rfl

/-- **The thread at border 3**: behind «LIN point» and «send o_u», at the letter `Said`, the tables that the
half sent at that member being the code words of the honest rows.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem pair_three {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (F : FiveFields (parKey Xs Pl) (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).stored K.weights (randKey K))
    (hlin : K.lin = planData (parKey Xs Pl)) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K.onU.place, K.onOmega.place].Nodup)
    (hN : Function.Injective Nm.tenant)
    (qr : AtPublicFiles.Stops.QuietHalf K.rng) (qU : AtPublicFiles.Stops.QuietHalf K.onU)
    (qO : AtPublicFiles.Stops.QuietHalf K.onOmega) (qw : AtPublicFiles.Stops.QuietHalf K.own)
    (k : Coins (keyBook K₀)) (hV : Vd (inK w₀ rc x))
    (hI : (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).Items
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).opened 0) k
      ((descriptionFromSource Xs Nr Pl).start₂ x) (startAt K o (inK w₀ rc x)) (envK K w₀ rc))
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hC : ∀ v, CellsAlone (Mg₀ v))
    (hbare : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[0]? = some blk →
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs.find? fun g => g.place == blk.place) = none)
    (ds₁ ds₂ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true)
    (hS : Said 0 k (startAt K o (inK w₀ rc x)))
    (hSN : ∀ b, b < 3 → SaidNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) Said b) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x))
        Said 3 k s m E ∧
      m.st.heard = ds₁ ++ ds₂ ∧
      (∃ y, s.st.oracles[num .oU]? = some y ∧ 0 < y.sampleRows.size) ∧
      PlayedSends (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) Said k ds₂ m E (fun ps =>
        TieU (parKey Xs Pl) (sentKey Xs Pl) ℓ (holds2 (parKey Xs Pl) K.weights (randKey K) k (inK w₀ rc x))
          (inK w₀ rc x).key (firstRv m.st.heard) ps
          ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).wit k m.st.input m.st.heard)) := by
  obtain ⟨layO, hA⟩ := asks_key Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd (inK w₀ rc x) hs scope hK₀ F hlin
    hsend hap hN
  have hQ := hA.plan
  obtain ⟨B⟩ := hQ.eight
  have e : parKey Xs Pl = QK := par_sourced hs scope
  have hsp₀ : (planData (parKey Xs Pl)).S.sharedSplitNeeded = true := hQ.facts.two
  have hsp : K.lin.S.sharedSplitNeeded = true := by
    rw [hlin]
    exact hsp₀
  have H := halves_key Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd hlin hsp hap (inK w₀ rc x)
  have E8 : AtEight (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) 1 (parKey Xs Pl) (planData (parKey Xs Pl)) K.weights :=
    atEight2 B (sentKey Xs Pl) Claim H
  have hfit := fits_key Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)
    hs.named.plan
  have hO' := over_key Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)
  have hno : NoStop (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs :=
    (AtPublicFiles.KeyFile.noStopAll_keyProver K qr qU qO qw).2.1
  have hM : ∀ b, MadeNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) b :=
    made_next _ hfit (by rw [hO'.bs]; exact (planOk_all hs.named.plan).2.1)
  obtain ⟨s₁, m₁, E₁, u₁, h₁⟩ := pair_one Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd Said o w₀ rc x
    hs scope k hV hI hKp hE hC hbare hS (hSN 0 (by omega))
  obtain ⟨l₁, l₂, -⟩ := AtPublicFiles.KeyThread.lengths scope hs.named
  have hl : (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = 12 := l₂
  have hb1 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[1]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 1 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  have hb2 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[2]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 2 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨blk₁, e₁⟩ := hb1
  obtain ⟨blk₂, e₂⟩ := hb2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := E8.eight
  obtain ⟨f₀, f₁, hfc⟩ := List.length_eq_two.1 (by simpa using of_atFull full_two hK₀)
  -- the member 1
  obtain ⟨hr1, ho1, hp1⟩ := hm 0 b1 rfl blk₁ e₁
  obtain ⟨p1, -, -, -⟩ := places4 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, o1, -, -, -, -⟩ := declares3 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hg1 : ({ place := place 1, parts := [liftK14 (planData (parKey Xs Pl)) K.weights quietPart] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) ∈
      (proverSidesOfSharedRounds (planData (parKey Xs Pl)) K.weights :
        List (Placed Empty (Common W₀ Rc TableKey) X₀)) := by
    rw [halves_eq]
    exact List.mem_append_left _ List.mem_cons_self
  have hf1 := E8.found _ hg1
  have hl1 := steps_half K₀ hK₀ pointPlace [1] (of_atFull full_point hK₀) (by decide) _ rfl rfl
    (fun i q hq => k14_stated hfc _ hsp₀ K.weights _ hg1 i q hq) blk₁ (hp1.trans p1)
    (by rw [ho1, o1, hr1, r1]; rfl) (by rw [hr1, r1]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs
    (by rw [hp1, p1]; exact hf1) k ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₁.st.input)
  obtain ⟨L₁, hL₁⟩ := hl1
  obtain ⟨s₂, m₂, E₂, u₂, h₂, -, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 1)
    (by omega) (by omega) hfit (hSN 1 (by omega)) (hM 1) e₁ u₁ (hd₁ _ e₁)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [blk₁] _ _) hL₁
  -- the member 2
  have hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨parKey Xs Pl, (planData (parKey Xs Pl)).atPoint⟩ K.weights (randKey K) :
      List (Placed Empty (Common W₀ Rc TableKey) X₀)), g ∈ (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs := by
    intro g hg
    refine sends_in K hsp g ?_
    rw [hsend]
    exact hg
  obtain ⟨SD, hf2⟩ := sendU_found E8 hh blk₂ e₂
  obtain ⟨-, -, hp2⟩ := hm 1 b2 rfl blk₂ e₂
  obtain ⟨-, pU, -, -⟩ := send_declares _ 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨d₀, d₁, os, hrr, hoo, hf₀, hf₁, ho₀, hs₀, ho₁, hs₁⟩ := SD.rounds
  have hpl : blk₂.place = foldedPlace := hp2.trans pU
  have hc : (⟨parKey Xs Pl, 0⟩ : K14.SendPub).P.codes = Lk6.AtPlan.keyFull.codes := by
    show (parKey Xs Pl).codes = _
    rw [e]
    rfl
  have hS : (⟨parKey Xs Pl, 0⟩ : K14.SendPub).P.S = Lk6.AtPlan.keyFull.once.shape := by
    show (parKey Xs Pl).S = _
    rw [e]
    rfl
  have hl2 := steps_half K₀ hK₀ foldedPlace [2] (of_atFull full_folded hK₀) (by decide)
    ({ place := blk₂.place
       parts := [liftSend (witOf (parKey Xs Pl) K.weights (randKey K))
         (sendingPart (jobU ⟨parKey Xs Pl, (planData (parKey Xs Pl)).atPoint⟩))] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) rfl rfl
    (fun i q hq => k14_sends_stated K₀ hK₀ ⟨parKey Xs Pl, 0⟩ hc hS K.weights (randKey K)
      ({ place := sendPlace 2
         parts := [liftSend (witOf (parKey Xs Pl) K.weights (randKey K))
           (sendingPart (jobU ⟨parKey Xs Pl, 0⟩))] } :
        Placed Empty (Common W₀ Rc TableKey) X₀)
      (by rw [sendHalves_eq]; exact List.mem_cons_self) i q hq) blk₂ hpl
    (by rw [hoo, hrr]; rfl) (by rw [hrr]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs hf2 k
    ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₂.st.input)
  obtain ⟨L₂, hL₂⟩ := hl2
  obtain ⟨s₃, m₃, E₃, u₃, h₃, kp, y, cols, hMv, hm₃, hE₃⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 2)
    (by omega) (by omega) hfit (hSN 2 (by omega)) (hM 2) e₂ u₂ (hd₂ _ e₂)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [blk₂] _ _) hL₂
  have hHeard : m₃.st.heard = ds₁ ++ ds₂ := by rw [h₃, h₂, h₁, List.nil_append]
  refine ⟨s₃, m₃, E₃, u₃, hHeard, ?_, ?_⟩
  -- at border 2 no message stands
  have hf2 : form2 (parKey Xs Pl) (fun _ _ => true) 2 s₂ = true := by
    have hh := u₂.1.2.2.1.1
    exact (Bool.and_eq_true_iff.mp hh).1
  have hsh : _root_.Desc.K14.Law.shapeP (parKey Xs Pl).par 0 s₂ = true := by
    unfold form2 at hf2
    rw [if_pos (by omega)] at hf2
    exact (Bool.and_eq_true_iff.mp hf2).1
  have hsz : s₂.st.oracles.size = 0 :=
    ((_root_.Desc.K14.Law.midB_iff _ _).1 ((_root_.Desc.K14.Law.shapeP_iff _ _ _).1 hsh).2.2.2).1
  -- what the sending has laid
  have k2 : keeps2 (parKey Xs Pl) (sentKey Xs Pl) 2 s₂ s₃ := by
    have kp' : keepsAll (parKey Xs Pl) (sentKey Xs Pl) Kp 2 s₂ s₃ := kp
    rw [keepsAll_eq _ _ _ 2 s₂ s₃ ⟨by omega, by omega⟩] at kp'
    exact kp'
  obtain ⟨ids, i0, i1, SA, -, -, -⟩ := k2.2.2.2.2.2.1 rfl
  obtain ⟨n, hn, hne⟩ := first_sampled (parKey Xs Pl) e (sentKey Xs Pl) rfl
  obtain ⟨y, hy, -, -, -, -, hq⟩ := SA.laid.new 0 n hn
  refine ⟨y, ?_, ?_⟩
  · have hy' : s₃.st.oracles[s₂.st.oracles.size + 0]? = some y := hy
    rw [hsz] at hy'
    exact hy'
  · rw [(hq hne).2]
    exact Nat.pos_of_ne_zero hne
  -- the tie of the tables to the words
  have hMv' := hMv
  obtain ⟨⟨l', hl', hy⟩, -⟩ := hMv
  obtain ⟨x₀, x₁, c, -, hcn, hpl', -⟩ := send_moved (jobU ⟨parKey Xs Pl, 0⟩)
    (witOf (parKey Xs Pl) K.weights (randKey K)) blk₂ d₀ d₁ os hrr hoo hf₀ hf₁ ho₀ hs₀ ho₁ hs₁ hf2 hl'
    m₂ ds₂ (hd₂ _ e₂)
  have ey := Except.ok.inj (hy.symm.trans hpl')
  rw [show blk₂.place = K14.sendPlace 2 from hp2.trans pU] at hcn
  have hV0 : m₂.st.input = inK w₀ rc x := u₂.1.2.2.2.2.2.2.1
  have hpos := (blocks_point (parKey Xs Pl) e b1 b2 b3 b4 b5 b6 b7 b8 hb)
  obtain ⟨rd, hrd, hdE⟩ := hpos
  have hfit₁ := hd₁ _ e₁
  rw [hr1, hrd] at hfit₁
  obtain ⟨dd, hds₁, hlen₁⟩ := one_draw hfit₁
  have hm₂h : m₂.st.heard = [dd] := by rw [h₂, h₁, List.nil_append, hds₁]
  have hfirst : firstRv m₃.st.heard = rvOf dd := by
    rw [hHeard, hds₁]
    rfl
  obtain ⟨-, -, hgo⟩ : True ∧ True ∧ _ := ⟨trivial, trivial, hQ.facts.goes⟩
  have eQ := jobU_par (Q := parKey Xs Pl) hgo 0
  have hs0 : ((jobU ⟨parKey Xs Pl, 0⟩).Q.sent.getD 0 default).shape = (parKey Xs Pl).par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (_root_.Desc.K14.Law.parU (parKey Xs Pl) (sentKey Xs Pl)) 0
      ⟨(parKey Xs Pl).par.S.fold.u, (parKey Xs Pl).par.S.fold.leafClass⟩
      (by rw [_root_.Desc.K14.Law.parK1_sent]; exact withU_zero hgo)).1
  have hsz : (jobU ⟨parKey Xs Pl, 0⟩).Q.sent.size ≤ 2 := by
    rw [eQ, _root_.Desc.K14.Law.parK1_sent, hQ.facts.goesTwo]
  have hSh : SendShapes (parKey Xs Pl) := hA.shapes
  have hagree := AtPublicFiles.KeyRowsAgree.rowsAgree_u (parKey Xs Pl)
    (_root_.Desc.K14.first (parKey Xs Pl).codes (inK w₀ rc x).key) (rvOf dd)
    (holds2 (parKey Xs Pl) K.weights (randKey K) k (inK w₀ rc x))
    (witOf (parKey Xs Pl) K.weights (randKey K) m₂.st.input) m₂.st.heard (coinsE c.1.1).toArray
    hsz hs0 hSh.u hSh.mask
    (by
      rw [← elems_one]
      show elems ((m₂.st.heard.drop 0).take 1) = _
      rw [hm₂h]
      rfl)
    (by
      rw [← elems_one, show elems [dd] = dd.elems.map OnBytes.E.ofTriple ++ [] from rfl,
        List.append_nil, List.length_map, hlen₁]
      exact hdE)
    (fun r q => by rw [hV0]; rfl)
    (by
      show readCoins (parKey Xs Pl).codes ((jobU ⟨parKey Xs Pl, 0⟩).Q.sent.getD 0 default).shape _ = _
      rw [hs0, coins_msg k (jobU ⟨parKey Xs Pl, 0⟩) (K14.sendPlace 2) hcn 0])
    (by
      rw [← coins_msg k (jobU ⟨parKey Xs Pl, 0⟩) (K14.sendPlace 2) hcn 1]
      show (holds2 (parKey Xs Pl) K.weights (randKey K) k (inK w₀ rc x)).cMask = _
      unfold holds2
      cases (parKey Xs Pl).S.testU.head? <;> rfl)
  have htab := sentTables_tie _ _ _ hagree
  refine ⟨s₂, m₂, E₂, blk₂, y, cols, u₂, e₂, hMv', hm₃, hE₃, ?_, ?_⟩
  · rw [ey, hfirst]
    exact congrArg (fun t => some (List.map some t)) (htab.trans (by rw [eQ]))
  · intro o part i ho
    have hw := word_at (o := o) (part := part) (i := i) (parKey Xs Pl) (sentKey Xs Pl) ℓ
      (holds2 (parKey Xs Pl) K.weights (randKey K)) rest k (inK w₀ rc x) m₃.st.heard ho hQ.facts.goesTwo
    have hv3 : m₃.st.input = inK w₀ rc x := u₃.1.2.2.2.2.2.2.1
    rw [hv3]
    exact hw

end

end AtPublicFiles.KeyStandThree

#print axioms AtPublicFiles.KeyStandThree.one_draw
#print axioms AtPublicFiles.KeyStandThree.point_closed
#print axioms AtPublicFiles.KeyStandThree.blocks_point
#print axioms AtPublicFiles.KeyStandThree.word_at
#print axioms AtPublicFiles.KeyStandThree.first_sampled_full
#print axioms AtPublicFiles.KeyStandThree.first_sampled
#print axioms AtPublicFiles.KeyStandThree.halves_key
#print axioms AtPublicFiles.KeyStandThree.next_pair
#print axioms AtPublicFiles.KeyStandThree.pair_three
