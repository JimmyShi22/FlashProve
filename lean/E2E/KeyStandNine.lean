-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandNine.lean: the key's shared thread at border 9: behind the eight members of the linear
claim, at a letter `Said`, at halves that send.

Why. `pair_three` (E2E/KeyStandThree.lean) has the thread behind «send o_u». The same steps carry it past
«(rec_gamma)», «LOC», «send o_omega», the joinings, «LIN zeta» and «SPLIT». Border 9 is the last border
before the first proximity test: no half of a test is reached.

Main names.
  `places_closed`, `counts_closed`: the eight members' places and their counts of rounds and oracle lists, at
    `QK`. By Lean's kernel.
  `full_loc`, `full_omega`, `full_zeta`, `full_split`: the three tests of `chainSteps` at these places, at the
    written book. By Lean's kernel.
  `HasRow`, `second_sampled_full`: a message with at least one sample row; both messages of the second
    sending are sampled.
  `pair_nine`: the pair at border 9; o_u, o_omega, o_sp each has a sample row in the state, G_u has
    answers + columns + 1 rows open and G_omega one.

What stays open. All premises of `pair_three`, and the lists of challenges. It is an implication
until a member is typed; see `stand_nine_full`. It is no run of the frame. It stands at no thread
behind border 9: the proximity tests' halves are not
reached. The tree-to-word tie: see the head of E2E/KeyStandMember.lean. It fires nothing behind `Thr` at borders 12 or 19.

NOT IN FRONT OF A LAW OVER COINS: `pair_nine` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: as at `pair_three`: `Said` under `hS` and `Vd` under `hV` are letters for
predicates, of the first kind, and `o` is no coin; `hSN` is bound over all coins and by itself picks none; `tt`
stands under no premise; `hKp`, `hE` name no coin. The thread's clauses at `k`, of the first kind; `F` where the input is made of the committer's coins; `hs`, `scope` read public files. None
of these is the term that the committer makes. None: the bar is flat. The closed facts name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyStandNine
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi sharedTests keyAsProof descriptionFromSource Claim)
open _root_.Desc.K14 (St blocks blocksOr)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub k14_stated k14_sends_stated of_atFull full_two atFull pointPlace
  foldedPlace gammaPlace locPlace omegaPlace joinsPlace zetaPlace splitPlace foldedTestPlace
  omegaTestPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared randK14)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey othersKey threadKey plan_key)
open AtPublicFiles.KeySharedQuiet (CellsAlone over_key fits_key)
open AtPublicFiles.KeyAsksKey (tableKey asks_key own_in sends_in)
open AtPublicFiles.KeyStandOne (startAt inK envK pair_one)
open AtPublicFiles.KeyStandThree (halves_key next_pair)
open AtPublicFiles.KeyHalfSteps (placeTests steps_half full_point full_folded)
open AtPublicFiles.KeyThread (steps_quiet_none)
open AtPublicFiles.Stops (NoStop)

/-- The state holds a message at the number o, and at least one sample row of it. -/
def HasRow (o : Nat) (s : St) : Prop :=
  ∃ y, s.st.oracles[o]? = some y ∧ 0 < y.sampleRows.size

theorem hasRow_quiet {o : Nat} {a b : St} (q : _root_.Desc.K14.Law.QuietStep a b) (h : HasRow o a) :
    HasRow o b := by
  obtain ⟨x, hx, hs⟩ := h
  have e := q.msgs.2 o
  rw [hx] at e
  obtain ⟨y, hy, e'⟩ := Option.map_eq_some_iff.1 e
  have e3 : y.sampleRows = x.sampleRows := (Prod.mk.inj (Prod.mk.inj e').2).2
  exact ⟨y, hy, by rw [e3]; exact hs⟩

theorem hasRow_send {o : Nat} {a b : St} (q : _root_.Desc.K14.Honest.SendStep a.st b.st)
    (hs : o < a.st.oracles.size) (h : HasRow o a) : HasRow o b := by
  obtain ⟨x, hx, hr⟩ := h
  exact ⟨x, by rw [q.old o hs]; exact hx, hr⟩

theorem hasRow_same {o : Nat} {a b : St} (e : b.st = a.st) (h : HasRow o a) : HasRow o b := by
  obtain ⟨x, hx, hr⟩ := h
  exact ⟨x, by rw [e]; exact hx, hr⟩

/-- Both messages of «send o_omega» are sampled, at the written value. By Lean's kernel. -/
theorem second_sampled_full :
    (((_root_.Desc.K14.withOmega QK.S)[0]?).map (·.shape.answers)).getD 0 ≠ 0 ∧
      (((_root_.Desc.K14.withOmega QK.S)[1]?).map (·.shape.answers)).getD 0 ≠ 0 := by
  decide +kernel

/-- So at a value that is the written one. -/
theorem second_sampled (Q : _root_.Desc.K14.P14) (e : Q = QK) :
    (∃ n, (_root_.Desc.K14.Law.parO Q).sent[0]? = some n ∧ n.shape.answers ≠ 0) ∧
      (∃ n, (_root_.Desc.K14.Law.parO Q).sent[1]? = some n ∧ n.shape.answers ≠ 0) := by
  subst e
  obtain ⟨h0, h1⟩ := second_sampled_full
  rw [_root_.Desc.K14.Law.parO, _root_.Desc.K14.Law.parK1_sent]
  constructor
  · cases hn : (_root_.Desc.K14.withOmega QK.S)[0]? with
    | none =>
      rw [hn] at h0
      exact absurd rfl h0
    | some n =>
      rw [hn] at h0
      exact ⟨n, rfl, h0⟩
  · cases hn : (_root_.Desc.K14.withOmega QK.S)[1]? with
    | none =>
      rw [hn] at h1
      exact absurd rfl h1
    | some n =>
      rw [hn] at h1
      exact ⟨n, rfl, h1⟩

/-- The rows named at border 9 are ranges with something in them, at the written value. -/
theorem ranges_closed : 0 < QK.par.S.fold.index.answers ∧ 0 < QK.par.S.fold.columns := by
  decide +kernel

theorem places_closed : (blocksOr QK).map (·.place) =
    [pointPlace, foldedPlace, gammaPlace, locPlace, omegaPlace, joinsPlace, zetaPlace, splitPlace] := by
  decide +kernel

theorem counts_closed : (blocksOr QK).map (fun b => (b.rounds.length, b.oracles.length)) =
    [(1, 1), (2, 2), (0, 0), (1, 1), (2, 2), (0, 0), (1, 1), (1, 1)] := by
  decide +kernel

theorem full_loc : atFull (fun K => placeTests K locPlace [1]) = true := by decide +kernel
theorem full_omega : atFull (fun K => placeTests K omegaPlace [2]) = true := by decide +kernel
theorem full_zeta : atFull (fun K => placeTests K zetaPlace [1]) = true := by decide +kernel
theorem full_split : atFull (fun K => placeTests K splitPlace [1]) = true := by decide +kernel

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

/-- **The thread at border 9**, at the letter.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem pair_nine {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
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
    (tU : K.onU.place = foldedTestPlace) (tO : K.onOmega.place = omegaTestPlace)
    (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true)
    (hd4 : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true)
    (hd5 : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true)
    (hd7 : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true)
    (hd8 : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true)
    (hS : Said 0 k (startAt K o (inK w₀ rc x)))
    (hSN : ∀ b, b < 9 → SaidNext (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)) Said b) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x))
        Said 9 k s m E ∧
      m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ∧
      HasRow (num .oU) s ∧ HasRow (num .oOmega) s ∧ HasRow (num .oSp) s ∧
      (_root_.Desc.K14.Law.rowsOn s s.loc.gU).length = (parKey Xs Pl).par.S.fold.index.answers +
        (parKey Xs Pl).par.S.fold.columns + 1 ∧
      (_root_.Desc.K14.Law.rowsOn s s.loc.gOmega).length = 1 ∧
      0 < (parKey Xs Pl).par.S.fold.index.answers ∧ 0 < (parKey Xs Pl).par.S.fold.columns := by
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
  obtain ⟨d₀, d₁, os, hrr, hoo, -⟩ := SD.rounds
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
  obtain ⟨s₃, m₃, E₃, u₃, h₃, kp₃, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 2)
    (by omega) (by omega) hfit (hSN 2 (by omega)) (hM 2) e₂ u₂ (hd₂ _ e₂)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [blk₂] _ _) hL₂

  -- closed facts at this value
  have pc := places_closed
  rw [← e] at pc
  have cc := counts_closed
  rw [← e] at cc
  have eb : blocksOr (parKey Xs Pl) = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hb]
    rfl
  rw [eb] at pc cc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at pc cc
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := pc
  obtain ⟨⟨c1r, c1o⟩, ⟨c2r, c2o⟩, ⟨c3r, c3o⟩, ⟨c4r, c4o⟩, ⟨c5r, c5o⟩, ⟨c6r, c6o⟩, ⟨c7r, c7o⟩,
    ⟨c8r, c8o⟩⟩ := cc
  have none_at : ∀ (blk : Block St Claim), blk.place ∉ [K14.place 1, K14.sendPlace 2, K14.place 4,
      K14.sendPlace 5, K14.place 7, K14.place 8, foldedTestPlace, omegaTestPlace] →
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs.find? fun g => g.place == blk.place) = none := by
    intro blk hn
    rw [List.find?_eq_none]
    intro g hg hbq
    apply hn
    have hmem : g.place ∈ (keyProver K).shared.map (·.place) := List.mem_map.2 ⟨g, hg, rfl⟩
    rw [keyProver_shared K hsp, tU, tO] at hmem
    rw [← beq_iff_eq.1 hbq]
    exact hmem
  have hb3 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[3]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 3 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₃, e₃⟩ := hb3
  have hb4 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[4]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 4 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₄, e₄⟩ := hb4
  have hb5 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[5]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 5 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₅, e₅⟩ := hb5
  have hb6 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[6]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 6 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₆, e₆⟩ := hb6
  have hb7 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[7]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 7 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₇, e₇⟩ := hb7
  have hb8 : ∃ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).bs[8]? = some blk := by
    rw [hO'.bs]
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    show 8 < (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    rw [hl]
    decide
  obtain ⟨bk₈, e₈⟩ := hb8

  -- the member 3: no round, no half
  obtain ⟨hr3, ho3, hp3⟩ := hm 2 b3 rfl bk₃ e₃
  have hR3 : bk₃.rounds = [] := List.length_eq_zero_iff.1 (by rw [hr3]; exact c3r)
  have hO3 : bk₃.oracles = [] := List.length_eq_zero_iff.1 (by rw [ho3]; exact c3o)
  have hF3 := none_at bk₃ (by rw [hp3, q3]; decide)
  obtain ⟨s₄, m₄, E₄, u₄, h₄, kp₄, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 3) (l := []) (ds := [])
    (by omega) (by omega) hfit (hSN 3 (by omega)) (hM 3) e₃ u₃ (by rw [hR3]; rfl)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₃] _ _) (steps_quiet_none hR3 hO3 hF3)
  -- the member 4
  obtain ⟨hr4, ho4, hp4⟩ := hm 3 b4 rfl bk₄ e₄
  have hg4 : ({ place := place 4, parts := [liftK14 (planData (parKey Xs Pl)) K.weights quietPart] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) ∈
      (proverSidesOfSharedRounds (planData (parKey Xs Pl)) K.weights :
        List (Placed Empty (Common W₀ Rc TableKey) X₀)) := by
    rw [halves_eq]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨L₄, hL₄⟩ := steps_half K₀ hK₀ locPlace [1] (of_atFull full_loc hK₀) (by decide) _ rfl rfl
    (fun i q hq => k14_stated hfc _ hsp₀ K.weights _ hg4 i q hq) bk₄ (hp4.trans q4)
    (by rw [ho4, hr4, c4o, c4r]) (by rw [hr4, c4r]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs
    (by rw [hp4, q4]; exact E8.found _ hg4) k ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₄.st.input)
  obtain ⟨s₅, m₅, E₅, u₅, h₅, kp₅, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 4)
    (by omega) (by omega) hfit (hSN 4 (by omega)) (hM 4) e₄ u₄ (hd4 _ e₄)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₄] _ _) hL₄
  -- the member 5
  obtain ⟨SD5, hf5⟩ := sendOmega_found E8 hh bk₅ e₅
  obtain ⟨-, -, hp5⟩ := hm 4 b5 rfl bk₅ e₅
  obtain ⟨d₅₀, d₅₁, os₅, hrr5, hoo5, -⟩ := SD5.rounds
  obtain ⟨L₅, hL₅⟩ := steps_half K₀ hK₀ omegaPlace [2] (of_atFull full_omega hK₀) (by decide)
    ({ place := bk₅.place
       parts := [liftSend (witOf (parKey Xs Pl) K.weights (randKey K))
         (sendingPart (jobOmega ⟨parKey Xs Pl, (planData (parKey Xs Pl)).atPoint⟩))] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) rfl rfl
    (fun i q hq => k14_sends_stated K₀ hK₀ ⟨parKey Xs Pl, 0⟩ hc hS K.weights (randKey K)
      ({ place := sendPlace 5
         parts := [liftSend (witOf (parKey Xs Pl) K.weights (randKey K))
           (sendingPart (jobOmega ⟨parKey Xs Pl, 0⟩))] } :
        Placed Empty (Common W₀ Rc TableKey) X₀)
      (by rw [sendHalves_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self) i q hq) bk₅
    (hp5.trans q5) (by rw [hoo5, hrr5]; rfl) (by rw [hrr5]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs hf5 k
    ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₅.st.input)
  obtain ⟨s₆, m₆, E₆, u₆, h₆, kp₆, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 5)
    (by omega) (by omega) hfit (hSN 5 (by omega)) (hM 5) e₅ u₅ (hd5 _ e₅)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₅] _ _) hL₅
  -- the member 6: no round, no half
  obtain ⟨hr6, ho6, hp6⟩ := hm 5 b6 rfl bk₆ e₆
  have hR6 : bk₆.rounds = [] := List.length_eq_zero_iff.1 (by rw [hr6]; exact c6r)
  have hO6 : bk₆.oracles = [] := List.length_eq_zero_iff.1 (by rw [ho6]; exact c6o)
  have hF6 := none_at bk₆ (by rw [hp6, q6]; decide)
  obtain ⟨s₇, m₇, E₇, u₇, h₇, kp₇, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 6) (l := []) (ds := [])
    (by omega) (by omega) hfit (hSN 6 (by omega)) (hM 6) e₆ u₆ (by rw [hR6]; rfl)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₆] _ _) (steps_quiet_none hR6 hO6 hF6)
  -- the member 7
  obtain ⟨hr7, ho7, hp7⟩ := hm 6 b7 rfl bk₇ e₇
  have hg7 : ({ place := place 7, parts := [liftK14 (planData (parKey Xs Pl)) K.weights quietPart] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) ∈
      (proverSidesOfSharedRounds (planData (parKey Xs Pl)) K.weights :
        List (Placed Empty (Common W₀ Rc TableKey) X₀)) := by
    rw [halves_eq]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨L₇, hL₇⟩ := steps_half K₀ hK₀ zetaPlace [1] (of_atFull full_zeta hK₀) (by decide) _ rfl rfl
    (fun i q hq => k14_stated hfc _ hsp₀ K.weights _ hg7 i q hq) bk₇ (hp7.trans q7)
    (by rw [ho7, hr7, c7o, c7r]) (by rw [hr7, c7r]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs
    (by rw [hp7, q7]; exact E8.found _ hg7) k ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₇.st.input)
  obtain ⟨s₈, m₈, E₈, u₈, h₈, kp₈, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 7)
    (by omega) (by omega) hfit (hSN 7 (by omega)) (hM 7) e₇ u₇ (hd7 _ e₇)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₇] _ _) hL₇
  -- the member 8
  obtain ⟨hr8, ho8, hp8⟩ := hm 7 b8 rfl bk₈ e₈
  have hg8 : ({ place := place 8
                parts := [liftK14 (planData (parKey Xs Pl)) K.weights
                  (splitPart (planData (parKey Xs Pl)))] } :
      Placed Empty (Common W₀ Rc TableKey) X₀) ∈
      (proverSidesOfSharedRounds (planData (parKey Xs Pl)) K.weights :
        List (Placed Empty (Common W₀ Rc TableKey) X₀)) := by
    rw [halves_eq, hsp₀, if_pos rfl]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨L₈, hL₈⟩ := steps_half K₀ hK₀ splitPlace [1] (of_atFull full_split hK₀) (by decide) _ rfl rfl
    (fun i q hq => k14_stated hfc _ hsp₀ K.weights _ hg8 i q hq) bk₈ (hp8.trans q8)
    (by rw [ho8, hr8, c8o, c8r]) (by rw [hr8, c8r]; rfl) (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).hs
    (by rw [hp8, q8]; exact E8.found _ hg8) k ((threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).φ.sees m₈.st.input)
  obtain ⟨s₉, m₉, E₉, u₉, h₉, kp₉, -⟩ := next_pair Xs Nr Pl K₀ K ℓ Nm Mg₀ tk tt rest Kp Vd Said w₀ rc x hA (b := 8)
    (by omega) (by omega) hfit (hSN 8 (by omega)) (hM 8) e₈ u₈ (hd8 _ e₈)
    (AtPublicFiles.Stops.chainStopAt_none _ hno [bk₈] _ _) hL₈
  have toK : ∀ b, 1 ≤ b → b ≤ 8 → ∀ a c, (threadKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd (inK w₀ rc x)).keeps b a c →
      keeps2 (parKey Xs Pl) (sentKey Xs Pl) b a c := by
    intro b h1 h8 a c kk
    have kp' : keepsAll (parKey Xs Pl) (sentKey Xs Pl) Kp b a c := kk
    rw [keepsAll_eq _ _ _ b a c ⟨h1, h8⟩] at kp'
    exact kp'
  -- no message at border 2, two at border 5
  have formAt : ∀ (b : Nat) (hb : 2 ≤ b ∧ b ≤ 9) (a : St), (form2 (parKey Xs Pl) (fun _ _ => true) b a &&
      (!decide ((VerifiableInference.Desc.Shared.sharedPlaces true).length ≤ b) || true)) = true →
      _root_.Desc.K14.Law.shapeK (parKey Xs Pl).par 0 2 (parKey Xs Pl).par.S.fold.columns b a = true := by
    intro b hb a hh
    have h2 := (Bool.and_eq_true_iff.mp hh).1
    unfold form2 at h2
    rw [if_pos hb] at h2
    exact (Bool.and_eq_true_iff.mp h2).1
  have hsz2 : s₂.st.oracles.size = 0 :=
    ((_root_.Desc.K14.Law.midB_iff _ _).1 ((_root_.Desc.K14.Law.shapeP_iff _ _ _).1
      (formAt 2 ⟨by omega, by omega⟩ s₂ u₂.1.2.2.1.1)).2.2.2).1
  have hsz5 : s₅.st.oracles.size = 2 :=
    ((_root_.Desc.K14.Law.midB_iff _ _).1 ((_root_.Desc.K14.Law.shapeM_iff _ _ _ _ _).1
      (formAt 5 ⟨by omega, by omega⟩ s₅ u₅.1.2.2.1.1)).2).1
  have k2 := toK 2 (by omega) (by omega) _ _ kp₃
  have k3 := toK 3 (by omega) (by omega) _ _ kp₄
  have k4 := toK 4 (by omega) (by omega) _ _ kp₅
  have k5 := toK 5 (by omega) (by omega) _ _ kp₆
  have k6 := toK 6 (by omega) (by omega) _ _ kp₇
  have k7 := toK 7 (by omega) (by omega) _ _ kp₈
  have k8 := toK 8 (by omega) (by omega) _ _ kp₉
  have q3 := k3.1 (Or.inl rfl)
  have q4 := k4.1 (Or.inr (Or.inl rfl))
  have q6 := k6.1 (Or.inr (Or.inr (Or.inl rfl)))
  have q8 := k8.1 (Or.inr (Or.inr (Or.inr rfl)))
  have e7 : s₈.st = s₇.st := (k7.2.1 rfl).1
  have send5 := (k5.2.2.2.1 rfl).2.2.2
  -- o_u
  obtain ⟨ids, i0, i1, SA, -, -, -⟩ := k2.2.2.2.2.2.1 rfl
  obtain ⟨n, hn, hne⟩ := AtPublicFiles.KeyStandThree.first_sampled (parKey Xs Pl) e (sentKey Xs Pl) rfl
  obtain ⟨y, hy, -, -, -, -, hq⟩ := SA.laid.new 0 n hn
  have rU₃ : HasRow 0 s₃ := ⟨y, by
    have hy' : s₃.st.oracles[s₂.st.oracles.size + 0]? = some y := hy
    rw [hsz2] at hy'
    exact hy', by
    rw [(hq hne).2]
    exact Nat.pos_of_ne_zero hne⟩
  have rU₅ : HasRow 0 s₅ := hasRow_quiet q4 (hasRow_quiet q3 rU₃)
  have rU₆ : HasRow 0 s₆ := hasRow_send send5 (by rw [hsz5]; omega) rU₅
  -- o_omega and o_sp
  obtain ⟨ids', j0, j1, SB, -, -, -⟩ := k5.2.2.2.2.2.2.1 rfl
  obtain ⟨⟨n₀, hn₀, hne₀⟩, ⟨n₁, hn₁, hne₁⟩⟩ := second_sampled (parKey Xs Pl) e
  obtain ⟨z₀, hz₀, -, -, -, -, hq₀⟩ := SB.laid.new 0 n₀ hn₀
  obtain ⟨z₁, hz₁, -, -, -, -, hq₁⟩ := SB.laid.new 1 n₁ hn₁
  have rO₆ : HasRow 2 s₆ := ⟨z₀, by
    have hy' : s₆.st.oracles[s₅.st.oracles.size + 0]? = some z₀ := hz₀
    rw [hsz5] at hy'
    exact hy', by
    rw [(hq₀ hne₀).2]
    exact Nat.pos_of_ne_zero hne₀⟩
  have rS₆ : HasRow 3 s₆ := ⟨z₁, by
    have hy' : s₆.st.oracles[s₅.st.oracles.size + 1]? = some z₁ := hz₁
    rw [hsz5] at hy'
    exact hy', by
    rw [(hq₁ hne₁).2]
    exact Nat.pos_of_ne_zero hne₁⟩
  have carry : ∀ o, HasRow o s₆ → HasRow o s₉ := fun o h =>
    hasRow_quiet q8 (hasRow_same e7 (hasRow_quiet q6 h))
  -- the rows at border 9
  have h9 := formAt 9 ⟨by omega, by omega⟩ s₉ u₉.1.2.2.1.1
  have hO9 := (_root_.Desc.K14.Law.shapeO_iff _ _ _ _ _ _).1 h9
  have hU9 := (_root_.Desc.K14.Law.shapeU_iff _ _ _ _).1 hO9.1
  have rc := ranges_closed
  rw [← e] at rc
  refine ⟨s₉, m₉, E₉, u₉, ?_, carry _ rU₆, carry _ rO₆, carry _ rS₆, hU9.2.2.2, hO9.2.2.2.2.1, rc.1, rc.2⟩
  rw [h₉, h₈, h₇, h₆, h₅, h₄, h₃, h₂, h₁]
  simp

end

end AtPublicFiles.KeyStandNine

#print axioms AtPublicFiles.KeyStandNine.hasRow_quiet
#print axioms AtPublicFiles.KeyStandNine.hasRow_send
#print axioms AtPublicFiles.KeyStandNine.hasRow_same
#print axioms AtPublicFiles.KeyStandNine.second_sampled_full
#print axioms AtPublicFiles.KeyStandNine.second_sampled
#print axioms AtPublicFiles.KeyStandNine.ranges_closed
#print axioms AtPublicFiles.KeyStandNine.places_closed
#print axioms AtPublicFiles.KeyStandNine.counts_closed
#print axioms AtPublicFiles.KeyStandNine.full_loc
#print axioms AtPublicFiles.KeyStandNine.full_omega
#print axioms AtPublicFiles.KeyStandNine.full_zeta
#print axioms AtPublicFiles.KeyStandNine.full_split
#print axioms AtPublicFiles.KeyStandNine.pair_nine
