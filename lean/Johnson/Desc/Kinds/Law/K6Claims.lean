-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Claims.lean: WHAT BOTH ROADS TO K6Out (Law/RowPins.lean: the fifth premise
of the output head's law) SHARE, CUT FREE OF THE BATCHING KIND's LAW: no file on RunOk's ground is
imported. Definitions, statements and proofs, TO THE LETTER out of Law/JoinRunAtS.lean,
Law/K6PromiseBorder.lean, Law/K6OutOfTerms.lean [not in this library],
Law/K6OutExchange.lean [not in this library] and Law/K6InOfBatching.lean [not in this library].

  1 THE RUN "join".  join_spec: where it returns. wide_bare. keyVectorsAt: the six calls' key
    vectors at given letters. join_hands: it hands back the record with one owed claim marked.
  2 THE HEAD's OWN HEARING AT A RECORD.  K6HeardAt · ledger_front · k6HeardAt_front · KeepsK6 (what
    a block between must keep) · k6HeardAt_keeps · k6Ready_at · k6_border (behind every yes of the
    head's block's step).
  3 FROM THE SEAT's CLAIMS TO K6Out.  claimsSeat, claimsTrue: the two fillings of the reads.
    K6Exchange: the exchange, as a sentence. joinForm_two · value_agree0 · cEnd_same.
    formsAt_of_claims, joinOpened_of_claims: two of the three sentences into which
    Law/WeightTwinAt.lean's k6Out_iff cuts K6Out. k6Out_of_claims: all three joined.
  4 THE EXCHANGE PAID.  noEnts_* · heardBare_of_hear (what the head's hearing returns names no
    entry) · keyVector_two · k6Exchange_of_entries: from Law/AlikeWorth.lean's EntriesAlike.
    join_slots_filled: every slot that the form of "join" names
    is filled.
  5 sizes_of_plan: two facts on the sizes, from the tests on the plan.

WHAT IT IS NOT. Implications all. K6Out is paid by nothing here: k6Out_of_claims takes the seat's
claims worth 0, the exchange, WeightAt, and that the lookup's last claim is worth the same in the
two worlds. x, the seat's filling of the reads, is a bare letter in part 3: its users pin it. The
block in k6_border is blockOf's, not the lot's guarded block. KeepsK6 is shown of no block. Nothing
on soundness.
LETTERS. K6HeardAt: g, H, F0, G, rs under "there are": g, H by the two readers' equations at the
record; F0, rs, G tied to H by the hearing's equation and to the record by "later".
K6Exchange.forms: fs, f: by the lookup's equation, the membership and the equation of worths.
join_spec, join_hands: by equations at the record.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsStill
import Johnson.Desc.Kinds.Law.KeysHave
import Johnson.Desc.Kinds.Law.RowFront
import Johnson.Desc.Kinds.Law.RunsFixedFront
import Johnson.Desc.Kinds.Law.K06HonestWhole
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.OpenedAll
import Johnson.Desc.Kinds.Law.WorldTie
import Johnson.Desc.Kinds.Law.OpenedSent
import Johnson.Desc.Kinds.Law.OpenedFromSeat
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.Kinds.Law.AlikeWorth
import Johnson.Desc.Kinds.Law.CoveredNormAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open Norm (lt ls d lPd T S2)

/-! ## 1 The run "join" -/

/-- **Where "join" returns.** -/
theorem join_spec (keys : S → Option (Array Aff)) (n : Nat) (s : S) (c : List Claim) (s₁ : S)
    (hy : K3.joinRun (K3.seatCalls asClaim) keys n s = .ok (c, s₁)) :
    ∃ (F : Fork) (g : OnBytes.Model.Forest.Heard) (KF : Array Aff), s.fork? = some F ∧
      s.lookHeard? = some g ∧ keys s = some KF ∧ c = [asClaim (Came.joinForm g KF)] ∧
      s₁ = s.putFork (F.paid g.owedJoin) := by
  unfold K3.joinRun at hy
  simp only [bind, Except.bind] at hy
  cases hF : (K3.seatCalls asClaim).fork s with
  | none => simp [hF, named] at hy
  | some F =>
    cases hg : (K3.seatCalls asClaim).heard s with
    | none => simp [hF, hg, named] at hy
    | some g =>
      simp only [hF, hg, named] at hy
      split at hy
      · cases hy
      · cases hK : keys s with
        | none => simp [hK] at hy
        | some KF =>
          simp only [hK] at hy
          cases hj : First.Look.joinF g KF F [] with
          | none => simp [hj] at hy
          | some x =>
            simp only [hj] at hy
            obtain ⟨_, hG, _, hx⟩ := (Came.joinF_spec g KF F x.2.1 [] x.2.2 x.1).mp hj
            have e := Except.ok.inj hy
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            refine ⟨F, g, KF, hF, hg, rfl, ?_, ?_⟩
            · rw [← e1, ← hx]
              rfl
            · rw [← e2, ← hG]
              rfl

/-- At the seat at the carried record an entry of the read "wide" names no slot. -/
theorem wide_bare (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s : S}
    {x : FinalNorm.Reads × Reads} (e : (seatAt h iU3).reads s = some x) :
    ∀ i, (x.1.wide i).slots = #[] := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · obtain ⟨tt, _, e1⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨tr, _, e2⟩ := Option.bind_eq_some_iff.mp e1
    split at e2
    · cases e2
    · have e3 := Option.some.inj e2
      subst e3
      exact fun _ => rfl
  · cases e

/-- The six calls' key vectors at given letters: the text of HeadCaller.lean's callerKeys. -/
def keyVectorsAt (v : Given × Behind × Places) : Array Form :=
  ((fun (g : Given) (_ : Behind) (_ : Places) => g.calls.map fun c => keyVector key c.1 c.2)
    v.1 v.2.1 v.2.2).toArray

section Hands

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **"join" hands back the record with one owed claim of the head's ledger marked.** -/
theorem join_hands (n : Nat) (e : S) (c : List Claim) (e₁ : S)
    (hr : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n e = .ok (c, e₁)) :
    ∃ (a : HeadOwn) (i : Nat), e.here = .head a ∧
      e₁ = { e with here := .head { a with F := a.F.paid i } } := by
  obtain ⟨F, g, KF, hF, _, _, _, rfl⟩ := join_spec _ n e c e₁ hr
  unfold S.fork? at hF
  cases hh : e.here with
  | head a =>
    rw [hh] at hF
    by_cases ho : a.opened = true
    · simp only [ho, if_true, Option.some.injEq] at hF
      refine ⟨a, g.owedJoin, rfl, ?_⟩
      unfold S.putFork
      rw [hh]
      simp only [ho, if_true, hF]
    · simp [ho] at hF
  | lay a =>
    exfalso
    obtain ⟨_, _, KF', _, _, hK, _, _⟩ := join_spec _ n e c _ hr
    unfold callerKeys at hK
    obtain ⟨v, hv, _⟩ := Option.map_eq_some_iff.mp hK
    cases hl : lettersAt p (seatAt h iU3) e with
    | error m => rw [hl] at hv; cases hv
    | ok w =>
      unfold lettersAt at hl
      have hH : (seatAt h iU3).heard e = none := by
        show (match e.here with
          | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
            allOf o.F x (some (keptOf q x.wpl.sL))
          | _ => none) = none
        rw [hh]
      cases hg : given p (seatAt h iU3) e with
      | error m => rw [hg] at hl; cases hl
      | ok g' => rw [hg, hH] at hl; cases hl
  | att a =>
    exfalso
    obtain ⟨_, _, KF', _, _, hK, _, _⟩ := join_spec _ n e c _ hr
    unfold callerKeys at hK
    obtain ⟨v, hv, _⟩ := Option.map_eq_some_iff.mp hK
    cases hl : lettersAt p (seatAt h iU3) e with
    | error m => rw [hl] at hv; cases hv
    | ok w =>
      unfold lettersAt at hl
      have hH : (seatAt h iU3).heard e = none := by
        show (match e.here with
          | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
            allOf o.F x (some (keptOf q x.wpl.sL))
          | _ => none) = none
        rw [hh]
      cases hg : given p (seatAt h iU3) e with
      | error m => rw [hg] at hl; cases hl
      | ok g' => rw [hg, hH] at hl; cases hl
  | between => rw [hh] at hF; cases hF
  | fin a => rw [hh] at hF; cases hF
  | mem a => rw [hh] at hF; cases hF

end Hands

/-! ## 2 The head's own hearing at a record -/

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **The head's own hearing is read back at the record.** -/
def K6HeardAt (s : S) : Prop :=
  ∃ (g : Given) (H : HeardAll) (F0 G : Fork) (rs : List Fmt.RoundView),
    given p (seatAt h iU3) s = .ok g ∧ (seatAt h iU3).heard s = some H ∧ WellLaid F0 ∧
    hear F0 rs = some (H, G, []) ∧ Later G ((seatAt h iU3).ledger s)

theorem ledger_front {s s' : S} (a : AlikeFront s s') :
    Later ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') := by
  obtain ⟨o, o', ho, ho', _, _, eo, _, _, _, hL⟩ := a
  show Later (s.fork?.getD {}) (s'.fork?.getD {})
  unfold S.fork?
  rw [ho, ho']
  simp only [eo]
  cases o.opened
  · exact Later.refl _
  · exact hL

/-- **It is carried along AlikeFront.** -/
theorem k6HeardAt_front {s s' : S} (a : AlikeFront s s') (k : K6HeardAt h iU3 p s) :
    K6HeardAt h iU3 p s' := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW, hh, hL⟩ := k
  exact ⟨g, H, F0, G, rs, (given_front h iU3 p a).trans hg, heard_front h iU3 a H hH, hW, hh,
    hL.trans (ledger_front h iU3 a)⟩

/-- **WHAT A BLOCK BETWEEN MUST KEEP.** -/
def KeepsK6 {Cl : Type} (b : Block S Cl) : Prop :=
  ∀ (firstTree : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    (∃ o, s.here = .head o) → b.step firstTree s rs cols = .ok (s', n) → AlikeFront s s'

theorem k6HeardAt_keeps {Cl : Type} (b : Block S Cl) (hb : KeepsK6 b) (firstTree : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat)
    (hs : b.step firstTree s rs cols = .ok (s', n)) (k : K6HeardAt h iU3 p s) :
    K6HeardAt h iU3 p s' := by
  refine k6HeardAt_front h iU3 p (hb firstTree s rs cols s' n ?_ hs) k
  obtain ⟨_, H, _, _, _, _, hH, _⟩ := k
  cases hh : s.here with
  | head o => exact ⟨o, rfl⟩
  | _ =>
    exfalso
    have hN : (seatAt h iU3).heard s = none := by
      show (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          allOf o.F x (some (keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    rw [hN] at hH
    cases hH

/-- **K6HeardAt AT A RECORD IS K6Ready AT WHAT THE RECORD SHOWS AND ITS OWN LEDGER.** -/
theorem k6Ready_at {s : S} {z : Seen} {U : Fork} (k : K6HeardAt h iU3 p s)
    (hz : seenOf s = some z) (hF : s.fork? = some U) : K6Ready h iU3 p z U := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW, hh, hL⟩ := k
  have hU : (seatAt h iU3).ledger s = U := by
    show s.fork?.getD {} = U
    rw [hF]
    rfl
  exact ⟨s, g, H, F0, G, rs, sees_of_seen hz hF, hg, hH, hW, hh, hU ▸ hL⟩

end At

/-- **BEHIND EVERY YES OF THE HEAD's BLOCK's STEP.** -/
theorem k6_border (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (firstTree : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (n : Nat) (hOn : K6On W s) (hcan : Canonical rs)
    (hstep : b.step firstTree s rs cols = .ok (s', n)) :
    K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s' := by
  obtain ⟨gs, hd⟩ := Came.step_decide firstTree b s rs cols s' n hstep
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  have hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
  rw [hr] at hWL ⊢
  have hd' : (blockAt W.hS iU3 (workOf W) l).decide s (rs.map noDigest) gs = .ok s' := hd
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, hs'⟩ :=
    decide_hears_at W.hS iU3 (workOf W) l s s' (rs.map noDigest) gs hd'
  obtain ⟨b1, b2, b3, _⟩ := seatBack_at W.hS iU3 (workOf W) s g (rs.map noDigest) [] F H w s1 s2 hg
    hWL (Came.canonical_noDigest hcan) hh e1 e2
  rw [hs']
  exact ⟨g, H, _, F, rs.map noDigest, b3.trans hg, b2, hWL, hh, by rw [b1]; exact Later.refl _⟩

/-! ## 3 From the seat's claims to K6Out -/

/-- The three runs' forms at letters as the seat reads them: the reads' entries are variables. -/
def claimsSeat (v : Given × Behind × Places) : List (String × List Form) :=
  (fun (_ : Given) (_ : Behind) (_ : Places) => claims) v.1 v.2.1 v.2.2

/-- The same with the reads read as the stated sums of the cells: the filling of the head's law. -/
def claimsTrue (g : Given) (H : HeardAll) (c : NCells) : List (String × List Form) :=
  let _ : Norm.Heard := H.1
  let _ : FinalNorm.Heard := H.2.1
  let _ : Heard := H.2.2
  let _ : FinalNorm.Reads := normReadsAtCells c
  let _ : Reads := readsAt c.toCells
  claims

/-- **THE EXCHANGE, AS A NAMED PREMISE.** W₁: the witness's world; W₂: the head's law's. -/
structure K6Exchange (g : Given) (H : HeardAll) (x : FinalNorm.Reads × Reads) (c : NCells)
    (W₁ W₂ : World K) : Prop where
  forms : ∀ name fs', (claimsTrue g H c).lookup name = some fs' → ∀ f' ∈ fs',
    ∃ fs f, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs ∧ f ∈ fs ∧
      vW W₁ f = vW W₂ f'
  keys : ∀ call, call < g.calls.length →
    vW W₁ ((keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).getD call (Aff.ofConst zeroE)) =
      vW W₂ ((keysAt g H c).getD call (Aff.ofConst zeroE))

section Two

variable (W₁ W₂ : World K)

theorem joinFold_two (g : OnBytes.Model.Forest.Heard) (KF KF' : Array Aff) :
    ∀ (l : List Nat) (f f' : Aff), vW W₁ f = vW W₂ f' →
    (∀ c, c ∈ l → vW W₁ (KF.getD c (Aff.ofConst zeroE)) = vW W₂ (KF'.getD c (Aff.ofConst zeroE))) →
    vW W₁ (l.foldl (Came.joinStep g KF) f) = vW W₂ (l.foldl (Came.joinStep g KF') f')
  | [], _, _, h, _ => h
  | c :: l, f, f', h, hk => by
    simp only [List.foldl_cons]
    refine joinFold_two g KF KF' l _ _ ?_ fun c' hc' => hk c' (List.mem_cons_of_mem _ hc')
    have h' := hk c List.mem_cons_self
    unfold vW at h h' ⊢
    unfold Came.joinStep
    rw [Aff.value_addMul, Aff.value_addMul, Aff.value_sub, Aff.value_sub, Aff.value_ofConst,
      Aff.value_ofConst, h, h']

/-- **The form of "join" in two worlds.** -/
theorem joinForm_two (g : OnBytes.Model.Forest.Heard) (KF KF' : Array Aff)
    (hs : KF.size = KF'.size)
    (hk : ∀ c, c < KF.size →
      vW W₁ (KF.getD c (Aff.ofConst zeroE)) = vW W₂ (KF'.getD c (Aff.ofConst zeroE)))
    (hc : vW W₁ g.cEnd = vW W₂ g.cEnd) :
    vW W₁ (Came.joinForm g KF) = vW W₂ (Came.joinForm g KF') := by
  have hf := joinFold_two W₁ W₂ g KF KF' (List.range KF.size) (Aff.ofConst zeroE)
    (Aff.ofConst zeroE) (by unfold vW; rw [Aff.value_ofConst, Aff.value_ofConst])
    fun c hc' => hk c (List.mem_range.1 hc')
  unfold vW at hf hc ⊢
  unfold Came.joinForm
  rw [Aff.value_sub, Aff.value_sub, Aff.value_add, Aff.value_add, Aff.value_ofConst,
    Aff.value_ofConst, ← hs, hf, hc]

end Two

/-- A form's value in two worlds that agree on what it names (Law/SlotsFilled.lean's value_agree,
without that file's letters). -/
theorem value_agree0 {K' : Type} [CommRing K'] (ρ : Reading K') (W1 W2 : World K') (f : Form)
    (hs : ∀ x, x ∈ f.slots.toList → W1.slot x.1 = W2.slot x.1)
    (he : ∀ x, x ∈ f.ents.toList → W1.entry x.tree x.row x.idx = W2.entry x.tree x.row x.idx) :
    f.value ρ W1 = f.value ρ W2 := by
  unfold OnBytes.Model.Aff.value
  have e1 : f.ents.toList.map (OnBytes.Model.Ent.value ρ W1)
      = f.ents.toList.map (OnBytes.Model.Ent.value ρ W2) :=
    List.map_congr_left fun x hx => by
      unfold OnBytes.Model.Ent.value
      rw [he x hx]
  have e2 : f.slots.toList.map (OnBytes.Model.slotValue ρ W1)
      = f.slots.toList.map (OnBytes.Model.slotValue ρ W2) :=
    List.map_congr_left fun x hx => by
      unfold OnBytes.Model.slotValue
      rw [hs x hx]
  rw [e1, e2]

/-- The lookup's last claim is worth the same in the witness's world at a later ledger and in the
head's law's world. -/
theorem cEnd_same (gk : OnBytes.Model.Forest.Heard) (G U : Fork) (mask : Nat → E)
    (m : Nat → K) (ent : Nat → Nat → Nat → K) (hfill : CEndFilled gk G)
    (hbare : gk.cEnd.ents = #[]) (hL : Later G U) (hm : ∀ j, m j = rd (mask j)) :
    vW (U.worldOf Reading.gl m ent) gk.cEnd = vW (worldE G mask noEnt) gk.cEnd := by
  unfold vW
  rw [worldE_eq]
  refine value_agree0 Reading.gl _ _ gk.cEnd (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨_, k2, k3⟩ := hL.keep x.1 (hfill x hx)
    show Reading.gl.val (U.vp.getD x.1 zeroE) - Reading.gl.val (U.mf.getD x.1 zeroE) * m x.1 =
      Reading.gl.val (G.vp.getD x.1 zeroE) - Reading.gl.val (G.mf.getD x.1 zeroE) * rd (mask x.1)
    rw [k2, k3, hm]
  · rw [hbare] at hx
    simp at hx

/-- The 35 forms at the reads in truth are worth 0: the second of the three sentences into which
Law/WeightTwinAt.lean's k6Out_iff cuts K6Out. -/
theorem formsAt_of_claims (W : OnBytes.Model.Verify.Public) (t : S) (d : Pinned) (g : Given)
    (H : HeardAll) (x : FinalNorm.Reads × Reads) (Wd : World K)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) t = .ok g)
    (hH : (seatAt W.hS (readsOf W)).heard t = some H)
    (h6 : OnBytes.okE (H.1.P.getD 6 {}).var.const = true)
    (hS : K6Exchange g H x d.1 Wd (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt))
    (h35 : ∀ name fs, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs →
      ∀ f ∈ fs, vW Wd f = 0) :
    FormsAt W t d.1 d.2 := by
  refine ⟨g, H, hg, hH, fun name fs hl f hf => ?_⟩
  have hl' : (claimsTrue g H d.1).lookup name = some fs := hl
  have hok : OnBytes.okE f.const = true := by
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    exact okE_form (normReadsAtCells d.1) (readsAt d.1.toCells) h6 name fs hl f hf
  apply zero_of_rd (okE_atWorld _ _ _ f hok)
  rw [rd_atWorld]
  obtain ⟨fs0, f0, h1, h2, h3⟩ := hS.forms name fs hl' f hf
  rw [← h3]
  exact h35 name fs0 h1 f0 h2

/-- The form of "join" at the key vectors in truth is worth 0: the third sentence. -/
theorem joinOpened_of_claims (W : OnBytes.Model.Verify.Public) (t : S) (d : Pinned) (g : Given)
    (H : HeardAll) (x : FinalNorm.Reads × Reads) (gk : OnBytes.Model.Forest.Heard) (Wd : World K)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) t = .ok g)
    (hH : (seatAt W.hS (readsOf W)).heard t = some H)
    (hS : K6Exchange g H x d.1 Wd (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt))
    (hj : vW Wd (Came.joinForm gk (keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩))) = 0)
    (hc : vW Wd gk.cEnd = vW (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt) gk.cEnd) :
    JoinOpened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) t d.1 d.2 gk := by
  refine ⟨g, H, hg, hH, ?_⟩
  rw [← joinForm_two Wd _ gk (keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩))
    (keysAt g H d.1) (by simp [keyVectorsAt, keysAt]) (fun c hc' => hS.keys c (by
      simpa [keyVectorsAt] using hc')) hc]
  exact hj

/-- **FROM THE SEAT's CLAIMS WORTH 0 TO K6Out.** t: the record behind the head's own step. The three
sentences are joined by Law/WeightTwinAt.lean's k6Out_iff. -/
theorem k6Out_of_claims (W : OnBytes.Model.Verify.Public) (t : S) (d : Pinned) (g : Given)
    (H : HeardAll) (x : FinalNorm.Reads × Reads) (gk : OnBytes.Model.Forest.Heard) (Wd : World K)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) t = .ok g)
    (hH : (seatAt W.hS (readsOf W)).heard t = some H) (hgk : t.lookHeard? = some gk)
    (h6 : OnBytes.okE (H.1.P.getD 6 {}).var.const = true)
    (hS : K6Exchange g H x d.1 Wd (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt))
    (hWt : WeightAt W t d.1.toCells d.2)
    (h35 : ∀ name fs, (claimsSeat (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)).lookup name = some fs →
      ∀ f ∈ fs, vW Wd f = 0)
    (hj : vW Wd (Came.joinForm gk (keyVectorsAt (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩))) = 0)
    (hc : vW Wd gk.cEnd = vW (worldE ((seatAt W.hS (readsOf W)).ledger t) d.2 noEnt) gk.cEnd) :
    K6Out W t d :=
  (Came.k6Out_iff W t d).2 ⟨hWt, formsAt_of_claims W t d g H x Wd hg hH h6 hS h35, gk, hgk,
    joinOpened_of_claims W t d g H x gk Wd hg hH hS hj hc⟩

/-! ## 4 The exchange paid: a sumcheck's own form names no entry -/

theorem noEnts_addMul {a b : Form} (ha : NoEnts a) (hb : NoEnts b) (k : E) :
    NoEnts (Aff.addMul a b k) := by
  have e := addMul_ents a b k
  unfold NoEnts at ha hb ⊢
  rw [ha, hb] at e
  simpa using e

theorem noEnts_const (v : E) : NoEnts (Aff.ofConst v) := by
  unfold NoEnts
  rfl

theorem noEnts_slot (j : Nat) : NoEnts (Aff.slot j) := by
  unfold NoEnts
  rfl

theorem noEnts_empty : NoEnts ({} : Form) := by
  unfold NoEnts
  rfl

theorem noEnts_onSlots : ∀ (u : List E) (first : Nat) (f : Form), NoEnts f →
    NoEnts (Part.MaskedSum.onSlots f first u) := by
  intro u
  induction u with
  | nil => intro first f hf; exact hf
  | cons x xs ih =>
    intro first f hf
    exact ih (first + 1) _ (noEnts_addMul hf (noEnts_slot _) _)

theorem noEnts_left (s : Sum) (S0 : E) (hs : ∀ h, s.psc = some h → NoEnts h.start) :
    NoEnts (s.left S0) := by
  unfold Sum.left
  cases hp : s.psc with
  | none => exact noEnts_const _
  | some h =>
    show NoEnts (Part.MaskedSum.rowForm h S0 {})
    unfold Part.MaskedSum.rowForm
    exact noEnts_addMul (noEnts_addMul (noEnts_onSlots _ _ _ (noEnts_const _))
      (noEnts_addMul (noEnts_const _) (hs h hp) _) _) noEnts_empty _

section Hear

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **WHERE THE HEAD's HEARING RETURNS: WHAT WAS HEARD NAMES NO ENTRY.** -/
theorem heardBare_of_hear {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rs = some (H, G, left)) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    HeardBare := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  obtain ⟨Fa, Fb, l1, hNorm, _, _, hsN, hsL, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fc, Fd, Fe, _, _, h1, _, h3, h4, h5, _⟩ := norm_parts hW hNorm
  have nW := batch_noEnts h1
  have nP := batch_noEnts h4
  obtain ⟨sqE, hq, eq1, eq2⟩ := level_noEnts h3
  obtain ⟨prC, prE, hp, ep1, ep2⟩ := sumcheck_noEnts h5
  obtain ⟨nmC, nmE, hn, en1, en2⟩ := sumcheck_noEnts hsN
  obtain ⟨lgC, lgE, hl, el1, el2⟩ := sumcheck_noEnts hsL
  have K0 : Kept NoEnts :=
    { addMul := fun k ha hb => noEnts_addMul ha hb k
      bare := fun _ he _ => he }
  exact
    { W := fun s _ => nW s
      P := fun n _ => nP n
      sqLeft := fun S0 => noEnts_left _ S0 fun x hx => by
        have hx' : H.1.squares.psc = some x := hx
        rw [eq1] at hx'
        obtain rfl := Option.some.inj hx'
        rw [eq2]
        unfold Norm.squaresStart
        exact K0.smulE _ (K0.sums _ _ fun i => K0.sums _ _ fun s => K0.smulE _ (nW _))
      sqEnd := fun j _ => sqE j
      prLeft := fun S0 => noEnts_left _ S0 fun x hx => by
        have hx' : H.1.products.psc = some x := hx
        rw [ep1] at hx'
        obtain rfl := Option.some.inj hx'
        exact ep2
      prClaimed := prC
      prEnd := fun j _ => prE j
      nmLeft := fun S0 => noEnts_left _ S0 fun x hx => by
        have hx' : H.2.1.normed.psc = some x := hx
        rw [en1] at hx'
        obtain rfl := Option.some.inj hx'
        exact en2
      nmClaimed := nmC
      nmEnd := fun j _ => nmE j
      lgLeft := fun S0 => noEnts_left _ S0 fun x hx => by
        have hx' : H.2.2.logits.psc = some x := hx
        rw [el1] at hx'
        obtain rfl := Option.some.inj hx'
        exact el2
      lgClaimed := lgC
      lgEnd := lgE 0 }

end Hear

/-! ## The key vectors -/

theorem fold_two (W₁ W₂ : World K) (a1 a2 : PlaceKey → Form)
    (h : ∀ k, vW W₁ (a1 k) = vW W₂ (a2 k)) : ∀ (keys : List PlaceKey) (a a' : Form),
    vW W₁ a = vW W₂ a' →
    vW W₁ ((keys.map a1).foldl (· + ·) a) = vW W₂ ((keys.map a2).foldl (· + ·) a')
  | [], _, _, h0 => h0
  | k :: keys, a, a', h0 => by
    simp only [List.map_cons, List.foldl_cons]
    exact fold_two W₁ W₂ a1 a2 h keys _ _ (by rw [vW_add, vW_add, h0, h k])

section Keys

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- **A call's key vector at two fillings of the reads.** -/
theorem keyVector_two (W₁ W₂ : World K) (hs : ∀ j, W₁.slot j = W₂.slot j)
    (N N' : FinalNorm.Reads) (R R' : Reads) (A : EntriesAlike W₁ W₂ N N' R R') (B : HeardBare)
    (hd : S2 ∣ d) (hJ : JVa ≤ JV) (padding : E) (keys : List PlaceKey) :
    vW W₁ (letI := N; letI := R; keyVector key padding keys) =
      vW W₂ (letI := N'; letI := R'; keyVector key padding keys) := by
  unfold keyVector
  refine fold_two W₁ W₂ _ _ (fun k => ?_) keys _ _ ?_
  · cases k with
    | inl k => exact worth_keyN W₁ W₂ hs N N' R R' A B hd k
    | inr k => exact worth_key W₁ W₂ hs N N' R R' A B hJ k
  · unfold vW
    show (Aff.ofConst padding).value _ _ = (Aff.ofConst padding).value _ _
    rw [Aff.value_ofConst, Aff.value_ofConst]

end Keys

/-- **THE EXCHANGE, PAID.** -/
theorem k6Exchange_of_entries (g : Given) (H : HeardAll) (x : FinalNorm.Reads × Reads) (c : NCells)
    (W₁ W₂ : World K) (hs : ∀ j, W₁.slot j = W₂.slot j) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    EntriesAlike W₁ W₂ x.1 (normReadsAtCells c) x.2 (readsAt c.toCells) → HeardBare → S2 ∣ d →
    JVa ≤ JV → K6Exchange g H x c W₁ W₂ := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  intro A B hd hJ
  refine ⟨fun name fs' hl f' hf' => ?_, fun call hc => ?_⟩
  · exact worth_claims W₁ W₂ hs x.1 (normReadsAtCells c) x.2 (readsAt c.toCells) A B hd name fs' hl
      f' hf'
  · unfold keyVectorsAt keysAt
    rw [Came.getD_map_toArray g.calls _ call hc (Aff.ofConst zeroE) (0, []),
      Came.getD_map_toArray g.calls _ call hc (Aff.ofConst zeroE) (0, [])]
    exact keyVector_two W₁ W₂ hs x.1 (normReadsAtCells c) x.2 (readsAt c.toCells) A B hd hJ _ _

/-! ## 4b The slots of the form of "join" -/

/-- Every slot that the form of "join" names at the seat's letters is filled in a ledger X that is
later than the one which the head's hearing left, if the lookup's last claim's slots are. -/
theorem join_slots_filled (v : Given × Behind × Places) (gk : OnBytes.Model.Forest.Heard)
    (F0 G X : Fork) (rs : List Fmt.RoundView) (hW : WellLaid F0)
    (hh : (letI := v.1
           hear F0 rs = some ((v.2.1.norm, v.2.1.final, v.2.1.head), G, [])))
    (hL : Later G X) (hc : CEndFilled gk X)
    (hb : (∀ r i, (v.2.2.final.entry r i).slots = #[]) ∧
      (∀ r i, (v.2.2.head.entry r i).slots = #[]) ∧ ∀ i, (v.2.2.final.wide i).slots = #[]) :
    ∀ x ∈ (Came.joinForm gk (keyVectorsAt v)).slots.toList, OnBytes.PscRun.Filled X x.1 := by
  letI := v.1
  letI := v.2.1
  letI := v.2.2
  have TT := hear_takes (⟨hW.2.1, hW.2.2, hW.1⟩ : OnBytes.PscRun.Sized F0) hh
  have fill : ∀ j, F0.next ≤ j → j < G.next → OnBytes.PscRun.Filled X j := fun j h1 h2 =>
    (hL.keep j (TT.full j h1 (by rw [← TT.next]; exact h2))).1
  have C : Kept fun f : Form => ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled X x.1 :=
    { addMul := fun {a b} k ha hb' x hx => by
        rw [addMul_slots] at hx
        rcases List.mem_append.mp hx with h' | h'
        · exact ha x h'
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h'
          exact hb' y hy
      bare := fun f _ hs x hx => by
        rw [hs] at hx
        simp at hx }
  refine joinForm_has C gk (keyVectorsAt v) (fun c hc' => ?_) hc
  have hks := keys_slotsIn hW hh hb.1 hb.2.1 hb.2.2
  unfold keyVectorsAt
  intro y hy
  have hlen : c < v.1.calls.length := by
    simpa [keyVectorsAt] using hc'
  rw [Came.getD_map_toArray v.1.calls (fun c => keyVector key c.1 c.2) c hlen (Aff.ofConst zeroE)
    (0, [])] at hy
  have := hks _ _ y hy
  exact fill _ this.1 this.2

/-! ## 5 The sizes -/

/-- Where the tests on the plan pass, at the letters that are read in front. -/
theorem sizes_of_plan {S' : Type} (p : Par) (L : Seat S') (e : S') (g : Given)
    (hok : p.ok = true) (hg : given p L e = .ok g) :
    (letI := g
     S2 ∣ Norm.d) ∧
    (letI := g
     JVa ≤ JV) := by
  obtain ⟨z, y, rfl⟩ := given_form hg
  letI := p.sizes
  letI := p.policy
  letI : Request := L.request e
  letI : Token := ⟨y⟩
  have hplan : planOk p.sT = true := hok
  have P := planFacts hplan
  exact ⟨Nat.dvd_of_mod_eq_zero P.hdS, JVa_le (by have := P.hV2; omega)⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_hands
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_border
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6HeardAt_keeps
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Ready_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joinForm_two
#print axioms VerifiableInference.Desc.Kinds.Head.Law.cEnd_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.formsAt_of_claims
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joinOpened_of_claims
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Out_of_claims
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heardBare_of_hear
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keyVector_two
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Exchange_of_entries
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sizes_of_plan
