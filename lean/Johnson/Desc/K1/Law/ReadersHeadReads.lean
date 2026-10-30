-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersHeadReads.lean: THE LAST FIVE: the runs (3, norm) (3, policy) (3, logits)
(2, planes) (3, join) of the output head's segment AT ITS READS' PLACE (a commitment, then the quiet
step that lays the reads' tables): what a run's reader answers in front it answers behind, UNDER THE
INVARIANT TablesOk (Johnson/Desc/K1/Law/TablesOk.lean) IN FRONT. And k01_fifty_atBase's binder hRd
with that laid in. Statements with their proofs.

How. Let s be the state in front, s₁ behind the commitment, s' behind the quiet step, t the tables
that the step lays, and e the state s with t laid. (1) e and s' part in nothing but what a commitment
writes and the field tl: so each run that is a member of R.Respects
(Johnson/Desc/K1/Law/RespectsHeadR.lean) answers at s' as at e. (2) Where the run is silent at s, the
second reader (k6Silent) answers what the run answers at the state with ITS tables laid: these are t,
where the two take the same three fields of the public parameters (hXW): that state is e. (3) Where
the run answers at s, tables are laid at s (each of the five reads them: Tabled); by TablesOk they
are t: so e is s. NO PREMISE "the run is silent in front" STAYS.
Main names:
  Tabled ρ            a run that answers only where tables are laid. tabled_flRun · tabled_guard ·
                      reads_tabled · planesAt_tabled · lettersAt_tabled · tabled_runsBy ·
                      k6_claims_tabled · k3At_planes_tabled · tabled_head3 · tabled_head2
  StepsVia · stepsVia_joined | _k1Reads · quiet_head_of   the reads' place's two steps
  behind_of_head      what the state behind is, from a state in the output head's segment
  reader_runs         where the reader answers, the run that the link states accepts
  reader_reads        **(1) (2) (3).**
  fwd_head_reads      **Fwd at the five runs over the reads' place of link 24.**
  fwd_all             **Fwd at every run of every later place of kind K1.**
  hRd_any             **hRd at any meaning and numbers** (for the tops that stand at mw1 with a letter
                      more in its "in order").
  hRd_paid3           **hRd, to the letter: NOTHING OF THE READERS STAYS.**
PREMISES THAT STAY IN hRd_paid3, BY NAME.
  hS hR O hDlk        binders that the top has.
  hlk · hX            as in Johnson/Desc/K1/Law/ReadersPaid.lean.
  hXW                 ON THE LETTER XV: its three fields hS, HLy, H are the opened description's.
  hTab                the promise in front of the output head's reads' place holds TablesOk. AT THE
                      WIDER MEANING mw1 AS IT STANDS WHILE THIS IS TYPED NO CLAUSE SAYS SO: it is to
                      become a conjunct of its "in order".
What is not claimed. hTab. TablesOk at a reached state. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K1.Law.RespectsHeadR
import Johnson.Desc.K1.Law.TablesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.K.Kc
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place named)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers More PubData
  flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf LinkHoles statesOfLink readersOfLink
  holesAt phAt flRun guestsNone)
open VerifiableInference.Desc.Kinds.Head (Seat seatAt planesAt callerReaders callerKeys runsBy
  kind kindWithJoin asClaim seatedClaims blockClaims lettersAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)
open ProofFile (Cl)

/-! ## 1 Runs that answer only where tables are laid -/

/-- The run accepts only at a state of the output head's segment in which tables are laid. -/
def Tabled (ρ : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ s y, ρ 0 s = .ok y → ∃ a t, s.here = .head a ∧ a.t = some t

theorem some_of_named {α : Type} {e : String} {o : Option α} {x : α} (h : named e o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => exact congrArg some (Except.ok.inj h)

theorem tabled_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim)
    (h2 : ∀ s c, pre2 s = .ok c → ∃ a t, s.here = .head a ∧ a.t = some t) :
    Tabled (flRun e0 pre1 e1 test pre2 e2 m out) := by
  intro s y e
  unfold flRun at e
  obtain ⟨F, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨b, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨_, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨c, hc, _⟩ := (bind_ok _ _ _).1 e
  exact h2 s c hc

theorem tabled_guard (same : S → S → Bool) (ρ : ℕ → S → Except String (List Claim × S))
    (h : Tabled ρ) : Tabled (IM.guardRun same ρ) := by
  intro s y e
  obtain ⟨z, hz, _⟩ := okOfBind _ _ _ e
  exact h s z hz

theorem planesAt_tabled (iU3 : ℕ) (s : S) {x : Kinds.Head.PlaneRead → ℕ → Option Kinds.Form}
    (e : planesAt iU3 s = some x) : ∃ a t, s.here = .head a ∧ a.t = some t := by
  unfold planesAt at e
  cases hh : s.here with
  | head o =>
    cases ht : o.t with
    | some t => exact ⟨o, t, rfl, ht⟩
    | none =>
      exfalso
      rw [hh] at e
      cases hf : s.fork? with
      | none =>
        rw [hf] at e
        cases e
      | some F =>
        rw [hf] at e
        simp only [ht, Option.bind_none] at e
        cases e
  | _ =>
    exfalso
    rw [hh] at e
    cases e

theorem reads_tabled (h : Head.Shape) (iU3 : ℕ) (s : S)
    (e : ((seatAt h iU3).reads s).isSome = true) : ∃ a t, s.here = .head a ∧ a.t = some t := by
  cases hh : s.here with
  | head o =>
    cases ht : o.t with
    | some t => exact ⟨o, t, rfl, ht⟩
    | none =>
      exfalso
      simp only [seatAt] at e
      rw [hh] at e
      cases hf : s.fork? with
      | none =>
        rw [hf] at e
        cases e
      | some F =>
        rw [hf] at e
        simp only [ht, Option.bind_none] at e
        cases e
  | _ =>
    exfalso
    simp only [seatAt] at e
    rw [hh] at e
    cases e

theorem lettersAt_tabled (p : Kinds.Head.Par) (h : Head.Shape) (iU3 : ℕ) (s : S)
    {z : Kinds.Head.Given × Kinds.Head.Behind × Kinds.Head.Places}
    (e : lettersAt p (seatAt h iU3) s = .ok z) : ∃ a t, s.here = .head a ∧ a.t = some t := by
  unfold lettersAt at e
  obtain ⟨g, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨H, _, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨x, hx, _⟩ := (bind_ok _ _ _).1 e
  exact reads_tabled h iU3 s (by rw [some_of_named hx]; rfl)

theorem tabled_runsBy (names : List String)
    (runs : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places →
      List (String × List Kinds.Form))
    (keys : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places → List Kinds.Form)
    (toCl : Kinds.Form → Claim) (p : Kinds.Head.Par) (h : Head.Shape) (iU3 : ℕ) :
    ∀ r ∈ runsBy names runs keys toCl p (seatAt h iU3), Tabled r.2 := by
  intro r hr
  unfold runsBy at hr
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 hr
  intro s y e
  obtain ⟨z, hz, _⟩ := (bind_ok _ _ _).1 e
  exact lettersAt_tabled p h iU3 s hz

theorem tabled_joinCalls (keys : S → Option (Array Aff))
    (hk : ∀ s c, keys s = some c → ∃ a t, s.here = .head a ∧ a.t = some t) :
    Tabled (K9.joinCalls keys) := by
  unfold K9.joinCalls
  exact tabled_flRun _ _ _ _ _ _ _ _ fun s c hc => hk s c (some_of_named hc)

theorem tabled_planesCalls (lm : ℕ) (readers : K3.Readers S)
    (hk : ∀ s c, readers s = some c → ∃ a t, s.here = .head a ∧ a.t = some t) :
    Tabled (K9.planesCalls lm readers) := by
  unfold K9.planesCalls
  exact tabled_flRun _ _ _ _ _ _ _ _ fun s c hc => hk s c (some_of_named hc)

theorem tabled_join (p : Kinds.Head.Par) (h : Head.Shape) (iU3 : ℕ) :
    Tabled (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3))) :=
  tabled_joinCalls _ fun s c h1 => by
    unfold callerKeys at h1
    obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.1 h1
    cases hl : lettersAt p (seatAt h iU3) s with
    | error e =>
      rw [hl] at hz
      cases hz
    | ok w => exact lettersAt_tabled p h iU3 s hl

theorem tabled_planes (lm iU3 : ℕ) :
    Tabled (K3.planesRun (K3.seatCalls K3Lot.ofForm) lm (callerReaders (planesAt iU3))) :=
  tabled_planesCalls lm _ fun s c h1 => by
    unfold callerReaders at h1
    obtain ⟨z, hz, _⟩ := Option.map_eq_some_iff.1 h1
    exact planesAt_tabled iU3 s hz

/-- K6's lot's sub-protocol: all four runs. -/
theorem k6_claims_tabled {W : Verify.Public} {l : ℕ} {ms : List (ℕ × ℕ)} {b' : Block S Claim}
    (h : seatedClaims W l ms = some b') : ∀ r ∈ b'.claims, Tabled r.2 := by
  unfold seatedClaims at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 h0
  have hk : ∀ (p : Kinds.Head.Par), ∀ r ∈ (kind asClaim (seatAt W.hS iU3) l 4 p).claims,
      Tabled r.2 := by
    intro p r hr
    unfold kind at hr
    dsimp only at hr
    exact tabled_runsBy _ _ _ asClaim p W.hS iU3 r hr
  intro r hr
  have hr' : r ∈ (kind asClaim (seatAt W.hS iU3) l 4
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.take 1
      ++ [("join", K3.joinRun (K3.seatCalls asClaim) (callerKeys
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))
        (seatAt W.hS iU3)))] ++
      (kind asClaim (seatAt W.hS iU3) l 4
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.drop 1 :=
    hr
  rcases List.mem_append.1 hr' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact hk _ r (List.mem_of_mem_take h2)
    · rw [List.mem_singleton.1 h2]
      exact tabled_join _ W.hS iU3
  · exact hk _ r (List.mem_of_mem_drop h1)

/-- The lookup's lot's sub-protocol on the calls at the output head's link: "planes". -/
theorem k3At_planes_tabled (W : Verify.Public) (Z : ProofFile.Pub) (a : Place) (ha : a.piece ≤ 3) (l : ℕ)
    (hl : a.link = some l) (hh : K3.isHead W l = true) (b' : Block S Cl)
    (h : IM.k3At W Z a = some b') : ∀ r ∈ b'.claims, r.1 = "planes" → Tabled r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, r.1 = "planes" → Tabled r.2 :=
    theWhole_calls_of (fun c => c.1 = "planes" → Tabled c.2) K3Lot.ofForm
      (fun piece laid sent p c hc hn => by
        exfalso
        have hc' : c ∈ [("objects", K9.objectsCalls), ("guests", guestsNone)] := hc
        have : c = ("objects", K9.objectsCalls) ∨ c = ("guests", guestsNone) := by simpa using hc'
        rcases this with e | e <;> rw [e] at hn <;> exact absurd hn (by decide)) W _ _ a ha b₀ h₀
  simp only [hl] at h'
  by_cases hp : (a.piece != K3.pieceAt W l false) = true
  · rw [if_pos hp] at h'
    obtain rfl : b₀ = b' := Option.some.inj h'
    exact e0
  · rw [if_neg hp] at h'
    cases hr : K3Lot.readersAt W l with
    | none =>
      simp only [hr] at h'
      obtain rfl : b₀ = b' := Option.some.inj h'
      exact e0
    | some rd =>
      simp only [hr] at h'
      obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h'
      simp only [K3Lot.readersAt, hh, if_true] at hr
      obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hr
      intro r hm hn
      have hm' : r ∈ b₀.claims ++ [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm
          (callerReaders (planesAt i)))] := hm
      rcases List.mem_append.1 hm' with h1 | h1
      · exact e0 r h1 hn
      · rw [List.mem_singleton.1 h1]
        exact tabled_planes p.lm i

/-! ## 2 The reads' place's two steps -/

/-- An accept of B is an accept of a commitment, then of the reads' quiet step as the lot joins it. -/
def StepsVia (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (B : Block S Unit) : Prop :=
  ∀ s s' rs gs, B.decide s rs gs = .ok s' → ∃ s₁, RestAlike s s₁ ∧
    ∃ nm p what piece rs₂ gs₂,
      (ProofFile.orLoud nm p what (ProofFile.readsQuietAt G l X piece)).decide s₁ rs₂ gs₂ = .ok s'

theorem stepsVia_joined (P : Par) (link moment : ℕ) (arrays : Option (List ℕ)) (nm nm' : String)
    (p : Place) (what : String) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (piece : ℕ) :
    StepsVia G l X (Block.andThen nm (commitAtS P link moment arrays)
      (ProofFile.orLoud nm' p what (ProofFile.readsQuietAt G l X piece))) := by
  intro s s' rs gs e
  have e' : ((commitAtS P link moment arrays : Block S Unit).decide s
      (rs.take (commitAtS P link moment arrays : Block S Unit).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Unit).openings)).bind (fun s₁ =>
      (ProofFile.orLoud nm' p what (ProofFile.readsQuietAt G l X piece)).decide s₁
        (rs.drop (commitAtS P link moment arrays : Block S Unit).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Unit).openings)) = .ok s' := e
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 e'
  exact ⟨s₁, commitAtS_alike P link moment arrays _ _ _ _ h1, _, _, _, _, _, _, h2⟩

theorem stepsVia_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : StepsVia G l X (IM.k1Reads Z G l X pr reads) :=
  stepsVia_joined _ _ _ _ _ _ _ _ G l X _

/-- At a state of the output head's segment the quiet step that accepts is the output head's. -/
theorem quiet_head_of (nm : String) (p : Place) (what : String) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (piece : ℕ) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {a : HeadOwn}
    (ha : s.here = .head a)
    (e : (ProofFile.orLoud nm p what (ProofFile.readsQuietAt G l X piece)).decide s rs gs = .ok s') :
    ∃ P : K8.ReadsQuiet.PH, P.h = G.W.hS ∧ P.L = G.W.HLy ∧ P.hp = G.W.H ∧
      (K8.ReadsQuiet.head P).decide s rs gs = .ok s' := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none =>
    rw [hq] at e
    exact nomatch e
  | some q =>
    rw [hq] at e
    have e' : q.decide s rs gs = .ok s' := e
    unfold ProofFile.readsQuietAt at hq
    by_cases h1 : (X.kind == 1) = true
    · rw [if_pos h1] at hq
      by_cases h2 : (piece == 4) = true
      · rw [if_pos h2] at hq
        exfalso
        unfold First.Att.readsAtO at hq
        obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
        obtain ⟨a2, t, tl, ha2, _⟩ := Meaning.K2.readsAtSO_eq e'
        rw [ha] at ha2
        cases ha2
      · rw [if_neg h2] at hq
        cases hq
    · rw [if_neg h1] at hq
      by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
      · rw [if_pos h2] at hq
        unfold K8.ReadsQuiet.blockAt at hq
        obtain ⟨k, -, hq⟩ := Option.bind_eq_some_iff.1 hq
        split at hq
        · exfalso
          obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 hq
          obtain ⟨a2, own, tl', ha2, _⟩ := K8.ReadsQuiet.layers_ok e'
          rw [ha] at ha2
          cases ha2
        · split at hq
          · obtain rfl := Option.some.inj hq
            exact ⟨_, rfl, rfl, rfl, e'⟩
          · cases hq
      · rw [if_neg h2] at hq
        cases hq

/-- What the state behind is. -/
theorem behind_of_head (G : ProofFile.Ground) (l : ℕ) (X : LinkH) {s s₁ s' : S} (hA : RestAlike s s₁)
    {nm : String} {p : Place} {what : String} {piece : ℕ} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (e : (ProofFile.orLoud nm p what (ProofFile.readsQuietAt G l X piece)).decide s₁ rs gs = .ok s')
    {a : HeadOwn} (ha : s.here = .head a) :
    ∃ a₁ cov x t tl', s₁.here = .head a₁ ∧ a.opened = true ∧
      s.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
      K8.ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
      s' = { s₁ with here := .head { a₁ with t := some t, tl := tl' } } := by
  have hh : (restOf s).here = (restOf s₁).here := congrArg S.here hA
  have hreq : s₁.req = s.req := (congrArg S.req hA).symm
  have hout : s₁.out = s.out := hA.out.symm
  cases ha₁ : s₁.here with
  | head a₁ =>
    have e1 : hereRest (.head a) = hereRest (.head a₁) := by
      rw [← ha, ← ha₁]
      exact hh
    have e2 := Here.head.inj e1
    have o1 : a₁.opened = a.opened := (congrArg HeadOwn.opened e2).symm
    have o2 : a₁.x = a.x := (congrArg HeadOwn.x e2).symm
    obtain ⟨P, p1, p2, p3, eq⟩ := quiet_head_of nm p what G l X piece ha₁ e
    obtain ⟨a2, cov, x, t, tl', ha2, ho, hcov, hx, ht, _, es⟩ := K8.ReadsQuiet.head_ok eq
    obtain rfl : a₁ = a2 := by
      rw [ha₁] at ha2
      exact Here.head.inj ha2
    rw [p1] at hcov
    rw [p1, p2, p3] at ht
    refine ⟨a₁, cov, x, t, tl', rfl, o1.symm.trans ho, ?_, o2.symm.trans hx, ht, es⟩
    unfold S.covered S.replyTok? S.coveredAt at hcov ⊢
    rw [← hreq, ← hout]
    exact hcov
  | _ =>
    exfalso
    have e1 : hereRest s.here = hereRest s₁.here := hh
    rw [ha, ha₁] at e1
    cases e1

/-! ## 3 The reader across the place -/

/-- Where the reader answers, the run that is stated under the name accepts. -/
theorem reader_runs (states : ℕ → List (RunOf S)) (b : ℕ) (name : String) {s : S} {X : Read}
    (h : readerOf states b name s = some X) :
    ∃ r z, (states b).find? (fun r => r.1 == name) = some r ∧ r.2 0 s = .ok z := by
  unfold readerOf at h
  obtain ⟨r, hr1, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i z F e1 e2
    exact ⟨r, z, hr1, e1⟩
  · cases h

theorem self_tables (s : S) (a : HeadOwn) (ha : s.here = .head a) (t : Head.Tables)
    (ht : a.t = some t) : ({ s with here := .head { a with t := some t } } : S) = s := by
  have e : ({ a with t := some t } : HeadOwn) = a := by
    rw [← ht]
  rw [e, ← ha]

/-- **What the readers of the segment answer in front, the run itself answers behind.** -/
theorem reader_reads (XV : OnBytes.Model.Verify.Public) (G : ProofFile.Ground)
    (hXW : XV.hS = G.W.hS ∧ XV.HLy = G.W.HLy ∧ XV.H = G.W.H) (m l : ℕ) (X : LinkH)
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → R.Respects r.2)
    (ht : ∀ r, (states b).find? (fun r => r.1 == name) = some r → Tabled r.2) {s s₁ s' : S}
    (hA : RestAlike s s₁) {nm : String} {p : Place} {what : String} {piece : ℕ} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (e : (ProofFile.orLoud nm p what (ProofFile.readsQuietAt G l X piece)).decide s₁ rs gs = .ok s')
    (k : TablesOk G.W.hS G.W.HLy G.W.H s) (Rr : Read)
    (hR : (match readerOf states b name s with
      | some R => some R
      | Option.none => k6Silent (phAt XV m) states b name s) = some Rr) :
    readerOf states b name s' = some Rr := by
  have key : ∀ a, s.here = .head a → ∀ t, (∀ cov x, s.covered G.W.hS.T G.W.hS.V = .ok cov →
      a.x = some x → K8.ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t →
      readerOf states b name { s with here := .head { a with t := some t } } = some Rr) →
      (∃ cov x, s.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
        K8.ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t) →
      readerOf states b name s' = some Rr := by
    intro a ha t h1 ⟨cov, x, c1, c2, c3⟩
    obtain ⟨a₁, cov', x', t', tl', ha₁, _, d1, d2, d3, rfl⟩ := behind_of_head G l X hA e ha
    obtain rfl : cov = cov' := Except.ok.inj (c1.symm.trans d1)
    obtain rfl : x = x' := Option.some.inj (c2.symm.trans d2)
    obtain rfl : t = t' := Except.ok.inj (c3.symm.trans d3)
    have al : R.RestAlike { s with here := .head { a with t := some t } }
        { s₁ with here := .head { a₁ with t := some t, tl := tl' } } := by
      refine (R.alike_of (alike_tables hA a a₁ ha ha₁ t)).trans ?_
      simp [R.RestAlike, R.restOf, R.blank, R.blankHere, restOf, hereRest]
    rw [R.readerOf_alike states b name hr al]
    exact h1 cov x c1 c2 c3
  cases h1 : readerOf states b name s with
  | some R₁ =>
    rw [h1] at hR
    obtain rfl : R₁ = Rr := Option.some.inj hR
    obtain ⟨r, z, f1, f2⟩ := reader_runs states b name h1
    obtain ⟨a, t, ha, hta⟩ := ht r f1 s z f2
    refine key a ha t (fun _ _ _ _ _ => ?_) (k a t ha hta)
    rw [self_tables s a ha t hta]
    exact h1
  | none =>
    rw [h1] at hR
    have hR' : (withTables (phAt XV m) s).bind (readerOf states b name) = some Rr := hR
    obtain ⟨e', he', h2⟩ := Option.bind_eq_some_iff.1 hR'
    obtain ⟨a, cov, x, tt, ha, _, hcov, hx, htt, rfl⟩ := (withTables_iff (phAt XV m) s e').1 he'
    have hcov' : s.covered G.W.hS.T G.W.hS.V = .ok cov := by
      rw [← hXW.1]
      exact hcov
    have htt' : K8.ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok tt := by
      rw [← hXW.1, ← hXW.2.1, ← hXW.2.2]
      exact htt
    exact key a ha tt (fun _ _ _ _ _ => h2) ⟨cov, x, hcov', hx, htt'⟩

/-! ## 4 Link 24 -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
  (hR : VerifierAndGoals.readFiles P = .ok pp)
  (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
include hS hR O

theorem tabled_head3 (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 3).find? (fun r => r.1 == name) = some r → Tabled r.2 := by
  obtain ⟨Lk, b, b', ms, e1, e2, -, k6, la, -⟩ := IM.k6_of hS hR O
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  intro r hr
  have hm : r ∈ statesOfLink lk 3 := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [e2] at hm
  have hm' : r ∈ b.claims := hm
  rw [IM.claims_alone la] at hm'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm'
  exact tabled_guard _ _ (k6_claims_tabled k6 q hq)

theorem tabled_head2 (lk : Link S Cl) (eL : c.links[24]? = some lk) :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == "planes") = some r → Tabled r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  have hh : K3.isHead Bs.G₀.W 24 = true := by
    show (24 == (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr) = true
    rw [show (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr = 24 from headLink_open hS hR O]
    rfl
  intro r hr
  have hb := List.find?_some (p := fun r : RunOf S => r.1 == "planes") hr
  have hnm : r.1 = "planes" := eq_of_beq hb
  have hm : r ∈ statesOfLink lk 2 := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [e2'] at hm
  have hm' : r ∈ b.claims := hm
  rw [IM.claims_alone la] at hm'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm'
  exact tabled_guard _ _ (k3At_planes_tabled Bs.G₀.W Z _ (by decide) 24 rfl hh b' k3 q hq hnm)

/-- **Fwd at the five runs over the reads' place of link 24.** -/
theorem fwd_head_reads {Pp : Type} (XV : OnBytes.Model.Verify.Public) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H) (X : LinkH)
    (arrs : Option (List ℕ)) (lk : Link S Cl) (eL : c.links[24]? = some lk) (x x' : Pp × S)
    (hy : YesOf (blkL Z Bs.G₀ 24 false X arrs) x x')
    (k : TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2) :
    ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (2, "planes"), (3, "join")],
      Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) p.1 p.2 x.2 x'.2 := by
  intro p hp
  have hb : ((p.1 = 3) ∨ (p.1 = 2 ∧ p.2 = "planes")) ∧ (p.2 == "K8.equations") = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  obtain ⟨s₁, hA, nm, pl, what, piece, rs₂, gs₂, hq⟩ :=
    stepsVia_k1Reads Z Bs.G₀ 24 X (k1Ix 24 false + 1) arrs _ _ _ _ hd
  have hr : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → R.Respects r.2 := by
    rcases hb.1 with e | ⟨e, _⟩
    · rw [e]
      exact R.states_head3 hS hR O lk eL p.2
    · rw [e]
      exact R.states_head2 hS hR O lk eL p.2
  have ht : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → Tabled r.2 := by
    rcases hb.1 with e | ⟨e, e'⟩
    · rw [e]
      exact tabled_head3 hS hR O lk eL p.2
    · rw [e, e']
      exact tabled_head2 hS hR O lk eL
  rw [hX]
  have es : (holesAt XV 24 24 lk).silent = k6Silent (phAt XV 24) (statesOfLink lk) := by
    unfold holesAt
    simp
  intro Rr hRr
  have h1 : (if (p.2 == "K8.equations") = true then (holesAt XV 24 24 lk).small x.2
    else
      match readerOf (statesOfLink lk) p.1 p.2 x.2 with
      | some R => some R
      | Option.none => (holesAt XV 24 24 lk).silent p.1 p.2 x.2) = some Rr := hRr
  rw [hb.2, es] at h1
  have h2 := reader_reads XV Bs.G₀ hXW 24 24 X (statesOfLink lk) p.1 p.2 hr ht hA hq k Rr h1
  show (if (p.2 == "K8.equations") = true then (holesAt XV 24 24 lk).small x'.2
    else
      match readerOf (statesOfLink lk) p.1 p.2 x'.2 with
      | some R => some R
      | Option.none => (holesAt XV 24 24 lk).silent p.1 p.2 x'.2) = some Rr
  rw [hb.2, h2]
  rfl

end

/-! ## 5 hRd -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Fwd at every run of every later place of kind K1.** hT: the invariant, asked in front of the
output head's reads' place alone. -/
theorem fwd_all {Pp : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H) (l : ℕ) (hl : l < 25)
    (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (lk : Link S Cl) (eL : c.links[l]? = some lk)
    (x x' : Pp × S) (hy : YesOf (blkL Z Bs.G₀ l d X arrs) x x')
    (hT : l = 24 → d = false → TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2) :
    ∀ p ∈ runsL l d,
      Fwd (readersOfLink (holesAt XV (headLink XV) l lk) lk) p.1 p.2 x.2 x'.2 := by
  have below : l < 24 → ∀ p ∈ runsL l false,
      Fwd (readersOfLink (holesAt XV (headLink XV) l lk) lk) p.1 p.2 x.2 x'.2 := by
    intro hl'
    refine fwd_below XV hX Z Bs.G₀ l hl' d X arrs lk
      (fun name => states_look hS hR O (headLink_open hS hR O) l hl' lk eL name) ?_ x x' hy
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact fun name =>
        states_k4 hS hR O (fun x _ => k4Block_respects x) g (by omega) lk eL name
    · exact fun name => states_k5 hS hR O g (by omega) lk eL name
  intro p hp
  by_cases h24 : l = 24
  · subst h24
    cases d with
    | false =>
      rw [runsHead] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact fwd_head_look hS hR O XV hX false X arrs lk eL x x' hy "objects" (Or.inl rfl)
      rcases List.mem_cons.1 hp with rfl | hp
      · exact fwd_head_look hS hR O XV hX false X arrs lk eL x x' hy "guests" (Or.inr rfl)
      exact fwd_head_reads hS hR O XV hX hXW X arrs lk eL x x' hy (hT rfl rfl) p hp
    | true =>
      rcases runsL_true 24 p hp with h | h
      · exact fwd_head_digits hS hR O XV hX X arrs lk eL x x' hy p h
      · obtain ⟨b, n⟩ := p
        obtain rfl : n = "K8.equations" := h
        exact fwd_digits Z Bs.G₀ 24 X arrs _ _ lk rfl (b, "K8.equations")
          (pairStays_small XV (headLink XV) 24 lk b) x x' hy
  · have hl' : l < 24 := by omega
    cases d with
    | false => exact below hl' p hp
    | true =>
      rcases runsL_true l p hp with h | h
      · exact below hl' p h
      · obtain ⟨b, n⟩ := p
        obtain rfl : n = "K8.equations" := h
        exact fwd_digits Z Bs.G₀ l X arrs _ _ lk rfl (b, "K8.equations")
          (pairStays_small XV (headLink XV) l lk b) x x' hy

/-- **hRd AT ANY MEANING Mg AND NUMBERS N**: of Mg its door's list is read (hfit), and that its
promise in front of the output head's reads' place holds the invariant (hTab). -/
theorem hRd_any (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H)
    (hfit : ∀ l, l < 25 → ∀ d : Bool, runsFitB Mg.more l d (runsL l d) = true)
    (hTab : ∀ x y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 false) x y →
      TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        Pub.formsInT m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 := by
  intro l hl d X arrs _
  refine hRd_of_runs N Mg Dm.pubD (show runsAt Dm.links = runsAt linksFull by rw [hDlk])
    (blkL Z Bs.G₀ l d X arrs) l d (runsL l d) (hfit l hl d) ?_
  intro x x' y hy hIn p hp
  show Fwd (K9.readersAt Dm.lk XV (headLink XV) l) p.1 p.2 x.2 x'.2
  cases e : Dm.lk l with
  | none =>
    rw [K9.readersAt_none _ _ _ _ e]
    intro R hR
    cases hR
  | some lk =>
    rw [K9.readersAt_some _ _ _ _ lk e]
    rw [hlk l hl] at e
    refine fwd_all hS hR O hX hXW l hl d X arrs lk e x x' hy (fun h1 h2 => ?_) p hp
    subst h1
    subst h2
    exact hTab x y hIn

/-- **hRd, to the letter: nothing of the readers stays.** -/
theorem hRd_paid3 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H)
    (hTab : ∀ x y, InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y →
      TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 :=
  hRd_paid2 Dm dk hS hR O hDlk hlk hX fun X arrs _ lk elk x x' y hy hIn =>
    fwd_head_reads hS hR O XV hX hXW X arrs lk elk x x' hy (hTab x y hIn)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.some_of_named
#print axioms VerifiableInference.Desc.K1.tabled_flRun
#print axioms VerifiableInference.Desc.K1.tabled_guard
#print axioms VerifiableInference.Desc.K1.planesAt_tabled
#print axioms VerifiableInference.Desc.K1.reads_tabled
#print axioms VerifiableInference.Desc.K1.lettersAt_tabled
#print axioms VerifiableInference.Desc.K1.tabled_runsBy
#print axioms VerifiableInference.Desc.K1.tabled_join
#print axioms VerifiableInference.Desc.K1.tabled_planes
#print axioms VerifiableInference.Desc.K1.k6_claims_tabled
#print axioms VerifiableInference.Desc.K1.k3At_planes_tabled
#print axioms VerifiableInference.Desc.K1.stepsVia_joined
#print axioms VerifiableInference.Desc.K1.stepsVia_k1Reads
#print axioms VerifiableInference.Desc.K1.quiet_head_of
#print axioms VerifiableInference.Desc.K1.behind_of_head
#print axioms VerifiableInference.Desc.K1.reader_runs
#print axioms VerifiableInference.Desc.K1.self_tables
#print axioms VerifiableInference.Desc.K1.reader_reads
#print axioms VerifiableInference.Desc.K1.tabled_head3
#print axioms VerifiableInference.Desc.K1.tabled_head2
#print axioms VerifiableInference.Desc.K1.fwd_head_reads
#print axioms VerifiableInference.Desc.K1.fwd_all
#print axioms VerifiableInference.Desc.K1.hRd_any
#print axioms VerifiableInference.Desc.K1.hRd_paid3
