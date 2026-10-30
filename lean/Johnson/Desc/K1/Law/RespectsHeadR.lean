-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RespectsHeadR.lean: MEMBERS OF R.Respects (Johnson/Desc/K1/Law/RestRDef.lean: a
run of claims reads nothing of what a later commitment of kind K1 writes, nor the approximate range
proof's part of the state): ALL SEVEN RUNS OF THE OUTPUT HEAD's SEGMENT, as link 24 of the opened
chain states them. Statements with their proofs. NOTHING HERE IS NEW IN ITS PROOF: each lemma is a
lemma of the narrower cut, with its proof, at this cut:
  section A: Johnson/Desc/K1/Law/ReadersStayAt.lean's members by the form of the run;
  section B: Johnson/Desc/K1/Law/RespectsAtt.lean's respects_flRun .. respects_planesCalls and
             block_respects;
  section C: Johnson/Desc/First/Link/Law/RespectsK6.lean's (its SeatRest is SeatRestH here):
             MIRRORED FROM THAT FILE, lemma for lemma;
  section D: Johnson/Desc/K1/Law/ReadersHeadDigits.lean's sections 2 to 5 (the lookup's lot's
             sub-protocol at the output head's link alone: k3At_calls_head).
Ends: states_head2 · states_head3: **each run that blocks 2 and 3 of link 24 state is a member.**
SO: none of the seven reads the field tl.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RestRDef
import Johnson.Desc.K1.Law.ReadersHeadDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.R
open OnBytes OnBytes.Params OnBytes.Model OnBytes.K.Kc Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Here HeadOwn)
open VerifiableInference.Desc.First.Att.P (seatCO parCOf ParC)
open VerifiableInference.Desc.K9 (Read Readers Fn RunOf readerOf lateOf ownRow LinkHoles statesOfLink
  readersOfLink readRun objectsBy guestsNone flRun joinCalls planesCalls planesProg firstAt keysAt
  secondAt asClaimsOf runOfForms ofForm)
open VerifiableInference.Desc.Kinds.Head (Seat Behind Places lettersAt given seatAt planesAt
  callerReaders callerKeys runsBy kind kindWithJoin asClaim seatedClaims blockClaims)
open ProofFile (Cl)

/-! # A -/

/-! ## Members, by the form of the run -/

/-- A run that reads the state, lays claims and leaves the state. -/
theorem respects_readRun (read : S → Except String (List Claim))
    (h : ∀ s s', RestAlike s s' → read s' = read s) : Respects (readRun read) :=
  respects_read read h

/-- K3's "guests" where no guest is handed. -/
theorem respects_guestsNone : Respects guestsNone := respects_readRun _ fun _ _ _ => rfl

/-- The lookup's run "objects", general in where what was heard is read. -/
theorem respects_objectsBy (heard : S → Option Forest.Heard)
    (h : ∀ s s', RestAlike s s' → heard s' = heard s) : Respects (objectsBy heard) := by
  intro s s' hA cl t e
  unfold objectsBy at e ⊢
  obtain ⟨F, hF, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨g, hg, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  cases hF0 : s.fork? with
  | none => rw [hF0] at hF; cases hF
  | some F₀ =>
    rw [hF0] at hF
    obtain rfl : F₀ = F := Except.ok.inj hF
    obtain ⟨F', g1, g2⟩ := hA.fork hF0
    refine ⟨s'.putFork (F'.paid g.owedObjects), ?_, hA.putFork (paid_rest g2.symm _)⟩
    rw [g1, h s s' hA]
    show (Except.ok F' : Except String Fork).bind _ = _
    simp only [Except.bind]
    rw [hg]
    rfl

/-- **K3's "objects" at the lookup on the calls.** -/
theorem respects_objectsCalls : Respects K9.objectsCalls :=
  respects_objectsBy _ fun _ _ hA => hA.lookHeard.symm

/-- The first chain's seat's test: "the two states hold the same reply". -/
theorem sameReply_alike (s s' t t' : S) (h : RestAlike s s') (k : RestAlike t t') :
    ProofFile.sameReply s' t' = ProofFile.sameReply s t := by
  unfold ProofFile.sameReply
  rw [h.out, k.out]

/-! # B -/

/-! ## A run made of such a program -/

theorem respects_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim) (h1 : ReadsRest pre1) (h2 : ReadsRest pre2)
    (ht : ∀ b F F', forkRest F = forkRest F' → test b F' = test b F)
    (hm : ∀ b c, Markless (m b c)) : Respects (flRun e0 pre1 e1 test pre2 e2 m out) := by
  intro s s' hA cl t e
  unfold flRun at e ⊢
  obtain ⟨F, hF, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨b, hb, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨_, hn, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨c, hc, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨x, hx, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  cases hF0 : s.fork? with
  | none => rw [hF0] at hF; cases hF
  | some F₀ =>
    rw [hF0] at hF
    obtain rfl : F₀ = F := Except.ok.inj hF
    obtain ⟨F', g1, g2⟩ := hA.fork hF0
    cases hm0 : m b c F₀ [] with
    | none => rw [hm0] at hx; cases hx
    | some x₀ =>
      rw [hm0] at hx
      obtain rfl : x₀ = x := Except.ok.inj hx
      have k := hm b c F₀ F' [] g2.symm
      rw [hm0] at k
      obtain ⟨G', k1, k2⟩ := k
      refine ⟨s'.putFork G', ?_, hA.putFork k2⟩
      rw [g1, h1.alike hA, h2.alike hA]
      show (Except.ok F' : Except String Fork).bind _ = _
      simp only [Except.bind]
      rw [hb]
      simp only [bind, Except.bind]
      rw [ht b F₀ F' g2.symm, hn, hc]
      simp only [k1]
      rfl

theorem readsRest_named {α : Type} (e : String) (f : S → Option α) (h : ReadsRest f) :
    ReadsRest fun s => named e (f s) := fun s => by
  show named e (f (restOf s)) = named e (f s)
  rw [h s]

/-- **K3's "join" at the calls**: where the caller's keys read the rest alone. -/
theorem respects_joinCalls (keys : S → Option (Array Aff)) (hk : ReadsRest keys) :
    Respects (joinCalls keys) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hk) (fun g F F' h => unpaid_rest g.owedJoin F F' h)
    fun g KF => joinF_markless g KF

/-- **K3's "planes" at the calls**: where the caller's readers read the rest alone. -/
theorem respects_planesCalls (lm : Nat) (readers : K3.Readers S) (hr : ReadsRest readers) :
    Respects (planesCalls lm readers) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hr) (fun g F F' h => unpaid_rest g.owedPlanes F F' h)
    fun g r => planesProg_markless lm g r

theorem block_respects (digits : Bool) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) :
    ∀ r ∈ (K3.block (if digits then K3.seatDigits ofForm else K3.seatCalls ofForm) piece laid
      before p []).claims, digits = false → Respects r.2 := by
  intro r hr hd
  subst hd
  have hr' : r ∈ [("objects", K9.objectsCalls), ("guests", guestsNone)] := hr
  have : r = ("objects", K9.objectsCalls) ∨ r = ("guests", guestsNone) := by
    simpa using hr'
  cases this with
  | inl h => rw [h]; exact respects_objectsCalls
  | inr h => rw [h]; exact respects_guestsNone


/-! # C -/

/-- **A seat of the head's kind whose readers read the rest alone.** -/
structure SeatRestH (L : Seat S) : Prop where
  reply : ReadsRest L.reply
  request : ReadsRest L.request
  lookup : ReadsRest L.lookup
  reads : ReadsRest L.reads
  heard : ReadsRest L.heard
  keys : ∀ s fs, L.setKeyForms s fs = s

/-- The letters that the runs are made of read the rest alone. -/
theorem lettersAt_rest (p : Kinds.Head.Par) (L : Seat S) (h : SeatRestH L) : ReadsRest (lettersAt p L) := by
  intro s
  unfold lettersAt given Kinds.Reply.token
  rw [h.lookup s, h.reply s, h.request s, h.heard s, h.reads s]

/-- What a list of named functions answers under a name. -/
theorem lookup_named {β : Type} (F : String → β) : ∀ (names : List String) (n : String) (r : β),
    (names.map fun x => (x, F x)).lookup n = some r → r = F n
  | [], _, _, h => nomatch h
  | x :: l, n, r, h => by
    rw [List.map_cons, List.lookup_cons] at h
    by_cases e : (n == x) = true
    · rw [e] at h
      obtain rfl : n = x := by simpa using e
      exact (Option.some.inj h).symm
    · have e' : (n == x) = false := by simpa using e
      rw [e'] at h
      exact lookup_named F l n r h

/-- **EVERY RUN OF runsBy AT SUCH A SEAT READS THE REST ALONE.** -/
theorem respects_runsBy (names : List String)
    (runs : Kinds.Head.Given → Behind → Places → List (String × List Kinds.Form))
    (keys : Kinds.Head.Given → Behind → Places → List Kinds.Form) (toCl : Kinds.Form → Claim) (p : Kinds.Head.Par)
    (L : Seat S)
    (h : SeatRestH L) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (runsBy names runs keys toCl p L).lookup name = some run) : Respects run := by
  unfold runsBy at hrun
  obtain rfl := lookup_named _ names name run hrun
  have e : (fun (_ : Nat) (s : S) => (do
      let (g, b, x) ← lettersAt p L s
      let fs ← named "the run is there" ((runs g b x).lookup name)
      pure (fs.map toCl, if names.head? == some name then L.setKeyForms s (keys g b x) else s) :
        Except String (List Claim × S))) =
      fun _ s => ((do
        let (g, b, x) ← lettersAt p L s
        let fs ← named "the run is there" ((runs g b x).lookup name)
        pure (fs.map toCl) : Except String (List Claim))).map fun l => (l, s) := by
    funext _ s
    simp only [h.keys, ite_self]
    cases lettersAt p L s with
    | error _ => rfl
    | ok y =>
      obtain ⟨g, b, x⟩ := y
      show (named "the run is there" ((runs g b x).lookup name) >>= fun fs =>
        pure (fs.map toCl, s)) = Except.map (fun l => (l, s))
          (named "the run is there" ((runs g b x).lookup name) >>= fun fs => pure (fs.map toCl))
      cases named "the run is there" ((runs g b x).lookup name) <;> rfl
  rw [e]
  refine respects_readRest _ fun s => ?_
  rw [lettersAt_rest p L h s]

/-- Every run that the kind states. -/
theorem respects_k6 (toCl : Kinds.Form → Claim) (L : Seat S) (h : SeatRestH L) (l piece : Nat)
    (p : Kinds.Head.Par) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind toCl L l piece p).claims.lookup name = some run) : Respects run := by
  unfold kind at hrun
  dsimp only at hrun
  exact respects_runsBy _ _ _ toCl p L h name run hrun

/-- **THE SEAT IN THE VERIFIER's STATE IS SUCH A SEAT.** -/
theorem seatRest_at (h : Model.Head.Shape) (iU3 : Nat) : SeatRestH (seatAt h iU3) where
  reply _ := rfl
  request _ := rfl
  lookup s := by
    show (restOf s).lookHeard?.map _ = s.lookHeard?.map _
    rw [lookHeard_rest]
  reads s := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head o =>
      by_cases ho : o.opened = true
      · simp only [seatAt, restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, ho, if_true, forkRest, Array.getElem?_map]
        cases o.t with
        | none => rfl
        | some tt => cases o.F.trees[iU3]? <;> rfl
      · simp only [seatAt, restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, if_neg ho]
    | _ => rfl
  heard s := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> rfl
  keys _ _ := rfl

/-! # D -/

/-! ## 2 The seat's form -/

theorem respects_laid1 {b b' : Block S Cl} {name : String} {a : Place}
    (la : IM.LaidAlone ProofFile.sameReply b b' name a) (h0 : ∀ r ∈ b'.claims, Respects r.2) :
    ∀ r ∈ b.claims, Respects r.2 := by
  intro r hr
  rw [IM.claims_alone la] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact respects_guarded ProofFile.sameReply (fun s s' t t' h k => sameReply_alike s s' t t' h k) c.2
    (h0 c hc)

theorem respects_states1 (lk : Link S Claim) (b : ℕ) (B : Block S Claim)
    (hB : lk.hear[b]? = some B) (h : ∀ r ∈ B.claims, Respects r.2) (name : String) :
    ∀ r, (statesOfLink lk b).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  intro r hr
  have hm : r ∈ statesOfLink lk b := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [hB] at hm
  exact h r hm

/-! ## 3 The output head's caller's readers and key vectors read the rest alone -/

theorem planesAt_rest (iU3 : ℕ) : ReadsRest (planesAt iU3) := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head o =>
    by_cases ho : o.opened = true
    · simp only [planesAt, restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, ho, if_true, forkRest, Array.getElem?_map]
      cases o.t with
      | none => rfl
      | some tt => cases o.F.trees[iU3]? <;> rfl
    · simp [planesAt, restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, ho]
  | _ => rfl

theorem callerReaders_rest (iU3 : ℕ) : ReadsRest (callerReaders (planesAt iU3)) := by
  intro s
  unfold callerReaders
  rw [planesAt_rest iU3 s]

theorem callerKeys_rest (p : Kinds.Head.Par) (h : Head.Shape) (iU3 : ℕ) :
    ReadsRest (callerKeys p (seatAt h iU3)) := by
  intro s
  unfold callerKeys
  rw [lettersAt_rest p _ (seatRest_at h iU3) s]

/-! ## 4 The lots' runs -/

/-- **The lookup's lot's sub-protocol on the calls, at the output head's link.** -/
theorem k3At_calls_head (W : Verify.Public) (Z : ProofFile.Pub) (a : Place) (ha : a.piece ≤ 3) (l : ℕ)
    (hl : a.link = some l) (hh : K3.isHead W l = true) (b' : Block S Cl)
    (h : IM.k3At W Z a = some b') : ∀ r ∈ b'.claims, Respects r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, Respects r.2 :=
    theWhole_calls_of (fun c => Respects c.2) K3Lot.ofForm
      (fun piece laid sent p c hc => block_respects false piece laid sent p c hc rfl) W _ _ a ha
      b₀ h₀
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
      have key : ReadsRest rd := by
        simp only [K3Lot.readersAt, hh, if_true] at hr
        obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hr
        exact callerReaders_rest i
      intro r hm
      have hm' : r ∈ b₀.claims ++ [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm rd)] :=
        hm
      rcases List.mem_append.1 hm' with h1 | h1
      · exact e0 r h1
      · rw [List.mem_singleton.1 h1]
        exact respects_planesCalls p.lm rd key

theorem lookup_mem {β : Type} (F : String → β) : ∀ (names : List String) (n : String), n ∈ names →
    (names.map fun x => (x, F x)).lookup n = some (F n)
  | [], _, h => nomatch h
  | x :: l, n, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : (n == x) = true
    · rw [e]
      obtain rfl : n = x := by simpa using e
      rfl
    · have e' : (n == x) = false := by simpa using e
      rw [e']
      rcases List.mem_cons.1 h with h1 | h1
      · rw [h1] at e
        simp at e
      · exact lookup_mem F l n h1

theorem respects_runsBy_mem (names : List String)
    (runs : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places →
      List (String × List Kinds.Form))
    (keys : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places → List Kinds.Form)
    (toCl : Kinds.Form → Claim) (p : Kinds.Head.Par) (L : Seat S) (h : SeatRestH L) :
    ∀ r ∈ runsBy names runs keys toCl p L, Respects r.2 := by
  intro r hr
  have hr' := hr
  unfold runsBy at hr'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hr'
  exact respects_runsBy names runs keys toCl p L h n _ (by
    unfold runsBy
    exact lookup_mem _ names n hn)

/-- **K6's lot's sub-protocol: all four runs.** -/
theorem k6_claims_respects {W : Verify.Public} {l : ℕ} {ms : List (ℕ × ℕ)} {b' : Block S Claim}
    (h : seatedClaims W l ms = some b') : ∀ r ∈ b'.claims, Respects r.2 := by
  unfold seatedClaims at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 h0
  have hk : ∀ (p : Kinds.Head.Par), ∀ r ∈ (kind asClaim (seatAt W.hS iU3) l 4 p).claims, Respects r.2 := by
    intro p r hr
    unfold kind at hr
    dsimp only at hr
    exact respects_runsBy_mem _ _ _ asClaim p _ (seatRest_at W.hS iU3) r hr
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
      exact respects_joinCalls _ (callerKeys_rest _ W.hS iU3)
  · exact hk _ r (List.mem_of_mem_drop h1)

/-! ## 5 Link 24 -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
  (hR : VerifierAndGoals.readFiles P = .ok pp)
  (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
include hS hR O

theorem states_head2 (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  have hh : K3.isHead Bs.G₀.W 24 = true := by
    show (24 == (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr) = true
    rw [show (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr = 24 from headLink_open hS hR O]
    rfl
  exact respects_states1 lk 2 b e2'
    (respects_laid1 la (k3At_calls_head Bs.G₀.W Z _ (by decide) 24 rfl hh b' k3)) name

theorem states_head3 (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 3).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  obtain ⟨Lk, b, b', ms, e1, e2, -, k6, la, -⟩ := IM.k6_of hS hR O
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  exact respects_states1 lk 3 b e2 (respects_laid1 la (k6_claims_respects k6)) name

end

end VerifiableInference.Desc.K1.R

#print axioms VerifiableInference.Desc.K1.R.sameReply_alike
#print axioms VerifiableInference.Desc.K1.R.respects_objectsCalls
#print axioms VerifiableInference.Desc.K1.R.respects_flRun
#print axioms VerifiableInference.Desc.K1.R.respects_joinCalls
#print axioms VerifiableInference.Desc.K1.R.respects_planesCalls
#print axioms VerifiableInference.Desc.K1.R.block_respects
#print axioms VerifiableInference.Desc.K1.R.lettersAt_rest
#print axioms VerifiableInference.Desc.K1.R.respects_runsBy
#print axioms VerifiableInference.Desc.K1.R.seatRest_at
#print axioms VerifiableInference.Desc.K1.R.respects_laid1
#print axioms VerifiableInference.Desc.K1.R.planesAt_rest
#print axioms VerifiableInference.Desc.K1.R.callerKeys_rest
#print axioms VerifiableInference.Desc.K1.R.k3At_calls_head
#print axioms VerifiableInference.Desc.K1.R.k6_claims_respects
#print axioms VerifiableInference.Desc.K1.R.states_head2
#print axioms VerifiableInference.Desc.K1.R.states_head3
