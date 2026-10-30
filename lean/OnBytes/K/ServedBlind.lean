-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ServedBlind.lean: the test of the user's statement that every yes of the program has
passed (`servedAt`, OnBytes/K/Served.lean) is blind to the values of the tokens behind the prompt.

A tie between the program and a verifier speaks of served statements alone. A "served" that let
through true claims alone would make the tie say nothing. The claimed output stands in the request
(`outputOf`, OnBytes/K/Tokens.lean). So it matters that the written test cannot tell one output from
another.

Main names:
  `Mate V x x'`: x' is x with other tokens behind the prompt: the same public files, options,
    lengths, r, e and prompt; x''s tokens and reply below V; x''s reply 0 before the window's end.
    No proof here reads that the prompts are the same: the test is blind to the prompt's tokens too.
  `Blind V Sv`: Sv holds of every mate of a statement of which it holds.
  `blind_servedAt`: `servedAt Z` is blind at V := the vocabulary's size in the planner's answer on
    Z's three files.
  On the way: `tailAt_free`: the whole end of the call is the same at two requests at which the
    stage request's findings are the same and what the answer is about is the same. `tail_refused`:
    where the stage request refuses, the end is no yes. `requestFound_ok`, `stFromCall_ok`,
    `coveredOf_ok`: what a stage request that has not refused has tested. `reqAlike_of_mate`: a
    served statement and a mate of it are alike (`ReqAlike`, OnBytes/K/ServedFree.lean).

Asked in `blind_servedAt`: the planner returns on Z's files; `ItemFree`: whether the item of the
request is made, and what the comparison with the public part says of it, hang on the request's
length alone. `itemStep_free` (OnBytes/K/ServedFreeItem.lean) proves its equation at all files, with
`itemStep` written out; no statement of this library concludes `ItemFree` by name.

Limits: `ItemFree` is a hypothesis by name in this file. That the planner returns is not shown here;
at `VerifierAndGoals.storedPublicFiles` it is (`planned_zFull_returns`, AtFullSide/Planner/MadeReturns.lean). That a
statement has a mate with another output is not shown here. Nothing here shows that the test passes
any statement: if it passes none, it is blind for nothing. What blindness shuts out is one thing: a
"served" that lets through true claims alone. It says nothing against a "served" that never says
yes, which is blind for free. No theorem here says "alike, so one end of the call": from `ReqAlike`
to the two hypotheses of `tailAt_free` the proof of `blind_servedAt` also takes the test on whole
words, `ItemFree` and the number of the request's words. No file calls the theorem. It is of
`servedAt` alone: a "served" that asks more (tests on dry runs, a reading of statements as
instances, a set of instances) is blind if each further clause is; that is shown of none here.
Nothing on the checks of the key file, the entry file and the proof file. For proofs only; the
program does not import this file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.ServedFree

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- A file has a quarter of its bytes as words. -/
theorem words32_size (b : ByteArray) : (words32 b).size = b.size / 4 := by
  simp [words32, fileWords]

/-- What the answer is about reads the number of words, r and e alone. -/
theorem cpCovered_alike (P P' : Array UInt32) (L : PolicyLines) (hs : P.size = P'.size)
    (hr : (P.getD (P.size - 2) 0).toNat = (P'.getD (P.size - 2) 0).toNat)
    (he : (P.getD (P.size - 2 + 1) 0).toNat = (P'.getD (P.size - 2 + 1) 0).toNat) :
    cpCovered P L = cpCovered P' L := by
  unfold cpCovered
  dsimp only
  rw [← hs, ← hr, ← he]

/-- The end of a whole call reads the request's words in what the answer is about alone. -/
theorem cpStagesRun_about (st : List StageOut) (bb : Bool) (asked : Nat) (id : CpId)
    (P P' : Array UInt32) (L : PolicyLines) (h : cpCovered P L = cpCovered P' L) :
    cpStagesRun st none bb asked id (some (P, L)) = cpStagesRun st none bb asked id (some (P', L))
      := by
  unfold cpStagesRun
  dsimp only
  rw [h]

/-- The end of the call is the same where the stage request's findings and what the answer is about
are. -/
theorem tailAt_free (p : Planned) (pol lay KL request y request' y' : ByteArray) (o : Options)
    (i hp : String)
    (hreq : requestFound (commonAt p i) o pol KL request y true =
      requestFound (commonAt p i) o pol KL request' y' true)
    (hcp : cpCovered (words32 request) (commonAt p i).policyLines =
      cpCovered (words32 request') (commonAt p i).policyLines) :
    tailAt p ⟨pol, lay, KL, request, y, o⟩ i hp =
      tailAt p ⟨pol, lay, KL, request', y', o⟩ i hp := by
  unfold tailAt outsAt
  dsimp only
  rw [hreq]
  exact cpStagesRun_about _ _ _ _ _ _ _ hcp

/-- The test is the same where the ends of the call are. -/
theorem servedAt_of_tail (Z : Pub) (pol lay KL request y request' y' : ByteArray) (o : Options)
    (H : ∀ p i hp, planned pol KL (some lay) = .ok p →
      tailAt p ⟨pol, lay, KL, request, y, o⟩ i hp = tailAt p ⟨pol, lay, KL, request', y', o⟩ i hp) :
    servedAt Z ⟨pol, lay, KL, request, y, o⟩ = servedAt Z ⟨pol, lay, KL, request', y', o⟩ := by
  unfold servedAt
  dsimp only
  congr 1
  cases h3 : planned pol KL (some lay) with
  | error _ => cases o.id.bind idAsked <;> cases Model.hPar pol KL (some lay) <;> rfl
  | ok p =>
    cases o.id.bind idAsked with
    | none => rfl
    | some i =>
      cases Model.hPar pol KL (some lay) with
      | error _ => rfl
      | ok hp =>
        show isYes _ = isYes _
        rw [H p i _ h3]

/-! ## A yes of the end of the call: no stage has refused -/

/-- A stage that has refused, without a record, shows a fault. -/
theorem stageFault_refused (asked : Nat) (own : Bool) (x : StageOut) (name : String)
    (h1 : x.acct = none) (h2 : x.ending = .no name) : (stageFault asked own x).isSome = true := by
  unfold stageFault
  rw [h1, h2]
  dsimp only
  split <;> rfl

/-- So do three stages of which the last shows one. -/
theorem firstFault_last (asked : Nat) (a b c : StageOut)
    (h : (stageFault asked false c).isSome = true) :
    (firstFault asked false [a, b, c]).isSome = true := by
  simp only [firstFault]
  split
  · rfl
  · split
    · rfl
    · exact h

/-- A whole call whose stages show a fault does not end in a yes. -/
theorem cpStagesRun_fault (st : List StageOut) (bb : Bool) (asked : Nat) (id : CpId)
    (about : Option (Array UInt32 × PolicyLines))
    (h : (firstFault asked false (st.map StageOut.asRead)).isSome = true) :
    isYes (cpStagesRun st none bb asked id about) = false := by
  unfold cpStagesRun
  dsimp only
  split
  · split <;> rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i hn
        rw [show (none : Option StageName).isSome = false from rfl] at hn
        rw [hn] at h
        cases h

/-- Where the stage request refuses, the end of the call is no yes. -/
theorem tail_refused (p : Planned) (x : UserStm) (i hp : String) (e : Refused)
    (h : requestFound (commonAt p i) x.options x.pol x.KL x.request x.y true = .error e) :
    isYes (tailAt p x i hp) = false := by
  unfold tailAt outsAt
  rw [h]
  refine cpStagesRun_fault _ _ _ _ _ ?_
  exact firstFault_last _ _ _ _ (stageFault_refused _ _ _ e.name rfl rfl)

/-! ## What a stage request that has not refused has tested -/

/-- Two steps in a row have returned: so has each. -/
theorem bind_returns {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A step that has returned under `named` has returned. -/
theorem named_returns {α : Type} {x : Except String α} {a : α} (h : named x = .ok a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => exact congrArg _ (Except.ok.inj h)

/-- A stage request that has not refused has read request and reply, and has the covered positions.
-/
theorem requestFound_ok {C : Common} {o : Options} {pol KL request y : ByteArray} {b : Bool}
    {f : Found} (h : requestFound C o pol KL request y b = .ok f) :
    ∃ so cov, Head.stFromCall (words32 request) (words32 y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov := by
  rw [requestFound_eq] at h
  obtain ⟨_, _, h⟩ := bind_returns h
  obtain ⟨so, h1, h⟩ := bind_returns h
  obtain ⟨cov, h2, _⟩ := bind_returns h
  exact ⟨so, cov, named_returns h1, named_returns h2⟩

/-- What the reader of request and reply returns, and two of its tests. -/
theorem stFromCall_ok {P Q : Array UInt32} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall P Q T = .ok so) :
    so = ⟨P, (P.getD T 0).toNat, (P.getD (T + 1) 0).toNat, (Q.getD 0 0).toNat⟩ ∧
      P.size = T + 2 ∧
      (decide ((P.getD (T + 1) 0).toNat < T) && (Q.getD 0 0).toNat != 0) = false := by
  unfold Head.stFromCall Head.needed at h
  dsimp only at h
  by_cases c1 : (!(P.isEmpty || Q.isEmpty)) = true
  · by_cases c2 : (!(P.size != T + 2 || Q.size != 1)) = true
    · by_cases c3 : (!(decide ((P.getD T 0).toNat ≥ (P.getD (T + 1) 0).toNat) ||
          decide ((P.getD (T + 1) 0).toNat > T) ||
          (decide ((P.getD (T + 1) 0).toNat < T) && (Q.getD 0 0).toNat != 0))) = true
      · rw [if_pos c1, if_pos c2, if_pos c3] at h
        refine ⟨(Except.ok.inj h).symm, ?_, ?_⟩
        · simp only [Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq] at c2
          exact c2.1
        · simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at c3
          exact c3.2
      · rw [if_pos c1, if_pos c2, if_neg c3] at h
        cases h
    · rw [if_pos c1, if_neg c2] at h
      cases h
  · rw [if_neg c1] at h
    cases h

/-- Two of the tests behind the covered positions: the reply and every token are below V. -/
theorem coveredOf_ok {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (h : Head.coveredOf so T V = .ok cov) :
    decide (so.y < V) = true ∧
      (((so.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true := by
  unfold Head.coveredOf Head.needed at h
  dsimp only at h
  by_cases c1 : decide (so.y < V) = true
  · by_cases c2 : (so.req.size == T + 2) = true
    · by_cases c3 : (((so.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true
      · exact ⟨c1, c3⟩
      · rw [if_pos c1, if_pos c2, if_neg c3] at h
        cases h
    · rw [if_pos c1, if_neg c2] at h
      cases h
  · rw [if_neg c1] at h
    cases h

/-- The program's test on the tokens, from the same on the list of tokens. -/
theorem all_of_tokens (P : Array UInt32) (T V : Nat)
    (h : ∀ t ∈ (P.toList.take T).map (·.toNat), t < V) :
    (((P.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro v hv
  have hv' : v ∈ ((P.extract 0 T).map (·.toNat)).toList := Array.mem_toList_iff.2 hv
  simp only [Array.toList_map, Array.toList_extract] at hv'
  exact decide_eq_true (h v hv')

/-! ## Blind -/

/-- x' is x with other tokens behind the prompt: the same public files, options, lengths, r, e and
prompt; every token and the reply below V; the reply 0 before the window's end. -/
structure Mate (V : Nat) (x x' : UserStm) : Prop where
  pol : x'.pol = x.pol
  lay : x'.lay = x.lay
  KL : x'.KL = x.KL
  options : x'.options = x.options
  sizeR : x'.request.size = x.request.size
  sizeY : x'.y.size = x.y.size
  r : rOf x' = rOf x
  e : eOf x' = eOf x
  prompt : promptOf x' = promptOf x
  range : (∀ t ∈ tokensOf x', t < V) ∧ yOf x' < V
  zero : eOf x' ≠ windowOf x' → yOf x' = 0

/-- A test of statements that holds of every mate of a statement of which it holds. -/
def Blind (V : Nat) (Sv : UserStm → Prop) : Prop := ∀ x x', Mate V x x' → Sv x → Sv x'

/-- What is asked of the item: whether it is made, and what the comparison with the public part says
of it, hang on the request's length alone. -/
def ItemFree (X : Public) (pol KL : ByteArray) : Prop :=
  ∀ request request' : ByteArray, request.size = request'.size →
    itemStep X pol KL request = itemStep X pol KL request'

/-- A statement on which the two readers have returned, and a mate of it, are alike. -/
theorem reqAlike_of_mate {T V : Nat} {x x' : UserStm} (m : Mate V x x') {so : Head.StOwn}
    {cov : Head.Covered} (h1 : Head.stFromCall (words32 x.request) (words32 x.y) T = .ok so)
    (h2 : Head.coveredOf so T V = .ok cov) :
    ReqAlike T V (words32 x.request) (words32 x.y) (words32 x'.request) (words32 x'.y) := by
  obtain ⟨rfl, hP, hy⟩ := stFromCall_ok h1
  obtain ⟨c1, c3⟩ := coveredOf_ok h2
  have sP : (words32 x.request).size = (words32 x'.request).size := by
    rw [words32_size, words32_size, m.sizeR]
  have sQ : (words32 x.y).size = (words32 x'.y).size := by
    rw [words32_size, words32_size, m.sizeY]
  have w : windowOf x = T := by
    unfold windowOf
    omega
  have w' : windowOf x' = T := by
    unfold windowOf
    omega
  have hr : ((words32 x.request).getD T 0).toNat = ((words32 x'.request).getD T 0).toNat := by
    have := m.r
    unfold rOf at this
    rw [w, w'] at this
    exact this.symm
  have he : ((words32 x.request).getD (T + 1) 0).toNat =
      ((words32 x'.request).getD (T + 1) 0).toNat := by
    have := m.e
    unfold eOf at this
    rw [w, w'] at this
    exact this.symm
  refine ⟨sP, sQ, hr, he, ?_, ?_, ?_⟩
  · rw [hy]
    by_cases c : ((words32 x.request).getD (T + 1) 0).toNat < T
    · have z : yOf x' = 0 := m.zero (by
        unfold eOf
        rw [w', ← he]
        omega)
      unfold yOf at z
      rw [z]
      simp
    · rw [decide_eq_false c, Bool.false_and]
  · have := m.range.2
    unfold yOf at this
    exact c1.trans (decide_eq_true this).symm
  · refine c3.trans (all_of_tokens _ _ _ ?_).symm
    have := m.range.1
    unfold tokensOf at this
    rw [w'] at this
    exact this

/-- The test of the user's statement that every yes of the program has passed is blind to the values
of the tokens behind the prompt. -/
theorem blind_servedAt (Z : Pub) (p : Planned) (hp : planned Z.pol Z.KL (some Z.lay) = .ok p)
    (hI : ItemFree p.X Z.pol Z.KL) : Blind p.X.P.h.V fun x => servedAt Z x = true := by
  intro x x' m hs
  obtain ⟨pol, lay, KL, request, y, o⟩ := x
  obtain ⟨pol', lay', KL', request', y', o'⟩ := x'
  obtain rfl : pol' = pol := m.pol
  obtain rfl : lay' = lay := m.lay
  obtain rfl : KL' = KL := m.KL
  obtain rfl : o = o' := m.options.symm
  have hs0 := hs
  unfold servedAt at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, _⟩, hy⟩ := hs
  rw [hp] at hy
  cases hi : o.id.bind idAsked with
  | none => rw [hi] at hy; cases hy
  | some i =>
    cases hh : Model.hPar Z.pol Z.KL (some Z.lay) with
    | error _ => rw [hi, hh] at hy; cases hy
    | ok hd =>
      rw [hi, hh] at hy
      have hy : isYes (tailAt p ⟨Z.pol, Z.lay, Z.KL, request, y, o⟩ i (Model.hex64 hd)) = true := hy
      cases hf : requestFound (commonAt p i) o Z.pol Z.KL request y true with
      | error e =>
        rw [tail_refused p ⟨Z.pol, Z.lay, Z.KL, request, y, o⟩ i _ e hf] at hy
        cases hy
      | ok f =>
        obtain ⟨so, cov, h1, h2⟩ := requestFound_ok hf
        have A : ReqAlike p.X.T p.X.P.h.V (words32 request) (words32 y) (words32 request')
            (words32 y') := reqAlike_of_mate m h1 h2
        have hP := (stFromCall_ok h1).2.1
        have e4 : (request.size % 4 != 0 || y.size % 4 != 0) =
            (request'.size % 4 != 0 || y'.size % 4 != 0) := by
          rw [show request'.size = request.size from m.sizeR, show y'.size = y.size from m.sizeY]
        rw [← hs0]
        refine (servedAt_of_tail Z Z.pol Z.lay Z.KL request y request' y' o ?_).symm
        intro p' i' hp' hq
        obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hq)
        refine tailAt_free p Z.pol Z.lay Z.KL request y request' y' o i' hp'
          (requestFound_free (commonAt p i') o Z.pol Z.KL request y request' y' true e4 A
            (hI request request' m.sizeR.symm)) ?_
        refine cpCovered_alike _ _ _ A.sizeP ?_ ?_
        · rw [hP]
          exact A.r
        · rw [hP]
          exact A.e

end OnBytes.K
