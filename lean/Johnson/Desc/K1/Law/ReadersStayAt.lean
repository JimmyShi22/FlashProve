-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ReadersStayAt.lean: THE ROW
"RS" OF K01_law: OVER A YES OF A LATER MOMENT's SENDING OF KIND K1 THE SEGMENT's READERS ANSWER AS
THEY DID, where each run that the item names reads nothing of what the sending writes. K1's HALF IS
PROVED; THE RUNS' HALF IS ONE NAMED PREMISE A RUN. Definitions, and statements with their proofs.
Why. The public item formsIn m k r (Johnson/Desc/First/Batch/FormsPub.lean) calls the readers D.Rd,
a letter, at the state: Johnson/Desc/K1/Law/PubAtLaterIndex.lean keeps the item under ReadersStay.
At the term that is meant (readersOfLink, Johnson/Desc/First/Batch/ReadersOfLink.lean) THE READER IS
THE RUN ITSELF, called at the state. The equation "the reader answers behind as in front" is owed
by every block between a run's hearing block and the batching, for every run then open: blocks
times runs. THE CUT HERE MAKES IT A SUM: a block's files are to show once what its yes writes;
a run's files are to show once that its run reads none of that.
OBJECT. commitAtS (Johnson/Desc/K1/AtS.lean), so laterAt (Johnson/Desc/K1/Places.lean): on any
rounds. NOT THE READS' PLACE's JOINED BLOCK: its quiet step writes the smallness test's fields and
the tables, which runs read. It is not wanted: BY A LOOK THROUGH LEAN AT THE TABLE's OWN LISTS (at
the full size) a forms' public item is open in front of and behind a later
place of K1 AT THE 25 DIGITS' PLACES ALONE; it is formsIn, of the sending's own segment; the runs:
layers (1, objects) (1, guests) (2, front) (2, back) (4, K8.equations); attention (1, objects) (1,
guests) (1, planes) (2, join) (2, first) (2, keys) (2, second) (4, K8.equations); the head (2,
objects) (2, guests) (2, planes) (3, join) (3, norm) (3, policy) (3, logits) (5, K8.equations).
USER. The row K01_law's files (FillL.pub at formsIn: pub_formsIn_digits) and whoever takes the
sentence forms back over the yes (formsQA_back asks the equation: readers_eq_commit).
THE TERMS (restOf, RestAlike, Respects, ReadsRest, PairStays) AND THE LAWS THAT ARE GENERAL IN THE
RUN (readerOf_alike, readersOfLink_alike, respects_read, respects_guarded) STAND IN A LIGHT FILE,
Johnson/Desc/K1/Law/RestDef.lean, over which a run's member can be typed.
Main names:
  commitAtS_alike     **K1's HALF: A YES WRITES NOTHING BUT WHAT restOf TAKES OFF THE STATE.**
                      (Its steps: rootTaken_rest .. commitOwn_forkRest, commitOwn_checkRest,
                      commitOwn_linkRest, rest_put.)
  readers_eq_commit, readers_eq_laterAt: the equation over a yes, from PairStays at each pair.
  readersStay_commit  ReadersStay so.
  pub_formsIn_digits  **formsIn m k r over a yes of laterAt**, ReadersStay paid so.
  Members, by the form of the run: respects_readRun, respects_guestsNone, respects_objectsBy,
  respects_objectsCalls; sameReply_alike: the first chain's seat's test, for respects_guarded.
IS IT EMPTY HERE? Respects has members: here K3's "objects" and "guests"; all seven runs of an
attention segment in Johnson/Desc/K1/Law/RespectsAtt.lean. A FACT BY A SEARCH OF THE SOURCES, NO
THEOREM: the mark "root" is read at one place of the verifier's model and the kinds' texts: the
commitment's own test "committed".
What is not claimed. Respects of K4's, the head's or the smallness test's runs. That a real chain's
link states the runs of which the members speak. That D.Rd is readersOfLink at any filling. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RestDef
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.First.Batch.BlindClaims
import Johnson.Desc.K1.Law.SmpStayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Here Pub PubData pubAll)
open VerifiableInference.Desc.K9 (Read Readers RunOf Fn readerOf lateOf ownRow LinkHoles
  statesOfLink readersOfLink readRun objectsBy guestsNone)

variable {Cl : Type}

/-! ## The sending leaves the rest -/

theorem rootTaken_rest (F : Fork) (t w : Nat) : forkRest (F.rootTaken t w) = forkRest F := by
  have e : (F.trees.modify t fun X => { X with root := some w }).map treeRest =
      F.trees.map treeRest := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_map, Array.getElem_modify]
      split <;> rfl
  unfold forkRest Fork.rootTaken
  dsimp only
  rw [e]

theorem commitOne_rest {L : LinkCtx} {F F' : Fork} {t : Nat} (h : L3.commitOne L F t = .ok F') :
    forkRest F' = forkRest F := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_rest _ _ _)
    | cases h

theorem commitAll_rest {L : LinkCtx} : ∀ (ts : List Nat) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → forkRest F' = forkRest F
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_rest ts F₁ F' h).trans (commitOne_rest h1)

theorem commitBehind_rest {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List Nat}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : forkRest F' = forkRest F := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact commitAll_rest ts F F₁ h1
    · cases h

theorem commitStep_rest {W : Type} {send : L3.Send W} {ts : List Nat} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    forkRest s'.F = forkRest s.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_rest (L' := y.1) (F' := y.2) h2

/-- The kind's block leaves the ledger but for the marks. -/
theorem commitOwn_forkRest {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {x y : Owing (L3.St (DState Unit))} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    forkRest y.held.F = forkRest x.held.F := by
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_rest h1
  · cases h

/-- The kind's block leaves the state of the calls but for the four. -/
theorem commitOwn_checkRest (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    checkRest s'.held.L.check = checkRest s.held.L.check := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', _, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      have hf : f' = _ := joinOwnP_frame _ _ _ _ _ _ a2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3, a3, hf]
        rfl
      · cases h3
  · cases h

theorem commitOwn_linkRest (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    linkRest s'.held.L = linkRest s.held.L := by
  have h1 := commitOwn_linkRec P link moment arrays s s' rs gs h
  have h2 := commitOwn_checkRest P link moment arrays s s' rs gs h
  calc linkRest s'.held.L
      = linkRest { s.held.L with check := s'.held.L.check, moments := s.held.L.moments + 1 } :=
        congrArg linkRest h1
    _ = { s.held.L with check := checkRest s'.held.L.check, moments := 0 } := rfl
    _ = { s.held.L with check := checkRest s.held.L.check, moments := 0 } := by rw [h2]
    _ = linkRest s.held.L := rfl

/-- The rest of a state into which a statement's part, a link's context and a ledger are laid. -/
theorem rest_put (s : S) (w : DState Unit) (L L' : LinkCtx) (F F' : Fork) (hL : s.link? = some L)
    (hF : s.fork? = some F) (hc : w.st.codes = s.st.codes) (h1 : linkRest L' = linkRest L)
    (h2 : forkRest F' = forkRest F) :
    restOf (((laid s w).putLink L').putFork F') = restOf s := by
  cases hh : s.here with
  | lay a =>
    have eL : a.L = L := by simpa [S.link?, hh] using hL
    have eF : a.F = F := by simpa [S.fork?, hh] using hF
    subst eL eF
    simp [restOf, hereRest, S.putFork, S.putLink, laid, hh, hc, h1, h2]
  | att a =>
    have eL : a.L = L := by simpa [S.link?, hh] using hL
    have eF : a.F = F := by simpa [S.fork?, hh] using hF
    subst eL eF
    simp [restOf, hereRest, S.putFork, S.putLink, laid, hh, hc, h1, h2]
  | head a =>
    have ho : a.opened = true := by
      by_contra hn
      simp [S.link?, hh, hn] at hL
    have eL : a.L = L := by simpa [S.link?, hh, ho] using hL
    have eF : a.F = F := by simpa [S.fork?, hh, ho] using hF
    subst eL eF
    simp [restOf, hereRest, S.putFork, S.putLink, laid, hh, ho, hc, h1, h2]
  | between => simp [S.link?, hh] at hL
  | fin a => simp [S.link?, hh] at hL
  | mem a => simp [S.link?, hh] at hL

/-- **A YES OF A LATER MOMENT's SENDING WRITES NOTHING ELSE.** -/
theorem commitAtS_alike (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    RestAlike s s' := by
  have hc : s'.st.codes = s.st.codes := (commitAtS_smpStay P link moment arrays s rs gs s' h).1
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL hF _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    rw [(putFork_st _ _).1, (putLink_st _ _).1] at hc
    exact (rest_put s y.held.w L y.held.L F y.held.F hL hF hc
      (commitOwn_linkRest P link moment arrays _ y rs gs hy) (commitOwn_forkRest hy)).symm
  · cases h

/-- **THE ROW "RS" AT A LINK's DIGITS' PLACE**: where segment m's readers are a link's, and each
pair that the item names stays: the equation that formsQA_back asks, over a yes of the sending. -/
theorem readers_eq_commit (D : PubData) (m k : Nat) (r : String) (H : LinkHoles)
    (l : Link S Claim) (hD : D.Rd m = readersOfLink H l)
    (hp : ∀ p ∈ D.runs m k r, PairStays H l p) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 s := by
  intro p hpm
  rw [hD]
  exact readersOfLink_alike H l p (hp p hpm) (commitAtS_alike P link moment arrays s s' rs gs h)

theorem readersStay_commit (D : PubData) (m k : Nat) (r : String) (H : LinkHoles)
    (l : Link S Claim) (hD : D.Rd m = readersOfLink H l)
    (hp : ∀ p ∈ D.runs m k r, PairStays H l p) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ReadersStay D m k r s s' :=
  readersStay_of_eq D m k r s s'
    (readers_eq_commit D m k r H l hD hp P link moment arrays s s' rs gs h)

/-! ## Members, by the form of the run -/

/-- A run that reads the state, lays claims and leaves the state. -/
theorem respects_readRun (read : S → Except String (List Claim))
    (h : ∀ s s', RestAlike s s' → read s' = read s) : Respects (readRun read) :=
  respects_read read h

/-- K3's "guests" where no guest is handed. -/
theorem respects_guestsNone : Respects guestsNone := respects_readRun _ fun _ _ _ => rfl

theorem paid_rest {F F' : Fork} (h : forkRest F = forkRest F') (i : Nat) :
    forkRest (F.paid i) = forkRest (F'.paid i) := by
  have e : ∀ G : Fork, forkRest (G.paid i) = (forkRest G).paid i := fun _ => rfl
  rw [e, e, h]

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

/-! ## The row's end -/

/-- Part 5's equation over a yes of a link's digits' block. -/
theorem readers_eq_laterAt (D : PubData) (m k : Nat) (r : String) (H : LinkHoles)
    (l : Link S Claim) (hD : D.Rd m = readersOfLink H l)
    (hp : ∀ p ∈ D.runs m k r, PairStays H l p) (q : Params.First) (gp : GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (laterAt q gp link piece moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∀ p ∈ D.runs m k r, (D.Rd m).forms p.1 p.2 s' = (D.Rd m).forms p.1 p.2 s :=
  readers_eq_commit D m k r H l hD hp _ _ _ _ s s' rs gs h

/-- **formsIn m k r OVER A YES OF A LINK's DIGITS' BLOCK**: what is left: that segment m's readers
are a link's; PairStays at each pair that the item names; the promise's clause on the book; the test
on the plan's seats. -/
theorem pub_formsIn_digits {Pp : Type} (D : PubData) (base : Pub → Pp × S → Bool) (m k : Nat)
    (r : String) (H : LinkHoles) (l : Link S Claim) (hD : D.Rd m = readersOfLink H l)
    (hp : ∀ p ∈ D.runs m k r, PairStays H l p) (q : Params.First) (gp : GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) (x x' : Pp × S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : (laterAt q gp link piece moment arrays : Block S Cl).decide x.2 rs gs = .ok x'.2)
    (t nT : Nat) (ht : t < 3) (hb : x.2.book.place.size = x.2.st.oracles.size)
    (hT : x.2.book.trees.size = nT)
    (hs : First.sameMembers ((List.range (parLater q gp link piece moment).sent.size).map fun i =>
      (nT + (layOf (parLater q gp link piece moment)).tree.getD i 0,
        (layOf (parLater q gp link piece moment)).part.getD i 0)) (D.N.sent m t) = true)
    (h0 : pubAll D base (.formsIn m k r) x = true) : pubAll D base (.formsIn m k r) x' = true :=
  pub_formsIn_later_plan (laterSend_laterAt q gp link piece moment arrays) D base x x' rs gs h2 h
    m k r (readersStay_of_eq D m k r x.2 x'.2
      (readers_eq_laterAt D m k r H l hD hp q gp link piece moment arrays x.2 x'.2 rs gs h))
    t nT ht hb hT hs h0

end VerifiableInference.Desc.K1
