-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/PromKeyD.lean: THE PROMISE
THAT RIDES BESIDE THE LINKS' ROWS, WRITTEN OUT: Promise (JoinKeyD.lean) is met by a promise that
speaks of the two messages' ledgers of mask entries alone, and the lists of entries that each lookup
is handed are computed from the two ledgers as they stand in front of the first link.

What a ledger hands out hangs on the ledger alone (stepLedger, takesOf, OnBytes/G4/Seat.lean: the
text of takeMaskP without its tests). So, from the two ledgers lo and lk in front of the first link
and the numbers of entries that each lookup takes (cntO, cntK), the ledgers behind i lookups
(ledBehind) and the entries handed to lookup i (handed) are plain functions.

Main names:
  ledAt: a message's ledger.
  takeMaskP_led, takeMasksInto_led, takeMasksP_led: where the description's takes return, they
    return that; the message's ledger is the ledger behind; every other message's ledger stays.
  cntO, cntK, ledBehind, handed: see above.
  Kept Ex: a clause Ex on the record that the link's blocks keep: blind to the three fields that
    they overwrite; kept by the ledgers' handing out; kept by the layer's two writings (handed the
    layer's two equations and that what was heard has a key for each part). kept_true.
    Ex is ONE clause for all i: it stands in PromL at every border, so it is to be worded of the
    lists as they stand.
  takeMasksP_only: the ledgers' handing out turns the messages' ledgers alone.
  PromL i: the index-mask message has the number idxN; the two ledgers are the ledgers behind i
    lookups; the statement has the tables for each of the n lookups (Fits); and Ex, a letter.
  fits_same: Fits reads the tables' sizes alone.
  promise_ledgers: PROMISE IS MET BY PromL, where the two messages are different messages and Ex is
    kept.
  promL_zero: PromL 0 from four plain facts on the record in front of the first link, and Ex there.

Limits. That the record behind the sending of the second message has these facts is not shown here.
Nothing says that the takes return. Ex is a letter: room for what another block's law wants to find
at the border behind the last link.

-/
import Johnson.RunOne.Law.JoinKeyD
import OnBytes.G4.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.PromKeyD
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.G4 (stepLedger takesOf)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState LookupRecord Claim)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.JoinKeyD

/-- The ledger of mask entries of message o. -/
def ledAt (S : Statement) (o : ℕ) : Option Ledger := (S.oracles[o]?).bind (·.ledger)

theorem takeMaskP_led {T : Type} {d d' : _root_.Desc.Plain.DState T} {o n : ℕ} {l : Ledger}
    (h : takeMaskP d o = some (n, d')) (hl : ledAt d.st o = some l) :
    n = (stepLedger l).1 ∧ ledAt d'.st o = some (stepLedger l).2 ∧
      ∀ o', o' ≠ o → ledAt d'.st o' = ledAt d.st o' := by
  have hl' : (d.st.oracles[o]?).bind (·.ledger) = some l := hl
  unfold takeMaskP at h
  split at h
  · rw [hl'] at h
    cases h
    refine ⟨rfl, ?_, fun o' ho => ?_⟩
    · unfold ledAt
      simp only [Array.getElem?_modify]
      cases hx : d.st.oracles[o]? with
      | none => simp [hx] at hl'
      | some x => simp [stepLedger]
    · unfold ledAt
      simp only [Array.getElem?_modify]
      simp [Ne.symm ho]
  · cases h

theorem takeMasksInto_led {T : Type} (o : ℕ) : ∀ (c : ℕ) (d d' : _root_.Desc.Plain.DState T)
    (acc : Array ℕ) (r : List ℕ) (l : Ledger), takeMasksInto o c d acc = some (r, d') →
    ledAt d.st o = some l →
    r = acc.toList ++ (takesOf l c).1 ∧ ledAt d'.st o = some (takesOf l c).2 ∧
      ∀ o', o' ≠ o → ledAt d'.st o' = ledAt d.st o'
  | 0, d, d', acc, r, l, h, hl => by
    cases h
    exact ⟨(List.append_nil _).symm, hl, fun _ _ => rfl⟩
  | c + 1, d, d', acc, r, l, h, hl => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h
      obtain ⟨a1, a2, a3⟩ := takeMaskP_led (n := x.1) (d' := x.2) h1 hl
      obtain ⟨b1, b2, b3⟩ := takeMasksInto_led o c x.2 d' _ r _ h a2
      refine ⟨?_, b2, fun o' ho => (b3 o' ho).trans (a3 o' ho)⟩
      rw [b1, a1]
      simp [takesOf]

/-- **Where the description's take of c entries returns**, it returns what the ledger hands out; the
message's ledger is the ledger behind; every other message's ledger stays. -/
theorem takeMasksP_led {T : Type} {d : _root_.Desc.Plain.DState T} {o c : ℕ}
    {x : List ℕ × _root_.Desc.Plain.DState T} {l : Ledger} (h : takeMasksP d o c = some x)
    (hl : ledAt d.st o = some l) :
    x.1 = (takesOf l c).1 ∧ ledAt x.2.st o = some (takesOf l c).2 ∧
      ∀ o', o' ≠ o → ledAt x.2.st o' = ledAt d.st o' := by
  obtain ⟨a, b, e⟩ := takeMasksInto_led o c d x.2 #[] x.1 l h hl
  exact ⟨by simpa using a, b, e⟩

theorem takeMaskP_only {T : Type} {d d' : _root_.Desc.Plain.DState T} {o n : ℕ}
    (h : takeMaskP d o = some (n, d')) :
    d' = { d with st := { d.st with oracles := d'.st.oracles } } := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      cases h
      rfl
  · cases h

theorem takeMasksInto_only {T : Type} (o : ℕ) : ∀ (c : ℕ) (d d' : _root_.Desc.Plain.DState T)
    (acc : Array ℕ) (r : List ℕ), takeMasksInto o c d acc = some (r, d') →
    d' = { d with st := { d.st with oracles := d'.st.oracles } }
  | 0, d, d', acc, r, h => by
    cases h
    rfl
  | c + 1, d, d', acc, r, h => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h
      have a := takeMaskP_only (n := x.1) (d' := x.2) h1
      have b := takeMasksInto_only o c x.2 d' _ r h
      rw [b, a]

/-- **The ledgers' handing out turns the messages' records alone**, and of these the ledgers alone
(takeMasksInto_bare, RideKeyD.lean). -/
theorem takeMasksP_only {T : Type} {d : _root_.Desc.Plain.DState T} {o c : ℕ}
    {x : List ℕ × _root_.Desc.Plain.DState T} (h : takeMasksP d o c = some x) :
    x.2 = { d with st := { d.st with oracles := x.2.st.oracles } } ∧
      x.2.st.oracles.map bareO = d.st.oracles.map bareO :=
  ⟨takeMasksInto_only o c d x.2 #[] x.1 h, (takeMasksInto_bare o c d x.2 #[] x.1 h).2⟩

/-- The ledger behind the first i lookups' takes; cnt k: how many entries lookup k takes. -/
def ledBehind (cnt : ℕ → ℕ) (l : Ledger) : ℕ → Ledger
  | 0 => l
  | i + 1 => (takesOf (ledBehind cnt l i) (cnt i)).2

/-- The entries handed to lookup i. -/
def handed (cnt : ℕ → ℕ) (l : Ledger) (i : ℕ) : List ℕ := (takesOf (ledBehind cnt l i) (cnt i)).1

variable (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (idxN n : ℕ) (lo lk : Ledger)

/-- How many entries of the own message lookup i takes. -/
def cntO (i : ℕ) : ℕ :=
  (faceOfLkp (Wf.lookupOf id m (L i))).slots -
    2 * (faceOfLkp (Wf.lookupOf id m (L i))).parts.length

/-- How many entries of the index-mask message lookup i takes. -/
def cntK (i : ℕ) : ℕ := 2 * (faceOfLkp (Wf.lookupOf id m (L i))).parts.length

/-- **A clause on the record that the link's blocks keep.** -/
structure Kept (Ex : FirstState → Prop) : Prop where
  blind : ∀ (s : FirstState) (f : Option OnBytes.Model.Fork) (h : Option HeardG) (hm : Array Slot),
      Ex s →
    Ex { s with base := { s.base with fork := f, heard := h, home := hm } }
  hand : ∀ (s : FirstState) (o c : ℕ) (x : List ℕ × VerifiableInference.Desc.Key.PlainState),
    takeMasksP s.d o c = some x → Ex s → Ex { s with d := x.2 }
  lays : ∀ (i : ℕ) (s : FirstState) (F : OnBytes.Model.Fork) (g : HeardG) (cls : List Claim)
    (rows : List Row) (keys : List Lkp.Keys), Ex s → s.base.rows.length = i →
    s.base.keys.length = i →
    VerifiableInference.Desc.Key.rowsInOrder (Wf.planesAt one.ranges one.codes i)
      (VerifiableInference.Desc.Key.layerOrder (cls.filter fun c => c.isLeft).length) F s.base.home
          cls =
        some rows →
    keyClaims (Wf.lookupOf id m (L i)) F s.base.home g = some keys →
    g.keys.length = (L i).parts.length →
    Ex { s with base := { s.base with
      rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } }

/-- The clause that says nothing is kept. -/
theorem kept_true : Kept one id m L fun _ => True :=
  ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    trivial⟩

/-- **The promise, written out.** lo, lk: the two ledgers in front of the first link. Ex: what else
is promised. -/
def PromL (Ex : FirstState → Prop) (i : ℕ) (s : FirstState) : Prop :=
  s.idx = idxN ∧ ledAt s.d.st one.ranges.messageId = some (ledBehind (cntO id m L) lo i) ∧
    ledAt s.d.st idxN = some (ledBehind (cntK id m L) lk i) ∧
    (∀ k < n, Fits one id m (L k) (handed (cntO id m L) lo k) (handed (cntK id m L) lk k) idxN
      s.d.st) ∧ Ex s

variable {one id m L idxN n lo lk}

/-- Fits reads the tables' sizes alone. -/
theorem fits_same {l : WfLookup} {oL kL : List ℕ} {S S' : Statement} (h : SameTables S S')
    (hf : Fits one id m l oL kL idxN S) : Fits one id m l oL kL idxN S' := by
  refine ⟨⟨?_, ?_⟩, fun t ht => ?_⟩
  · rw [h.1]
    exact hf.1.there
  · rw [h.2]
    exact hf.1.size
  · rw [h.1, h.2]
    exact hf.2 t ht

/-- **Promise is met by the promise written out**, where the own message and the index-mask message
are different messages. -/
theorem promise_ledgers {Ex : FirstState → Prop} (hne : one.ranges.messageId ≠ idxN)
    (hE : Kept one id m L Ex) :
    Promise one id m L (handed (cntO id m L) lo) (handed (cntK id m L) lk) idxN n
      (PromL one id m L idxN n lo lk Ex) where
  blind := fun _ s f h hm hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hE.blind s f h hm hp.2.2.2.2⟩
  lays := fun i s F g cls rows keys hp h1 h2 h3 h4 h5 =>
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hE.lays i s F g cls rows keys hp.2.2.2.2 h1 h2 h3 h4 h5⟩
  gives := fun i s hi h => by
    refine ⟨⟨h.1, fun o k h1 h2 => ?_⟩, h.2.2.2.1 i hi⟩
    obtain ⟨a1, -, a3⟩ := takeMasksP_led h1 h.2.1
    have hk : ledAt o.2.st s.idx = some (ledBehind (cntK id m L) lk i) := by
      rw [h.1, a3 idxN (Ne.symm hne)]
      exact h.2.2.1
    obtain ⟨b1, -, -⟩ := takeMasksP_led h2 hk
    exact ⟨a1, b1⟩
  step := fun i s o k h h1 h2 => by
    obtain ⟨-, a2, a3⟩ := takeMasksP_led h1 h.2.1
    have hk : ledAt o.2.st s.idx = some (ledBehind (cntK id m L) lk i) := by
      rw [h.1, a3 idxN (Ne.symm hne)]
      exact h.2.2.1
    obtain ⟨-, b2, b3⟩ := takeMasksP_led h2 hk
    refine ⟨h.1, ?_, ?_, fun k' hk' =>
      fits_same ((takeMasksP_same h1).trans (takeMasksP_same h2)) (h.2.2.2.1 k' hk'),
      hE.hand { s with d := o.2 } s.idx _ k h2 (hE.hand s _ _ o h1 h.2.2.2.2)⟩
    · show ledAt k.2.st one.ranges.messageId = _
      rw [b3 _ (by rw [h.1]; exact hne), a2]
      rfl
    · rw [h.1] at b2
      exact b2

/-- **The promise in front of the first link, from four plain facts, and Ex there.** -/
theorem promL_zero {Ex : FirstState → Prop} {s : FirstState} (h1 : s.idx = idxN)
    (h2 : ledAt s.d.st one.ranges.messageId = some lo) (h3 : ledAt s.d.st idxN = some lk)
    (h4 : ∀ k < n, Fits one id m (L k) (handed (cntO id m L) lo k) (handed (cntK id m L) lk k) idxN
      s.d.st) (h5 : Ex s) : PromL one id m L idxN n lo lk Ex 0 s :=
  ⟨h1, h2, h3, h4, h5⟩

end Johnson.RunOne.Law.PromKeyD

#print axioms Johnson.RunOne.Law.PromKeyD.takeMasksP_led
#print axioms Johnson.RunOne.Law.PromKeyD.takeMasksP_only
#print axioms Johnson.RunOne.Law.PromKeyD.kept_true
#print axioms Johnson.RunOne.Law.PromKeyD.fits_same
#print axioms Johnson.RunOne.Law.PromKeyD.promise_ledgers
#print axioms Johnson.RunOne.Law.PromKeyD.promL_zero
