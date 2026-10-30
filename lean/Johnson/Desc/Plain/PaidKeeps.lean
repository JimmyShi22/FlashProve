-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/PaidKeeps.lean: the joining of a row in the plain form. A tool; no
protocol occurs here.

What it is for. A description's pieces (`piecesAt`, Johnson/Desc/Sound/PaidAtDesc.lean) hold the
blocks `held b`: the test "every word is below the prime" in front (`below`), lifted to the pair
(what was handed to the chain, the chain's own record). A kind's law is proved of the kind's own
block, at the chain's own record. This file carries such a law, block by block along the maker's
row (`cutRow`, Johnson/Desc/Sound/Tiles.lean), to the row that `piecesAt` holds.

Why "for every t". A promise and a relation of a file's table read the pair. A block turns the
second part alone, and the lifted block hands the first part on, for certain. So the law is asked
at the second part, with the first part t as a parameter, ONE t ON BOTH SIDES of the relation. A
promise or a claim on what was handed then needs no tool of its own.

  `Rest.down`: of what a piece holds beside its block at the pair: the errors; an idle extractor.
  `held_decide`: the held block's yes: what was handed is handed on, and the block itself said yes.
  `leads_heldU`: ONE PIECE, at a general relation Q: (for every t, `Leads` of the piece of
    `below b`) gives `Leads` of the piece of `held b`, at the same errors. General in the rest x.
  `leads_held`: the same from the piece of the bare block b (more is asked: all transcripts).
  `keeps_heldU`, `keeps_held`: the case `Keeps`.
  `eachLeadsOfCutU`, `eachKeepsOfCutU`, `eachKeepsOfCut`: THE ROW, by induction over `cutRow`.
  `paidLeadsU`, `paidKeepsU`, `paidKeeps`: the three chains, at `atDesc F (piecesAt …)`.

WHICH TOP IT SERVES. The plain tops of Johnson/Desc/Plain/ ask `EachLeads` (the key file: thrice,
KeyAtDesc.lean; the proof file: its first and its third chain, AtDesc.lean) and, at the proof file's
shared chain, a KEYED form (`EachLeadsK`, `EachLeadsBN`). None asks `EachKeeps`. So:
`paidLeadsU` feeds a premise `EachLeads` as it stands, at any relation Q, the map form
(Q k a b := on (k + 1) b ∧ ∀ w, R (k + 1) b w → R k a (E a b w)) among them; `paidKeeps…` reaches
such a premise through `EachKeeps.leads`, where Q is chosen as "the promise behind, and true behind
→ true in front". THE KEYED FORM IS NOT SERVED: of the proof file's three chains the shared one is
left out.

At the key file all three can be served.

Limits. A rule: as empty as its premise; no member is shown. `on := False`, or errors that are a
round's number of challenges, make premise and conclusion true for nothing (Leads.lean's limits).
Nothing on soundness.

-/
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Plain.LiftBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {P S Cl W : Type} {C : CK} {F : Frame}

/-- The errors; an idle extractor. -/
def _root_.VerifiableInference.Desc.Sound.Rest.down {ds : List RDT}
    (x : Rest C F (P × S) W ds) : Rest C F S W ds := ⟨fun _ _ w => w, x.err⟩

/-- A condition on the pair's statements, read at the second part, the first being t. -/
abbrev atT (t : P) (f : (P × S) × F.E.Str → Prop) : S × F.E.Str → Prop :=
  fun a => f ((t, a.1), a.2)

/-- A relation likewise: one t on both sides. -/
abbrev atT₂ (t : P) (Q : (P × S) × F.E.Str → (P × S) × F.E.Str → Prop) :
    S × F.E.Str → S × F.E.Str → Prop :=
  fun a c => Q ((t, a.1), a.2) ((t, c.1), c.2)

/-- A maker's row as one list. -/
abbrev rowL {T : Type} (x : T × List T) : List T := x.1 :: x.2

/-- **What the held block's yes says.** -/
theorem held_decide (b : Block S Cl) (a : P × S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (a' : P × S)
    (h : (held b : Block (P × S) Cl).decide a rs gs = .ok a') :
    a'.1 = a.1 ∧ b.decide a.2 rs gs = .ok a'.2 := by
  have h' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide a.2 rs gs
      else .error "a word is not below the prime").map fun s => (a.1, s)) = .ok a' := h
  split at h'
  · cases hb : b.decide a.2 rs gs with
    | error e => rw [hb] at h'; cases h'
    | ok s' =>
      rw [hb] at h'
      have e : (a.1, s') = a' := Except.ok.inj h'
      rw [← e]
      exact ⟨rfl, rfl⟩
  · cases h'

/-- **One piece, at a general relation**: from the law of the piece of `below b`. -/
theorem leads_heldU (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (x : Rest C F (P × S) W ds) (on : (P × S) × F.E.Str → Prop)
    (Q : (P × S) × F.E.Str → (P × S) × F.E.Str → Prop)
    (h : ∀ t : P, (pieceOf (below b) base ds back x.down).ior.red.Leads (atT t on) (atT₂ t Q)
      (pieceOf (below b) base ds back x.down).err) :
    (pieceOf (held b) base ds back x).ior.red.Leads on Q (pieceOf (held b) base ds back x).err := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h a.1.1 (a.1.2, a.2) ha)
  intro τ hτ b' hb'
  have e := liftOut (P × S) S Cl W C F Prod.snd (fun t s => (t.1, s))
    (pieceOf (below b) base ds back x.down) (fun _ _ => rfl) (fun _ _ _ => rfl) a τ
  have hb'' : ((pieceOf (below b) base ds back x.down).lift Prod.snd
      fun t s => (t.1, s)).ior.red.out a τ = some b' := hb'
  rw [e] at hb''
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb''
  exact hτ b₀ hb₀

/-- The same from the law of the piece of the bare block: it is asked at all transcripts. -/
theorem leads_held (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (hb : viewWordsBelowPrime ⟨back, []⟩ = true) (x : Rest C F (P × S) W ds)
    (on : (P × S) × F.E.Str → Prop) (Q : (P × S) × F.E.Str → (P × S) × F.E.Str → Prop)
    (h : ∀ t : P, (pieceOf b base ds back x.down).ior.red.Leads (atT t on) (atT₂ t Q)
      (pieceOf b base ds back x.down).err) :
    (pieceOf (held b) base ds back x).ior.red.Leads on Q (pieceOf (held b) base ds back x).err :=
  leads_heldU b base ds back x on Q fun t =>
    leads_under (pieceOf b base ds back x.down) hb _ _ (h t)

/-- The case "promise, and true behind → true in front", from the piece of `below b`. -/
theorem keeps_heldU (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (x : Rest C F (P × S) W ds) (on on' L L' : (P × S) × F.E.Str → Prop)
    (h : ∀ t : P, (pieceOf (below b) base ds back x.down).ior.red.Keeps (atT t on) (atT t on')
      (atT t L) (atT t L') (pieceOf (below b) base ds back x.down).err) :
    (pieceOf (held b) base ds back x).ior.red.Keeps on on' L L'
      (pieceOf (held b) base ds back x).err :=
  leads_heldU b base ds back x on (fun a c => on' c ∧ (L' c → L a)) h

/-- The same from the piece of the bare block. -/
theorem keeps_held (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (hb : viewWordsBelowPrime ⟨back, []⟩ = true) (x : Rest C F (P × S) W ds)
    (on on' L L' : (P × S) × F.E.Str → Prop)
    (h : ∀ t : P, (pieceOf b base ds back x.down).ior.red.Keeps (atT t on) (atT t on')
      (atT t L) (atT t L') (pieceOf b base ds back x.down).err) :
    (pieceOf (held b) base ds back x).ior.red.Keeps on on' L L'
      (pieceOf (held b) base ds back x).err :=
  leads_held b base ds back hb x on (fun a c => on' c ∧ (L' c → L a)) h

/-- No round and no opened leaf: the words' test says yes. -/
theorem okView_nil : viewWordsBelowPrime ⟨[], []⟩ = true := rfl

/-- The sealing round holds no word. -/
theorem okView_seal : viewWordsBelowPrime ⟨[sealRound], []⟩ = true := rfl

section Row
variable (rest : (i : ℕ) → (ds : List RDT) → Rest C F (P × S) W ds) (back : List Fmt.RoundView)

/-- **The row, at general relations.** hand: the hand-over clause of `EachLeads`, at the pair: it
speaks of on and Q alone. -/
theorem eachLeadsOfCutU (on : ℕ → (P × S) × F.E.Str → Prop)
    (Q : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → Prop)
    (hand : ∀ i a b, on i a → Q i a b → on (i + 1) b) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT) (k : ℕ),
      (∀ t : P, EachLeads (fun k => atT t (on k)) (fun k => atT₂ t (Q k)) k
        (rowL (cutRow (fun i ds => (rest i ds).down) back i base ds (below b) (l.map below)))) →
      EachLeads on Q k (rowL (cutRow rest back i base ds (held b) (l.map held))) := by
  intro l
  induction l with
  | nil =>
    intro b i base ds k h
    exact ⟨leads_heldU b base ds back (rest i ds) _ _ fun t => (h t).1, hand k, trivial⟩
  | cons b' l ih =>
    intro b i base ds k h
    exact ⟨leads_heldU b base (ds.take b.rounds.length) [] (rest i (ds.take b.rounds.length)) _ _
        fun t => (h t).1, hand k,
      ih b' (i + 1) (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) (k + 1)
        fun t => (h t).2.2⟩

/-- **The row, for promises and truth**, from the laws of the pieces of `below b`. -/
theorem eachKeepsOfCutU (on L : ℕ → (P × S) × F.E.Str → Prop) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT) (k : ℕ),
      (∀ t : P, EachKeeps (fun k => atT t (on k)) (fun k => atT t (L k)) k
        (rowL (cutRow (fun i ds => (rest i ds).down) back i base ds (below b) (l.map below)))) →
      EachKeeps on L k (rowL (cutRow rest back i base ds (held b) (l.map held))) := by
  intro l
  induction l with
  | nil =>
    intro b i base ds k h
    exact ⟨keeps_heldU b base ds back (rest i ds) _ _ _ _ fun t => (h t).1, trivial⟩
  | cons b' l ih =>
    intro b i base ds k h
    exact ⟨keeps_heldU b base (ds.take b.rounds.length) [] (rest i (ds.take b.rounds.length))
        _ _ _ _ fun t => (h t).1,
      ih b' (i + 1) (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) (k + 1)
        fun t => (h t).2⟩

/-- The same from the laws of the pieces of the bare blocks. -/
theorem eachKeepsOfCut (hb : viewWordsBelowPrime ⟨back, []⟩ = true)
    (on L : ℕ → (P × S) × F.E.Str → Prop) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ) (ds : List RDT) (k : ℕ),
      (∀ t : P, EachKeeps (fun k => atT t (on k)) (fun k => atT t (L k)) k
        (rowL (cutRow (fun i ds => (rest i ds).down) back i base ds b l))) →
      EachKeeps on L k (rowL (cutRow rest back i base ds (held b) (l.map held))) := by
  intro l
  induction l with
  | nil =>
    intro b i base ds k h
    exact ⟨keeps_held b base ds back hb (rest i ds) _ _ _ _ fun t => (h t).1, trivial⟩
  | cons b' l ih =>
    intro b i base ds k h
    exact ⟨keeps_held b base (ds.take b.rounds.length) [] okView_nil
        (rest i (ds.take b.rounds.length)) _ _ _ _ fun t => (h t).1,
      ih b' (i + 1) (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) (k + 1)
        fun t => (h t).2⟩

end Row

section AtDesc
variable {Xi : Type} (F : FileDescription Xi) (D : WholeD) (C : CK)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (d wEnd : W)

/-- The pieces of which the three forms below speak. -/
abbrev paidT : ThreeAt C D (allOf D) F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W :=
  atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)

/-- **At the pieces of a description, general relations.** -/
theorem paidLeadsU
    (on₁ : ℕ → (F.XiPub × F.S₁) × (EAll D (allOf D)).Str → Prop)
    (Q₁ : ℕ → (F.XiPub × F.S₁) × (EAll D (allOf D)).Str →
      (F.XiPub × F.S₁) × (EAll D (allOf D)).Str → Prop)
    (on₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D (allOf D)).Str → Prop)
    (Q₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D (allOf D)).Str →
      ((F.XiPub × F.S₁) × F.S₂) × (EAll D (allOf D)).Str → Prop)
    (on₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll D (allOf D)).Str → Prop)
    (Q₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll D (allOf D)).Str →
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll D (allOf D)).Str → Prop)
    (hand₁ : ∀ i a b, on₁ i a → Q₁ i a b → on₁ (i + 1) b)
    (hand₂ : ∀ i a b, on₂ i a → Q₂ i a b → on₂ (i + 1) b)
    (hand₃ : ∀ i a b, on₃ i a → Q₃ i a b → on₃ (i + 1) b)
    (h₁ : ∀ t, EachLeads (fun k => atT t (on₁ k)) (fun k => atT₂ t (Q₁ k)) 0
      (rowL (cutRow (fun i ds => (rest₁ i ds).down) [sealRound] 0 0 D.ds₁ (below b₁)
        (l₁.map below))))
    (h₂ : ∀ t, EachLeads (fun k => atT t (on₂ k)) (fun k => atT₂ t (Q₂ k)) 0
      (rowL (cutRow (fun i ds => (rest₂ i ds).down) [] 0 D.t₁ D.ds₂ (below b₂) (l₂.map below))))
    (h₃ : ∀ t, EachLeads (fun k => atT t (on₃ k)) (fun k => atT₂ t (Q₃ k)) 0
      (rowL (cutRow (fun i ds => (rest₃ i ds).down) [] 0 (D.t₁ + D.t₂) D.ds₃ (below b₃)
        (l₃.map below)))) :
    EachLeads on₁ Q₁ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁) ∧
    EachLeads on₂ Q₂ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂) ∧
    EachLeads on₃ Q₃ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₃ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₃) :=
  ⟨eachLeadsOfCutU rest₁ [sealRound] on₁ Q₁ hand₁ l₁ b₁ 0 0 D.ds₁ 0 h₁,
    eachLeadsOfCutU rest₂ [] on₂ Q₂ hand₂ l₂ b₂ 0 D.t₁ D.ds₂ 0 h₂,
    eachLeadsOfCutU rest₃ [] on₃ Q₃ hand₃ l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃ 0 h₃⟩

variable (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll D (allOf D)).Str → Prop)
  (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll D (allOf D)).Str → Prop)
  (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll D (allOf D)).Str → Prop)

/-- **At the pieces of a description, promises and truth**: from the laws of `below b`. -/
theorem paidKeepsU
    (h₁ : ∀ t, EachKeeps (fun k => atT t (on₁ k)) (fun k => atT t (L₁ k)) 0
      (rowL (cutRow (fun i ds => (rest₁ i ds).down) [sealRound] 0 0 D.ds₁ (below b₁)
        (l₁.map below))))
    (h₂ : ∀ t, EachKeeps (fun k => atT t (on₂ k)) (fun k => atT t (L₂ k)) 0
      (rowL (cutRow (fun i ds => (rest₂ i ds).down) [] 0 D.t₁ D.ds₂ (below b₂) (l₂.map below))))
    (h₃ : ∀ t, EachKeeps (fun k => atT t (on₃ k)) (fun k => atT t (L₃ k)) 0
      (rowL (cutRow (fun i ds => (rest₃ i ds).down) [] 0 (D.t₁ + D.t₂) D.ds₃ (below b₃)
        (l₃.map below)))) :
    EachKeeps on₁ L₁ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁) ∧
    EachKeeps on₂ L₂ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂) ∧
    EachKeeps on₃ L₃ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₃ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₃) :=
  ⟨eachKeepsOfCutU rest₁ [sealRound] on₁ L₁ l₁ b₁ 0 0 D.ds₁ 0 h₁,
    eachKeepsOfCutU rest₂ [] on₂ L₂ l₂ b₂ 0 D.t₁ D.ds₂ 0 h₂,
    eachKeepsOfCutU rest₃ [] on₃ L₃ l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃ 0 h₃⟩

/-- The same from the laws of the bare blocks. -/
theorem paidKeeps
    (h₁ : ∀ t, EachKeeps (fun k => atT t (on₁ k)) (fun k => atT t (L₁ k)) 0
      (rowL (cutRow (fun i ds => (rest₁ i ds).down) [sealRound] 0 0 D.ds₁ b₁ l₁)))
    (h₂ : ∀ t, EachKeeps (fun k => atT t (on₂ k)) (fun k => atT t (L₂ k)) 0
      (rowL (cutRow (fun i ds => (rest₂ i ds).down) [] 0 D.t₁ D.ds₂ b₂ l₂)))
    (h₃ : ∀ t, EachKeeps (fun k => atT t (on₃ k)) (fun k => atT t (L₃ k)) 0
      (rowL (cutRow (fun i ds => (rest₃ i ds).down) [] 0 (D.t₁ + D.t₂) D.ds₃ b₃ l₃))) :
    EachKeeps on₁ L₁ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁) ∧
    EachKeeps on₂ L₂ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂) ∧
    EachKeeps on₃ L₃ 0 ((paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₃ ::
      (paidT F D C b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₃) :=
  ⟨eachKeepsOfCut rest₁ [sealRound] okView_seal on₁ L₁ l₁ b₁ 0 0 D.ds₁ 0 h₁,
    eachKeepsOfCut rest₂ [] okView_nil on₂ L₂ l₂ b₂ 0 D.t₁ D.ds₂ 0 h₂,
    eachKeepsOfCut rest₃ [] okView_nil on₃ L₃ l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃ 0 h₃⟩

end AtDesc

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.held_decide
#print axioms VerifiableInference.Desc.Plain.leads_heldU
#print axioms VerifiableInference.Desc.Plain.leads_held
#print axioms VerifiableInference.Desc.Plain.keeps_heldU
#print axioms VerifiableInference.Desc.Plain.keeps_held
#print axioms VerifiableInference.Desc.Plain.eachLeadsOfCutU
#print axioms VerifiableInference.Desc.Plain.eachKeepsOfCutU
#print axioms VerifiableInference.Desc.Plain.eachKeepsOfCut
#print axioms VerifiableInference.Desc.Plain.paidLeadsU
#print axioms VerifiableInference.Desc.Plain.paidKeepsU
#print axioms VerifiableInference.Desc.Plain.paidKeeps
