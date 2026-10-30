-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTie.lean: "WHAT RIDES" AT THE THREE QUIET SUB-PROTOCOLS OF A
SEGMENT's END (the batching; the frame's sub-protocol behind it; "the segment is shut"), AT THE
COMPOSED MEANING (`mgAll 𝔇 Mg`): THE FIFTH TIE: the field `t5` of `TieRestR`
(LinkTiedR.lean), to the letter: every item that is open in front of the sub-protocol, and that it
neither closes nor reads, holds in front, at the same witness, where it holds behind.

Which items ride there (by Lean's evaluator at the written full list; no theorem): the committed
table's pin; the pile; the index masks' pin; the four parts idn, lookCalls, rider, small of LATER
segments' relations and of the output head's; the segment's own rows (three samples, carried,
position); at the shutting "carry" and the kept pins; AND, at the layers' and the head's segments,
"wo": the one rider that reads a part of a segment of its own.

What is said.
  `Quiet9 s t`: the two states are one but for what the three sub-protocols write (`rest9`,
    Rest9.lean: the link's context, the ledger of forms, the approximate range proof's state, the
    rows owed).
  `rows_rest9`, `lin_rest9`, `rowAt_rest9`: the rows on the table, the claim of the test on the
    table and the reader of the pending claim on the weights read none of these.
  `sameRead_quiet9`: so `SameRead` (Johnson/Top/H0/Walk/FrameFieldsBack.lean).
  `wo_back_quiet9`: **"wo" goes back over a step with `Quiet9`.**
  `read3_quiet9`: the three premises on the readers (`Read3`, FrameItemsOpen.lean), where 𝔇's three
    parameters are the meant terms (`MeantAt`, FrameReadKeptAt.lean).
  `WoOpen`, `holds_back_open9`: `holds_back_open` with "wo" among the items.
  `t5_of_back`: THE FIELD FROM "every rider goes back": at any piece whose extractor lays nothing.
  `BlockYes b s t`, `yes_of_out`: an accepting step of a sub-protocol; a piece's yes is one.
  `t5_quiet`: **THE FIELD AT A PIECE WHOSE SUB-PROTOCOL's ACCEPTING STEP GIVES `Quiet9`.** The two
    parameters' payers are handed the step's own relation, not `Quiet9`.
  `quiet9_batch`, `quiet9_behind`, `quiet9_shut`: the three's accepting steps give it
    (`rest_blocks`, `rest_shut`, called): the first two under the two fields hb₁ and stand of
    `LinkShare` (RidesAtMg.lean), written out: that file is not imported.

Limits. Left as premises, each by name: `MeantAt`; `CarryOpen` and `HeadOpen` (FrameItemsOpen.lean:
two parameters, asked only where their item rides); on every rider: it has no part of a segment of
its own or is "wo", it is not the digits' part, its pins' trees lie below the piece's first tree.
The one equation's sub-protocol is not treated: it pushes a row onto a group. No soundness
statement.

-/
import Johnson.Top.H0.Walk.FrameReadKeptAt
import Johnson.Top.H0.Walk.FrameItemsOpen
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Desc.First.Link.Law.Rest9
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Desc.First.Link.Law.LinkTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start)
open VerifiableInference.Desc.JoinAtBlocks
open VerifiableInference.Desc.K13.Law (linAt rwBook_same)
open Johnson.Desc.First.Walk.Tied
open _root_.Run.PQ (CK)

/-- The two states are one but for what the three sub-protocols write. -/
def Quiet9 (s t : S) : Prop := ∃ L₀ F₀ t₀, rest9 L₀ F₀ t₀ t = rest9 L₀ F₀ t₀ s

/-- An accepting step of the sub-protocol b from s to t. -/
def BlockYes {Cl : Type} (b : Block S Cl) (s t : S) : Prop :=
  ∃ ft rs cols k, b.step ft s rs cols = .ok (t, k)

/-- A yes of a piece that holds `below b` is an accepting step of b. -/
theorem yes_of_out {C : CK} {F : Frame} {Cl W : Type} {q : Piece C F S Cl W} {b : Block S Cl}
    (hqb : q.b = below b) {a a' : S × F.E.Str} {τ : Iop.Tr (uLT C q.ds)}
    (hout : q.ior.red.out a τ = some a') : BlockYes b a.1 a'.1 := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hqb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨_, _, _, j, hstep⟩

theorem rows_rest9 (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) : ReadsRest9 L₀ F₀ t₀ S.rows := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

theorem lin_rest9 (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) : ReadsRest9 L₀ F₀ t₀ linAt := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

theorem rowAt_rest9 (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) (lay : WsLay) (n : ℕ)
    (lin : Params.LinShape) :
    ReadsRest9 L₀ F₀ t₀ (Johnson.Desc.First.Walk.Law.rowAt lay n lin) := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

namespace Quiet9
variable {s t : S} (h : Quiet9 s t)
include h

theorem st : t.st = s.st := by
  obtain ⟨L₀, F₀, t₀, e⟩ := h
  exact congrArg (·.st) e

theorem book : t.book = s.book := by
  obtain ⟨L₀, F₀, t₀, e⟩ := h
  exact congrArg (·.book) e

theorem failed : t.failed = s.failed := by
  obtain ⟨L₀, F₀, t₀, e⟩ := h
  exact congrArg (·.failed) e

end Quiet9

/-- **What the eight sentences read of the state is not turned.** -/
theorem sameRead_quiet9 {s t : S} (h : Quiet9 s t) : SameRead s t := by
  have hst := h.st
  have hbk := h.book
  have hfl := h.failed
  obtain ⟨L₀, F₀, t₀, e⟩ := h
  refine ⟨fun k => by rw [← hfl]; exact k, hbk, by rw [hst], by rw [hst], by rw [hst],
    fun i => by rw [hst], fun r hr => ?_, fun l hl => ?_⟩
  · rw [(rows_rest9 L₀ F₀ t₀).alike L₀ F₀ t₀ e]
    exact hr
  · rw [(lin_rest9 L₀ F₀ t₀).alike L₀ F₀ t₀ e]
    exact hl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- **"wo" goes back over a step with `Quiet9`.** -/
theorem wo_back_quiet9 (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Quiet9 s t) (base : ℕ)
    (In : P × S → Strs → Prop) (m : ℕ) :
    GoesBack (StepRel rel base In) (First.FillP1.woAt 𝔇.d1 𝔇.rw13 m) := by
  intro a y b y' w hr h
  obtain ⟨p, s⟩ := a
  obtain ⟨p', t⟩ := b
  obtain ⟨e, hq, -, -⟩ := hr
  obtain rfl : p' = p := e
  have hQ := hrel s t hq
  have hst := hQ.st
  have hbk := hQ.book
  obtain ⟨L₀, F₀, t₀, eq⟩ := hQ
  unfold First.FillP1.woAt at h ⊢
  intro r hrow
  have e2 : 𝔇.rw13 (p', t) w = 𝔇.rw13 (p', s) w :=
    rwBook_same 𝔇.arr 𝔇.mat13 (p', s) (p', t) hbk (by rw [hst]) (fun o => by rw [hst]) w
  have h1 := h r (by
    show Johnson.Desc.First.Walk.Law.rowAt _ _ _ t = some r
    rw [(rowAt_rest9 L₀ F₀ t₀ _ _ _).alike L₀ F₀ t₀ eq]
    exact hrow)
  rw [e2] at h1
  exact h1

/-- The three premises on the readers, at the meant terms. -/
theorem read3_quiet9 {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (hM : MeantAt 𝔇 seats r)
    (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Quiet9 s t) (base : ℕ)
    (In : P × S → Strs → Prop) : Read3 𝔇 (fun j => j < base) (StepRel rel base In) where
  req a y b y' h := by rw [hM.req, hM.req, h.1]
  dec a y b y' h c := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact hM.dec c p' s t
  smp a y b y' h x _ _ := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    rw [hM.smp]
    exact (smpNamed_same 𝔇.cs seats (p', s) (p', t) (hrel s t h.2.1).st x.1 x.2).symm

/-- "wo" goes back at the segments whose item rides. -/
def WoOpen (Op : Item → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop :=
  ∀ m, Op (.wo m) → GoesBack R (First.FillP1.woAt 𝔇.d1 𝔇.rw13 m)

/-- **Every rider goes back, "wo" among them.** -/
theorem holds_back_open9 (N : Numbers) (Op : Item → Prop) (low : ℕ → Prop)
    (R : P × S → Strs → P × S → Strs → Prop) (hR : RelReads low R) (h3 : Read3 𝔇 low R)
    (hc : CarryOpen 𝔇 Op R) (hH : HeadOpen 𝔇 Op R) (hw : WoOpen 𝔇 Op R)
    (hO : ∀ i, Op i → (i.part = none ∨ ∃ m, i = .wo m) ∧ notOwn ownDigits i ∧ lowItem N low i) :
    ∀ i, Op i → GoesBack R (i.holds N (mgAll 𝔇 Mg)) := by
  intro i hi
  rcases (hO i hi).1 with hp | ⟨m, rfl⟩
  · exact holds_back_open 𝔇 Mg N (fun j => Op j ∧ j.part = none) low R hR h3
      (fun m hm => hc m hm.1) (fun p hp' => hH p hp'.1)
      (fun j hj => ⟨hj.2, (hO j hj.1).2.1, (hO j hj.1).2.2⟩) i ⟨hi, hp⟩
  · show GoesBack R ((mgAll 𝔇 Mg).wo m)
    rw [mgAll_wo]
    exact hw m hi

variable {C : CK} {F : Frame}

/-- **THE FIELD FROM "EVERY RIDER GOES BACK"**, at a piece whose extractor lays nothing. -/
theorem t5_of_back (Nm : Numbers) (M : Meaning P WT) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (q : Piece C F S Claim WT)
    (hext : ∀ a τ w, q.ext a τ w = w) (rel : S → S → Prop) (In : P × S → Strs → Prop)
    (hstep : ∀ a τ b, onTR Nm M links pl (fun s : S => (z, s)) Rz k a →
      q.ior.red.out a τ = some b → rel a.1 b.1 ∧ In (z, a.1) (strsOf F a.2))
    (hback : ∀ i, openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i →
      ¬ insQ links pl k i → GoesBack (StepRel rel q.base In) (i.holds Nm M)) :
    ∀ a τ b w i, onTR Nm M links pl (fun s : S => (z, s)) Rz k a → q.ior.red.out a τ = some b →
      onQ Nm M links pl (fun s : S => (z, s)) (k + 1) b →
      relQ Nm M links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ Nm M (fun s : S => (z, s)) i a (q.ext a τ w) := by
  intro a τ b w i ha hout _ hrel ho hn
  rw [hext]
  obtain ⟨h1, h2⟩ := hstep a τ b ha hout
  have hb : meansQ Nm M (fun s : S => (z, s)) i b w := hrel i (Or.inl ⟨ho, hn⟩)
  refine hback i ho hn (z, a.1) (strsOf F a.2) (z, b.1) (strsOf F b.2) w ⟨rfl, h1, ?_, h2⟩ hb
  rw [out_strs hout]
  exact stays_behind C F q.base q.ds a.2 τ

/-- **THE FIFTH TIE AT A PIECE WHOSE SUB-PROTOCOL's ACCEPTING STEP GIVES `Quiet9`.** The relation
that the two parameters' payers are handed is THE STEP's OWN (`BlockYes b`), not `Quiet9`: the
carried word's sentence reads the link's own copy of the calls' state, of which `Quiet9` says
nothing. In: what the payers may spend of the promise in front. -/
theorem t5_quiet (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (b : Block S Claim) (q : Piece C F S Claim WT)
    (hqb : q.b = below b) (hext : ∀ a τ w, q.ext a τ w = w)
    (hq : ∀ s t, BlockYes b s t → Quiet9 s t) (In : P × S → Strs → Prop)
    (hIn : ∀ a, onTR Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) Rz k a →
      In (z, a.1) (strsOf F a.2))
    {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (hM : MeantAt 𝔇 seats r)
    (hc : CarryOpen 𝔇 (fun i => openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i ∧
      ¬ insQ links pl k i) (StepRel (BlockYes b) q.base In))
    (hH : HeadOpen 𝔇 (fun i => openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i ∧
      ¬ insQ links pl k i) (StepRel (BlockYes b) q.base In))
    (hO : ∀ i, openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i →
      ¬ insQ links pl k i → (i.part = none ∨ ∃ m, i = .wo m) ∧ notOwn ownDigits i ∧
        lowItem Nm (fun j => j < q.base) i) :
    ∀ a τ b' w i, onTR Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) Rz k a →
      q.ior.red.out a τ = some b' →
      onQ Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) (k + 1) b' →
      relQ Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) (k + 1) b' w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ Nm (mgAll 𝔇 Mg) (fun s : S => (z, s)) i a (q.ext a τ w) :=
  t5_of_back Nm (mgAll 𝔇 Mg) links pl z Rz k q hext (BlockYes b) In
    (fun a _ _ ha hout => ⟨yes_of_out hqb hout, hIn a ha⟩)
    fun i ho hn => holds_back_open9 𝔇 Mg Nm _ _ _
      (relReads_step (BlockYes b) q.base In fun s t h => sameRead_quiet9 (hq s t h))
      (read3_quiet9 𝔇 hM (BlockYes b) hq q.base In) hc hH
      (fun m _ => wo_back_quiet9 𝔇 (BlockYes b) hq q.base In m)
      (fun j hj => hO j hj.1 hj.2) i ⟨ho, hn⟩

end

/-! ### the three sub-protocols -/

theorem quiet9_batch (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hst : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (s t : S) (h : BlockYes L.batchB s t) : Quiet9 s t := by
  obtain ⟨ft, rs, cols, j, hstep⟩ := h
  exact ⟨{ check := s.check }, {}, {}, (rest_blocks _ _ _ L pp hb₁ hst).1 _ _ _ _ _ j hstep⟩

theorem quiet9_behind (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hst : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (s t : S) (h : BlockYes L.behindB s t) : Quiet9 s t := by
  obtain ⟨ft, rs, cols, j, hstep⟩ := h
  exact ⟨{ check := s.check }, {}, {}, (rest_blocks _ _ _ L pp hb₁ hst).2 _ _ _ _ _ j hstep⟩

theorem quiet9_shut (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (s t : S) (h : BlockYes b₅ s t) : Quiet9 s t := by
  obtain ⟨ft, rs, cols, j, hstep⟩ := h
  exact ⟨{ check := s.check }, {}, {}, rest_shut _ _ _ pw piece b₅ hb₅ _ _ _ _ _ j hstep⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sameRead_quiet9
#print axioms VerifiableInference.Desc.LinkJoin.wo_back_quiet9
#print axioms VerifiableInference.Desc.LinkJoin.read3_quiet9
#print axioms VerifiableInference.Desc.LinkJoin.holds_back_open9
#print axioms VerifiableInference.Desc.LinkJoin.t5_of_back
#print axioms VerifiableInference.Desc.LinkJoin.t5_quiet
#print axioms VerifiableInference.Desc.LinkJoin.quiet9_batch
#print axioms VerifiableInference.Desc.LinkJoin.quiet9_behind
#print axioms VerifiableInference.Desc.LinkJoin.quiet9_shut
