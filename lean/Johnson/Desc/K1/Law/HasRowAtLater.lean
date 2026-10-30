-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HasRowAtLater.lean: K01_law, rows
P.hasRow and G.wo: the pending row that the frame's reader gives at the state (`rowAt`,
Johnson/Top/H0/Walk/FrameRow.lean) over a yes of a later moment's block and of the quiet step behind
the reads' sending. Statements with their proofs.

Why it holds. The reader reads three things of the state: what the open link's sub-proof has left
for its row (`leftOf`); the walk's result `S.out`, for the number of the index masks' message; and
of the statement's messages just one thing, that message's ledger of mask entries (`pendingRowO`,
Johnson/Desc/First/Pend/Row.lean). A sending leaves every older message whole (`Kept`,
`kept_behind`, Johnson/Desc/K1/Law/Sound.lean); a joining writes a message's field `groups` alone;
the block lays the statement, the book, the roots and the open link's L and F back. The quiet step
writes the open link's tl and t alone.

Main names.
  `LedgerOld A B`, `LedgerOld.trans`, `ledgerOld_of_kept`, `joinP_ledger`, `joinAll_ledger`,
    `joinOwnP_ledger`, `decideSend_ledger`, `commitAtS_ledger`: no message goes, and every message
    of A has in B the ledger that it had.
  `leftOf_put`, `commitAtS_left'`: what the sub-proof has left stays.
  `pendingRowO_other`: at two lists of messages with one ledger at that number the row is one.
  `RowAlike s s'`, `RowAlike.trans`, `rowAlike_of_same`, `bind_of_map`; `rowAt_of_alike`: the row
    that the reader gives in front it gives behind; `rowAt_eq_of_alike`: one value at both, where
    the index masks' message is there in front; `hasRow_of_alike`.
  `KeepsRow B`; its members `keepsRow_commitAtS`, `keepsRow_laterAt`, `keepsRow_layers`,
    `keepsRow_head`, `keepsRow_att`, `keepsRow_blockAt`, `keepsRow_readsQuietAt`;
    `keepsRow_andThen`.
  `keepsHasRow_of`; `rowAt_onLedger`, `wo_back`: the two rows at any block with `KeepsRow`; "wo"
    under one premise more: the two readings of the witness, at the state behind and at the state
    in front, agree (`AgreeAt`,
    Johnson/Desc/K13/Law/Agree.lean).
  `hasRowAtCommit`, `hasRowSameAtCommit`, `hasRowPubAtCommit` (Johnson/Desc/K1/Law/HasRowOwed.lean),
    `woBackAtCommit` (Johnson/Desc/K1/Law/WoOwed.lean): **the rows' statements.**

Is it empty here? No premise but the block's own yes. That such a block ever says yes is not shown.
Limits. Without "the index masks' message is there in front" the test is not shown to answer alike:
a message that the block sends could take that number. The reads' place's joined block:
Johnson/Desc/K1/Law/HasRowAtReads.lean. K01_law is not proved by this. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.HasRowOwed
import Johnson.Desc.K1.Law.WoOwed
import Johnson.Desc.K1.Places
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub)
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.Close (leftHead)
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk (leftLay)
open Johnson.Desc.First.Walk.Law (hasRow rowAt rowAt_some leftOf pendingRowO_spec)

variable {L Cl : Type}

/-! ## 1 The older messages' ledgers of mask entries -/

/-- No message goes, and every message of A has in B the ledger that it had. -/
def LedgerOld (A B : Statement) : Prop :=
  A.oracles.size ≤ B.oracles.size ∧ ∀ j : Nat, j < A.oracles.size →
    (B.oracles[j]?).map (fun x : OnBytes.Oracle => x.ledger) =
      (A.oracles[j]?).map fun x : OnBytes.Oracle => x.ledger

theorem LedgerOld.trans {A B C : Statement} (h1 : LedgerOld A B) (h2 : LedgerOld B C) :
    LedgerOld A C :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj =>
    (h2.2 j (Nat.lt_of_lt_of_le hj h1.1)).trans (h1.2 j hj)⟩

theorem ledgerOld_of_kept {d d' : DState L} (h : Kept d d') : LedgerOld d.st d'.st :=
  ⟨(old_of_kept h).size, fun j hj => by rw [h.2.2 j hj]⟩

theorem joinP_ledger (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') : LedgerOld d.st d'.st := by
  refine ⟨(old_of_same (joinP_msgs d d' g o kept h)).size, fun j _ => ?_⟩
  unfold Ground.joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Means.map_modify _ _ _ _ _ fun _ => rfl
  · cases h

theorem joinAll_ledger (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' → LedgerOld d.st d'.st
  | [], d, d', h => by
    obtain rfl : d = d' := Option.some.inj h
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | _ :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (joinP_ledger d d₁ _ _ _ h1).trans (joinAll_ledger p g l d₁ d' h2)

theorem joinOwnP_ledger (p : GPar) (d d' : DState L) (f f' : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (h : joinOwnP groundG p d f sent ids = some (f', d')) :
    LedgerOld d.st d'.st := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d₁, h1, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : d₁ = d' := (Prod.mk.inj e).2
    exact joinAll_ledger p _ _ d d₁ h1
  · cases h

theorem decideSend_ledger (P : Par) (owed : Option Nat) (d d' : DState L) (rs : List Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) : LedgerOld d.st d'.st := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    exact ledgerOld_of_kept (kept_behind P d _ _)

/-- **A yes of a later moment's block leaves the older messages' ledgers.** -/
theorem commitAtS_ledger (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    LedgerOld s.st s'.st := by
  obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs h
  obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
  have a := decideSend_ledger P _ _ d₁ rs ids h2
  rw [e0] at a
  rw [e1]
  exact LedgerOld.trans a (joinOwnP_ledger _ _ _ _ _ _ _ h3)

/-! ## 2 What the open link's sub-proof has left for its row -/

theorem leftOf_put (s : S) (w : DState Unit) (C : LinkCtx) (F : Fork) :
    leftOf (((laid s w).putLink C).putFork F) = leftOf s := by
  cases hs : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [leftOf, leftLay, leftHead, S.putFork, S.putLink, laid, hs, ho]
  | _ => simp [leftOf, leftLay, leftHead, S.putFork, S.putLink, laid, hs]

theorem commitAtS_left' (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    leftOf s' = leftOf s := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, _, rfl⟩ := (map_ok _ _ _).1 h
    exact leftOf_put s _ _ _
  · cases h

/-! ## 3 The pending row reads one ledger of the messages -/

/-- Where two lists of messages hold one ledger at the number im, the pending row is one. -/
theorem pendingRowO_other {lay : WsLay} {im n : Nat} {o : WsForkOut} {Sh : Params.LinShape}
    {A B os : Array OnBytes.Oracle} {row : TensorRow}
    (e : (B[im]?).bind (·.ledger) = (A[im]?).bind (·.ledger))
    (h : pendingRowO lay im o n Sh A = .ok (row, os)) :
    ∃ os', pendingRowO lay im o n Sh B = .ok (row, os') := by
  unfold pendingRowO at h ⊢
  rw [e]
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  repeat' (split at h)
  all_goals (try (simp at h; done))
  all_goals (
    simp at h
    simp_all)

/-! ## 4 What the frame's reader of the pending row reads -/

/-- What the reader of the pending row reads of s stands in s'. -/
structure RowAlike (s s' : S) : Prop where
  left : leftOf s' = leftOf s
  out : s'.out = s.out
  ledger : LedgerOld s.st s'.st

theorem RowAlike.trans {s s₁ s' : S} (h : RowAlike s s₁) (h' : RowAlike s₁ s') : RowAlike s s' :=
  ⟨h'.left.trans h.left, h'.out.trans h.out, h.ledger.trans h'.ledger⟩

/-- From: the same "left", the same walk's result, the same statement. -/
theorem rowAlike_of_same {s s' : S} (hl : leftOf s' = leftOf s) (ho : s'.out = s.out)
    (hs : s'.st = s.st) : RowAlike s s' :=
  ⟨hl, ho, by rw [hs]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩⟩

theorem bind_of_map {α β : Type} {f : α → Option β} {x y : Option α} (h : x.map f = y.map f) :
    x.bind f = y.bind f := by
  cases x <;> cases y <;> simp_all

/-- **The row that the reader gives in front it gives behind.** -/
theorem rowAt_of_alike {s s' : S} (h : RowAlike s s') {lay : WsLay} {n : Nat}
    {lin : Params.LinShape} {r : TensorRow} (hr : rowAt lay n lin s = some r) :
    rowAt lay n lin s' = some r := by
  obtain ⟨w, os, hw, hp⟩ := rowAt_some.1 hr
  obtain ⟨l, _, _, hl, _, _, _⟩ := pendingRowO_spec hp
  have hlt : s.out.indexMasks < s.st.oracles.size := by
    by_contra hx
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hx)] at hl
    cases hl
  obtain ⟨os', hp'⟩ := pendingRowO_other (bind_of_map (h.ledger.2 _ hlt)) hp
  exact rowAt_some.2 ⟨w, os', by rw [h.left]; exact hw, by rw [h.out]; exact hp'⟩

/-- Where the index masks' message is there in front, the reader gives one value at both. -/
theorem rowAt_eq_of_alike {s s' : S} (h : RowAlike s s')
    (hlt : s.out.indexMasks < s.st.oracles.size) (lay : WsLay) (n : Nat) (lin : Params.LinShape) :
    rowAt lay n lin s' = rowAt lay n lin s := by
  refine Option.ext fun r => ⟨fun hr => ?_, rowAt_of_alike h⟩
  obtain ⟨w, os, hw, hp⟩ := rowAt_some.1 hr
  rw [h.out] at hp
  obtain ⟨os', hp'⟩ := pendingRowO_other (bind_of_map (h.ledger.2 _ hlt)).symm hp
  exact rowAt_some.2 ⟨w, os', by rw [← h.left]; exact hw, hp'⟩

theorem hasRow_of_alike {s s' : S} (h : RowAlike s s') {lay : WsLay} {n : Nat}
    {lin : Params.LinShape} (h0 : hasRow lay n lin s = true) : hasRow lay n lin s' = true := by
  unfold hasRow at h0 ⊢
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h0
  rw [rowAt_of_alike h hr]
  rfl

/-! ## 5 The blocks -/

/-- A yes of B, on any rounds, leaves what the reader of the pending row reads. -/
def KeepsRow (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, B.decide s rs gs = .ok s' → RowAlike s s'

/-- **A later moment's block.** -/
theorem keepsRow_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    KeepsRow (commitAtS P link moment arrays : Block S Cl) := fun s s' rs gs h =>
  ⟨commitAtS_left' P link moment arrays s s' rs gs h,
    (commitAtS_ok P link moment arrays s s' rs gs h).choose_spec.choose_spec.2.2.2,
    commitAtS_ledger P link moment arrays s s' rs gs h⟩

/-- A segment's later moment at the plan's numbers. -/
theorem keepsRow_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    KeepsRow (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsRow_commitAtS _ _ _ _

theorem keepsRow_andThen (name : String) (p q : Block S Cl) (hp : KeepsRow p) (hq : KeepsRow q) :
    KeepsRow (p.andThen name q) := by
  intro s s' rs gs h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact (hp _ _ _ _ h1).trans (hq _ _ _ _ h2)

theorem keepsRow_layers (P : K8.ReadsQuiet.PG) : KeepsRow (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact rowAlike_of_same (by simp [leftOf, leftLay, leftHead, ha]) rfl rfl

theorem keepsRow_head (P : K8.ReadsQuiet.PH) : KeepsRow (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact rowAlike_of_same (by simp [leftOf, leftLay, leftHead, ha]) rfl rfl

theorem keepsRow_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : KeepsRow q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  exact rowAlike_of_same (by simp [leftOf, leftLay, leftHead, ha]) rfl rfl

theorem keepsRow_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : KeepsRow q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact keepsRow_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact keepsRow_head _
    · cases h

/-- The quiet step behind the reads' sending, wherever one is made. -/
theorem keepsRow_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) : KeepsRow q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact keepsRow_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact keepsRow_blockAt h
    · rw [if_neg h2] at h
      cases h

/-! ## 6 The two rows, at any block that keeps what the reader reads -/

theorem keepsHasRow_of {B : Block S Cl} (hB : KeepsRow B) : KeepsHasRow B :=
  fun _ _ _ _ _ _ _ h h0 => hasRow_of_alike (hB _ _ _ _ h) h0

/-- The pending row names mask entries of the index masks' message alone. -/
theorem rowAt_onLedger {s : S} {lay : WsLay} {n : Nat} {lin : Params.LinShape} {r : TensorRow}
    (hr : rowAt lay n lin s = some r) : K13.Law.OnLedger s.out.indexMasks r := by
  obtain ⟨w, os, _, hp⟩ := rowAt_some.1 hr
  obtain ⟨_, c, _, _, _, hm, _⟩ := pendingRowO_spec hp
  intro t ht
  rw [hm, List.mem_singleton] at ht
  rw [ht]

/-- "wo" goes back over an accept of B, where the two readings of the witness agree on the matrix
and on the mask entries of the index masks' message. -/
theorem wo_back {B : Block S Cl} (hB : KeepsRow B) {Pp W : Type} {nR kC : ℕ}
    (d : First.FillP1.PubData) (rw : Pp × S → W → First.FillP1.PileWit nR kC) (m : Nat)
    (x x' : Pp × S) (y y' : Strs) (w : W) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide x.2 rs gs = .ok x'.2)
    (hA : K13.Law.AgreeAt x.2.out.indexMasks (rw x' w) (rw x w))
    (h0 : First.FillP1.woAt d rw m x' y' w) : First.FillP1.woAt d rw m x y w :=
  fun r hr => (K13.Law.holds_congr Reading.gl (rowAt_onLedger hr) hA).1
    (h0 r (rowAt_of_alike (hB _ _ _ _ h) hr))

/-- **Row P.hasRow, at a segment's later moment.** -/
theorem hasRowAtCommit : HasRowAtCommit := fun _ P link moment arrays =>
  keepsHasRow_of (keepsRow_commitAtS P link moment arrays)

theorem hasRowSameAtCommit : HasRowSameAtCommit := by
  intro Cl P link moment arrays lay n lin s s' rs gs h hlt
  unfold hasRow
  rw [rowAt_eq_of_alike (keepsRow_commitAtS P link moment arrays s s' rs gs h) hlt]

theorem hasRowPubAtCommit : HasRowPubAtCommit :=
  fun Cl _ P link moment arrays d _ m _ _ rs gs h h0 =>
    hasRowAtCommit Cl P link moment arrays d.lay (d.ncl m) d.lin _ _ rs gs h h0

/-- **Row G.wo, at a segment's later moment.** -/
theorem woBackAtCommit : WoBackAtCommit :=
  fun _ _ _ _ _ P link moment arrays d rw m x x' y y' w rs gs h hA h0 =>
    wo_back (keepsRow_commitAtS P link moment arrays) d rw m x x' y y' w rs gs h hA h0

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.LedgerOld.trans
#print axioms VerifiableInference.Desc.K1.ledgerOld_of_kept
#print axioms VerifiableInference.Desc.K1.joinP_ledger
#print axioms VerifiableInference.Desc.K1.joinAll_ledger
#print axioms VerifiableInference.Desc.K1.joinOwnP_ledger
#print axioms VerifiableInference.Desc.K1.decideSend_ledger
#print axioms VerifiableInference.Desc.K1.commitAtS_ledger
#print axioms VerifiableInference.Desc.K1.leftOf_put
#print axioms VerifiableInference.Desc.K1.commitAtS_left'
#print axioms VerifiableInference.Desc.K1.pendingRowO_other
#print axioms VerifiableInference.Desc.K1.RowAlike.trans
#print axioms VerifiableInference.Desc.K1.rowAlike_of_same
#print axioms VerifiableInference.Desc.K1.bind_of_map
#print axioms VerifiableInference.Desc.K1.rowAt_of_alike
#print axioms VerifiableInference.Desc.K1.rowAt_eq_of_alike
#print axioms VerifiableInference.Desc.K1.hasRow_of_alike
#print axioms VerifiableInference.Desc.K1.keepsRow_commitAtS
#print axioms VerifiableInference.Desc.K1.keepsRow_laterAt
#print axioms VerifiableInference.Desc.K1.keepsRow_andThen
#print axioms VerifiableInference.Desc.K1.keepsRow_layers
#print axioms VerifiableInference.Desc.K1.keepsRow_head
#print axioms VerifiableInference.Desc.K1.keepsRow_att
#print axioms VerifiableInference.Desc.K1.keepsRow_blockAt
#print axioms VerifiableInference.Desc.K1.keepsRow_readsQuietAt
#print axioms VerifiableInference.Desc.K1.keepsHasRow_of
#print axioms VerifiableInference.Desc.K1.rowAt_onLedger
#print axioms VerifiableInference.Desc.K1.wo_back
#print axioms VerifiableInference.Desc.K1.hasRowAtCommit
#print axioms VerifiableInference.Desc.K1.hasRowSameAtCommit
#print axioms VerifiableInference.Desc.K1.hasRowPubAtCommit
#print axioms VerifiableInference.Desc.K1.woBackAtCommit
