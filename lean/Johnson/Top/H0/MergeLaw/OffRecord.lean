-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/OffRecord.lean: the merge's law with no number of the claim among its
letters: three numbers are read off the record. Definitions, and theorems with their proofs.

Why. In `merge_goodIn_cap` (AtSeat.lean) the numbers N of the slots are letters, and the condition
in front ties two of them to the record: the claim's unit and the slot of its value. A promise that
has to hand on these ties needs somebody who makes them. But what a piece owes (`Piece.GoodIn`) is
asked statement by statement, and the cap's piece reads no N: so at each statement the law can be
called at the numbers that the record itself holds.

Main names:
  `recNums`: the numbers of the slots made of the block's numbers (`planNums`, OfPlan.lean), of a
    unit ui, a slot sv and an entry c below ni.
  `ReadsAt s ui sv`: the record stands in the head's part; the claim and what the head heard are
    laid; the claim is on unit ui; its value was heard under slot sv. `EntryAt s c`: the index
    masks' ledger gives c as its next entry. Each is a function of the record (`.unique`).
  `frontR`: the condition in front: a test on the record: the ledger's three arrays have one entry a
    slot, and the ledger has the plan's number of slots.
  `reads_stay`: the merge's yes leaves the three readings. `reads_of_yes`: at a yes, under `frontR`,
    the record has the first two inside their bounds: the unit by the block's own test, the slot
    because it is filled. `frontW_of_R`: so the law's own condition holds at the numbers read.
  `RelFrontR`, `RelBehindR`, `BehindR`: `RelFront`, `RelBehind`, `BehindOk` at numbers that are read
    off the record, under "there are".
  `merge_goodIn_rec`: the cap's piece, at every block that narrows the merge's, has `GoodIn` from
    `frontR`'s yes to `BehindR` between `RelFrontR` and `RelBehindR`. Where the record lacks a
    reading the block refuses, and nothing is owed.

What it pays beside. "The index masks' ledger's next entry is N.c" stands inside `WoHere`
(Here.lean): at the entry that is read off the record it holds by the make.

Limits. Letters still: the block's numbers P; that its layout is a return of `wsLayOf`, and 2 lk + 3
≤ nMsg (both shown of every public record that the planner returns: PlanNums.lean); ni, the number
of the index masks' message's entries, with 0 < ni; `RelBehindR` asks c < ni of whoever pays it; the
written rounds; the readers of the oracles, as AtTable.lean's head says. "The ledger has the plan's
number of slots" is a clause of the condition in front. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.AtSeat
import Johnson.Top.H0.MergeLaw.OfPlan
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading WsShape wsLayOf)
open VerifiableInference.Desc (FileDescription Wit Strs Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece Mem MsgT InMsg Fenced strsOf Sending below)
open VerifiableInference.Desc.First.Pend (takeEntry)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries headClaimMergeKind headMergeDecide)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open K11Caller (ofLay_pos ofLay_unit)
open _root_.Run (ckP)

section
variable (P : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s₀ p3 lkW = .ok P.lay)
  (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ)

/-- **The numbers of the slots, three of them to be read off a record**: the claim's unit ui, the
slot sv of its value, the entry c of the index masks' message. -/
def recNums (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni) :
    K11Caller.Nums (planPlace P h ui) :=
  { planNums P h ui sv hsv hn with ni := ni, c := c, hc := hc }

/-- The record stands in the head's part; the claim on the weights and what the head heard are laid;
the claim is on unit ui; its value was heard under slot sv. -/
def ReadsAt (s : S) (ui sv : ℕ) : Prop :=
  ∃ a claim x0, s.here = .head a ∧ a.claim = some claim ∧ a.x = some x0 ∧ claim.ui = ui ∧ x0.sV = sv

/-- The index masks' ledger gives c as its next entry. -/
def EntryAt (s : S) (c : ℕ) : Prop := ∃ l l', ledgerAt s = some l ∧ takeEntry l = some (c, l')

theorem ReadsAt.unique {s : S} {ui sv ui' sv' : ℕ} (a : ReadsAt s ui sv) (b : ReadsAt s ui' sv') :
    ui = ui' ∧ sv = sv' := by
  obtain ⟨a1, c1, x1, e1, e2, e3, e4, e5⟩ := a
  obtain ⟨a2, c2, x2, f1, f2, f3, f4, f5⟩ := b
  obtain rfl : a1 = a2 := by
    rw [e1] at f1
    exact Here.head.inj f1
  rw [e2] at f2
  rw [e3] at f3
  obtain rfl := Option.some.inj f2
  obtain rfl := Option.some.inj f3
  exact ⟨e4.symm.trans f4, e5.symm.trans f5⟩

theorem EntryAt.unique {s : S} {c c' : ℕ} (a : EntryAt s c) (b : EntryAt s c') : c = c' := by
  obtain ⟨l, l1, e1, e2⟩ := a
  obtain ⟨m, m1, f1, f2⟩ := b
  rw [e1] at f1
  obtain rfl := Option.some.inj f1
  rw [e2] at f2
  exact congrArg Prod.fst (Option.some.inj f2)

/-- **The condition in front, with no number of the claim in it**: a test on the record: where it
stands in the head's part: the ledger's three arrays have one entry a slot, and the ledger has the
plan's number of slots. -/
def frontR (s : S) : Bool :=
  match s.here with
  | .head a =>
    a.F.vp.size == a.F.ns && a.F.mf.size == a.F.ns && a.F.gotF.size == a.F.ns && a.F.ns == P.nMsg
  | _ => true

/-- What the merge's yes leaves of the three readings. -/
theorem reads_stay {s s' : S} {rs : List Fmt.RoundView} (hd : headMergeDecide P s rs = .ok s') :
    (∀ ui sv, ReadsAt s ui sv ↔ ReadsAt s' ui sv) ∧ ∀ c, EntryAt s c ↔ EntryAt s' c := by
  obtain ⟨a, a', e1, e2, e3, e4, _⟩ := isLocal P s rs s' hd
  have hc : a'.claim = a.claim := by rw [e4]
  have hx : a'.x = a.x := by rw [e4]
  have hl : ledgerAt s' = ledgerAt s := by
    rw [e3]
    rfl
  refine ⟨fun ui sv => ⟨?_, ?_⟩, fun c => by unfold EntryAt; rw [hl]⟩
  · rintro ⟨b, cl, x0, f1, f2, f3, f4, f5⟩
    obtain rfl : a = b := by
      rw [e1] at f1
      exact Here.head.inj f1
    exact ⟨a', cl, x0, e2, by rw [hc]; exact f2, by rw [hx]; exact f3, f4, f5⟩
  · rintro ⟨b, cl, x0, f1, f2, f3, f4, f5⟩
    obtain rfl : a' = b := by
      rw [e2] at f1
      exact Here.head.inj f1
    exact ⟨a, cl, x0, e1, by rw [← hc]; exact f2, by rw [← hx]; exact f3, f4, f5⟩

/-- **Where the merge's decision says yes, under the condition in front: the record has the two
readings, inside their bounds.** -/
theorem reads_of_yes {s s' : S} {rs : List Fmt.RoundView} (hd : headMergeDecide P s rs = .ok s')
    (hf : frontR P s = true) :
    ∃ ui sv, ui < P.lay.U.size ∧ sv < P.nMsg ∧ ReadsAt s ui sv := by
  obtain ⟨a, a', tp, F, claim, x, wo, e1, e2, e3, e4, e5, e6, e7, -⟩ := decide_inv hd
  unfold frontR at hf
  rw [e1] at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨l1, l2⟩, l3⟩, l4⟩ := hf
  obtain ⟨xx, mu, eps, c, beta, v, T, r1, rY, rV, qs, -, -, -, hp, -⟩ := mergeHear_inv e7
  have hu : claim.ui < P.lay.U.size := by
    have := (hear_tests e7).2.1
    simpa using this
  exact ⟨claim.ui, x.sV, hu, by rw [← l4]; exact OnBytes.PscRun.filled_lt l3 (filled_of_public hp),
    a, claim, x, e1, e3, e4, rfl, rfl⟩

/-- The condition in front and the readings give the law's own condition at the numbers read. -/
theorem frontW_of_R {s : S} (hf : frontR P s = true) (ui : Fin P.lay.U.size) (sv : ℕ)
    (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni) (hr : ReadsAt s ui.val sv) :
    frontW (recNums P h hn ni ui sv hsv c hc) s = true := by
  obtain ⟨a, claim, x0, e1, e2, e3, e4, e5⟩ := hr
  unfold frontR at hf
  unfold frontW
  rw [e1] at hf ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨l1, l2⟩, l3⟩, _⟩ := hf
  simp only [e2, e3, l1, l2, l3, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_finRange, true_implies]
  refine ⟨?_, fun i => e4⟩
  rw [e5]
  rfl

end

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {F : Frame} (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem)
  (posM posI : ℕ → Bool × ℕ × ℕ)
  (P : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s₀ p3 lkW = .ok P.lay)
  (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ)

/-- **The merge's relation in front, its numbers read off the record.** -/
def RelFrontR (a : S × F.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt a.1 ui.val sv ∧
      RelFront cs G arr smp rc decT (recNums P h hn ni ui sv hsv c hc) xM xI posM a w

/-- **The merge's relation behind, its numbers read off the record.** -/
def RelBehindR (b : S × F.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt b.1 ui.val sv ∧ EntryAt b.1 c ∧
      RelBehind cs G arr smp rc decT (recNums P h hn ni ui sv hsv c hc) claims lin xM xI posM posI
        b w

/-- What the yes leaves for certain behind, at the numbers read off the record. -/
def BehindR (s' : S) : Prop :=
  ∃ (ui : Fin P.lay.U.size) (sv : ℕ) (hsv : sv < P.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt s' ui.val sv ∧ BehindOk (recNums P h hn ni ui sv hsv c hc) s'

/-- **THE MERGE's LAW WITH NO NUMBER OF THE CLAIM AMONG ITS LETTERS**: the unit, the slot of the
claim's value and the entry of the index masks' message are read off the record. -/
theorem merge_goodIn_rec (hni : 0 < ni) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind)
    (hinM : ∀ j, j < P.nMsg → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    (base : ℕ) (hF : Fenced base [xM, xI]) (B' : Block S Claim)
    (hB : B'.Narrows (headClaimMergeKind P)) :
    (⟨below B', base, L, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) L)⟩ :
      Piece (ckP .two) F S Claim (Wit Cells Tok MsgT)).GoodIn
      (fun a => frontR P a.1 = true) (fun b => BehindR P h hn ni b.1)
      (RelFrontR cs G arr smp rc decT xM xI posM P h hn ni)
      (RelBehindR cs G arr smp rc decT claims lin xM xI posM posI P h hn ni) := by
  intro a ha
  by_cases hr : ∃ ui sv, ui < P.lay.U.size ∧ sv < P.nMsg ∧ ReadsAt a.1 ui sv
  · obtain ⟨ui, sv, hui, hsv, hra⟩ := hr
    obtain ⟨c, hc, hce⟩ : ∃ c, c < ni ∧ ∀ c', c' < ni → EntryAt a.1 c' → c' = c := by
      by_cases hx : ∃ c, c < ni ∧ EntryAt a.1 c
      · obtain ⟨c, hc, hcx⟩ := hx
        exact ⟨c, hc, fun c' _ h' => h'.unique hcx⟩
      · exact ⟨0, hni, fun c' h1 h2 => absurd ⟨c', h1, h2⟩ hx⟩
    have g := merge_goodIn_cap (F := F) (Tok := Tok) cs G arr smp rc decT
      (recNums P h hn ni ⟨ui, hui⟩ sv hsv c hc) claims lin xM xI posM posI P rfl rfl (ofLay_pos h)
      (by
        show P.nMsg - (2 * P.lay.lk + 3) + 1 + 2 * P.lay.lk + 2 = P.nMsg
        omega)
      (fun _ u hu => ofLay_unit h _ u hu) L he hkd hinM hinI hsmp hdec base hF B' hB
    refine Doomed.mono _ _ ?_ (g a (frontW_of_R P h hn ni ha ⟨ui, hui⟩ sv hsv c hc hra))
    intro τ hτ b hb
    obtain ⟨hok, himp⟩ := hτ b hb
    obtain ⟨rs, hd⟩ := seat_yes P (⟨below B', base, L, [], fun _ _ w => w,
      Err.cap 128 (uLT (ckP .two) L)⟩ : Piece (ckP .two) F S Claim (Wit Cells Tok MsgT)) B' hB rfl
      a b τ hb
    obtain ⟨hst, hen⟩ := reads_stay P hd
    refine ⟨⟨⟨ui, hui⟩, sv, hsv, c, hc, (hst ui sv).1 hra, hok⟩, fun w hw => ?_⟩
    obtain ⟨ui', sv', hsv', c', hc', hrb, heb, hrel⟩ := hw
    obtain ⟨u1, u2⟩ := hrb.unique ((hst ui sv).1 hra)
    obtain rfl : ui' = ⟨ui, hui⟩ := Fin.ext u1
    subst u2
    obtain rfl := hce c' hc' ((hen c').2 heb)
    exact ⟨⟨ui, hui⟩, sv', hsv', c', hc', hra, himp w hrel⟩
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨rs, hd⟩ := seat_yes P (⟨below B', base, L, [], fun _ _ w => w,
      Err.cap 128 (uLT (ckP .two) L)⟩ : Piece (ckP .two) F S Claim (Wit Cells Tok MsgT)) B' hB rfl
      a b τ hb
    exact absurd (reads_of_yes P hd ha) hr

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.reads_of_yes
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_goodIn_rec
