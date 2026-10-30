-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Law.lean: the merge of the claims on the committed weights at the head's
link
(Johnson/Desc/First/Fork/MergeKind.lean), held against the library's proved block for it
(Johnson/Top/H/Merge.lean: kMerge; Cb/Pv/Lay/Weights.lean: the block; Ior/Draw.lean: the draw). The
ground file: definitions, and theorems with their proofs.

Why the law is not "the block's yes gives the proved block's yes". The proved block is one draw (the
powers of one element), then the short masked sumcheck at the programs' pick of the coefficient that
is left out. At that pick its verifier never rejects (`blkOut`). So that sentence is empty. The
merge hears and hands on: the law says that what it hands on is what the typed merge puts out
(Johnson/Top/H0/MergeLaw/Said.lean, Says.lean).

Main names:
  `RoundsAre`, `roundsAre`: the block's declared rounds have the written names and numbers.
  `brought`: the proved block is Good at every caller (a call of the library's merge_good).
  `BlkOut`, `blkOut`: the whole typed block's own output is TWhole.shortV at every input.
  `TapeIs`, `tapeIs`: the tape is the stretch, round by round.
  `Local`, `isLocal`: what the decision reads and writes.
  `leavesSeven`, `leavesReply`: seven of the carried record's nine fields, the reply that was heard
    among them, are left as they were.

The library's theorems that are spent: merge_good (Johnson/Top/H/Merge.lean), short_out
(Cb/G6/Value.lean), MergeL.pick_ok (Cb/Pv/Lay/Merge.lean).

Limits: nothing on soundness, on an honest prover or on hiding. No error is reckoned. That the
decision says yes anywhere is not proved. `roundsAre` reads five fields of an entry alone. The
head's
link alone.

-/
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Top.H.Merge
import Cb.G6.Value

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay TWhole Johnson.L5.Layers
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (MergeCaller)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim mergeTapeE)

/-- The block's declared rounds: five fields of each entry (name, bytes sent, elements drawn, draws
other than 0, rows),
written out. The whole entry is held against the plan by the description's own test on the plan, not
here. -/
def RoundsAre {S Cl : Type} (b : Block S Cl) (k n : ℕ) : Prop :=
  b.rounds.map (fun r => (r.entry.name, r.entry.msg, r.entry.drawE, r.entry.drawNZ, r.entry.rows)) =
    ("BAT-sigma", 0, 1, 0, n) :: ("PSC epsilon", 24, 1, 0, 0) ::
      (List.replicate k ("PSC round", 48, 1, 0, 0) ++ [("PSC Y", 24, 1, 1, 0), ("PSC values", 24, 0,
          0, 0)])

variable {E : Type} [Field E] [Fintype E]

/-- **shortV is the whole typed block's own output**, at every oracle. A statement on the library's
text alone. -/
def BlkOut (c : MergeCaller E) : Prop :=
  ∀ (x : c.G.St) (y : c.Ex.Str) (ρ : E) (τ : Tr (shapeS c.G.L.T.par)),
    (c.G.blk (c.G.L.V1 c.Ex)).out x y
        (show Tr (drawRound E :: shapeS c.G.L.T.par) from (((), ()), ρ, τ)) =
      some (shortV c.G.L.T.par c.G.L.F1 (c.G.L.tg (x, ρ), (x, ρ)) τ)

/-- `BlkOut`, proved: by unfolding the draw, the step without rounds and the sequence, and the
library's `short_out` (Cb/G6/Value.lean) at the lawful pick (MergeL.pick_ok). -/
theorem blkOut (c : MergeCaller E) : BlkOut c := fun x y ρ τ =>
  TWhole.short_out c.G.L.T.par c.G.L.F1 c.Ex c.G.L.pick_ok (c.G.L.tg (x, ρ), (x, ρ)) y τ

/-- `RoundsAre`, proved of the kind's own block, at every place's numbers. -/
theorem roundsAre (P : HeadMergeP) : RoundsAre (Johnson.Desc.First.ForkMerge.headClaimMergeKind P) P.lay.lk
    1 := by
  simp [RoundsAre, Johnson.Desc.First.ForkMerge.headClaimMergeKind,
      Johnson.Desc.First.ForkMerge.mergeEntries,
    OnBytes.Model.RoundName.name, List.map_replicate]

/-! ### the two small laws on the text itself -/

/-- **The tape is the stretch, round by round**: where the maker says yes, the tape is `flatOf` of
each round with its entry. -/
def TapeIs : Prop :=
  ∀ rs es tp, mergeTapeE rs es = .ok tp →
    rs.length = es.length ∧ tp = (rs.zip es).map fun x => OnBytes.K.Kc.flatOf x.1 (some x.2)

open VerifiableInference.Desc.First.Look (elemsOf roundS tapeS) in
/-- Where all items are scalars, the leading scalars are all of them. -/
theorem leading_of_elemsOf : ∀ (l : List Fmt.ItemValue) (xs : List OnBytes.E), elemsOf l = some xs →
    OnBytes.K.Kc.leading l = xs
  | [], xs, h => by simpa [elemsOf, OnBytes.K.Kc.leading] using h
  | .e x :: l, xs, h => by
    simp only [elemsOf, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    simp [OnBytes.K.Kc.leading, leading_of_elemsOf l ys hy]
  | .f _ :: _, _, h => by simp [elemsOf] at h
  | .word _ :: _, _, h => by simp [elemsOf] at h
  | .root _ :: _, _, h => by simp [elemsOf] at h
  | .answer _ :: _, _, h => by simp [elemsOf] at h

open VerifiableInference.Desc.First.Look (elemsOf roundS tapeS) in
/-- The strict maker's round is `flatOf` of the round with its entry. -/
theorem roundS_flatOf (r : Fmt.RoundView) (e : Fmt.Entry) (x : OnBytes.K.Kc.FlatRound) (h : roundS r e =
           some x) :
    x = OnBytes.K.Kc.flatOf r (some e) := by
  unfold roundS at h
  split at h
  · exact absurd h (by simp)
  · rename_i sent hs
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [OnBytes.K.Kc.flatOf, leading_of_elemsOf _ _ hs]
    · exact absurd h (by simp)

open VerifiableInference.Desc.First.Look (elemsOf roundS tapeS) in
/-- The strict maker's tape is the stretch, round by round. -/
theorem tapeS_zip : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (tp : OnBytes.K.Kc.Tape), tapeS rs es
    = some tp →
    rs.length = es.length ∧ tp = (rs.zip es).map fun x => OnBytes.K.Kc.flatOf x.1 (some x.2)
  | [], [], tp, h => by simp [tapeS] at h; simp [← h]
  | [], _ :: _, _, h => by simp [tapeS] at h
  | _ :: _, [], _, h => by simp [tapeS] at h
  | r :: rs, e :: es, tp, h => by
    unfold tapeS at h
    split at h
    · rename_i x t hx ht
      simp only [Option.some.injEq] at h
      obtain ⟨h1, h2⟩ := tapeS_zip rs es t ht
      subst h
      simp [h1, ← h2, roundS_flatOf r e x hx]
    · exact absurd h (by simp)

/-- `TapeIs`, proved. -/
theorem tapeIs : TapeIs := by
  intro rs es tp h
  match rs, es, h with
  | [], _, h => simp [mergeTapeE] at h
  | _ :: _, [], h => simp [mergeTapeE] at h
  | r :: rs, e :: es, h =>
    by_cases h1 : VerifiableInference.Desc.First.Door.batchEntryB e = true
    · by_cases h2 : VerifiableInference.Desc.First.Door.batchRoundB e r = true
      · cases ht : VerifiableInference.Desc.First.Look.tapeS rs es with
        | none =>
          simp [mergeTapeE, VerifiableInference.Desc.need, VerifiableInference.Desc.named, h1, h2,
              ht, bind,
            Except.bind] at h
        | some t =>
          simp [mergeTapeE, VerifiableInference.Desc.need, VerifiableInference.Desc.named, h1, h2,
              ht, bind,
            Except.bind, pure, Except.pure] at h
          obtain ⟨a, b⟩ := tapeS_zip rs es t ht
          subst h
          simp [a, ← b]
      · simp [mergeTapeE, VerifiableInference.Desc.need, h1, h2, bind, Except.bind] at h
    · simp [mergeTapeE, VerifiableInference.Desc.need, h1, bind, Except.bind] at h

/-- **decide reads the head's claim, the slot of its value, the ledger, what is owed, and its
rounds; it writes what the merge leaves, the two ledgers, the slot, and that nothing is
owed; all else is handed on as it was.** -/
def Local (P : HeadMergeP) : Prop :=
  ∀ s rs s', headMergeDecide P s rs = .ok s' →
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧
      s' = { s with rowsOwed := none, here := .head a' } ∧
      a' = { a with wo := a'.wo, F := a'.F, Fm := a.F, slot := a'.slot } ∧
      ∀ s₂ a₂, s₂.here = .head a₂ → a₂.opened = a.opened → a₂.claim = a.claim → a₂.x.map (·.sV) =
          a.x.map (·.sV) →
        a₂.F = a.F →
        s₂.rowsOwed = s.rowsOwed →
        ∃ s₂' a₂', headMergeDecide P s₂ rs = .ok s₂' ∧ s₂'.here = .head a₂' ∧
          a₂'.wo = a'.wo ∧ a₂'.F = a'.F ∧ a₂'.slot = a'.slot

open Johnson.Desc.First.ForkMerge (mergeHear mergeEntries) in
open VerifiableInference.Desc (need named) in
/-- `Local`, proved. -/
theorem isLocal (P : HeadMergeP) : Local P := by
  intro s rs s' h
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true
    · by_cases hw : s.noneWaits = true
      · cases ht : mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) with
        | error e => simp [headMergeDecide, hh, ho, hw, ht, need, bind, Except.bind] at h
        | ok t =>
          cases hcl : a.claim with
          | none => simp [headMergeDecide, hh, ho, hw, ht, hcl, need, named, bind, Except.bind] at h
          | some claim =>
          cases hx : a.x with
          | none => simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, need, named, bind, Except.bind]
                at h
          | some x =>
          cases hm : mergeHear P.lay #[claim] #[x.sV] a.F t with
          | error e => simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, need, named, bind,
                Except.bind] at h
          | ok r =>
            obtain ⟨wo, F, t'⟩ := r
            by_cases he : t'.isEmpty = true
            · by_cases hc : (F.next == P.nMsg) = true
              · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind, pure,
                  Except.pure] at h
                subst h
                refine ⟨a, { a with
                    wo := some wo
                    F := { F with planClaimsF := P.nLin }
                    Fm := a.F
                    slot := some F.next },
                  rfl, by simp [ho, hcl, hx], by simp [ho, hcl, hx], rfl, ?_⟩
                intro s₂ a₂ h₂ e1 e2 e3 e4 e5
                obtain ⟨x₂, hx₂, hsv⟩ : ∃ x₂, a₂.x = some x₂ ∧ x₂.sV = x.sV := by
                  rw [hx] at e3
                  cases hx₂ : a₂.x with
                  | none => simp [hx₂] at e3
                  | some y => exact ⟨y, rfl, by simpa [hx₂] using e3⟩
                refine ⟨{ s₂ with
                    rowsOwed := none
                    here := .head { a₂ with
                      wo := some wo
                      F := { F with planClaimsF := P.nLin }
                      Fm := a₂.F
                      slot := some F.next } }, { a₂ with
                    wo := some wo
                    F := { F with planClaimsF := P.nLin }
                    Fm := a₂.F
                    slot := some F.next }, ?_, rfl, rfl, rfl, rfl⟩
                have hw₂ : s₂.noneWaits = true := by
                  have : s₂.noneWaits = s.noneWaits := by simp [S.noneWaits, e5]
                  rw [this, hw]
                simp [headMergeDecide, h₂, e1, e2, hcl, hx₂, hsv, e4, ho, hw₂, ht, hm, he, hc, need,
                    named, bind,
                  Except.bind, pure, Except.pure]
              · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind] at h
            · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, need, named, bind,
                  Except.bind] at h
      · simp [headMergeDecide, hh, ho, hw, need, bind, Except.bind] at h
    · simp [headMergeDecide, hh, ho, need, bind, Except.bind] at h
  | _ => simp [headMergeDecide, hh] at h

/-- **Where the block's decision goes on, seven of the carried record's nine fields are as they
were**: all but what is owed and the link's own part. -/
theorem leavesSeven (P : HeadMergeP) (s : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (s' : S)
    (h : (Johnson.Desc.First.ForkMerge.headClaimMergeKind P).decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.roots = s.roots ∧ s'.failed = s.failed ∧ s'.check = s.check
        ∧ s'.out = s.out ∧
      s'.req = s.req := by
  obtain ⟨a, a', _, _, e, _⟩ := isLocal P s rs s' h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The reply that was heard is left as it was**: to the letter the unfolding of `Block.Leaves
(fun s => s.out.reply) (headClaimMergeKind P)` (Johnson/Desc/Sound/FoldHeard.lean). -/
theorem leavesReply (P : HeadMergeP) : ∀ (s : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List
           UInt64))) (s' : S),
    (Johnson.Desc.First.ForkMerge.headClaimMergeKind P).decide s rs gs = .ok s' → s'.out.reply =
        s.out.reply :=
  fun s rs gs s' h => by rw [(leavesSeven P s rs gs s' h).2.2.2.2.2.1]

end VerifiableInference.Desc.First.MergeLaw

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.OnPublicFiles

/-- The proved block is Good at every caller: a call of the library's `merge_good`. -/
theorem brought {E : Type} [Field E] [Fintype E] (c : MergeCaller E) : ((kMerge [c]).toKind.block
    c).Good :=
  merge_good [c] c (List.mem_singleton.2 rfl)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.brought
#print axioms VerifiableInference.Desc.First.MergeLaw.blkOut
#print axioms VerifiableInference.Desc.First.MergeLaw.roundsAre
#print axioms VerifiableInference.Desc.First.MergeLaw.tapeIs
#print axioms VerifiableInference.Desc.First.MergeLaw.isLocal
#print axioms VerifiableInference.Desc.First.MergeLaw.leavesReply
