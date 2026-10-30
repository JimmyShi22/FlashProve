-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ShutLaw.lean
(kind K9's soundness lemma): THEOREMS: THE LAST OF THE THREE BLOCKS THAT CLOSE A SEGMENT: K9.shut
(Batch/Place.lean): no round, no test but "a segment is open": it marks the link's record.
  shut_inv      where its step says yes: a link's record L is there and the state behind is the
                state with closed L L.check.frame written; no column is taken.
  shut_rec      K10's part of the state (K9.recOf: the rows owed, the live frame, the statement) is
                the same in front and behind: so whatever K10's law says behind the closing is
                carried past this block.
  shut_part     K9's own part: the ledger and the statement are the same; the link's record is the
                closed one: its group's number, rows and frame are the same.
  shut_group    so "every open row of the segment's group holds" is the same sentence in front and
                behind.
  shut_goodIn   **the piece of this block is good, at any errors, between any two relations of
                which the one behind gives the one in front along the block's writing** (hcarry:
                asked at the two states of shut_inv).
It draws nothing; no transcript is bad.

-/
import Johnson.Desc.First.Batch.Law.GoodInEq
import Johnson.Desc.First.Batch.Law.AtSLens
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Iop (Doomed)
open VerifiableInference.Desc.K9 (atS Where shut closed recOf there)
open VerifiableInference.Desc.First (S)

variable {W K Cl : Type} {C : CK} {F : Frame}

/-- Where the block's step says yes. -/
theorem shut_inv (p : Where) (piece ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : Nat) (h : (shut (Cl := Cl) p piece).step ft s rs cols = .ok (s', k)) :
    ∃ L, s.link? = some L ∧ s' = s.putLink (closed L L.check.frame) := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t, ht, h⟩ := ok_bind h
  have e : t = s' := congrArg Prod.fst (Except.ok.inj h)
  subst e
  obtain ⟨L, hL, ht⟩ := ok_bind ht
  exact ⟨L, there_ok hL, (Except.ok.inj ht).symm⟩

/-- K10's part of the state stays. -/
theorem shut_rec (s : S) (L : LinkCtx) (hL : s.link? = some L) :
    recOf (s.putLink (closed L L.check.frame)) = recOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl := Option.some.inj hL
    rfl
  | att x =>
    obtain rfl := Option.some.inj hL
    rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp only [S.link?, ho, if_true, Option.some.injEq] at hL
      subst hL
      simp [recOf, S.putLink, S.live, S.link?, K9.owedOf, closed, ho]
    · simp [S.link?, ho] at hL
  | between => simp [S.link?] at hL
  | fin x => simp [S.link?] at hL
  | mem x => simp [S.link?] at hL

/-- K9's own part behind the block. -/
theorem shut_part (s : S) (L : LinkCtx) (hL : s.link? = some L) (a : K9.Part)
    (ha : atS.get? s = some a) :
    ∃ a', atS.get? (s.putLink (closed L L.check.frame)) = some a' ∧ a'.F = a.F ∧
      a'.d.st = a.d.st ∧ a'.L = closed a.L a.L.check.frame := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl := Option.some.inj hL
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | att x =>
    obtain rfl := Option.some.inj hL
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · simp only [S.link?, ho, if_true, Option.some.injEq] at hL
      subst hL
      cases hs : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs] at ha
      | some n =>
        simp only [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs, if_true, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at ha
        subst ha
        simp [atS, S.putLink, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs]
    · simp [S.link?, ho] at hL
  | between => simp [S.link?] at hL
  | fin x => simp [S.link?] at hL
  | mem x => simp [S.link?] at hL

/-- "Every open row of the segment's group holds" is the same sentence in front and behind. -/
theorem shut_group [CommRing K] (ρ : Reading K) (N : Nat) (s : S) (L : LinkCtx)
    (hL : s.link? = some L) (hs : (atS.get? s).isSome = true)
    (tab : Nat → OnBytes.Part → Nat → K) :
    GroupHoldsAt atS ρ N (s.putLink (closed L L.check.frame)) tab ↔ GroupHoldsAt atS ρ N s tab := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', ha', _, e2, e3⟩ := shut_part s L hL a ha
  have eg : a'.L.check.group = a.L.check.group := by rw [e3]; rfl
  constructor
  · intro h b hb G hG row hrow
    have eb : b = a := Option.some.inj (hb.symm.trans ha)
    subst eb
    have := h a' ha' G (by rw [e2, eg]; exact hG) row hrow
    rwa [e2] at this
  · intro h b hb G hG row hrow
    have eb : b = a' := Option.some.inj (hb.symm.trans ha')
    subst eb
    rw [e2]
    exact h a ha G (by rw [← e2, ← eg]; exact hG) row hrow

/-- **The piece of this block is good**, at any errors. -/
theorem shut_goodIn (pw : Where) (piece : Nat) (p : Piece C F S Cl W)
    (hb : p.b = below (shut pw piece)) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w L, on a → p.ior.red.out a τ = some b → a.1.link? = some L →
      b.1 = a.1.putLink (closed L L.check.frame) → R' b w → R a w) :
    p.GoodIn on on' R R' := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep⟩ := fold_one hfold
  obtain ⟨L, hL, e⟩ := shut_inv pw piece F.ft a.1 _ _ b.1 k hstep
  exact hcarry a τ b w L ha hout hL e hw

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.shut_inv
#print axioms VerifiableInference.Desc.K9L.shut_rec
#print axioms VerifiableInference.Desc.K9L.shut_part
#print axioms VerifiableInference.Desc.K9L.shut_group
#print axioms VerifiableInference.Desc.K9L.shut_goodIn
