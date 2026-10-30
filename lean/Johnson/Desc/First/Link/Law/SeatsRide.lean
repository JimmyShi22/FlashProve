-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SeatsRide.lean: THE SECOND AND THE THIRD SHARE OF THE PUBLIC TEST
`totalIn` (Johnson/Desc/First/Batch/FormsIn.lean: the mask row's message is seated; each array of
the
ledger is there, at a seat that may be read) RIDE OVER AN ACCEPTING STEP OF THE BATCHING AND OF THE
FRAME's SUB-PROTOCOL BEHIND IT. Definitions and theorems. No text already in the library turns.

Why. `maskSeat` and `arrayIn` read, of the verifier's state, the book of trees and, of the open
link's context, its list of arrays and the state of the calls. The link's runs write the ledger and
the approximate range proof's structure; the draw turns, of the context, two other fields.
  `Rs s s'`: the book, and the open link's list of arrays and state of the calls, are as they were.
    `Rs.refl`, `Rs.trans`; `rs_putTl`, `rs_putFork`, `rs_putLink`, `rs_head`, `rs_wrote`.
  `rests_rs`: **`RelRests Rs`** (Johnson/Desc/First/Link/Law/RelRuns.lean): so every known run of a
    link's two orders stands in `Rs`. `rs_set`: the lens's writing. `drawn_ctx`: the draw (the like
    stands at `Meaning.K2.drawn_ctx`, Johnson/Goal/Meaning/OwnMakers.lean: another cone, not
    imported here).
  `rs_batch`, `rs_behind`: **an accepting step of each of the two stands in `Rs`**, from the same of
    every run of the link's two orders.
  `part_book`, `seats_of_rs`: under `Rs` the two readings give what they gave.
  `SeatsThere own n s`: a part is there; the mask row's message is seated; each array below n is
    there. `seats_ride`: **it passes along `Rs`, where a part is there behind.**
Limits. The runs' share is a premise, as in BkLink.lean; at the known runs it is `rests_rs`, the
lookups' runs aside. THAT `SeatsThere` HOLDS IN FRONT OF THE BATCHING IS NOT SHOWN. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.BkLink
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS Where drawn drawnClean maskSeat arrayIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- What the two readings read of a link's context. -/
def ctxRead (L : LinkCtx) : Array (ℕ × String) × ChainCheck := (L.arrayOf, L.check)

/-- **What the two readings read of the verifier's state is as it was.** -/
structure Rs (s s' : S) : Prop where
  book : s'.book = s.book
  ctx : s'.link?.map ctxRead = s.link?.map ctxRead

theorem Rs.refl (s : S) : Rs s s := ⟨rfl, rfl⟩

theorem Rs.trans {s t u : S} (a : Rs s t) (b : Rs t u) : Rs s u :=
  ⟨b.book.trans a.book, b.ctx.trans a.ctx⟩

theorem rs_putTl (s : S) (tl : HTailF2) : Rs s (s.putTl tl) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> constructor <;> simp [S.putTl, S.link?, ho]
  | _ => exact ⟨rfl, rfl⟩

theorem rs_putFork (s : S) (G : Fork) : Rs s (s.putFork G) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> constructor <;> simp [S.putFork, S.link?, ho]
  | _ => exact ⟨rfl, rfl⟩

/-- A writing of the link's context that keeps what is read of it. -/
theorem rs_putLink (s : S) (L0 L : LinkCtx) (h : s.link? = some L0) (hl : ctxRead L = ctxRead L0) :
    Rs s (s.putLink L) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true
    · have e : x.L = L0 := by simpa [S.link?, ho] using h
      constructor <;> simp [S.putLink, S.link?, ho, hl, e]
    · simp [S.link?, ho] at h
  | lay x =>
    have e : x.L = L0 := Option.some.inj h
    exact ⟨rfl, by show some (ctxRead L) = some (ctxRead x.L); rw [hl, e]⟩
  | att x =>
    have e : x.L = L0 := Option.some.inj h
    exact ⟨rfl, by show some (ctxRead L) = some (ctxRead x.L); rw [hl, e]⟩
  | _ => exact nomatch h

theorem rs_head (s : S) (a : First.HeadOwn) (G : Fork) (h : s.here = .head a) :
    Rs s { s with here := .head { a with F := G } } := by
  refine ⟨rfl, ?_⟩
  unfold S.link?
  rw [h]

theorem rs_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) : Rs e e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  refine ⟨rfl, ?_⟩
  unfold S.link?
  rw [h1]

/-- **Every known writing of a link's runs stands in Rs.** -/
theorem rests_rs : RelRests Rs where
  refl := Rs.refl
  wrote _ _ _ _ hw := rs_wrote hw
  head := rs_head
  eq n e c e₁ h := by
    obtain ⟨G, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok n e e₁ c h
    exact (rs_putTl e tl').trans (rs_putFork _ F1)
  ls e e₁ h := by
    obtain ⟨G, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
    exact rs_putTl e _
  tests nU e e₁ h := by
    obtain ⟨G, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
    exact (rs_putTl e tl).trans (rs_putFork _ _)

/-- The lens's writing of a part whose context reads as the one that it has read. -/
theorem rs_set (e : S) (q q' : K9.Part) (hq : atS.get? e = some q)
    (hl : ctxRead q'.L = ctxRead q.L) : Rs e (atS.set e q') := by
  obtain ⟨hL, _⟩ := part_reads e q hq
  have h1 := (rs_putLink e q.L q'.L hL hl).trans (rs_putFork _ q'.F)
  exact ⟨h1.book, h1.ctx⟩

/-- The draw leaves the link's list of arrays and the state of the calls. -/
theorem drawn_ctx (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ) (L : LinkCtx) (F : Fork)
    (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) : ctxRead o.L = ctxRead L := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  rfl

/-- **An accepting step of the batching stands in Rs.** -/
theorem rs_batch (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → Rs e e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) : Rs s s' := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, _, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  have h0 : Rs s (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) :=
    rs_set s a _ ha (drawn_ctx _ _ _ _ _ _ _ hd)
  have h1 : Rs s e := gather_holds (Rs s) (fun _ => []) [] (runsIn L.hear L.order)
    (fun r' hr' n e0 c0 e1 hr0 hx => by
      obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
      obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
      exact hx.trans (hk o' ho' run hrun n e0 c0 e1 hr0)) ([], _) (c, e)
    (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  exact h1.trans (rs_set e q _ hq rfl)

/-- **An accepting step of the frame's sub-protocol behind the batching stands in Rs.** -/
theorem rs_behind (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) : Rs s s' := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact ran_holds (Rs s) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq))
    (fun o ho run hl x x₁ hr hx => hx.trans (hk o ho run hl x x₁ hr)) (Rs.refl s)

/-- The lens hands on the state's book. -/
theorem part_book (e : S) (q : K9.Part) (hq : atS.get? e = some q) : q.d.book = e.book := by
  unfold atS at hq
  simp only [Option.bind_eq_bind, Option.pure_def] at hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  rw [← Option.some.inj hq]

/-- **Under Rs the two readings give what they gave.** -/
theorem seats_of_rs (own : List (ℕ × ℕ)) {s s' : S} (h : Rs s s') (a a' : K9.Part)
    (ha : atS.get? s = some a) (ha' : atS.get? s' = some a') :
    maskSeat own a' = maskSeat own a ∧ arrayIn own a' = arrayIn own a := by
  have hb : a'.d.book = a.d.book := by rw [part_book s' a' ha', part_book s a ha, h.book]
  have hc : ctxRead a'.L = ctxRead a.L := by
    have e := h.ctx
    rw [(part_reads s' a' ha').1, (part_reads s a ha).1] at e
    exact Option.some.inj e
  obtain ⟨h1, h2⟩ := Prod.mk.inj hc
  refine ⟨?_, ?_⟩
  · unfold maskSeat
    rw [h2, hb]
  · funext t
    unfold arrayIn
    rw [h1, h2, hb]

/-- A part is there; the mask row's message is seated; each array below n is there. -/
def SeatsThere (own : List (ℕ × ℕ)) (n : ℕ) (s : S) : Prop :=
  ∃ a, atS.get? s = some a ∧ (maskSeat own a).isSome = true ∧
    ∀ i, i < n → (arrayIn own a i).isSome = true

/-- **It passes along Rs, where a part is there behind.** -/
theorem seats_ride (own : List (ℕ × ℕ)) (n : ℕ) {s s' : S} (h : Rs s s') (a' : K9.Part)
    (ha' : atS.get? s' = some a') (hs : SeatsThere own n s) :
    (maskSeat own a').isSome = true ∧ ∀ i, i < n → (arrayIn own a' i).isSome = true := by
  obtain ⟨a, ha, h2, h3⟩ := hs
  obtain ⟨e1, e2⟩ := seats_of_rs own h a a' ha ha'
  rw [e1, e2]
  exact ⟨h2, h3⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_rs
#print axioms VerifiableInference.Desc.LinkJoin.rs_set
#print axioms VerifiableInference.Desc.LinkJoin.drawn_ctx
#print axioms VerifiableInference.Desc.LinkJoin.rs_batch
#print axioms VerifiableInference.Desc.LinkJoin.rs_behind
#print axioms VerifiableInference.Desc.LinkJoin.part_book
#print axioms VerifiableInference.Desc.LinkJoin.seats_of_rs
#print axioms VerifiableInference.Desc.LinkJoin.seats_ride
