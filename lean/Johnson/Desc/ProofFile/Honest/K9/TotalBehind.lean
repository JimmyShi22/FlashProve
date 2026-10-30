-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalBehind.lean: FOR THE ITEM "totalB": WHAT STANDS BEHIND THE BATCHING's STEP, OFF
THE SEALED LIBRARY's LAWS AT A LINK; AND THAT THE LINK's TESTS BEHIND THE ADDING PASS. Statements and proofs ON THE
VERIFIER's TEXT, under `SealLaw` (Honest/K9/TotalFront.lean); no prover is in this file, and no goal is stated.
  **`behind_fixed`**   under `SealLaw`, at a yes of the batching's step at s with s' behind, where what is fixed at s
      meets the promise Ok: s' goes on from what is fixed at s (`Fx9`) and is good (`good9`); K9's part b is there;
      ITS LEDGER COUNTS JUST THE RUNS' NUMBERS' SUM, off what is fixed at s (`lenRuns`); and the three numbers
      (`numOf`) are those at s. The library's `fitsM_atS`, `move_adv`, `drawMoves_num`, called
  `shows_same`     so what φ shows of the smallness test's state (its fourteen written fields blanked) and of the
      tables is the same at s' as at s
  `counts_ride`    the link's counts behind the adding but the first read none of the fourteen fields: they hold at s'
      if they hold at s
  `get_parts`, `countsHold_all`   where K9's lens reads a part the ledger is that part's and the smallness test's state
      is there · counts that all hold pass
  **`tests_pass`**   so, of a segment of which `SeatedFree` holds: where K9's share of the fall says nothing at s',
      the runs' numbers' sum is the plan's, and the other counts hold AT s: the link's tests behind the adding pass at
      s'
No member. `tests_pass`, `behind_fixed`, `shows_same` and `get_parts` are called by Honest/K9/TotalAfter.lean.
WHAT IS NOT CLAIMED. `SealLaw` at any link. Ok at any state. The premises of `tests_pass` at any state. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalJoin
import Johnson.Desc.ProofFile.Honest.K9.FallFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option K9L.Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ}

/-- **Behind the step.** -/
theorem behind_fixed (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (k : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', k))
    (hOk : Ok (K9L.fixed9 φ s)) :
    K9L.Fx9 φ Ok (K9L.fixed9 φ s) s' ∧ K9L.good9 s' ∧ K9L.numOf u s' = K9L.numOf u s ∧
      ∃ b, Desc.K9.atS.get? s' = some b ∧
        b.F.nClaim = K9L.lenRuns (K9L.fixed9 φ s) (LinkJoin.rlOf Lk tmOf lenOf) := by
  have HF := K9L.fitsM_atS (K := Cb.Gl.E) φ A.runs.hφ Ok (LinkJoin.FullAt nU) p
  have hon := K9L.yes_onA p _ _ A.share.hb₁ ft s rs cols s' k hs
  have hnum := K9L.drawMoves_num u p _ _ A.share.hb₁ (fun m hm => by
    obtain rfl := List.mem_singleton.1 hm
    exact A.num _ (List.mem_append_left _ List.mem_cons_self)) ft s rs cols s' k hs
  obtain ⟨r, x, a, o, cls, _, _, ha, ho, hy⟩ := A.share.hb₁ ft s rs cols s' k hs
  obtain ⟨_, _, d3, _, _, _, _, _, _, _, _, d12⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ ho
  obtain ⟨f1, g1⟩ := HF.atDraw s a o x ⟨hon, hOk⟩ ha ho
  obtain ⟨a₁, ha₁, hF⟩ := HF.lens s { a with owed := o.owed, L := o.L, F := o.F } (by rw [ha]; rfl)
  have hF' : a₁.F = o.F := hF
  obtain ⟨v, c, c', h1, ⟨rfl, rfl⟩, rfl⟩ := hy
  obtain ⟨hl, b, Ad⟩ := K9L.move_adv Reading.gl Desc.K9.atS (K9L.O9 φ Ok (LinkJoin.FullAt nU)) (K9L.Fx9 φ Ok) p HF
    _ (moves_ok A _ (List.mem_append_left _ List.mem_cons_self)) (K9L.fixed9 φ s) _ s' a₁ c f1 g1 ha₁
    (by rw [hF']; exact d12) h1
  refine ⟨Ad.fixed, Ad.good, hnum, b, Ad.part, ?_⟩
  rw [Ad.count, hF', d3, Nat.zero_add]
  exact hl

/-- What φ shows of the smallness test's state and of the tables is the same behind as in front. -/
theorem shows_same (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (s z : S)
    (hz : K9L.Fx9 φ Ok (K9L.fixed9 φ s) z) :
    z.tl?.map (TailClaims.Law.blank u) = s.tl?.map (TailClaims.Law.blank u) ∧ z.funs? = s.funs? := by
  have e : φ z = φ s := hz.2.1
  have h := A.reads z
  rw [e, A.reads s] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

/-- The counts but the first read none of the fourteen written fields. -/
theorem counts_ride (u : HTailF2) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (s z : S)
    (h1 : z.tl?.map (TailClaims.Law.blank u) = s.tl?.map (TailClaims.Law.blank u)) (h2 : z.funs? = s.funs?)
    (hc : ((Desc.K9.countsAt w.1 w.2.1).tail.all fun q => q.2 s) = true) :
    ((Desc.K9.countsAt w.1 w.2.1).tail.all fun q => q.2 z) = true := by
  have key : ∀ (f : HTailF2 → Bool), (∀ t, f (TailClaims.Law.blank u t) = f t) →
      z.tl?.map f = s.tl?.map f := fun f hf => by
    have e := congrArg (Option.map f) h1
    rw [Option.map_map, Option.map_map] at e
    have e2 : (f ∘ TailClaims.Law.blank u) = f := funext hf
    rw [e2] at e
    exact e
  have hT : Desc.K9.tablesHeld z = Desc.K9.tablesHeld s := by
    unfold Desc.K9.tablesHeld
    rw [h2]
    cases hf : s.funs? with
    | none => cases z.tl? <;> cases s.tl? <;> rfl
    | some funs =>
      have e := key (fun t => Desc.K9.closedList t funs) (fun _ => rfl)
      cases hz : z.tl? with
      | none =>
        cases hs : s.tl? with
        | none => rfl
        | some t2 => rw [hz, hs] at e; exact nomatch e
      | some t1 =>
        cases hs : s.tl? with
        | none => rw [hz, hs] at e; exact nomatch e
        | some t2 => rw [hz, hs] at e; exact Option.some.inj e
  obtain ⟨k, n, x⟩ := w
  cases k with
  | layers =>
    simp only [Desc.K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true] at hc ⊢
    rw [hT]; exact hc
  | attention =>
    simp only [Desc.K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true] at hc ⊢
    rw [hT]; exact hc
  | head =>
    simp only [Desc.K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true] at hc ⊢
    rw [hT, key (fun t => t.foldDrawn == 1) (fun _ => rfl), key (fun t => 1 + t.groupsRun == 2) (fun _ => rfl)]
    exact hc

/-- Where K9's lens reads a part, the ledger is that part's and the smallness test's state is there. -/
theorem get_parts (t : S) (a : Desc.K9.Part) (h : Desc.K9.atS.get? t = some a) :
    t.fork? = some a.F ∧ ∃ tl, t.tl? = some tl := by
  refine ⟨Desc.K9.get_fork t a h, ?_⟩
  have h' : (t.link?.bind fun L => t.fork?.bind fun F => t.tl?.bind fun tl => (Desc.K9.usedOf t).bind fun used =>
      some ({ owed := Desc.K9.owedOf t, used := used, laid := Desc.K9.laidOf tl, L := L, F := F,
              d := { st := t.st, book := t.book, roots := t.roots, opened := [], loc := () } } : Desc.K9.Part)) =
      some a := h
  cases h1 : t.link? with
  | none => rw [h1] at h'; exact nomatch h'
  | some L =>
    rw [h1] at h'
    cases h2 : t.fork? with
    | none => rw [h2] at h'; exact nomatch h'
    | some F =>
      rw [h2] at h'
      cases h3 : t.tl? with
      | none => rw [h3] at h'; exact nomatch h'
      | some tl => exact ⟨tl, rfl⟩

/-- Counts that all hold pass. -/
theorem countsHold_all (t : S) : ∀ (cs : List (String × (S → Bool))), (cs.all fun q => q.2 t) = true →
    Desc.K9.countsHold cs t = .ok ()
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have ih := countsHold_all t cs h.2
    unfold Desc.K9.countsHold at ih ⊢
    show (Desc.K9.need c.1 (c.2 t) >>= fun _ => cs.forM fun c => Desc.K9.need c.1 (c.2 t)) = Except.ok ()
    rw [h.1]
    exact ih

variable {c : Chain S Claim} {Z : ProofFile.Pub} {k : ℕ} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **The link's tests behind the adding pass.** -/
theorem tests_pass (Sd : SeatedFree c Z l k Lk p w) (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (ft : ℕ)
    (s s' : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (j : ℕ)
    (hs : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', j))
    (hOk : Ok (K9L.fixed9 φ s)) (hfree : freeSlotShare w.2.2.filled s' = none)
    (hlen : K9L.lenRuns (K9L.fixed9 φ s) (LinkJoin.rlOf Lk tmOf lenOf) = w.2.1)
    (hc : ((Desc.K9.countsAt w.1 w.2.1).tail.all fun q => q.2 s) = true) : Lk.tests s' = .ok () := by
  obtain ⟨hFx, _, _, b, hb, hn⟩ := behind_fixed A ft s s' rs cols j hs hOk
  obtain ⟨hf, tl, htl⟩ := get_parts s' b hb
  obtain ⟨e1, e2⟩ := shows_same A s s' hFx
  have hc' := counts_ride u w s s' e1 e2 hc
  refine (Sd.tests s').2 ⟨?_, ?_, countsHold_all s' _ ?_⟩
  · show (s'.fork?.bind fun F => s'.tl?.bind fun tl => some (⟨Desc.K9.mergeOf s', tl, F⟩ : Desc.K9.TPart)).isSome = true
    rw [hf, htl]
    rfl
  · unfold freeSlotShare at hfree
    by_cases h : slotsFree w.2.2.filled s' = true
    · exact h
    · rw [if_neg h] at hfree
      exact nomatch hfree
  · have h1 : Desc.K9.claimsCounted w.2.1 s' = true := by
      unfold Desc.K9.claimsCounted
      rw [hf, Option.map_some, Option.getD_some, hn, hlen]
      exact beq_self_eq_true _
    obtain ⟨q, n, x⟩ := w
    cases q <;>
      · simp only [Desc.K9.countsAt, List.tail_cons] at hc'
        simp only [Desc.K9.countsAt, List.all_cons, Bool.and_eq_true]
        exact ⟨h1, by simpa only [List.all_cons, Bool.and_eq_true] using hc'⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.get_parts
#print axioms ProofFile.Honest.K9.countsHold_all
#print axioms ProofFile.Honest.K9.tests_pass
#print axioms ProofFile.Honest.K9.behind_fixed
#print axioms ProofFile.Honest.K9.shows_same
#print axioms ProofFile.Honest.K9.counts_ride
