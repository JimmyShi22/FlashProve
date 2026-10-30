-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/SizedRides.lean: THE PUBLIC ITEM «THE SEGMENT's LEDGER IS WELL LAID» (a
ledger is open, and its three arrays on slots have as many entries as it has slots) IS KEPT BY AN
ACCEPTING STEP OF THE BATCHING, OF THE FRAME's SUB-PROTOCOL BEHIND IT, AND OF THE SHUTTING (our
files call a sub-protocol a block). Its Bool reads the ledger, which these sub-protocols write: so
it is not kept for nothing. Definitions and theorems.

What is said.
  `ledgerOk s`: the item's Bool, written out (an abbreviation: it meets `First.ledgerB` by
    unfolding). `ledgerOk_iff`: it says: a ledger is open and is `Sized` (OnBytes/Tie/Pv/Psc).
    `ForkRests P`: five closure rules for a property of a ledger (under a later ledger with the same
    core; a run of hidings; a mark «paid»; the approximate range proof's equations; its
    coefficients). `rests_fork`: **under them «a ledger is open and has P» passes an accepting call
    of each of the nine known runs** (RunRel.lean). `sized_rests`, `sizedLS_rests`: the rules at
    `Sized`, and at `Sized` with «as many sums on slots as slots». `has_puts`: what passes both at a
    lookup's run. `drawn_same`: the draw leaves the slots' arrays. `ledger_batch`, `ledger_behind`,
    `ledger_shut`: **`ledgerOk s = true → ledgerOk s' = true` at an accepting step of each of the
    three**, the first two from the runs' share in RunRel.lean's general form.

Limits. THE RUNS' SHARE IS A PREMISE: every run of the link's two orders passes the property. At the
nine known runs it is `rests_fork`. AT A LOOKUP's RUNS THE ONE SENTENCE «an accepting call turns the
state by a writing of the ledger alone» DOES NOT SUFFICE HERE (whatever ledger): what suffices is
`has_puts`' premise, which is shown of no run here; the ties of a
link's entries to these runs are owed. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Link.Law.BkLink
import Johnson.Desc.First.Batch.Law.RowsRide
import OnBytes.Tie.Pv.Psc.Run.PscWriters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Sized hideRun_later)
open OnBytes.Model.Road (SameSlots)
open OnBytes.Desc.First.K4 (Wrote Core frontAtC_pays backAtC_pays hideRun_core paid_core)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side eq_later)
open VerifiableInference.Desc.First.TailClaims (equations coefBody)
open VerifiableInference.Desc.K9 (atS Where shut drawn drawnClean)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.Kinds.Head.Law (join_hands)
open VerifiableInference.Desc.JoinAtBlocks

/-- The public item's Bool (`First.ledgerB`, Johnson/Desc/First/FillKeeper.lean), written out. -/
abbrev ledgerOk (s : S) : Bool :=
  s.fork?.any fun G => G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns

theorem ledgerOk_iff (s : S) : ledgerOk s = true ↔ ∃ G, s.fork? = some G ∧ Sized G := by
  unfold ledgerOk
  cases s.fork? with
  | none => simp
  | some G =>
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, Option.some.injEq, exists_eq_left']
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- «A ledger is open and has P.» -/
def HasFork (P : Fork → Prop) (s : S) : Prop := ∃ G, s.fork? = some G ∧ P G

/-- **Five closure rules for a property of a ledger.** -/
structure ForkRests (P : Fork → Prop) : Prop where
  later : ∀ F G, Core F G → Later F G → P F → P G
  hide : ∀ (F G : Fork) (first : ℕ) (v : Array E) (k : E), F.hideRun first v k = some G → P F → P G
  paid : ∀ (F : Fork) (i : ℕ), P F → P (F.paid i)
  eq : ∀ front tl funs F tl' F1 c, equations front tl funs F = .ok (tl', F1, c) → P F → P F1
  coef : ∀ tl g F, P F → P (coefBody tl g F)

theorem has_wrote {P : Fork → Prop} {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (h : P a.F → P G) : HasFork P e → HasFork P e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  rintro ⟨F, hF, hP⟩
  have e0 : F = a.F := by
    unfold S.fork? at hF
    rw [h1] at hF
    exact (Option.some.inj hF).symm
  exact ⟨G, rfl, h (e0 ▸ hP)⟩

theorem has_head {P : Fork → Prop} {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (h : P a.F → P G) :
    HasFork P e → HasFork P { e with here := .head { a with F := G } } := by
  rintro ⟨F, hF, hP⟩
  have hF' : (if a.opened = true then some a.F else none) = some F := by
    unfold S.fork? at hF
    rw [h1] at hF
    exact hF
  by_cases ho : a.opened = true
  · rw [if_pos ho] at hF'
    obtain rfl : a.F = F := Option.some.inj hF'
    exact ⟨G, by show (if a.opened = true then some G else none) = some G; rw [if_pos ho], h hP⟩
  · rw [if_neg ho] at hF'
    exact nomatch hF'

theorem fork_puts (e : S) (F : Fork) (hF : e.fork? = some F) (tl : HTailF2) (G : Fork) :
    ((e.putTl tl).putFork G).fork? = some G := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.putFork, S.fork?, ho]
    · simp [S.fork?, ho] at hF
  | _ => exact nomatch hF

theorem fork_putTl (e : S) (tl : HTailF2) : (e.putTl tl).fork? = e.fork? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, S.fork?, ho]
  | _ => rfl

/-- **«A ledger is open and has P» passes each of the nine known runs.** -/
theorem rests_fork {P : Fork → Prop} (H : ForkRests P) :
    RunRests fun e e₁ => HasFork P e → HasFork P e₁ where
  refl _ := id
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, hl, _⟩ := frontAtC_pays h0 hr
    exact has_wrote hw (H.later _ _ hc hl)
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, hl, _⟩ := backAtC_pays h0 hr
    exact has_wrote hw (H.later _ _ hc hl)
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact has_wrote hw id
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact has_head h1 (H.hide _ _ _ _ _ hrunG)
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact has_head h1 (H.paid _ i)
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, hF, _, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    rintro ⟨F', hF', hP⟩
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨F1, fork_puts e F hF tl' F1, H.eq _ _ _ _ _ _ _ he hP⟩
  ls e e₁ hr := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    rintro ⟨F', hF', hP⟩
    exact ⟨F', by rw [fork_putTl]; exact hF', hP⟩
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    rintro ⟨F', hF', hP⟩
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨_, fork_puts e F hF tl _, H.coef tl g F hP⟩

theorem sized_same {F G : Fork} (h : SameSlots F G) (hs : Sized F) : Sized G :=
  ⟨by rw [h.vp, h.ns]; exact hs.1, by rw [h.mf, h.ns]; exact hs.2.1,
    by rw [h.got, h.ns]; exact hs.2.2⟩

theorem coef_same (tl : HTailF2) (g : Forest.Heard) (F : Fork) : SameSlots F (coefBody tl g F) :=
  ⟨(coef_side tl g F).2.1, (coef_side tl g F).2.2.2.1, (coef_side tl g F).2.2.2.2.1,
    (coef_side tl g F).2.2.1⟩

/-- The rules at Sized. -/
theorem sized_rests : ForkRests Sized where
  later _ _ _ hl := hl.sized
  hide _ _ _ _ _ h hs := (hideRun_later hs h).sized hs
  paid _ _ hs := hs
  eq _ _ _ _ _ _ _ he := (eq_later he).sized
  coef tl g F := sized_same (coef_same tl g F)

/-- The rules at Sized with «as many sums on slots as slots». -/
theorem sizedLS_rests : ForkRests fun F => Sized F ∧ F.LS.size = F.ns where
  later _ _ hc hl h := ⟨hl.sized h.1, by rw [hc.LS, hc.ns]; exact h.2⟩
  hide _ _ _ _ _ hr h := ⟨(hideRun_later h.1 hr).sized h.1, by
    rw [(hideRun_core hr).LS, (hideRun_core hr).ns]; exact h.2⟩
  paid _ _ h := h
  eq _ _ _ _ _ _ _ he h := ⟨(eq_later he).sized h.1, by
    rw [(eq_side he).LS, (eq_side he).ns]; exact h.2⟩
  coef tl g F h := ⟨sized_same (coef_same tl g F) h.1, by
    rw [(coef_side tl g F).2.2.2.2.2.1, (coef_side tl g F).2.1]; exact h.2⟩

theorem fork_putFork (e : S) (F : Fork) (hF : e.fork? = some F) (G : Fork) :
    (e.putFork G).fork? = some G := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putFork, S.fork?, ho]
    · simp [S.fork?, ho] at hF
  | _ => exact nomatch hF

/-- **A lookup's run**: where, from an open ledger that has its sizes, an accepting call turns the
state by a writing of a ledger with the same sums on slots, the same number of slots, and its
sizes: both properties pass. -/
theorem has_puts {e e₁ : S}
    (h : ∀ F, e.fork? = some F → Sized F →
      ∃ G : Fork, e₁ = e.putFork G ∧ G.LS = F.LS ∧ G.ns = F.ns ∧ Sized G) :
    (HasFork Sized e → HasFork Sized e₁) ∧
      (HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
        HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨F, hF, hS⟩
    obtain ⟨G, rfl, _, _, hG⟩ := h F hF hS
    exact ⟨G, fork_putFork e F hF G, hG⟩
  · rintro ⟨F, hF, hS, hL⟩
    obtain ⟨G, rfl, e1, e2, hG⟩ := h F hF hS
    exact ⟨G, fork_putFork e F hF G, hG, by rw [e1, e2]; exact hL⟩

/-- The draw leaves the slots' arrays and the sums on slots. -/
theorem drawn_same (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ) (L : LinkCtx) (F : Fork)
    (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    SameSlots F o.F ∧ o.F.LS = F.LS := by
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
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- What the lens's writing says of the open ledger. -/
theorem fork_of_set (s : S) (a : K9.Part) (h : (atS.get? s).isSome = true) :
    (atS.set s a).fork? = some a.F := by
  obtain ⟨a', ha', hF, _⟩ := atS_reads s a h
  rw [fork_part _ a' ha', hF]

/-- **At the batching.** -/
theorem ledger_batch (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
        HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) (hs : ledgerOk s = true) :
    ledgerOk s' = true := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, hadd, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  obtain ⟨F0, hF0, hS0⟩ := (ledgerOk_iff s).1 hs
  obtain rfl : F0 = a.F := Option.some.inj (hF0.symm.trans (fork_part s a ha))
  obtain ⟨hsame, hLS⟩ := drawn_same _ _ _ _ _ _ _ hd
  have hls : a.F.LS.size = a.F.ns := (drawnClean_tests _ _ _ _ _ _ _ hd).2.2.2.2.2.2.1
  have h0 : HasFork (fun F => Sized F ∧ F.LS.size = F.ns)
      (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) :=
    ⟨o.F, fork_of_set s _ (by rw [ha]; rfl), sized_same hsame hS0, by
      rw [hLS, hsame.ns]; exact hls⟩
  have h1 : HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e :=
    gather_holds (HasFork fun F => Sized F ∧ F.LS.size = F.ns) (fun _ => []) []
      (runsIn L.hear L.order)
      (fun r' hr' n e0 c0 e1 hr0 hx => by
        obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
        obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
        exact hk o' ho' run hrun n e0 c0 e1 hr0 hx) ([], _) (c, e)
      (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  obtain ⟨F1, hF1, hS1, hL1⟩ := h1
  obtain rfl : F1 = q.F := Option.some.inj (hF1.symm.trans (fork_part e q hq))
  have hfr := (addAll_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ c q.F G hL1 hadd).2.1
  refine (ledgerOk_iff _).2 ⟨G, fork_of_set e _ (by rw [hq]; rfl), ?_⟩
  rw [hfr]
  exact hS1

/-- **At the frame's sub-protocol behind the batching.** -/
theorem ledger_behind (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork Sized e → HasFork Sized e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hs : ledgerOk s = true) :
    ledgerOk s' = true := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact (ledgerOk_iff _).2 (ran_holds (HasFork Sized) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hq))
    (fun o ho run hl x x₁ hr hx => hk o ho run hl x x₁ hr hx) ((ledgerOk_iff s).1 hs))

/-- **At the shutting.** -/
theorem ledger_shut {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₅.step ft s rs cols = .ok (s', k)) (hs : ledgerOk s = true) : ledgerOk s' = true := by
  obtain ⟨L, _, rfl⟩ := shut_inv pw piece _ _ _ _ _ k (hb₅ _ _ _ _ _ h)
  have e : (s.putLink (K9.closed L L.check.frame)).fork? = s.fork? := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [S.putLink, S.fork?, ho]
    | _ => rfl
  unfold ledgerOk at hs ⊢
  rw [e]
  exact hs

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_fork
#print axioms VerifiableInference.Desc.LinkJoin.sized_rests
#print axioms VerifiableInference.Desc.LinkJoin.has_puts
#print axioms VerifiableInference.Desc.LinkJoin.sizedLS_rests
#print axioms VerifiableInference.Desc.LinkJoin.ledger_batch
#print axioms VerifiableInference.Desc.LinkJoin.ledger_behind
#print axioms VerifiableInference.Desc.LinkJoin.ledger_shut
