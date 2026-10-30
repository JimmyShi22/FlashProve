-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeadApart.lean: THE SMALLNESS TEST: AT THE HEAD's SEGMENT: EACH OF THE TEN RUNS OF
CLAIMS BUT "K8.equations" KEEPS AN INVARIANT AND MAKES CLAIMS THAT NAME ONE ARRAY ALONE, AND
"K8.equations" KEEPS THE INVARIANT, FROM PREMISES ON THE STATE IN FRONT OF THE BATCHING. Definitions
and lemmas; none of the library's goals. No prover stands in them; nothing on completeness,
soundness or hiding.

  `headKeep u`   the six fields that LinkJoin.frontSix gathers
      (Johnson/Desc/First/Link/Law/FrontStays.lean); what the two lookups have heard; what the
      head's merge has left (PhiAll.woOf, Johnson/Desc/First/Link/Law/PhiAll.lean)
  `wo_putFork`, `wo_putTl`, `wo_putLink`, `wo_set`, `front_putLink`, `front_set`,
  `headKeep_putFork`, `headKeep_head`, `headKeep_drawn`, `headKeep_k8`   it rests under the laying
      of a ledger, of the head's own ledger, under the batching's draw and under what a yes of
      "K8.equations" writes. LinkJoin.front_put (FrontStays.lean) is the like of `front_set` for
      another writing
  `laterS_putFork`, `laterS_drawn`   laying a later ledger, and the draw, leave a later state
      (First.LaterS, Johnson/Desc/First/LedgerLater.lean)
  `HeadWants h iU3 p6 s`, `HeadInv s u`, `HeadInv.alike`, `HeadInv.merge`, `onlyArray_bare`   eight
      premises on the state in front; the invariant: `headKeep` is that state's and the ledger is a
      later one; under it the state is alike the state in front (Kinds.Head.Law.AlikeFront,
      Johnson/Desc/Kinds/Law/RunsFixedFront.lean) and the merge's condition holds
  **`head_pre_apart`**, **`head_k8_keeps`**, **`head_post_apart`**   the sentence of the title, at
      the eight entries of the order in front of "K8.equations", at that entry, and at the two
      behind. THE RUNS ARE OPENED BY THE TIES AS IN THE PROOF OF LinkJoin.keeps_head
      (Johnson/Desc/First/Link/Law/KeepsAny.lean)
By: Kinds.Head.Law.namesNot_run_front, namesNot_keys_front, namesNot_readers (K6NamesNot.lean) ·
ProofFile.Honest.K3.Law.namesNot_objects, namesNot_joinCalls, namesNot_planesCalls (NamesKept.lean) ·
mergeRunBare (Bare.lean) · LinkJoin.alikeFront_of_later
(Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean) · that each writing lays a later ledger:
K9L.drawn_later (Johnson/Desc/First/Batch/Law/FitsAtS.lean), OnPublicFiles.objects_later, planes_later
(Johnson/Top/H/K3LedgerKeeps.lean) with OnPublicFiles.seatCalls_fits, seatDigits_fits (K3SeatFits.lean),
Kinds.Head.Law.k6_join (Johnson/Desc/Kinds/Law/HeadRunsCarry.lean) with PscRun.paid_later,
Law.eq_later (Johnson/Desc/First/TailClaims/EquationsLater.lean), MergeLaw.claim_inv
(Johnson/Top/H0/MergeLaw/Run.lean) with PscRun.hideRun_keeps · Kinds.Head.Law.k6_same
(HeadRunsCarry.lean) · OnPublicFiles.objects_puts, planes_puts (Johnson/Top/H/Keep/RunsPutFork.lean) ·
LinkJoin.laterZ_of_laterS (Johnson/Desc/First/Link/Law/LaterStretch.lean) · LinkJoin.fork_putFork,
fork_putTl (SizedRides.lean) · LinkJoin.putFork_front, putTl_front (FrontStays.lean) ·
OnPublicFiles.planes_heard (Johnson/Top/H/Keep/K3Inv.lean) · Kinds.Head.Law.lookup_mem
(HeadRunsCarry.lean) · K9L.atS_reads (Johnson/Desc/First/Batch/Law/AtSLens.lean) · K9.get_fork
(Johnson/Desc/First/Batch/BlindK3.lean) · Law.eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean) · OnPublicFiles.look_set, look_putFork, look_putTl
(Johnson/Top/H/Keep/LookBlind.lean); and smaller ones.
TWO PAIRS ARE ONE BY UNFOLDING, AND LEAN's WORD FOR IT IS THIS FILE's: `NamesNot`
(Johnson/Desc/K8/Honest/NamesOff.lean), over which `OnlyArray` is made, and Kinds.Head.Law.NamesNot
(K6NamesNot.lean), in which that file's three lemmas end; Kinds.Head.asClaim
(Johnson/Stored/HeadAddsAtS.lean), at which the tie of the head's "join" stands, and K3Lot.ofForm
(Johnson/Desc/ProofFile/Lot/K3.lean), at which namesNot_joinCalls stands.
Limits. THE PREMISES ARE SHOWN OF NO STATE HERE. The ties are premises. That the array iU3 is the
one that the state's data name is not said.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LayersApart
import Johnson.Desc.K8.Honest.FallHead
import Johnson.Desc.Kinds.Law.K6NamesNot
import Johnson.Desc.K11.Live.Bare
import Johnson.Desc.First.Link.Law.PayHead
import Johnson.Desc.First.Link.Law.FrontStays
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.Desc.First.Link.Law.LaterStretch
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.PhiAll
import Johnson.Desc.First.LedgerLater
import Johnson.Desc.First.TailClaims.EquationsLater
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Batch.Law.AtSLens
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Top.H.K3LedgerKeeps
import Johnson.Top.H.K3SeatFits
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H0.MergeLaw.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- **What of the state the sentences on the head's segment's runs read, the ledger aside**: the six
fields that LinkJoin.frontSix gathers; what the lookup on the calls has heard; what the digits'
lookup has heard; what the head's merge has left (PhiAll.woOf). -/
def headKeep (u : S) :=
  (LinkJoin.frontSix u, u.lookHeard?, u.tl?.bind (·.heard), PhiAll.woOf u)

/-- What the head's merge has left rests under the laying of a ledger. -/
theorem wo_putFork (s : S) (G : Fork) : PhiAll.woOf (s.putFork G) = PhiAll.woOf s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putFork, PhiAll.woOf, hs, ho]
  | _ => simp [S.putFork, PhiAll.woOf, hs]

/-- It rests under the laying of the data. -/
theorem wo_putTl (s : S) (tl : HTailF2) : PhiAll.woOf (s.putTl tl) = PhiAll.woOf s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putTl, PhiAll.woOf, hs, ho]
  | _ => simp [S.putTl, PhiAll.woOf, hs]

/-- It rests under the laying of the link's context. -/
theorem wo_putLink (s : S) (L : LinkCtx) : PhiAll.woOf (s.putLink L) = PhiAll.woOf s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putLink, PhiAll.woOf, hs, ho]
  | _ => simp [S.putLink, PhiAll.woOf, hs]

/-- It rests under the batching's writing. -/
theorem wo_set (s : S) (q : K9.Part) : PhiAll.woOf (K9.atS.set s q) = PhiAll.woOf s := by
  show PhiAll.woOf ({ (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } : S) = _
  exact (wo_putFork (s.putLink q.L) q.F).trans (wo_putLink s q.L)

/-- The six fields rest under the laying of the link's context. -/
theorem front_putLink (s : S) (L : LinkCtx) :
    LinkJoin.frontSix (s.putLink L) = LinkJoin.frontSix s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putLink, LinkJoin.frontSix, hs, ho]
  | _ => simp [S.putLink, LinkJoin.frontSix, hs]

/-- They rest under the batching's writing. -/
theorem front_set (s : S) (q : K9.Part) :
    LinkJoin.frontSix (K9.atS.set s q) = LinkJoin.frontSix s := by
  show LinkJoin.frontSix
    ({ (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } : S) = _
  exact (LinkJoin.putFork_front (s.putLink q.L) q.F).trans (front_putLink s q.L)

/-- It rests under the laying of a ledger. -/
theorem headKeep_putFork (s : S) (G : Fork) : headKeep (s.putFork G) = headKeep s := by
  unfold headKeep
  rw [LinkJoin.putFork_front, OnPublicFiles.look_putFork, LinkJoin.tl_putFork', wo_putFork]

/-- It rests under the laying of the head's own ledger, opened or not. -/
theorem headKeep_head (s : S) (a : HeadOwn) (G : Fork) (h : s.here = .head a) :
    headKeep { s with here := .head { a with F := G } } = headKeep s := by
  simp only [headKeep, LinkJoin.frontSix, S.lookHeard?, S.tl?, PhiAll.woOf, h]

/-- It rests under the batching's draw. -/
theorem headKeep_drawn (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    headKeep t = headKeep s := by
  obtain ⟨a, x, o, -, -, -, rfl⟩ := drawnAt_ok p s t d h
  unfold headKeep
  rw [front_set, OnPublicFiles.look_set, set_tl, wo_set]

/-- It rests under what a yes of "K8.equations" writes. -/
theorem headKeep_k8 (u : S) (tl₀ tl₁ : HTailF2) (F₀ F₂ : Fork) (funs₀ : Array HFun)
    (k8 : List Claim) (n : Nat) (ht : u.tl? = some tl₀)
    (h : equations n tl₀ funs₀ F₀ = .ok (tl₁, F₂, k8)) :
    headKeep ((u.putTl tl₁).putFork F₂) = headKeep u := by
  have eH : tl₁.heard = tl₀.heard :=
    Law.eq_same (·.heard) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  rw [headKeep_putFork]
  unfold headKeep
  rw [LinkJoin.putTl_front, OnPublicFiles.look_putTl, wo_putTl, First.K8.putTl_tl u tl₀ tl₁ ht, ht]
  show (LinkJoin.frontSix u, u.lookHeard?, tl₁.heard, PhiAll.woOf u) =
    (LinkJoin.frontSix u, u.lookHeard?, tl₀.heard, PhiAll.woOf u)
  rw [eH]

/-- Laying a later ledger leaves a later state. -/
theorem laterS_putFork {u : S} {F G : Fork} (hF : u.fork? = some F) (hL : PscRun.Later F G) :
    LaterS u (u.putFork G) := fun F' hF' => by
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  exact ⟨G, LinkJoin.fork_putFork u F hF G, hL⟩

/-- **Behind the draw the ledger is a later one.** -/
theorem laterS_drawn (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    LaterS s t := fun F hF => by
  obtain ⟨a0, x0, o, ha0, -, hdc, rfl⟩ := drawnAt_ok p s t d h
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  obtain rfl : a0.F = F := Option.some.inj ((K9.get_fork s a0 ha0).symm.trans hF)
  exact ⟨o.F, by rw [K9.get_fork _ a' ha', hF'], (K9L.drawn_later _ _ _ _ _ _ _ hdc).1⟩

/-- **What is asked of the state in front of the head's segment's batching.** -/
structure HeadWants (h : Model.Head.Shape) (iU3 : Nat) (p6 : Kinds.Head.Par) (s : S) : Prop where
  calls : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  cEnd : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]
  leaves : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]
  digits : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  ok : p6.ok = true
  k6 : Kinds.Head.Law.K6HeardAt h iU3 p6 s
  head : ∃ o, s.here = .head o ∧ o.opened = true ∧ PscRun.Sized o.F
  merge : Johnson.Desc.First.ForkMerge.Live.MergeBare s

/-- The invariant: the fields are those of the state in front, and the ledger is a later one. -/
def HeadInv (s u : S) : Prop := headKeep u = headKeep s ∧ LaterS s u

/-- Under the invariant the state is alike the state in front, as the head's sentences ask. -/
theorem HeadInv.alike {h : Model.Head.Shape} {iU3 : Nat} {p6 : Kinds.Head.Par} {s u : S}
    (hs : HeadWants h iU3 p6 s) (hu : HeadInv s u) : Kinds.Head.Law.AlikeFront s u := by
  obtain ⟨o, ho, hop, hz⟩ := hs.head
  have e : LinkJoin.frontSix u = LinkJoin.frontSix s := congrArg (·.1) hu.1
  exact LinkJoin.alikeFront_of_later ⟨e, LinkJoin.laterZ_of_laterS hu.2⟩ ho hop hz

/-- Under the invariant the merge's condition is handed on. -/
theorem HeadInv.merge {h : Model.Head.Shape} {iU3 : Nat} {p6 : Kinds.Head.Par} {s u : S}
    (hs : HeadWants h iU3 p6 s) (hu : HeadInv s u) :
    Johnson.Desc.First.ForkMerge.Live.MergeBare u := by
  obtain ⟨a, wo, sv, rho, ha, hwo, hst⟩ := hs.merge
  have e : PhiAll.woOf u = PhiAll.woOf s := congrArg (·.2.2.2) hu.1
  have es : PhiAll.woOf s = some wo := by simp only [PhiAll.woOf, ha, hwo]
  rw [es] at e
  cases hh : u.here with
  | head a' =>
    have e' : a'.wo = some wo := by
      simp only [PhiAll.woOf, hh] at e
      exact e
    exact ⟨a', wo, sv, rho, hh, e', hst⟩
  | _ => simp [PhiAll.woOf, hh] at e

/-- A claim without an entry and without a run of entries. -/
theorem onlyArray_bare {n3 : Nat} {cl : Claim} (he : cl.form.ents = #[]) (hr : cl.runs = #[]) :
    OnlyArray n3 cl :=
  onlyArray_of hr fun x hx => by
    rw [he] at hx
    exact absurd hx (Array.not_mem_empty x)

/-- **THE EIGHT RUNS IN FRONT OF "K8.equations" AT THE HEAD's SEGMENT**: each keeps the invariant
and makes claims that name the array iU3 alone. -/
theorem head_pre_apart (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L h iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Kinds.Head.callerReaders (Kinds.Head.planesAt iU3))))
    (s : S) (hs : HeadWants h iU3 p6 s) :
    ∀ o ∈ headPre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      HeadInv s u → run m u = .ok (c, u') →
      (∀ cl ∈ c, OnlyArray iU3 cl) ∧ HeadInv s u' := by
  intro o ho run hat m u u' c hu hr
  have e1 : u.lookHeard? = s.lookHeard? := congrArg (·.2.1) hu.1
  have e2 : u.tl?.bind (·.heard) = s.tl?.bind (·.heard) := congrArg (·.2.2.1) hu.1
  have al := hu.alike hs
  have back : u' = u → HeadInv s u' := fun e => by rw [e]; exact hu
  have put : ∀ G, u' = u.putFork G → LaterS u u' → HeadInv s u' := fun G e k =>
    ⟨by rw [e]; exact (headKeep_putFork u G).trans hu.1, LaterS.trans s u u' hu.2 k⟩
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run', LinkJoin.At L (3, name) run' →
      run' m u = .ok (c, u') → (∀ cl ∈ c, OnlyArray iU3 cl) ∧ HeadInv s u' :=
    fun name hn run' hat' hr' => by
      obtain ⟨r, h0, hun⟩ := ties.tK6 name hn run' hat'
      have hy := hun _ _ _ _ hr'
      exact ⟨fun cl hcl t ht => by
        have q := Kinds.Head.Law.namesNot_run_front h iU3 p6 hs.ok l piece name r h0 hs.k6 al m c
          u' hy ht cl hcl
        exact ⟨q.1, q.2⟩,
        back (Kinds.Head.Law.k6_same h iU3 l piece p6 (name, r)
          (Kinds.Head.Law.lookup_mem _ _ _ h0) m u (c, u') hy)⟩
  simp only [headPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hy := tC run hat _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.objects_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls
      m u c u' hy
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatCalls K3Lot.ofForm)
      OnPublicFiles.k03_atS2_calls m u c u' hy (fun g hg => hs.calls g (e1 ▸ hg)) t cl hcl,
      put G e fun F hF => by
        obtain ⟨G', hG', -, hL⟩ := OnPublicFiles.objects_later (K3.seatCalls K3Lot.ofForm) (·.form)
          (OnPublicFiles.seatCalls_fits _ _ fun _ => rfl) (n := m) hF hy
        exact ⟨G', hG', hL⟩⟩
  · have hy := ties.tGuests 2 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, e⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj hy)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), back e.symm⟩
  · exact k6 "norm" (by simp) run hat hr
  · have hy := ties.tJoin run hat _ _ _ _ hr
    obtain ⟨F, g, hF, hg, e0⟩ := Kinds.Head.Law.k6_join _ m u (c, u') hy
    have e : u' = u.putFork (F.paid g.owedJoin) := e0
    refine ⟨fun cl hcl t ht => ProofFile.Honest.K3.Law.namesNot_joinCalls _ m u c u' hy
      (fun g' hg' => hs.cEnd g' (e1 ▸ hg')) t (fun KF hKF i hi x hx => ?_) cl hcl,
      put _ e (by rw [e]; exact laterS_putFork hF (PscRun.paid_later F _))⟩
    have hm : KF.getD i (Aff.ofConst zeroE) ∈ KF := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      exact Array.getElem_mem hi
    exact Kinds.Head.Law.namesNot_keys_front h iU3 p6 hs.ok hs.k6 al KF hKF ht _ hm x hx
  · exact k6 "policy" (by simp) run hat hr
  · obtain ⟨lm, hun⟩ := tP run hat
    have hy := hun _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.planes_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls lm _
      m u c u' hy
    obtain ⟨F, g, hF, hg⟩ := OnPublicFiles.planes_heard (K3.seatCalls K3Lot.ofForm) lm _ (i := m) hy
    exact ⟨fun cl hcl t ht => ProofFile.Honest.K3.Law.namesNot_planesCalls lm _ m u c u' hy
      (fun g' hg' => hs.leaves g' (e1 ▸ hg')) t
      (fun r hr' => (Kinds.Head.Law.namesNot_readers iU3 hr' ht).1)
      (fun r hr' => (Kinds.Head.Law.namesNot_readers iU3 hr' ht).2) cl hcl,
      put G e fun F' hF' => by
        obtain ⟨G', hG', -, hL⟩ := OnPublicFiles.planes_later (K3.seatCalls K3Lot.ofForm) (·.form)
          (OnPublicFiles.seatCalls_fits _ _ fun _ => rfl) lm _ (n := m) hF' hg hy
        exact ⟨G', hG', hL⟩⟩
  · have hy := tD run hat _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.objects_puts (K3.seatDigits K3Lot.ofForm) OnPublicFiles.k03_atS2_digits
      m u c u' hy
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatDigits K3Lot.ofForm)
      OnPublicFiles.k03_atS2_digits m u c u' hy (fun g hg => hs.digits g (e2 ▸ hg)) t cl hcl,
      put G e fun F hF => by
        obtain ⟨G', hG', -, hL⟩ := OnPublicFiles.objects_later (K3.seatDigits K3Lot.ofForm) (·.form)
          (OnPublicFiles.seatDigits_fits _ _ fun _ => rfl) (n := m) hF hy
        exact ⟨G', hG', hL⟩⟩
  · have hy := ties.tGuests 7 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, e⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj hy)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), back e.symm⟩

/-- **"K8.equations" itself keeps the invariant.** -/
theorem head_k8_keeps (s u : S) (tl₀ tl₁ : HTailF2) (F₀ F₂ : Fork) (funs₀ : Array HFun)
    (k8 : List Claim) (n : Nat) (hu : HeadInv s u) (hF : u.fork? = some F₀)
    (ht : u.tl? = some tl₀) (h : equations n tl₀ funs₀ F₀ = .ok (tl₁, F₂, k8)) :
    HeadInv s ((u.putTl tl₁).putFork F₂) :=
  ⟨(headKeep_k8 u tl₀ tl₁ F₀ F₂ funs₀ k8 n ht h).trans hu.1,
    LaterS.trans s u _ hu.2 fun F hF' => by
      obtain rfl : F₀ = F := Option.some.inj (hF.symm.trans hF')
      exact ⟨F₂, LinkJoin.fork_putFork _ F₀ ((LinkJoin.fork_putTl u tl₁).trans hF) F₂,
        Law.eq_later h⟩⟩

/-- **THE TWO RUNS BEHIND IT.** -/
theorem head_post_apart (L : Link S Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L h iU3 l piece p6 nU)
    (s : S) (hs : HeadWants h iU3 p6 s) :
    ∀ o ∈ headPost, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      HeadInv s u → run m u = .ok (c, u') →
      (∀ cl ∈ c, OnlyArray iU3 cl) ∧ HeadInv s u' := by
  intro o ho run hat m u u' c hu hr
  simp only [headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · obtain ⟨r, h0, hun⟩ := ties.tK6 "logits" (by simp) run hat
    have hy := hun _ _ _ _ hr
    have e : u' = u := Kinds.Head.Law.k6_same h iU3 l piece p6 ("logits", r)
      (Kinds.Head.Law.lookup_mem _ _ _ h0) m u (c, u') hy
    exact ⟨fun cl hcl t ht => by
      have q := Kinds.Head.Law.namesNot_run_front h iU3 p6 hs.ok l piece "logits" r h0 hs.k6
        (hu.alike hs) m c u' hy ht cl hcl
      exact ⟨q.1, q.2⟩, by rw [e]; exact hu⟩
  · have hy := ties.tMerge run hat _ _ _ _ hr
    obtain ⟨q, -⟩ := Johnson.Desc.First.ForkMerge.Live.mergeRunBare m u (c, u') (hu.merge hs) hy
    obtain ⟨a, wo, G, ha, -, e, -, hG⟩ := MergeLaw.claim_inv hy
    refine ⟨fun cl hcl => onlyArray_bare (q cl hcl).1 (q cl hcl).2, ?_, ?_⟩
    · rw [e]
      exact (headKeep_head u a G ha).trans hu.1
    · refine LaterS.trans s u u' hu.2 fun F hF => ?_
      rw [e]
      have hop : a.opened = true ∧ a.F = F := by
        simp only [S.fork?, ha] at hF
        split at hF
        · exact ⟨by assumption, Option.some.inj hF⟩
        · exact nomatch hF
      exact ⟨G, by simp [S.fork?, hop.1], hop.2 ▸ PscRun.hideRun_keeps hG⟩

end P1K8

#print axioms P1K8.wo_putFork
#print axioms P1K8.wo_putTl
#print axioms P1K8.wo_putLink
#print axioms P1K8.wo_set
#print axioms P1K8.front_putLink
#print axioms P1K8.front_set
#print axioms P1K8.headKeep_putFork
#print axioms P1K8.headKeep_head
#print axioms P1K8.headKeep_drawn
#print axioms P1K8.headKeep_k8
#print axioms P1K8.laterS_putFork
#print axioms P1K8.laterS_drawn
#print axioms P1K8.HeadInv.alike
#print axioms P1K8.HeadInv.merge
#print axioms P1K8.onlyArray_bare
#print axioms P1K8.head_pre_apart
#print axioms P1K8.head_k8_keeps
#print axioms P1K8.head_post_apart
#print axioms P1K8.headKeep
#print axioms P1K8.HeadWants
#print axioms P1K8.HeadInv
