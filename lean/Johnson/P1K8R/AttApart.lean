-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AttApart.lean: THE SMALLNESS TEST: AT AN ATTENTION SEGMENT: EACH OF THE NINE RUNS OF
CLAIMS IN FRONT OF "K8.equations" KEEPS AN INVARIANT AND MAKES CLAIMS THAT NAME THE PLAN's ARRAY OF
THE READS ALONE, FROM PREMISES ON THE STATE IN FRONT OF THE BATCHING. Definitions and lemmas; none
of the library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `attKeep u`, `heard5_set`, `attKeep_putFork`, `attKeep_drawn`   what the lookup on the calls, the
      digits' lookup and the segment's own rounds have heard; it rests under the laying of a ledger
      and under the batching's draw
  `AttLedger A Kc u`, `u3At_trees`, `attLedger_own`, `attLedger_run`, `u3At_fill`,
  `attLedger_drawn`   the ledger's clause: the state stands in an attention segment, the batching
      finds its part there, and that ledger has the plan's array of the reads (Att.P.U3At,
      Johnson/Desc/First/Att/K05EntsOf.lean). No function of the state that rests under the laying
      of ANY ledger says this: it is carried run by run, by `PlainRun`'s field on the ledger
      (Johnson/Desc/K8/Honest/PlainRuns.lean), and across the draw by K9L.fill_looks
      (Johnson/Desc/First/Batch/Law/FitsAtS.lean)
  `AttAsks s`, `AttAsks.of_keep`, `AttInv A s u`   five premises on the state in front, which read
      it through `attKeep` alone; the invariant: `attKeep` is that state's, and the ledger's clause
  **`att_pre_apart`**   the sentence of the title. THE RUNS ARE OPENED BY THE TIES AS IN THE PROOF
      OF LinkJoin.keeps_attention (Johnson/Desc/First/Link/Law/KeepsAny.lean) and of `att_pre`
      (Johnson/Desc/K8/Honest/FallAtt.lean), which is also called
By: H2K5.Honest.first_namesOnly, second_namesOnly, keys_none, keys_tree, readers_tree
(NamesOnly.lean) · ProofFile.Honest.K3.Law.namesNot_objects, namesNot_joinCalls, namesNot_planesCalls
(NamesKept.lean) · OnPublicFiles.objects_puts, join_puts, planes_puts
(Johnson/Top/H/Keep/RunsPutFork.lean) · K5Law.runOfForms_hands
(Johnson/Desc/First/Att/Claims/RunsHand.lean) · K5Law.heard5_putFork, heard5_putLink (WalkK5.lean) ·
OnPublicFiles.look_set, look_putFork (Johnson/Top/H/Keep/LookBlind.lean) · `OnlyArray`, `onlyArray_of`
(LayersApart.lean) · `drawnAt_ok`, `drawn_trees` (Johnson/Desc/K8/Honest/FallDraw.lean) ·
K9L.atS_reads (Johnson/Desc/First/Batch/Law/AtSLens.lean).
Limits. THE PREMISES ARE SHOWN OF NO STATE HERE. The ties are premises. That the plan's array of the
reads is the one that the state's data name is not said.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LayersApart
import Johnson.Desc.K8.Honest.FallAtt
import Johnson.Desc.K5.Honest.Law.NamesOnly
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Att.Claims.WalkK5
import Johnson.Desc.First.Att.Claims.RunsHand
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Att.K05EntsOf
import Johnson.Desc.First.Att.K05PublicB
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Batch.Law.AtSLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- **What of the state the sentences on an attention segment's runs read, the ledger aside**: what
the lookup on the calls has heard; what the digits' lookup has heard; what the segment's own rounds
have heard. -/
def attKeep (u : S) : Option Forest.Heard × Option Forest.Heard × Option Att.P.Heard :=
  (u.lookHeard?, u.tl?.bind (·.heard), u.heard5?)

/-- What the segment's own rounds have heard rests under the batching's writing. -/
theorem heard5_set (s : S) (q : K9.Part) : (K9.atS.set s q).heard5? = s.heard5? := by
  show ({ (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } : S).heard5? = _
  exact (K5Law.heard5_putFork (s.putLink q.L) q.F).trans (K5Law.heard5_putLink s q.L)

/-- It rests under the laying of a ledger. -/
theorem attKeep_putFork (s : S) (G : Fork) : attKeep (s.putFork G) = attKeep s := by
  unfold attKeep
  rw [OnPublicFiles.look_putFork, LinkJoin.tl_putFork', K5Law.heard5_putFork]

/-- It rests under the batching's draw. -/
theorem attKeep_drawn (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    attKeep t = attKeep s := by
  obtain ⟨a, x, o, -, -, -, rfl⟩ := drawnAt_ok p s t d h
  unfold attKeep
  rw [OnPublicFiles.look_set, set_tl, heard5_set]

/-- **The ledger's clause**: the state stands in an attention segment; the batching finds its part
there; the ledger has the plan's array of the reads, of one row, at width Kc. -/
def AttLedger (A : Attention.Plan) (Kc : Nat) (u : S) : Prop :=
  ∃ (a : AttOwn) (x : K9.Part), u.here = .att a ∧ K9.atS.get? u = some x ∧ Att.P.U3At A Kc x.F

/-- The condition on the ledger reads its arrays alone. -/
theorem u3At_trees {A : Attention.Plan} {Kc : Nat} {F G : Fork} (e : G.trees = F.trees)
    (h : Att.P.U3At A Kc F) : Att.P.U3At A Kc G := by
  unfold Att.P.U3At at h ⊢
  rw [e]
  exact h

/-- At such a state the open segment's own ledger has the array. -/
theorem attLedger_own {A : Attention.Plan} {Kc : Nat} {u : S} (h : AttLedger A Kc u) :
    ∃ a : AttOwn, u.here = .att a ∧ Att.P.U3At A Kc a.F := by
  obtain ⟨a, x, ha, hx, hU⟩ := h
  have e1 : u.fork? = some x.F := K9.get_fork u x hx
  have e2 : u.fork? = some a.F := by simp [S.fork?, ha]
  obtain e : x.F = a.F := Option.some.inj (e1.symm.trans e2)
  exact ⟨a, ha, e ▸ hU⟩

/-- **A run that is free of the batching element and lays at most a ledger keeps the clause.** -/
theorem attLedger_run {A : Attention.Plan} {Kc : Nat}
    {f : Nat → S → Except String (List Claim × S)} (hp : PlainRun f) {n : Nat} {u : S}
    {y : List Claim × S} (hy : f n u = .ok y) (hw : y.2 = u ∨ ∃ G, y.2 = u.putFork G)
    (h : AttLedger A Kc u) : AttLedger A Kc y.2 := by
  obtain ⟨a, x, ha, hx, hU⟩ := h
  obtain ⟨b, hb, ss⟩ := hp.ledger n u y x hy hx
  have hh : ∃ a' : AttOwn, y.2.here = .att a' := by
    rcases hw with e | ⟨G, e⟩
    · exact ⟨a, by rw [e]; exact ha⟩
    · exact ⟨{ a with F := G }, by rw [e]; simp [S.putFork, ha]⟩
  obtain ⟨a', ha'⟩ := hh
  exact ⟨a', b, ha', hb, u3At_trees ss.trees hU⟩

/-- The draw keeps the clause's last part: it fills weights; the arrays' numbers of rows and of
columns stay. -/
theorem u3At_fill {A : Attention.Plan} {Kc : Nat} {F : Fork} (T : Tail2)
    (h : Att.P.U3At A Kc F) : Att.P.U3At A Kc (t2FillL F T) := by
  obtain ⟨X, hX, hK, hW, hR⟩ := h
  have e := congrArg (fun a : Array LinkJoin.Look => a[A.iU3]?) (K9L.fill_looks F T)
  simp only [Array.getElem?_map, hX, Option.map_some] at e
  obtain ⟨Y, hY, eY⟩ := Option.map_eq_some_iff.1 e
  have kR : Y.R = X.R := congrArg (·.2.1) eY
  have kK : Y.K = X.K := congrArg (·.2.2.1) eY
  exact ⟨Y, hY, kK.trans hK, by rw [kK]; exact hW, kR.trans hR⟩

/-- **Behind the draw the clause holds, where the state in front stands in an attention segment and
its ledger has the array.** -/
theorem attLedger_drawn {A : Attention.Plan} {Kc : Nat} (p : K9.Where) (s t : S) (d : Fmt.Drawn)
    (h : drawnAt p s d = .ok t) (a : AttOwn) (ha : s.here = .att a)
    (hU : Att.P.U3At A Kc a.F) : AttLedger A Kc t := by
  obtain ⟨a0, x0, o, ha0, -, hdc, rfl⟩ := drawnAt_ok p s t d h
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have e1 : s.fork? = some a0.F := K9.get_fork s a0 ha0
  have e2 : s.fork? = some a.F := by simp [S.fork?, ha]
  obtain e : a0.F = a.F := Option.some.inj (e1.symm.trans e2)
  refine ⟨{ { a with L := o.L } with F := o.F }, a', ?_, ha', ?_⟩
  · show ({ (s.putLink o.L).putFork o.F with st := a0.d.st, rowsOwed := o.owed } : S).here = _
    simp [S.putFork, S.putLink, ha]
  · rw [hF']
    refine u3At_trees (drawn_trees _ _ _ _ _ _ _ hdc) ?_
    rw [e]
    exact u3At_fill _ hU

/-- **What is asked of the state in front of an attention segment's batching.** -/
structure AttAsks (s : S) : Prop where
  calls : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  cEnd : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]
  leaves : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]
  digits : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  five : ∃ hd, s.heard5? = some hd ∧ K5Law.HeardPlain hd

/-- The condition reads the state through `attKeep` alone. -/
theorem AttAsks.of_keep {s u : S} (h : AttAsks s) (e : attKeep u = attKeep s) : AttAsks u := by
  have e1 : u.lookHeard? = s.lookHeard? := congrArg (·.1) e
  have e2 : u.tl?.bind (·.heard) = s.tl?.bind (·.heard) := congrArg (·.2.1) e
  have e3 : u.heard5? = s.heard5? := congrArg (·.2.2) e
  exact ⟨fun g hg => h.calls g (e1 ▸ hg), fun g hg => h.cEnd g (e1 ▸ hg),
    fun g hg => h.leaves g (e1 ▸ hg), fun g hg => h.digits g (e2 ▸ hg), e3 ▸ h.five⟩

/-- The invariant. -/
def AttInv (A : Attention.Plan) (s u : S) : Prop :=
  attKeep u = attKeep s ∧ AttLedger A (Att.P.plannedK A) u

/-- **THE NINE RUNS IN FRONT OF "K8.equations" AT AN ATTENTION SEGMENT**: each keeps the invariant
and makes claims that name the plan's array of the reads alone. -/
theorem att_pre_apart (L : Link S Claim) (A : Attention.Plan) (nU : Array Nat)
    (ties : LinkJoin.AttTies L (Att.P.parCOf A) nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run → LinkJoin.Under run
      (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run → ∃ lm, LinkJoin.Under run
      (K9.planesCalls lm (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (s : S) (hs : AttAsks s) :
    ∀ o ∈ attPre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      AttInv A s u → run m u = .ok (c, u') →
      (∀ cl ∈ c, OnlyArray A.iU3 cl) ∧ AttInv A s u' := by
  intro o ho run hat m u u' c hu hr
  have hU := hs.of_keep hu.1
  obtain ⟨hd, h5, hpl⟩ := hU.five
  obtain ⟨f, hun, hp⟩ := att_pre L (Att.P.parCOf A) nU ties tC tD tJ tP o ho run hat
  have hf := hun _ _ _ _ hr
  have back : u' = u → AttInv A s u' := fun e =>
    ⟨by rw [e]; exact hu.1, attLedger_run hp hf (Or.inl e) hu.2⟩
  have put : ∀ G, u' = u.putFork G → AttInv A s u' := fun G e =>
    ⟨by rw [e]; exact (attKeep_putFork u G).trans hu.1, attLedger_run hp hf (Or.inr ⟨G, e⟩) hu.2⟩
  have only : ∀ cl : Claim, H2K5.Honest.NamesOnly A.iU3 cl → OnlyArray A.iU3 cl := fun cl q =>
    onlyArray_of q.1 fun x hx => q.2 x (Array.mem_toList_iff.2 hx)
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := tC run hat _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.objects_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls
      m u c u' h
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatCalls K3Lot.ofForm)
      OnPublicFiles.k03_atS2_calls m u c u' h hU.calls t cl hcl, put G e⟩
  · have h := ties.tGuests 1 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, e⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj h)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), back e.symm⟩
  · have h := ties.tFirst run hat _ _ _ _ hr
    exact ⟨fun cl hcl => only cl (H2K5.Honest.first_namesOnly A h5 hpl h cl hcl),
      back (K5Law.runOfForms_hands _ _ _ (K5Law.rFirst_mem _) m u c u' h).1⟩
  · have h := ties.tKeys run hat _ _ _ _ hr
    have e0 : c = [] := H2K5.Honest.keys_none A h
    exact ⟨fun cl hcl => by rw [e0] at hcl; exact absurd hcl (List.not_mem_nil),
      back (K5Law.runOfForms_hands _ _ _ (K5Law.rKeys_mem _) m u c u' h).1⟩
  · have h := tJ run hat _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.join_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls _
      m u c u' h
    refine ⟨fun cl hcl t ht => ProofFile.Honest.K3.Law.namesNot_joinCalls _ m u c u' h hU.cEnd t
      (fun KF hKF i hi x hx e3 => ht ?_) cl hcl, put G e⟩
    have hm : KF.getD i (Aff.ofConst zeroE) ∈ KF.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    exact e3.symm.trans (H2K5.Honest.keys_tree A h5 hpl hKF _ hm x (Array.mem_toList_iff.2 hx))
  · have h := ties.tSecond run hat _ _ _ _ hr
    exact ⟨fun cl hcl => only cl (H2K5.Honest.second_namesOnly A h5 hpl h cl hcl),
      back (K5Law.runOfForms_hands _ _ _ (K5Law.rSecond_mem _) m u c u' h).1⟩
  · obtain ⟨lm, hun'⟩ := tP run hat
    have h := hun' _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.planes_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls lm _
      m u c u' h
    obtain ⟨a₀, ha₀, hU3⟩ := attLedger_own hu.2
    refine ⟨fun cl hcl t ht => ProofFile.Honest.K3.Law.namesNot_planesCalls lm _ m u c u' h hU.leaves t
      (fun r hr' e' col f' hf' x hx e3 => ht ?_) (fun r hr' col f' hf' x hx e3 => ht ?_) cl hcl,
      put G e⟩
    · exact e3.symm.trans (((H2K5.Honest.readers_tree A ha₀ hU3 hr').1 e' col f' hf' x
        (Array.mem_toList_iff.2 hx)).1)
    · exact e3.symm.trans (((H2K5.Honest.readers_tree A ha₀ hU3 hr').2 col f' hf' x
        (Array.mem_toList_iff.2 hx)).1)
  · have h := tD run hat _ _ _ _ hr
    obtain ⟨G, e⟩ := OnPublicFiles.objects_puts (K3.seatDigits K3Lot.ofForm) OnPublicFiles.k03_atS2_digits
      m u c u' h
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatDigits K3Lot.ofForm)
      OnPublicFiles.k03_atS2_digits m u c u' h hU.digits t cl hcl, put G e⟩
  · have h := ties.tGuests 6 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, e⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj h)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), back e.symm⟩

end P1K8

#print axioms P1K8.heard5_set
#print axioms P1K8.attKeep_putFork
#print axioms P1K8.attKeep_drawn
#print axioms P1K8.u3At_trees
#print axioms P1K8.attLedger_own
#print axioms P1K8.attLedger_run
#print axioms P1K8.u3At_fill
#print axioms P1K8.attLedger_drawn
#print axioms P1K8.AttAsks.of_keep
#print axioms P1K8.att_pre_apart
#print axioms P1K8.attKeep
#print axioms P1K8.AttLedger
#print axioms P1K8.AttAsks
#print axioms P1K8.AttInv
