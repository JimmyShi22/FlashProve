-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LayersApart.lean: THE SMALLNESS TEST: AT A LAYERS' SEGMENT: EACH RUN OF CLAIMS BUT
"K8.equations" KEEPS THREE FIELDS OF THE STATE AND MAKES CLAIMS THAT NAME ONE ARRAY ALONE, FROM
THREE PREMISES ON THE STATE IN FRONT OF THE BATCHING. Definitions and lemmas; none of the library's
goals. No prover stands in them; nothing on completeness, soundness or hiding. Two of the files that
it imports lie by path under the honest side's folder:
Johnson/Desc/ProofFile/Honest/K3/Law/NamesKept.lean,
Johnson/Desc/ProofFile/Honest/K4/Law/RunsName.lean: laws on which arrays the claims of a run name.

  `OnlyArray n3 cl`, `onlyArray_of`   the claim names no entry and no run of entries of any array
      but n3 (`NamesNot`, Johnson/Desc/K8/Honest/NamesOff.lean, at every other array); so a claim
      without a run whose form's entries all lie in n3
  `layKeep u`   what the lookup on the calls has heard; what the digits' lookup has heard; what the
      layers' own rounds have heard
  `own_set`, `layKeep_putFork`, `layKeep_wrote`, `layKeep_drawn`, `layKeep_k8`   it rests under the
      laying of a ledger; under what a run of the layers' own kind writes
      (OnBytes.Desc.First.K4.wrote_reads, Johnson/Desc/First/K4/ReadsAtS.lean, has the third
      component; all three are shown here at once); under the batching's draw; under what a yes of
      "K8.equations" writes. LinkJoin.FieldRests (Johnson/Desc/First/Link/Law/KeepsAny.lean) is not
      called: the second component does not rest under the laying of ANY data
  `LayAsks p4 n3 s`, `LayAsks.of_keep`, `own_of_runsPre`   the three premises; they read the state
      through `layKeep` alone; the third, at the array that the state's data name, is
      ProofFile.Honest.K4.RunsPre
  **`lay_pre`**, **`lay_post`**   the sentence of the title, at the five entries of the order in
      front of "K8.equations" and at the one behind. THE RUNS ARE OPENED BY THE TIES AS IN THE PROOF
      OF LinkJoin.keeps_layers (KeepsAny.lean) and of `plain_layers`
      (Johnson/Desc/K8/Honest/CountFrom.lean)
By: ProofFile.Honest.K3.Law.namesNot_objects (NamesKept.lean) · ProofFile.Honest.K4.front_names, back_names
(RunsName.lean) · OnPublicFiles.objects_puts (Johnson/Top/H/Keep/RunsPutFork.lean) · OnPublicFiles.look_set,
look_putFork, look_putTl (LookBlind.lean) · LinkJoin.putFork_own, putLink_own
(Johnson/Desc/First/Link/Law/StretchParts.lean) · LinkJoin.tl_putFork' (TotalMoves.lean) ·
First.K8.putTl_own (Johnson/Desc/First/K8/LawFunsStay.lean) · First.K8.putTl_tl (LawAtS.lean) ·
frontAtC, backAtC (Johnson/Desc/First/K4/RunsAtC.lean) · `set_tl`, `drawnAt_ok`
(Johnson/Desc/K8/Honest/GathersPlain.lean, FallDraw.lean) · eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean).
Limits. THE THREE PREMISES ARE SHOWN OF NO STATE HERE. The ties are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.NamesOff
import Johnson.Desc.K8.Honest.GathersPlain
import Johnson.Desc.ProofFile.Honest.K3.Law.NamesKept
import Johnson.Desc.ProofFile.Honest.K4.Law.RunsName
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.Link.Law.TotalMoves
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.Desc.First.K8.LawAtS
import Johnson.Top.H.Keep.RunsPutFork
import Johnson.Top.H.Keep.LookBlind
import Johnson.Desc.First.TailClaims.EquationsCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest

/-- The claim names no entry and no run of entries of any array but n3. -/
def OnlyArray (n3 : Nat) (cl : Claim) : Prop := ∀ t, t ≠ n3 → NamesNot t cl

/-- A claim without a run of entries whose form's entries all lie in array n3. -/
theorem onlyArray_of {n3 : Nat} {cl : Claim} (hr : cl.runs = #[])
    (he : ∀ x ∈ cl.form.ents, x.tree = n3) : OnlyArray n3 cl := fun t ht =>
  ⟨fun x hx e => ht (e.symm.trans (he x hx)), fun u hu => by
    rw [hr] at hu
    exact absurd hu (Array.not_mem_empty u)⟩

/-- **What of the state the sentences on a layers' segment's runs read**: what the lookup on the
calls has heard; what the digits' lookup has heard; what the layers' own rounds have heard. -/
def layKeep (u : S) : Option Forest.Heard × Option Forest.Heard × Option Layer.Own :=
  (u.lookHeard?, u.tl?.bind (·.heard), u.own?)

/-- What the layers' own rounds have heard rests under the batching's writing. -/
theorem own_set (s : S) (q : K9.Part) : (K9.atS.set s q).own? = s.own? := by
  show ({ (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } : S).own? = _
  exact (LinkJoin.putFork_own (s.putLink q.L) q.F).trans (LinkJoin.putLink_own s q.L)

/-- It rests under the laying of a ledger. -/
theorem layKeep_putFork (s : S) (G : Fork) : layKeep (s.putFork G) = layKeep s := by
  unfold layKeep
  rw [OnPublicFiles.look_putFork, LinkJoin.tl_putFork', LinkJoin.putFork_own]

/-- It rests under what a run of the layers' own kind writes. -/
theorem layKeep_wrote {e e₁ : S} {a : LayOwn} {G : Fork}
    (h : OnBytes.Desc.First.K4.Wrote e a G e₁) : layKeep e₁ = layKeep e := by
  obtain ⟨h1, rfl⟩ := h
  simp only [layKeep, S.lookHeard?, S.tl?, S.own?, h1]

/-- It rests under the batching's draw. -/
theorem layKeep_drawn (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    layKeep t = layKeep s := by
  obtain ⟨a, x, o, -, -, -, rfl⟩ := drawnAt_ok p s t d h
  unfold layKeep
  rw [OnPublicFiles.look_set, set_tl, own_set]

/-- It rests under what a yes of "K8.equations" writes. -/
theorem layKeep_k8 (u : S) (tl₀ tl₁ : HTailF2) (F₀ F₂ : Fork) (funs₀ : Array HFun)
    (k8 : List Claim) (n : Nat) (ht : u.tl? = some tl₀)
    (h : equations n tl₀ funs₀ F₀ = .ok (tl₁, F₂, k8)) :
    layKeep ((u.putTl tl₁).putFork F₂) = layKeep u := by
  have eH : tl₁.heard = tl₀.heard :=
    Law.eq_same (·.heard) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  rw [layKeep_putFork]
  unfold layKeep
  rw [OnPublicFiles.look_putTl, First.K8.putTl_own, First.K8.putTl_tl u tl₀ tl₁ ht, ht]
  show (u.lookHeard?, tl₁.heard, u.own?) = (u.lookHeard?, tl₀.heard, u.own?)
  rw [eH]

/-- **What is asked of the state in front of a layers' segment's batching**: the rows that the two
lookups have heard name no entry; what the layers' own rounds have heard meets the condition of the
layers' sentences at the array n3. -/
structure LayAsks (p4 : OnBytes.Desc.First.K4.Par) (n3 : Nat) (s : S) : Prop where
  calls : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  digits : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  own : ∀ o, s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o n3

/-- The condition reads the state through `layKeep` alone. -/
theorem LayAsks.of_keep {p4 : OnBytes.Desc.First.K4.Par} {n3 : Nat} {s u : S}
    (h : LayAsks p4 n3 s) (e : layKeep u = layKeep s) : LayAsks p4 n3 u := by
  have e1 : u.lookHeard? = s.lookHeard? := congrArg (·.1) e
  have e2 : u.tl?.bind (·.heard) = s.tl?.bind (·.heard) := congrArg (·.2.1) e
  have e3 : u.own? = s.own? := congrArg (·.2.2) e
  exact ⟨fun g hg => h.calls g (e1 ▸ hg), fun g hg => h.digits g (e2 ▸ hg),
    fun o ho => h.own o (e3 ▸ ho)⟩

/-- **THE RUNS IN FRONT OF "K8.equations" AT A LAYERS' SEGMENT**: each keeps `layKeep` and makes
claims that name array n3 alone. -/
theorem lay_pre (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (n3 : Nat) (s : S) (hs : LayAsks p4 n3 s) :
    ∀ o ∈ [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")],
      ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      layKeep u = layKeep s → run m u = .ok (c, u') →
      (∀ cl ∈ c, OnlyArray n3 cl) ∧ layKeep u' = layKeep s := by
  intro o ho run hat m u u' c hu hr
  have hU := hs.of_keep hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · have h := tC run hat _ _ _ _ hr
    obtain ⟨G, rfl⟩ := OnPublicFiles.objects_puts (K3.seatCalls K3Lot.ofForm) OnPublicFiles.k03_atS2_calls
      m u c u' h
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatCalls K3Lot.ofForm)
      OnPublicFiles.k03_atS2_calls m u c _ h hU.calls t cl hcl, (layKeep_putFork u G).trans hu⟩
  · have h := ties.tGuests 1 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, rfl⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj h)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), hu⟩
  · obtain ⟨r, h0, hun⟩ := ties.tFront run hat
    have h := hun _ _ _ _ hr
    obtain ⟨a, _, _, G, _, _, _, hw⟩ := OnBytes.Desc.First.K4.frontAtC h0 h
    exact ⟨fun cl hcl => by
      obtain ⟨q1, q2⟩ := ProofFile.Honest.K4.front_names h0 h hU.own cl hcl
      exact onlyArray_of q1 q2, (layKeep_wrote hw).trans hu⟩
  · have h := tD run hat _ _ _ _ hr
    obtain ⟨G, rfl⟩ := OnPublicFiles.objects_puts (K3.seatDigits K3Lot.ofForm) OnPublicFiles.k03_atS2_digits
      m u c u' h
    exact ⟨fun cl hcl t _ => ProofFile.Honest.K3.Law.namesNot_objects (K3.seatDigits K3Lot.ofForm)
      OnPublicFiles.k03_atS2_digits m u c _ h hU.digits t cl hcl, (layKeep_putFork u G).trans hu⟩
  · have h := ties.tGuests 6 (by simp) run hat _ _ _ _ hr
    obtain ⟨rfl, rfl⟩ : [] = c ∧ u = u' := Prod.mk.inj (Except.ok.inj h)
    exact ⟨fun cl hcl => absurd hcl (List.not_mem_nil), hu⟩

/-- **THE RUN BEHIND IT.** -/
theorem lay_post (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU) (n3 : Nat) (s : S) (hs : LayAsks p4 n3 s) :
    ∀ o ∈ [(2, "back")], ∀ run, LinkJoin.At L o run →
      ∀ (m : Nat) (u u' : S) (c : List Claim), layKeep u = layKeep s → run m u = .ok (c, u') →
      (∀ cl ∈ c, OnlyArray n3 cl) ∧ layKeep u' = layKeep s := by
  intro o ho run hat m u u' c hu hr
  have hU := hs.of_keep hu
  obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
  obtain ⟨r, h0, hun⟩ := ties.tBack run hat
  have h := hun _ _ _ _ hr
  obtain ⟨a, _, _, G, _, _, _, hw⟩ := OnBytes.Desc.First.K4.backAtC h0 h
  exact ⟨fun cl hcl => by
    obtain ⟨q1, q2⟩ := ProofFile.Honest.K4.back_names h0 h hU.own cl hcl
    exact onlyArray_of q1 q2, (layKeep_wrote hw).trans hu⟩

/-- The third premise at the array that the state's own data name as the third array of reads is the
layers' sentences' own hypothesis (ProofFile.Honest.K4.RunsPre,
Johnson/Desc/ProofFile/Honest/K4/Law/RunsName.lean). -/
theorem own_of_runsPre {p4 : OnBytes.Desc.First.K4.Par} {s : S} {tl : HTailF2}
    (h : ProofFile.Honest.K4.RunsPre p4 s) (ht : s.tl? = some tl) :
    ∀ o, s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o ((tl.ix.U.getD 2 none).getD 0) :=
  fun o ho => h tl o ht ho

end P1K8

#print axioms P1K8.onlyArray_of
#print axioms P1K8.own_set
#print axioms P1K8.layKeep_putFork
#print axioms P1K8.layKeep_wrote
#print axioms P1K8.layKeep_drawn
#print axioms P1K8.layKeep_k8
#print axioms P1K8.LayAsks.of_keep
#print axioms P1K8.lay_pre
#print axioms P1K8.lay_post
#print axioms P1K8.own_of_runsPre
#print axioms P1K8.OnlyArray
#print axioms P1K8.layKeep
#print axioms P1K8.LayAsks
