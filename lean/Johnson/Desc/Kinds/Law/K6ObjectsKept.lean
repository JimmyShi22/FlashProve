-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6ObjectsKept.lean: ONE PUBLIC TEST OF THE TABLE'S PROMISE IS KEPT ACROSS AN
ACCEPT OF THE OUTPUT HEAD'S SUB-PROTOCOL, AT THE COMPOSED MEANING mgAll D Mg
(Johnson/Desc/Sound/MgAll.lean), AT THE FULL CHAIN: the test formsInT 24 3 "objects": "the readers
of the lookup's runs (2, "objects") and (2, "guests") answer, and each form names only what is
there".
It is tied to the claim formsT 24 3 "objects", which stays open across place 341: so the promise
behind asks it again.

HOW. Another file's rule formsInT_on (Johnson/Desc/Sound/FormsT.lean) carries the test from
an earlier state of a segment to a later one, where the reader gives ONE answer at both. That it
answers behind is the weight: the reader is the run itself, called at the state
(Johnson/Desc/First/Batch/ReaderOf.lean).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  readerOf_objects_on, readerOf_guests_on: where a ledger is open (for "objects" also: something is
      heard, and no kept row names an entry of an array), the run's reader ANSWERS keptOf.
  readers_kept_on: so does the segment's reader.
  kept_on: the test at one of the two names goes forward over the turning of the head's ledger, of
      what it has heard and of its sumcheck.
  kept_objects: THE CLAUSE: the public test behind an accept of the piece at place 341.

Every letter under "there is": none in this file's statements.
For-all letters that one premise alone reads: small, P8 (hreaders); bef, B, bS (Hs).

What it does not say. THAT ITS PREMISES CAN BE MET TOGETHER: NO EXAMPLE. hruns, hback
(Johnson/Desc/Kinds/Law/ObjectsStates.lean, ObjectsBack.lean: on the IOP as written in Lean), hobj
(an equation on the meaning's parameters), hbare (on the verifier's state in front: no row that the
lookup on the calls keeps names an entry) and hled (the promise's test on the ledger's sizes, in
front) are premises. WHY hbare: the reader answers only where every entry of every form passes a
test at the ledger at hand, which behind the accept is the later ledger; that the sub-protocol
leaves the arrays' numbers of rows is said by no law here; where no entry is named the test is
empty. THE FULL CHAIN ALONE. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6RidersAtMgAll
import Johnson.Desc.Kinds.Law.ObjectsBack
import Johnson.Desc.Kinds.Law.GrowsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning HeadOwn)
open VerifiableInference.Desc.K9 (RunOf readerOf lateOf readersOfLink statesOfLink segAt? formsInT)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ linksFull MgData mgAll formsInT_on
  onParts_of_on)

/-! ## 1 The reader answers -/

theorem readerOf_objects_on {states : ℕ → List (RunOf S)} {b : ℕ}
    {run : ℕ → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == "objects") = some ("objects", run))
    (hu : ∀ k t y, K9.objectsCalls k t = .ok y → run k t = .ok y) (t : S) (F : Fork)
    (g : Model.Forest.Heard) (hF : t.fork? = some F) (hg : t.lookHeard? = some g)
    (hbare : ∀ f ∈ g.rows.toList, f.ents = #[]) :
    readerOf states b "objects" t = keptOf "objects" t.lookHeard? := by
  have h0 : K9.objectsCalls 0 t = .ok (g.rows.toList.map (fun a => ({ form := a } : Claim)),
      t.putFork (F.paid g.owedObjects)) := by
    simp [K9.objectsCalls, K9.objectsBy, hF, hg, named, bind, Except.bind, pure, Except.pure]
  have h1 := hu 0 t _ h0
  have hall : ((g.rows.toList.map (fun a => ({ form := a } : Claim))).all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow F)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hc
    simp [hbare f hf']
  unfold readerOf
  rw [hf]
  simp only [Option.bind_some, h1, hF, S.fork_putFork t F _ hF, lateOf_paid, hall, if_true]
  simp [keptOf, hg, List.map_map, Function.comp_def]

theorem readerOf_guests_on {states : ℕ → List (RunOf S)} {b : ℕ}
    {run : ℕ → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == "guests") = some ("guests", run))
    (hu : ∀ k t y, K9.guestsNone k t = .ok y → run k t = .ok y) (t : S) (F : Fork)
    (hF : t.fork? = some F) : readerOf states b "guests" t = keptOf "guests" t.lookHeard? := by
  have h1 := hu 0 t ([], t) rfl
  unfold readerOf
  rw [hf]
  simp only [Option.bind_some, h1, hF, lateOf_self]
  simp [keptOf]

/-- **The segment's reader answers keptOf at the two names.** -/
theorem readers_kept_on {Lk : Link S Claim} {b : ℕ} (hS : ObjectsStates (statesOfLink Lk) b)
    (hB : ObjectsBack (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH) (small : S → Option K9.Read)
    (name : String) (hn : name = "objects" ∨ name = "guests") (t : S) (F : Fork)
    (g : Model.Forest.Heard) (hF : t.fork? = some F) (hg : t.lookHeard? = some g)
    (hbare : ∀ f ∈ g.rows.toList, f.ents = #[]) :
    (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b name t =
      keptOf name t.lookHeard? := by
  obtain ⟨⟨r1, f1, _⟩, r2, f2, _⟩ := hS
  have key : readerOf (statesOfLink Lk) b name t = keptOf name t.lookHeard? := by
    rcases hn with rfl | rfl
    · exact readerOf_objects_on f1 (hB.1 r1 f1) t F g hF hg hbare
    · exact readerOf_guests_on f2 (hB.2 r2 f2) t F hF
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl <;> decide
  obtain ⟨R, hR⟩ : ∃ R, keptOf name t.lookHeard? = some R := by
    unfold keptOf
    rw [hg]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  show (if (name == "K8.equations") = true then small t
    else match readerOf (statesOfLink Lk) b name t with
      | some R => some R
      | Option.none => k6Silent P8 (statesOfLink Lk) b name t) = _
  rw [hne, key, hR]
  rfl

/-! ## 2 The test goes forward -/

/-- **At one of the two names the promise's test goes forward over the turning of the head's ledger,
of what it has heard and of its sumcheck.** -/
theorem kept_on {Lk : Link S Claim} {b : ℕ} (hS : ObjectsStates (statesOfLink Lk) b)
    (hB : ObjectsBack (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH) (small : S → Option K9.Read)
    (own : List (ℕ × ℕ)) (name : String) (hn : name = "objects" ∨ name = "guests") (s : S)
    (o : HeadOwn) (F1 : Fork) (X : Model.Head.Heard) (Q : Model.Psc) (ho : s.here = .head o)
    (hop : o.opened = true) (hL : Later o.F F1) (hSz : Sized o.F) (g : Model.Forest.Heard)
    (hg : s.lookHeard? = some g) (hbare : ∀ f ∈ g.rows.toList, f.ents = #[])
    (hin : formsInT (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) own b name s = true) :
    formsInT (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) own b name
      { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } = true := by
  have ha := segAt_head s o ho hop
  have hb := segAt_head { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
    { o with F := F1, x := some X, squaresP := some Q } rfl hop
  have hlk : ({ s with here := .head { o with F := F1, x := some X, squaresP := some Q } } :
      S).lookHeard? = s.lookHeard? := by
    unfold S.lookHeard?
    rw [ho]
  have hFa : s.fork? = some o.F := by
    unfold S.fork?
    rw [ho]
    show (if o.opened then some o.F else none) = some o.F
    rw [hop]
    rfl
  have hFb : ({ s with here := .head { o with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    show (if o.opened then some F1 else none) = some F1
    rw [hop]
    rfl
  have ka := readers_kept_on hS hB P8 small name hn s o.F g hFa hg hbare
  have kb := readers_kept_on hS hB P8 small name hn _ F1 g hFb (hlk.trans hg) hbare
  rw [hlk] at kb
  obtain ⟨R, hR, hlate⟩ : ∃ R, keptOf name s.lookHeard? = some R ∧ R.late = [] := by
    unfold keptOf
    rw [hg]
    split
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  have hSz1 := hL.sized hSz
  refine formsInT_on own _ b name s _ _ _ R ha hb (ka.trans hR) (kb.trans hR) ?_ ?_ ?_ rfl rfl ?_
    hin
  · unfold K9.mergeOf
    rw [ho]
  · exact ⟨rfl, rfl, fun _ _ _ e => e, fun _ e => e, fun _ _ e => e, fun _ _ _ _ => ⟨rfl, rfl⟩,
      fun j _ hj => ⟨(hL.keep j hj).2.1, (hL.keep j hj).2.2⟩⟩
  · exact ⟨hL.ns, fun j hj => (hL.keep j hj).1,
      Nat.le_of_eq (hSz.1.trans (hL.ns.symm.trans hSz1.1.symm)),
      Nat.le_of_eq (hSz.2.1.trans (hL.ns.symm.trans hSz1.2.1.symm))⟩
  · rw [hlate]
    rfl

/-! ## 3 The clause -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {Fr : Frame}
  {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **THE PUBLIC TEST formsInT 24 3 "objects" IS KEPT ACROSS AN ACCEPT OF THE PIECE AT PLACE
341.** -/
theorem kept_objects (Hs : Seated Wp .two Fr q 24 bef B bS) {Lk : Link S Claim}
    {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs 24 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2) (hback : ObjectsBack (statesOfLink Lk) 2)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (hled : First.ledgerB a.1.2 = true)
    (hbare : ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]) :
    (MGA).pub (.formsInT 24 3 "objects") b.1 = true := by
  obtain ⟨o, F1, X, Q, ho, hop, _, e⟩ := k6_behind Hs a b τ hb
  have fa : a.1.2.fork? = some o.F := by
    unfold S.fork?
    rw [ho]
    show (if o.opened then some o.F else none) = some o.F
    rw [hop]
    rfl
  have hL' : Later o.F F1 := by
    have fb : b.1.2.fork? = some F1 := by
      rw [e]
      show (if o.opened then some F1 else none) = some F1
      rw [hop]
      rfl
    have h0 : Later (a.1.2.fork?.getD {}) (b.1.2.fork?.getD {}) := later_at_piece Hs a b τ hb
    rw [fa, fb] at h0
    exact h0
  have hSz : Sized o.F := (sized_iff fa).1 hled
  have hpub : (MGA).pub (.formsInT 24 3 "objects") a.1 = true :=
    (onParts_of_on D.N MGA linksFull PS (fun a => a) 341 a ha hm).pub _
      (List.mem_append_right _ (by decide +kernel))
  have hin : ∀ p ∈ D.runs 24 3 "objects",
      formsInT (D.Rd 24) (D.N.sent 24 0) p.1 p.2 a.1.2 = true :=
    fun p hp => List.all_eq_true.1 hpub p hp
  -- something is heard: the reader of "objects" answers in front
  obtain ⟨g, hg⟩ : ∃ g, a.1.2.lookHeard? = some g := by
    have h2 := hin (2, "objects") (by rw [hobj]; simp)
    rw [hreaders] at h2
    unfold formsInT at h2
    rw [segAt_head a.1.2 o ho hop] at h2
    cases e2 : (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms 2 "objects"
        a.1.2 with
    | none =>
      rw [e2] at h2
      exact absurd h2 Bool.false_ne_true
    | some R =>
      have k0 := readers_kept hruns P8 small "objects" (Or.inl rfl) a.1.2 R e2
      unfold keptOf at k0
      rw [if_pos rfl] at k0
      obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.1 k0
      exact ⟨g, hg⟩
  rw [e]
  refine List.all_eq_true.2 fun p hp => ?_
  have h2 := hin p hp
  rw [hobj] at hp
  have hp' : p.1 = 2 ∧ (p.2 = "objects" ∨ p.2 = "guests") := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  rw [hreaders, hp'.1] at h2
  show formsInT (D.Rd 24) (D.N.sent 24 0) p.1 p.2 _ = true
  rw [hreaders, hp'.1]
  exact kept_on hruns hback P8 small _ p.2 hp'.2 a.1.2 o F1 X Q ho hop hL' hSz g hg (hbare g hg) h2

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.readerOf_objects_on
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.readerOf_guests_on
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.readers_kept_on
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_on
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_objects
