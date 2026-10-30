-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawModel.lean: law 2's walk of OnBytes/Model/ (and the diagonal of law 1: every
statement is for every G and d).

By the command's print (49 modules: 254 routines have their law, 4 are STUCK, 2 records' fields are
passed over) each of these 254 routines of the model's checks, from contexts that are alike
(OnBytes/TypedOracleCompiler/Laws/LawAlike.lean) and from one state of its own layers, fails alike or gives equal
values and equal states and leaves contexts that are alike: it does not hang on a digest drawn or on
root and start of a given source. Lean holds this sentence only as far as a theorem that is written
out uses it: a routine that is STUCK is a line of the print, and leaves this file green. For the
routines that take a block, or a function into blocks, as an argument (pscRound, planesAt,
planeClaims, planeLins, LinkM.sub, LinkM.call, weighted, overG, lessPieces) the law is over the like
law of that argument; `linksOf_runs` ends with no such hypothesis left.

How. The command walk_modules OnBytes.Model (OnBytes/TypedOracleCompiler/Laws/LawAuto.lean) walks the 49 modules
that OnBytes.Model.VerifyLinks imports, and prints each routine with how it fell. By hand, before
it: closeAs (it returns what was drawn: its law is at `DrawnAlike`, with the step `same_of_closeAs`
for a text that goes on without the digest); SubM.change, take, ask (functions of the state);
LinkM.sub, call. By hand, after it: runLinkH, runLinksFrom, runLinksH, which run a check out of a
record's field: over the hypothesis that each link's check is `SameL`.

Main names. `carries_closeAs`, `same_of_closeAs`; `sameS_change`, `take`, `ask`; `sameL_sub`,
`call`; auto.<routine> (added by the command); `same_runLinkH`, `same_runLinksFrom`,
`same_runLinksH`.
  `listLinksH_runs`   each link of listLinksH runs the check of one of the plans that it was given
  `linksOf_runs`      every link of Verify.linksOf X cov has a check that is `SameL`
  `zipped_runs`       so has every link that the program passes to Proof.check
                      (OnBytes/Model/VerifyStages.lean)

Not claimed. That a routine does not read the book's other fields, or the statement: these are equal
in contexts that are alike. Nothing on two runs from two states, or at two requests. By the print
the four lines STUCK are closeAs and the three routines by hand, which have their laws here, and the
two fields passed over are LinkH.run and SubPlanH.run. No theorem says that these are all.

-/
import OnBytes.TypedOracleCompiler.Laws.LawAuto
import OnBytes.Model.VerifyLinks

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Model

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

/-! ## By hand: the calls that are written as functions of the state, and closeAs -/

theorem carries_closeAs (n : String) (k : Fmt.Kind) (e nz t : Nat) :
    Carries (Alike G d) DrawnAlike (closeAs n k e nz t) (closeAs n k e nz t) := by
  unfold closeAs
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind (carries_close _ _ _) fun x y h => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun _ => ?_
  exact Carries.pure h

theorem same_of_closeAs {β : Type} (n : String) (k : Fmt.Kind) (e nz t : Nat)
    {f : Fmt.Drawn → Blk β}
    (hf : ∀ e p t g g', Carries (Alike G d) Eq (f ⟨e, p, t, g⟩) (f ⟨e, p, t, g'⟩)) :
    Same (Alike G d) (closeAs n k e nz t >>= f) :=
  ⟨Carries.bind (carries_closeAs n k e nz t) fun x x' h => by
    obtain ⟨e, p, t, g⟩ := x
    obtain ⟨e', p', t', g'⟩ := x'
    obtain ⟨h1, h2, h3⟩ := h
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    exact hf _ _ _ _ _⟩

macro_rules
  | `(tactic| walk_more) =>
    `(tactic| (
      (with_reducible refine same_of_closeAs _ _ _ _ _ (fun _ _ _ _ _ => ?_))
      try dsimp only
      refine Carries.of_same ?_))

instance sameS_change (f : Fork → Option Fork) : SameS (Alike G d) (SubM.change f) :=
  ⟨fun F => ⟨fun c c' h => by
    unfold SubM.change
    cases f F with
    | none => exact Out.err _
    | some x => exact Out.ok rfl h⟩⟩

instance sameS_take {α : Type} (f : Fork → Option (α × Fork)) : SameS (Alike G d) (SubM.take f) :=
  ⟨fun F => ⟨fun c c' h => by
    unfold SubM.take
    cases f F with
    | none => exact Out.err _
    | some x => exact Out.ok rfl h⟩⟩

instance sameS_ask {α : Type} (f : Fork → Option α) : SameS (Alike G d) (SubM.ask f) :=
  ⟨fun F => ⟨fun c c' h => by
    unfold SubM.ask
    cases f F with
    | none => exact Out.err _
    | some x => exact Out.ok rfl h⟩⟩

instance sameL_sub {α : Type} (x : SubM α) [hx : SameS (Alike G d) x] :
    SameL (Alike G d) (LinkM.sub x) :=
  ⟨fun L => SameS.bind hx fun a => sameS_pure (a, L)⟩

instance sameL_call (f : ChainCheck → Blk ChainCheck) [hf : ∀ k, Same (Alike G d) (f k)] :
    SameL (Alike G d) (LinkM.call f) :=
  ⟨fun L => by unfold LinkM.call SubM.must; walkAll⟩

walk_modules OnBytes.Model

/-! ## By hand: the routines that run a link's check out of a record's field -/

open Stages in
theorem same_runLinkH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat) (X : LinkH)
    (hX : SameL (Alike G d) X.run) (check : ChainCheck) (out : Proof.LinksResult) :
    Same (Alike G d) (runLinkH links p wsLay l X check out) := by
  unfold runLinkH; walkAll

open Stages in
theorem same_runLinksFrom (links : Array LinkH) (p : Params.First) (wsLay : WsLay)
    (rest : List LinkH) (h : ∀ X ∈ rest, SameL (Alike G d) X.run) (l : Nat) (check : ChainCheck)
    (out : Proof.LinksResult) : Same (Alike G d) (runLinksFrom links p wsLay rest l check out) := by
  induction rest generalizing l check out with
  | nil => unfold runLinksFrom; walkAll
  | cons X rest ih =>
    unfold runLinksFrom
    have i1 := fun c o => same_runLinkH links p wsLay l X (h X List.mem_cons_self) c o
    have i2 := fun l c o => ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)) l c o
    walkAll

/-- Law 2 (and the diagonal of law 1) at the links of a proof's first chain, over one hypothesis:
each link's check, a field of its record, is one text with equal values. -/
theorem same_runLinksH (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay)
    (h : ∀ X ∈ links.toList, SameL (Alike G d) X.run) :
    Same (Alike G d) (Stages.runLinksH links p wsLay) := by
  unfold Stages.runLinksH
  have i1 := fun l c o => same_runLinksFrom links p wsLay links.toList h l c o
  walkAll

/-! ## The links that the program passes to Proof.check -/

/-- A loop in Except whose steps keep a property keeps it. -/
theorem forIn_keeps {ε α β : Type} (P : β → Prop) (l : List α) (f : α → β → Except ε (ForInStep β))
    (hs : ∀ a ∈ l, ∀ b r, P b → f a b = .ok r → P (match r with | .done x => x | .yield x => x))
    (init out : β) (h0 : P init) (h : forIn l init f = .ok out) : P out := by
  induction l generalizing init with
  | nil =>
    rw [List.forIn_nil] at h
    cases h
    exact h0
  | cons a l ih =>
    rw [List.forIn_cons] at h
    cases e : f a init with
    | error x => rw [e] at h; cases h
    | ok r =>
      rw [e] at h
      have k := hs a List.mem_cons_self init r h0 e
      cases r with
      | done x => cases h; exact k
      | yield x => exact ih (fun a ha => hs a (List.mem_cons_of_mem _ ha)) x k h

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mem_push {α : Type} {P : α → Prop} {a : Array α} {x : α} (ha : ∀ y ∈ a.toList, P y)
    (hx : P x) : ∀ y ∈ (a.push x).toList, P y := by
  intro y hy
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
  rcases hy with h | rfl
  · exact ha y h
  · exact hx

/-- Each link of listLinksH runs the check of one of the plans that it was given. -/
theorem listLinksH_runs (Q : LinkM (Option WsForkOut) → Prop) (NGr : Nat) (p4 : Bool)
    (Gs As : Array Stages.SubPlanH) (H : Stages.SubPlanH) (hG : ∀ s ∈ Gs.toList, Q s.run)
    (hA : ∀ (i : Nat) (a : Stages.SubPlanH), As[i]? = some a → Q a.run) (hH : Q H.run)
    (links : Array Stages.LinkH) (h : Stages.listLinksH NGr p4 Gs As H = .ok links) :
    ∀ X ∈ links.toList, Q X.run := by
  unfold Stages.listLinksH at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨r, hr, h⟩ := bind_ok h
    cases h
    refine mem_push ?_ hH
    refine forIn_keeps (fun ls : Array Stages.LinkH => ∀ X ∈ ls.toList, Q X.run) _ _ ?_ _ _ ?_ hr
    · rintro ⟨s, g⟩ hm b r hb hf
      have hs : Q s.run := hG s (List.fst_mem_of_mem_zipIdx hm)
      dsimp only at hf
      split at hf
      · split at hf
        · rename_i a ha
          cases hf
          exact mem_push (mem_push hb hs) (hA _ _ ha)
        · cases hf
          exact mem_push hb hs
      · cases hf
        exact mem_push hb hs
    · intro X hX
      cases hX

/-- The three forms of a link's check, as OnBytes/Model/VerifyLinks.lean makes them, are each one
text with equal values; so is every link's check of linksOf. -/
theorem linksOf_runs (X : Verify.Public) (cov : Head.Covered) (links : Array Stages.LinkH)
    (h : Verify.linksOf X cov = .ok links) : ∀ L ∈ links.toList, SameL (Alike G d) L.run := by
  unfold Verify.linksOf at h
  refine listLinksH_runs (fun r => SameL (Alike G d) r) _ _ _ _ _ ?_ ?_ ?_ links h
  · intro s hs
    rw [Array.mem_toList_iff, Array.mem_mapIdx] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    unfold Verify.layersPlanOf
    dsimp only
    infer_instance
  · intro i a ha
    rw [Array.getElem?_map] at ha
    cases e : X.A[i]? with
    | none => rw [e] at ha; cases ha
    | some A =>
      rw [e] at ha
      cases ha
      unfold Verify.attentionPlanOf
      dsimp only
      infer_instance
  · unfold Verify.headPlanOf
    dsimp only
    infer_instance

/-- The links that the program passes to Proof.check (OnBytes/Model/VerifyStages.lean): the
built links, each with the check of the link of linksOf at its place. -/
theorem zipped_runs (built links : Array Stages.LinkH)
    (h : ∀ L ∈ links.toList, SameL (Alike G d) L.run) :
    ∀ L ∈ (built.zipWith (fun b l => { b with run := l.run }) links).toList,
      SameL (Alike G d) L.run := by
  intro L hL
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hL
  obtain ⟨i, hi, rfl⟩ := hL
  have hi2 : i < links.size := by
    have k := hi
    rw [Array.size_zipWith] at k
    omega
  rw [Array.getElem_zipWith]
  exact h links[i] (Array.mem_toList_iff.2 (Array.getElem_mem hi2))

#print axioms same_runLinksH
#print axioms linksOf_runs
#print axioms zipped_runs

end OnBytes.TwoLaws
