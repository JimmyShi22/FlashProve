-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/BookBlocks.lean: every opening in the rounds that the dry run of one of a
file's three chains' blocks returns is the opening of a tree of the book at the run's end, and that
book has grown out of the book at the start.

Definitions, statements and proofs, from OnBytes/Tie/Pv/Keeps/BookModel.lean.
Main names (namespace OnBytes.Tie.Pv.Keeps.Book):
  `dryRun_book`: of any block with `BookB`: there is a book that has grown out of the start's, and
    every opening of a round that the dry run returns is `noteOf` of a tree of it.
  `EndsBook b`: what b returns holds the book of the context that b leaves.
  `links_book`: the block of the links that the stage request runs has `BookB`, with no hypothesis
    but that linksOf has returned the list.
  `first_opens`, `oneTime_opens`, `shared_opens`: for the three blocks that return a book: that book
    is the one which they return.
  `second_opens`: for the second chain's block, at every start.
Limits: one direction: from a dry run that returns. Nothing on which trees a book holds beyond those
of the start. `first_opens` asks `BookB` of the block of the links.
-/
import OnBytes.Key.OneTime
import OnBytes.Tie.Pv.Keeps.BookModel
import OnBytes.Tie.Pv.Keeps.KeepsLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Book

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

/-- The context from which a dry run starts, and the context at its end. -/
theorem dryRun_ends {α : Type} {b : Blk α} {s : Start} {rs : Params.Rounds} {a : α}
    (h : b.dryRun s = some (rs, a)) :
    ∃ c0 c, b c0 = .ok (a, c) ∧ c0.ch.dry = true ∧ c0.ch.noted = #[] ∧ c0.book = s.book ∧
      rs = c.ch.noted.toList.map fun n => (⟨n.entry, n.kind, n.items, n.opens⟩, n.stored) := by
  unfold Blk.dryRun Blk.dryRunNamed at h
  split at h
  · cases h
  · rename_i a' c hr
    split at h
    · have e : (c.ch.noted.toList.map fun n =>
          ((⟨n.entry, n.kind, n.items, n.opens⟩ : Fmt.Round), n.stored), a') = (rs, a) :=
        Option.some.inj h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      unfold Blk.runNamed at hr
      split at hr
      · exact ⟨_, c, hr, rfl, rfl, rfl, rfl⟩
      · cases hr
    · cases h

/-- The openings of the rounds are openings of trees of the book B. -/
def OpensIn (R : Params.Rounds) (B : TreeBook) : Prop :=
  ∀ r ∈ R, ∀ o ∈ r.1.opens, ∃ t ∈ B.trees.toList, noteOf t = o

/-- At the run's end. -/
theorem dryRun_at {α : Type} {b : Blk α} (k : BookB b) {s : Start} {rs : Params.Rounds} {a : α}
    (h : b.dryRun s = some (rs, a)) :
    ∃ c0 c, b c0 = .ok (a, c) ∧ Grows s.book c.book ∧ OpensIn rs c.book := by
  obtain ⟨c0, c, hr, hd, hn, hb, rfl⟩ := dryRun_ends h
  obtain ⟨_, g, n⟩ := k c0 a c hr hd
  refine ⟨c0, c, hr, hb ▸ g, fun r hr' o ho => ?_⟩
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr'
  exact n (fun m' hm' => by rw [hn] at hm'; cases hm') m hm o ho

theorem dryRun_book {α : Type} {b : Blk α} (k : BookB b) {s : Start} {rs : Params.Rounds} {a : α}
    (h : b.dryRun s = some (rs, a)) : ∃ B, Grows s.book B ∧ OpensIn rs B := by
  obtain ⟨_, c, _, g, o⟩ := dryRun_at k h
  exact ⟨c.book, g, o⟩

instance bl_runLinkH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat)
    (X : LinkH) (check : ChainCheck) (out : Proof.LinksResult) [KeepsM X.run] :
    KeepsM (runLinkH links p wsLay l X check out) := by
  unfold runLinkH; keepsM

theorem bl_runLinksFrom (links : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    ∀ (rest : List LinkH), (∀ X ∈ rest, KeepsM X.run) → ∀ (l : Nat) (check : ChainCheck)
      (out : Proof.LinksResult), KeepsM (runLinksFrom links p wsLay rest l check out)
  | [], _, l, check, out => by unfold runLinksFrom; keepsM
  | X :: rest, h, l, check, out => by
    haveI := h X List.mem_cons_self
    haveI := bl_runLinksFrom links p wsLay rest fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    unfold runLinksFrom; keepsM

/-- Every link's routine has the property. -/
def AllB (ls : Array LinkH) : Prop := ∀ l ∈ ls, KeepsM l.run

theorem bl_runLinksH (links : Array LinkH) (p : Params.First) (wsLay : WsLay)
    (h : AllB links) : KeepsM (runLinksH links p wsLay) := by
  haveI := bl_runLinksFrom links p wsLay links.toList fun X hX =>
    h X (Array.mem_toList_iff.1 hX)
  unfold runLinksH; keepsM

instance bl_layersPlan (X : Verify.Public) (tokv : Array Nat) (g : Nat) (hp : Layer.HPlan2) :
    KeepsM (Verify.layersPlanOf X tokv g hp).run := by
  unfold Verify.layersPlanOf; keepsM

instance bl_attentionPlan (A : Attention.Plan) : KeepsM (Verify.attentionPlanOf A).run := by
  unfold Verify.attentionPlanOf; keepsM

instance bl_headPlan (X : Verify.Public) (cov : Head.Covered) :
    KeepsM (Verify.headPlanOf X cov).run := by
  unfold Verify.headPlanOf; keepsM

theorem AllB.push {ls : Array LinkH} (h : AllB ls) {l : LinkH} (hl : KeepsM l.run) :
    AllB (ls.push l) := by
  intro x hx
  rcases Array.mem_push.1 hx with h1 | rfl
  · exact h x h1
  · exact hl

theorem bl_link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool)
    (h : KeepsM s.run) : KeepsM (s.link name gid kind g fv).run := h

theorem bl_listLinksH {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (hG : ∀ s ∈ G, KeepsM s.run) (hA : ∀ a ∈ A, KeepsM a.run)
    (hH : KeepsM H.run) (h : listLinksH NGr p4 G A H = .ok ls) : AllB ls := by
  unfold listLinksH at h
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain ⟨_, -, h⟩ := L5.bind_ok h
    obtain ⟨r, hr, h⟩ := L5.bind_ok h
    cases h
    refine AllB.push ?_ (bl_link _ _ _ _ _ _ hH)
    refine L5.forIn_inv AllB _ _ _ _ (fun _ hx => absurd hx (Array.not_mem_empty _)) ?_ hr
    rintro ⟨s0, g⟩ hx b s hb hs
    have hs0 : KeepsM s0.run := hG s0 (Array.mem_toList_iff.1 (mem_zipIdx_fst _ _ _ hx))
    dsimp only at hs
    split at hs
    · split at hs
      · rename_i a ha
        cases hs
        exact (hb.push (bl_link _ _ _ _ _ _ hs0)).push
          (bl_link _ _ _ _ _ _ (hA a (Array.mem_of_getElem? ha)))
      · cases hs
        exact hb.push (bl_link _ _ _ _ _ _ hs0)
    · cases hs
      exact hb.push (bl_link _ _ _ _ _ _ hs0)

theorem bl_linksOf {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) : AllB ls := by
  unfold Verify.linksOf at h
  refine bl_listLinksH ?_ ?_ inferInstance h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hs
    rw [Array.getElem_mapIdx]
    infer_instance
  · intro a ha
    obtain ⟨A, -, rfl⟩ := Array.mem_map.1 ha
    infer_instance

theorem bl_zipped {ls : Array LinkH} (h : AllB ls) (built : Array LinkH) :
    AllB (built.zipWith (fun b l => { b with run := l.run }) ls) := by
  intro Z hZ
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hZ
  have hi' : i < ls.size := by
    rw [Array.size_zipWith] at hi
    omega
  rw [Array.getElem_zipWith]
  exact h (ls[i]'hi') (Array.getElem_mem hi')

/-- The block of the links that the stage request runs has the property, in plain words. -/
theorem links_book {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) (built : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    BookB (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) p wsLay) :=
  (bl_runLinksH _ p wsLay (bl_zipped (bl_linksOf h) built)).out


/-! ## The blocks that return a book -/

/-- What the block returns holds, under f, the book of the context that it leaves. -/
def EndsBook {α : Type} (f : α → TreeBook) (b : Blk α) : Prop :=
  ∀ c e c', b c = .ok (e, c') → f e = c'.book

theorem EndsBook.behind {α β : Type} {f : β → TreeBook} (x : Blk α) {g : α → Blk β}
    (hg : ∀ a, EndsBook f (g a)) : EndsBook f (x >>= g) := fun c e c2 h => by
  obtain ⟨a, c1, _, h2⟩ := (Blk.yields_bind x g c c2 e).1 ((Blk.yields_iff _ _ _ _).2 h)
  exact hg a c1 e c2 ((Blk.yields_iff _ _ _ _).1 h2)

theorem handOver_endsBook {α : Type} (f : α → TreeBook) (w : Statement × TreeBook → α)
    (hw : ∀ z, f (w z) = z.2) :
    EndsBook f (Blk.handOver >>= fun z => (pure (w z) : Blk α)) := fun c e c' h => by
  cases h
  exact hw _

theorem firstEnd_endsBook (lin : LinFirst) : EndsBook (·.book) (Proof.firstEnd lin) := by
  unfold Proof.firstEnd
  exact EndsBook.behind _ fun _ =>
    handOver_endsBook (·.book) (fun z => (⟨z.1, z.2, lin⟩ : Proof.FirstEnd)) fun _ => rfl

theorem firstBlock_endsBook (p : Params.First) (links : Blk Proof.LinksResult) (reply : E) :
    EndsBook (·.book) (Proof.firstBlock p links reply) := by
  unfold Proof.firstBlock
  exact EndsBook.behind _ fun _ => EndsBook.behind _ fun _ => EndsBook.behind _ fun _ =>
    EndsBook.behind _ fun _ => EndsBook.behind _ fun lin => firstEnd_endsBook lin

theorem oneTime_endsBook (p : Params.OneTime) : EndsBook (·.book) (Key.oneTime p) := by
  unfold Key.oneTime
  exact EndsBook.behind _ fun _ => EndsBook.behind _ fun _ => EndsBook.behind _ fun _ =>
    EndsBook.behind _ fun first => firstEnd_endsBook first

theorem sharedBlock_endsBook (S : Params.LinShape) (key : TableKey) :
    EndsBook (·.book) (Proof.sharedBlock S key) := by
  unfold Proof.sharedBlock
  exact EndsBook.behind _ fun x => EndsBook.behind _ fun _ => EndsBook.behind _ fun _ =>
    EndsBook.behind _ fun _ =>
      handOver_endsBook (·.book) (fun z => (⟨z.1, z.2, x⟩ : Proof.SharedEnd)) fun _ => rfl

theorem opens_of {α : Type} {f : α → TreeBook} {b : Blk α} (k : BookB b) (e : EndsBook f b)
    {s : Start} {rs : Params.Rounds} {a : α} (h : b.dryRun s = some (rs, a)) :
    Grows s.book (f a) ∧ OpensIn rs (f a) := by
  obtain ⟨c0, c, hr, g, o⟩ := dryRun_at k h
  rw [e c0 a c hr]
  exact ⟨g, o⟩

/-! ## In plain words -/

/-- A proof file's first chain. -/
theorem first_opens {p : Params.First} {links : Blk Proof.LinksResult} {reply : E}
    (hl : BookB links) {s : Start} {R : Params.Rounds} {dry : Proof.FirstEnd}
    (h : (Proof.firstBlock p links reply).dryRun s = some (R, dry)) :
    Grows s.book dry.book ∧ OpensIn R dry.book := by
  haveI : KeepsM links := ⟨hl⟩
  have k : KeepsM (Proof.firstBlock p links reply) := by
    unfold Proof.firstBlock; keepsM
  exact opens_of k.out (firstBlock_endsBook p links reply) h

/-- A key file's first chain. -/
theorem oneTime_opens {p : Params.OneTime} {s : Start} {R : Params.Rounds} {dry : Proof.FirstEnd}
    (h : (Key.oneTime p).dryRun s = some (R, dry)) :
    Grows s.book dry.book ∧ OpensIn R dry.book := by
  have k : KeepsM (Key.oneTime p) := by
    unfold Key.oneTime; keepsM
  exact opens_of k.out (oneTime_endsBook p) h

/-- The shared chain. -/
theorem shared_opens {S : Params.LinShape} {key : TableKey} {s : Start} {R : Params.Rounds}
    {dry : Proof.SharedEnd} (h : (Proof.sharedBlock S key).dryRun s = some (R, dry)) :
    Grows s.book dry.book ∧ OpensIn R dry.book :=
  opens_of (inferInstance : KeepsM (Proof.sharedBlock S key)).out (sharedBlock_endsBook S key) h

/-- The second chain, at every start. -/
theorem second_opens {S : Params.LinShape} {first : LinFirst} {shared : Proof.SharedEnd}
    {s : Start} {R : Params.Rounds} (h : (Proof.secondBlock S first shared).rounds s = some R) :
    ∃ B, Grows s.book B ∧ OpensIn R B := by
  unfold Blk.rounds at h
  obtain ⟨⟨R', u⟩, h1, h2⟩ := Option.map_eq_some_iff.1 h
  obtain rfl : R' = R := h2
  exact dryRun_book (inferInstance : KeepsM (Proof.secondBlock S first shared)).out h1

end OnBytes.Tie.Pv.Keeps.Book

#print axioms OnBytes.Tie.Pv.Keeps.Book.links_book
#print axioms OnBytes.Tie.Pv.Keeps.Book.first_opens
#print axioms OnBytes.Tie.Pv.Keeps.Book.oneTime_opens
#print axioms OnBytes.Tie.Pv.Keeps.Book.shared_opens
#print axioms OnBytes.Tie.Pv.Keeps.Book.second_opens
