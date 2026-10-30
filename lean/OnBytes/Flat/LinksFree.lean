-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFree.lean: the rounds of a proof's first chain do not hang on the request, if four
statements on parts of the program hold, and one inequality between two public numbers.

`PlannedFirstFree p` (OnBytes/Flat/LinksDry.lean) says: at any two requests that `Head.coveredOf`
and `Verify.linksOf` take, at all replies and every start, the dry runs of the first chain's block
both fail, or both return, with the same rounds, the same statement, the same book of trees and the
same four numbers of what the test on the table passes on. Two dry runs that both fail count as
alike, whatever the names of the two failures. The statement speaks of the requests that
`Head.coveredOf` takes and at which `Verify.linksOf` returns: at a p where one of the two never
returns it holds idly. Here it is cut down.

How the request goes through the block, by the program's text. Every link starts from its record's
own state (`runLinkH`, OnBytes/Model/StagesLinks.lean), and of what its check leaves the block keeps
the state of the chain's calls, three fields of the link's context, the sizes of the arrays, and
what the merge of the claims on the weights returns (`WsForkOut`). That value gives a row on the
table (`pendingRowH`), and the rows go to the first part of the test on the table
(`memberFirstVerify`).

The relations. `OutAlike`: two values of the merge agree in all but what is left of each claim;
there they name the same units, with factors of the same sizes. `RowAlike`: two rows on the table
agree in all but their weights, which have the same numbers of variables. `RunFree r r'`: two checks
of a link, from one context of the link, one state and one dry context, both fail, or both return,
with one context left, one context of the link, states that `samePlan` does not tell apart, and
values that are both missing (the check of attention returns none) or both there and in `OutAlike`.

The four statements, each a definition by name:
 `LayerFree`    of the check of a group of layers at two lists of tokens;
 `HeadFree p`   of the check of the head at two requests that `Head.coveredOf` takes;
 `PendingFree`  of `pendingRowH`;
 `MemberFree`   of `memberFirstVerify`.

Main theorem: `plannedFirstFree_of`: `PlannedFirstFree p` from the four, and from hV: the size of
the vocabulary by which `Head.coveredOf` tests the request's tokens (`p.X.P.h.V`) is at most the one
that the checks of the layers hold (`p.X.layers.V`). WITHOUT hV `PlannedFirstFree p` NEED NOT HOLD:
it is said of every value p of the type, and at a p with a smaller number in the layers' place the
first group's check refuses one request's tokens and takes another's. `Verify.publicOf` lays one
number at both places; that is read from its text, not shown here. On the way: `runLinkH_rel`,
`runLinksH_rel`, `firstBlock_rel`, `listLinksH_ok` (the list of the links as a fold),
`listLinksH_alike`, `covered_tokens`.

Not claimed: any of the four statements. Nothing on a run on a view. For proofs only; no module of
the program imports this file.


-/
import OnBytes.Flat.DryRel
import OnBytes.Flat.LinksDry
import OnBytes.Flat.BlocksKeep

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Stages

/-- Closes `Blk.Keeps b` by the walk. -/
local macro "keeps_blk" : tactic => `(tactic| (show Over.K (m := Blk) _; keeps))

/-! ## The relations -/

/-- Two factors on the rows have the same sizes. -/
def RowFacAlike (x x' : WsRowFac) : Prop :=
  x.HV.size = x'.HV.size ∧ x.pl.size = x'.pl.size ∧ x.AV.size = x'.AV.size

/-- What is left of two claims: one unit, factors of the same sizes. -/
def RecAlike (c c' : WsRecClaim) : Prop := c.ui = c'.ui ∧ All2 RowFacAlike c.f c'.f

/-- Two values that the merge of the claims on the weights returns. -/
def OutAlike (o o' : WsForkOut) : Prop :=
  o.toWsMerged = o'.toWsMerged ∧ All2 RecAlike o.recs o'.recs

/-- Two values that a link's check returns. -/
def OptAlike : Option WsForkOut → Option WsForkOut → Prop
  | none, none => True
  | some o, some o' => OutAlike o o'
  | _, _ => False

/-- Two rows on the table: all is equal but the weights, which have the same numbers of
variables. -/
def RowAlike (r r' : TensorRow) : Prop :=
  r.psi = r'.psi ∧ r.masks = r'.masks ∧ r.target = r'.target ∧
    r.g.map Tensor.vars = r'.g.map Tensor.vars

/-- Two values that the block of the links returns. -/
def ResultAlike (x x' : Proof.LinksResult) : Prop :=
  x.indexMasks = x'.indexMasks ∧ x.reply = x'.reply ∧ All2 RowAlike x.pending x'.pending

/-- Two checks of one link. -/
def RunFree (r r' : LinkM (Option WsForkOut)) : Prop :=
  ∀ (C : LinkCtx) (F : Fork),
    relB (fun x x' => OptAlike x.1.1 x'.1.1 ∧ x.1.2 = x'.1.2 ∧
        ∀ (X : LinkH) (l : Tail2), samePlan X x.2 l = samePlan X x'.2 l)
      (StateT.run (StateT.run r C) F) (StateT.run (StateT.run r' C) F)

/-- Two records of one link: all is equal but the checks; the first check leaves the two flags of a
run as they are. -/
def LinkAlike (X X' : LinkH) : Prop :=
  X' = { X with run := X'.run } ∧ Over.K X.run ∧ RunFree X.run X'.run

/-! ## The four statements -/

/-- Of the check of a group of layers, at two lists of as many tokens, of which both or neither
have a token from V on. -/
def LayerFree : Prop :=
  ∀ (P : Layer.Pub) (t t' : Array Nat) (hp : Layer.HPlan2) (g : Nat), t.size = t'.size →
    t.any (· ≥ P.V) = t'.any (· ≥ P.V) →
    RunFree (some <$> Layer.runForkHidG2 { P with tokv := t } hp g)
      (some <$> Layer.runForkHidG2 { P with tokv := t' } hp g)

/-- Of the check of the head, at two requests that `Head.coveredOf` takes. -/
def HeadFree (p : Verify.Planned) : Prop :=
  ∀ (so so' : Head.StOwn) (cov cov' : Head.Covered),
    Head.coveredOf so p.X.T p.X.P.h.V = .ok cov → Head.coveredOf so' p.X.T p.X.P.h.V = .ok cov' →
    RunFree (Verify.headPlanOf p.X cov).run (Verify.headPlanOf p.X cov').run

/-- Of the row that a sub-proof leaves on the table. -/
def PendingFree : Prop :=
  ∀ (wsLay : WsLay) (im : Nat) (o o' : WsForkOut) (n : Nat) (S : Params.LinShape), OutAlike o o' →
    relB RowAlike (pendingRowH wsLay im o n S) (pendingRowH wsLay im o' n S)

/-- Of the first part of the test on the table. -/
def MemberFree : Prop :=
  ∀ (S : Params.LinShape) (im : Nat) (rows rows' : List TensorRow),
    All2 RowAlike rows rows' →
    relB LinFirst.Alike (memberFirstVerify S im rows) (memberFirstVerify S im rows')

/-! ## One link -/

theorem relB_inPlace {α : Type} {R : α → α → Prop} {b b' : Blk α} (place : String)
    (h : relB R b b') : relB R (Blk.inPlace place b) (Blk.inPlace place b') := by
  intro c hc
  have h0 := h c hc
  unfold Blk.inPlace
  revert h0
  cases b c <;> cases b' c <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact h0

/-- After one and the same block. -/
theorem relB_same {α β : Type} {R : β → β → Prop} {x : Blk α} {f f' : α → Blk β}
    (hk : Blk.Keeps x) (hf : ∀ a, relB R (f a) (f' a)) : relB R (x >>= f) (x >>= f') :=
  relB_bind hk (relB_refl x) fun a a' e => by subst e; exact hf a

theorem indexMasksH_eq {L L' : Array LinkH} (h : onTable L = onTable L') (p : Params.First)
    (check : ChainCheck) : indexMasksH L p check = indexMasksH L' p check := by
  unfold indexMasksH
  rw [h]

/-- **One link.** -/
theorem runLinkH_rel (hP : PendingFree) {L L' : Array LinkH} (hT : onTable L = onTable L')
    (p : Params.First) (wsLay : WsLay) (l : Nat) {X X' : LinkH} (hX : LinkAlike X X')
    (check : ChainCheck) {out out' : Proof.LinksResult} (ho : ResultAlike out out') :
    relB (fun x x' => x.1 = x'.1 ∧ ResultAlike x.2 x'.2) (runLinkH L p wsLay l X check out)
      (runLinkH L' p wsLay l X' check out') := by
  obtain ⟨e, hk, hr⟩ := hX
  generalize X'.run = r' at e hr
  subst e
  unfold runLinkH
  refine relB_same (by keeps_blk) fun check => ?_
  rw [indexMasksH_eq hT]
  have hs : ∀ (F F' : Fork) (l : Tail2),
      (∀ (X : LinkH) (l : Tail2), samePlan X F l = samePlan X F' l) →
      samePlan { X with run := r' } F' l = samePlan X F l := fun F F' l h => (h _ _).symm
  have hout : ∀ (o o' : Proof.LinksResult), ResultAlike o o' →
      ResultAlike (if (X.kind == 2) = true then { o with reply := check.plain[0]? } else o)
        (if (X.kind == 2) = true then { o' with reply := check.plain[0]? } else o') := by
    intro o o' h
    split
    · exact ⟨h.1, rfl, h.2.2⟩
    · exact h
  dsimp only
  by_cases hl : (l == 0) = true
  case' pos =>
    simp only [hl, if_true]
    refine relB_same (by keeps_blk) fun im => ?_
    refine relB_bind (S := ResultAlike) (Blk.keeps_pure _) (relB_pure ⟨rfl, ho.2.1, ho.2.2⟩)
      fun out out' ho => ?_
  case' neg =>
    simp only [hl, Bool.false_eq_true, if_false]
    refine relB_bind (S := ResultAlike) (Blk.keeps_pure _) (relB_pure ho) fun out out' ho => ?_
  all_goals
    refine relB_same (by keeps_blk) fun _ => ?_
    refine relB_same (by keeps_blk) fun _ => ?_
    refine relB_bind ?_ (relB_inPlace _ (hr _ _)) fun x x' hx => ?_
    · keeps_blk
    obtain ⟨⟨o, C⟩, F⟩ := x
    obtain ⟨⟨o', C'⟩, F'⟩ := x'
    obtain ⟨h1, h2, h3⟩ := hx
    have h2' : C = C' := h2
    subst h2'
    dsimp only at h1 h3 ⊢
    refine relB_same (by keeps_blk) fun _ => ?_
    rw [hs F F' C.list h3]
    refine relB_same (by keeps_blk) fun _ => ?_
    have ho2 := hout out out' ho
    by_cases hfv : X.fv = true
    · simp only [hfv, if_true]
      cases o with
      | none =>
        cases o' with
        | none => exact fun c _ => trivial
        | some o' => exact h1.elim
      | some o =>
        cases o' with
        | none => exact h1.elim
        | some o' =>
          dsimp only
          rw [ho2.1]
          refine relB_bind (by keeps_blk) (hP _ _ _ _ _ _ h1) fun row row' hrow => ?_
          exact relB_pure ⟨rfl, rfl, ho2.2.1, ho2.2.2.append (.cons hrow .nil)⟩
    · simp only [hfv, Bool.false_eq_true, if_false]
      exact relB_pure ⟨rfl, ho2⟩

/-! ## All links, and the block of the first chain -/

/-- The links that are still to come. -/
theorem runLinksFrom_rel (hP : PendingFree) {L L' : Array LinkH} (hT : onTable L = onTable L')
    (p : Params.First) (wsLay : WsLay) {rest rest' : List LinkH} (h : All2 LinkAlike rest rest') :
    ∀ (l : Nat) (check : ChainCheck) {out out' : Proof.LinksResult}, ResultAlike out out' →
      relB (fun x x' => x.1 = x'.1 ∧ ResultAlike x.2 x'.2)
        (runLinksFrom L p wsLay rest l check out) (runLinksFrom L' p wsLay rest' l check out') := by
  induction h with
  | nil =>
    intro l check out out' ho
    unfold runLinksFrom
    exact relB_pure ⟨rfl, ho⟩
  | cons hX _ ih =>
    intro l check out out' ho
    unfold runLinksFrom
    refine relB_bind (keeps_runLinkH _ _ _ _ _ _ _ hX.2.1)
      (runLinkH_rel hP hT p wsLay l hX check ho) fun x x' hx => ?_
    obtain ⟨c, o⟩ := x
    obtain ⟨c', o'⟩ := x'
    obtain ⟨h1, h2⟩ := hx
    have h1' : c = c' := h1
    subst h1'
    exact ih _ _ h2

theorem onTable_eq {L L' : Array LinkH} (h : All2 LinkAlike L.toList L'.toList) :
    onTable L = onTable L' := by
  unfold onTable
  generalize L.toList = l at h
  generalize L'.toList = l' at h
  induction h with
  | nil => rfl
  | cons hX _ ih =>
    obtain ⟨e, -, -⟩ := hX
    rw [e]
    simp only [List.filter_cons]
    split <;> simp [ih]

theorem keeps_of_all2 {l l' : List LinkH} (h : All2 LinkAlike l l') : ∀ X ∈ l, Over.K X.run := by
  induction h with
  | nil => intro X hX; cases hX
  | cons hX _ ih =>
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h'
    · exact hX.2.1
    · exact ih Y h'

/-- **The block of the links.** -/
theorem runLinksH_rel (hP : PendingFree) {L L' : Array LinkH}
    (h : All2 LinkAlike L.toList L'.toList) (p : Params.First) (wsLay : WsLay) :
    relB ResultAlike (runLinksH L p wsLay) (runLinksH L' p wsLay) := by
  unfold runLinksH
  refine relB_same (by keeps_blk) fun check => ?_
  refine relB_bind (keeps_runLinksFrom _ _ _ _ (keeps_of_all2 h) _ _ _)
    (runLinksFrom_rel hP (onTable_eq h) p wsLay h 0 check ⟨rfl, rfl, .nil⟩) fun x x' hx => ?_
  obtain ⟨c, o⟩ := x
  obtain ⟨c', o'⟩ := x'
  obtain ⟨h1, h2⟩ := hx
  have h1' : c = c' := h1
  subst h1'
  exact relB_same (by keeps_blk) fun _ => relB_pure h2

/-- **The block of a first chain.** -/
theorem firstBlock_rel (hM : MemberFree) (p : Params.First) {links links' : Blk Proof.LinksResult}
    (hk : Blk.Keeps links) (h : relB ResultAlike links links') (reply reply' : E) :
    relB FirstEnd.Alike (Proof.firstBlock p links reply) (Proof.firstBlock p links' reply') := by
  unfold Proof.firstBlock
  refine relB_bind hk h fun r r' hr => ?_
  obtain ⟨h1, h2, h3⟩ := hr
  rw [← h1, ← h2, ← h3.length]
  refine relB_same (by keeps_blk) fun got => ?_
  refine relB_bind (by keeps_blk) (relB_check _ _ _) fun _ _ _ => ?_
  refine relB_same (by keeps_blk) fun _ => ?_
  refine relB_bind (by keeps_blk) (hM _ _ _ _ h3) fun lin lin' hl => ?_
  unfold Proof.firstEnd
  refine relB_same (by keeps_blk) fun _ => ?_
  exact relB_same (by keeps_blk) fun _ => relB_pure ⟨rfl, rfl, hl⟩

/-- So the two dry runs are alike. -/
theorem firstFree_of_rel (hM : MemberFree) (p : Params.First)
    {links links' : Blk Proof.LinksResult} (hk : Blk.Keeps links)
    (h : relB ResultAlike links links') : FirstFree p links links' := by
  intro reply reply' st
  have h0 := relB_dryRun (firstBlock_rel hM p hk h reply reply') st
  revert h0
  cases (Proof.firstBlock p links reply).dryRun st <;>
    cases (Proof.firstBlock p links' reply').dryRun st <;> exact id

/-! ## The list of the links -/

theorem OutAlike.refl (o : WsForkOut) : OutAlike o o :=
  ⟨rfl, All2.refl (fun _ => ⟨rfl, All2.refl (fun _ => ⟨rfl, rfl, rfl⟩) _⟩) _⟩

/-- A check is in relation with itself. -/
theorem RunFree.refl (r : LinkM (Option WsForkOut)) : RunFree r r := fun C F =>
  relB_mono (fun x x' e => by
    subst e
    refine ⟨?_, rfl, fun _ _ => rfl⟩
    cases x.1.1 with
    | none => trivial
    | some o => exact OutAlike.refl o) (relB_refl _)

/-- Two plans of one sub-proof: all is equal but the checks. -/
def PlanAlike (s s' : SubPlanH) : Prop :=
  s' = { s with run := s'.run } ∧ Over.K s.run ∧ RunFree s.run s'.run

theorem PlanAlike.link {s s' : SubPlanH} (h : PlanAlike s s') (name : String) (gid kind g : Nat)
    (fv : Bool) : LinkAlike (s.link name gid kind g fv) (s'.link name gid kind g fv) := by
  obtain ⟨e, k, r⟩ := h
  generalize s'.run = r' at e r
  subst e
  exact ⟨rfl, k, r⟩

/-- One turn of the loop of `listLinksH`. -/
def stepLinks (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) (x : SubPlanH × Nat)
    (links : Array LinkH) : Array LinkH :=
  if p4 = true then
    match A[x.2]? with
    | some a =>
      (links.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)).push
        (a.link ("A" ++ toString x.2) (2 + NGr + x.2) 1 x.2 false)
    | none => links.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)
  else links.push (x.1.link ("G" ++ toString x.2) (1 + x.2) 0 x.2 true)

/-- A loop whose every turn goes on is a fold. -/
theorem forIn_yield {ε α β : Type} {f : α → β → Except ε (ForInStep β)} {g : α → β → β}
    (h : ∀ a s, f a s = .ok (.yield (g a s))) :
    ∀ (l : List α) (init : β), forIn l init f = .ok (l.foldl (fun s a => g a s) init)
  | [], _ => rfl
  | a :: l, init => by
      rw [List.forIn_cons, h]
      exact forIn_yield h l (g a init)

/-- The list of the links, written as a fold. -/
theorem listLinksH_ok {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {links : Array LinkH} (h : listLinksH NGr p4 G A H = .ok links) :
    links = (G.toList.zipIdx.foldl (fun s x => stepLinks NGr p4 A x s) #[]).push
      (H.link "H" (1 + NGr) 2 0 true) := by
  unfold listLinksH at h
  dsimp only at h
  split at h
  · cases h
  rw [forIn_yield (g := stepLinks NGr p4 A)] at h
  · cases h
    rfl
  · intro x s
    obtain ⟨sp, g⟩ := x
    unfold stepLinks
    dsimp only
    split
    · generalize A[g]? = o
      cases o <;> rfl
    · rfl

theorem all2_zipIdx {l l' : List SubPlanH} (h : All2 PlanAlike l l') :
    ∀ k : Nat, All2 (fun x x' => PlanAlike x.1 x'.1 ∧ x.2 = x'.2) (l.zipIdx k) (l'.zipIdx k) := by
  induction h with
  | nil => exact fun _ => .nil
  | cons h0 _ ih => exact fun k => .cons ⟨h0, rfl⟩ (ih (k + 1))

theorem all2_push {s s' : Array LinkH} {x x' : LinkH} (h : All2 LinkAlike s.toList s'.toList)
    (hx : LinkAlike x x') : All2 LinkAlike (s.push x).toList (s'.push x').toList := by
  rw [Array.toList_push, Array.toList_push]
  exact h.append (.cons hx .nil)

theorem stepLinks_alike (NGr : Nat) (p4 : Bool) {A : Array SubPlanH}
    (hA : ∀ s ∈ A, Over.K s.run) {x x' : SubPlanH × Nat} (hx : PlanAlike x.1 x'.1 ∧ x.2 = x'.2)
    {s s' : Array LinkH} (hs : All2 LinkAlike s.toList s'.toList) :
    All2 LinkAlike (stepLinks NGr p4 A x s).toList (stepLinks NGr p4 A x' s').toList := by
  obtain ⟨sp, g⟩ := x
  obtain ⟨sp', g'⟩ := x'
  obtain ⟨hp, hg⟩ := hx
  have hg' : g = g' := hg
  subst hg'
  unfold stepLinks
  dsimp only
  split
  · cases ha : A[g]? with
    | none => exact all2_push hs (hp.link ..)
    | some a =>
      exact all2_push (all2_push hs (hp.link ..))
        (PlanAlike.link ⟨rfl, hA a (Array.mem_of_getElem? ha), RunFree.refl _⟩ ..)
  · exact all2_push hs (hp.link ..)

/-- **Two lists of links from plans that are alike.** -/
theorem listLinksH_alike {NGr : Nat} {p4 : Bool} {G G' A : Array SubPlanH} {H H' : SubPlanH}
    {links links' : Array LinkH} (h : listLinksH NGr p4 G A H = .ok links)
    (h' : listLinksH NGr p4 G' A H' = .ok links') (hG : All2 PlanAlike G.toList G'.toList)
    (hA : ∀ s ∈ A, Over.K s.run) (hH : PlanAlike H H') :
    All2 LinkAlike links.toList links'.toList := by
  rw [listLinksH_ok h, listLinksH_ok h']
  refine all2_push ?_ (hH.link ..)
  have key : ∀ {l l' : List (SubPlanH × Nat)},
      All2 (fun x x' => PlanAlike x.1 x'.1 ∧ x.2 = x'.2) l l' → ∀ {s s' : Array LinkH},
      All2 LinkAlike s.toList s'.toList →
      All2 LinkAlike (l.foldl (fun s x => stepLinks NGr p4 A x s) s).toList
        (l'.foldl (fun s x => stepLinks NGr p4 A x s) s').toList := by
    intro l l' hl
    induction hl with
    | nil => exact fun hs => hs
    | cons h0 _ ih => exact fun hs => ih (stepLinks_alike NGr p4 hA h0 hs)
  exact key (all2_zipIdx hG 0) .nil

/-- The links as built, each with the check of the link at its place. -/
theorem zipWith_alike : ∀ (bs : List LinkH) {ls ls' : List LinkH}, All2 LinkAlike ls ls' →
    All2 LinkAlike (List.zipWith (fun (b l : LinkH) => { b with run := l.run }) bs ls)
      (List.zipWith (fun (b l : LinkH) => { b with run := l.run }) bs ls')
  | [], _, _, _ => by simp only [List.zipWith_nil_left]; exact .nil
  | _ :: _, _, _, .nil => by simp only [List.zipWith_nil_right]; exact .nil
  | b :: bs, _, _, .cons h0 h1 => by
      rw [List.zipWith_cons_cons, List.zipWith_cons_cons]
      exact .cons ⟨rfl, h0.2.1, h0.2.2⟩ (zipWith_alike bs h1)

/-! ## The theorem -/

/-- A step of a computation that can refuse. -/
private theorem ok_bind' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = .ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

private theorem needed_ok {b : Bool} {name : String} {u : Unit}
    (h : Head.needed b name = .ok u) : b = true := by
  unfold Head.needed at h
  cases b with
  | true => rfl
  | false => cases h

/-- What `Head.coveredOf` returns has T tokens, each below V. -/
theorem covered_tokens {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (h : Head.coveredOf so T V = .ok cov) :
    cov.tokv.size = T ∧ cov.tokv.all (fun v => decide (v < V)) = true := by
  unfold Head.coveredOf at h
  obtain ⟨_, -, h⟩ := ok_bind' h
  obtain ⟨_, h2, h⟩ := ok_bind' h
  dsimp only at h
  obtain ⟨_, h3, h⟩ := ok_bind' h
  obtain ⟨_, -, h⟩ := ok_bind' h
  cases h
  have h2' := needed_ok h2
  have h3' := needed_ok h3
  refine ⟨?_, h3'⟩
  simp only [beq_iff_eq] at h2'
  simp only [Array.size_map, Array.size_extract, h2']
  omega

/-- No token is V' or more, if V is at most V'. -/
theorem none_from {t : Array Nat} {V V' : Nat} (h : t.all (fun v => decide (v < V)) = true)
    (hV : V ≤ V') : t.any (· ≥ V') = false := by
  rw [Array.any_eq_false]
  rw [Array.all_eq_true] at h
  intro i hi
  have := h i hi
  simp only [decide_eq_true_eq] at this ⊢
  omega

/-- **The rounds of a proof's first chain do not hang on the request**, under the four statements.
hV: the size of the vocabulary by which the request's tokens are tested is at most the one that the
checks of the layers hold; `Verify.publicOf` lays one number at both places. -/
theorem plannedFirstFree_of (hL : LayerFree) (hP : PendingFree) (hM : MemberFree)
    (p : Verify.Planned) (hH : HeadFree p) (hV : p.X.P.h.V ≤ p.X.layers.V) :
    PlannedFirstFree p := by
  intro so so' cov cov' links links' hc hc' hl hl'
  have hA : All2 LinkAlike links.toList links'.toList := by
    refine listLinksH_alike hl hl' ?_ ?_ ⟨rfl, head_run _ _, hH so so' cov cov' hc hc'⟩
    · rw [Array.toList_mapIdx, Array.toList_mapIdx]
      have t1 := covered_tokens hc
      have t2 := covered_tokens hc'
      have key : ∀ (l : List Layer.HPlan2) (k : Nat),
          All2 PlanAlike
            (l.mapIdx fun g hp => Verify.layersPlanOf p.X cov.tokv (g + k) hp)
            (l.mapIdx fun g hp => Verify.layersPlanOf p.X cov'.tokv (g + k) hp) := by
        intro l
        induction l with
        | nil => exact fun _ => .nil
        | cons hp l ih =>
          intro k
          rw [List.mapIdx_cons, List.mapIdx_cons]
          refine .cons ⟨rfl, layers_run _ _ _ _, hL _ _ _ _ _ (t1.1.trans t2.1.symm)
            ((none_from t1.2 hV).trans (none_from t2.2 hV).symm)⟩ ?_
          have := ih (k + 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k] using this
      exact key _ 0
    · intro s hs
      obtain ⟨a, _, rfl⟩ := Array.mem_map.1 hs
      exact attention_run a
  have hZ : All2 LinkAlike
      (p.built.links.zipWith (fun b l => { b with run := l.run }) links).toList
      (p.built.links.zipWith (fun b l => { b with run := l.run }) links').toList := by
    rw [Array.toList_zipWith, Array.toList_zipWith]
    exact zipWith_alike _ hA
  exact firstFree_of_rel hM _ (links_keep hl _ _ _) (runLinksH_rel hP hZ _ _)

end OnBytes.Flat
