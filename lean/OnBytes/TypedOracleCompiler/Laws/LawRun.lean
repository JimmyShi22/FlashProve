-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawRun.lean: from a pair of blocks that carries `Alike G d`
(OnBytes/TypedOracleCompiler/Laws/LawAlike.lean) to the three functions by which the program runs a block
(OnBytes/Iop/Ground.lean): `Blk.runNamed`, `Blk.runOn` (the run on a whole view, for the verdict),
`Blk.dryRun` (the rounds of a chain's description, and the block's value).

Main names.
  `StartAlike G s s'`   two starts: equal but for the given sources in the book
  `ViewAlike v v'`      two views: equal but for the digests drawn
  `ExAlike Q`           two results of a run on a view: one failure, or values in Q
  `RoundAlike G`        a round of a description with its stored trees: equal but for given sources
  `Carries.runOn`       law 2 at a whole run: from starts and views that are alike, the two runs are
                        refused under one name, or both give values in Q
  `Carries.dryRun`      law 1 at a whole dry run: from starts that are alike, both dry runs fail, or
                        both give rounds that are alike and values in Q
  `NoGiven`, `roundAlike_eq`   under the G that no two given sources meet, "alike" is "equal"

Not claimed. Nothing on any block in particular.

-/
import OnBytes.TypedOracleCompiler.Laws.LawGround

namespace OnBytes.TwoLaws

open OnBytes

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

theorem ArrAlike.empty {α : Type} (P : α → α → Prop) : ArrAlike P #[] #[] := fun i => by
  simp only [Array.getElem?_empty]; exact .none

theorem LAlike.of_get {α : Type} {P : α → α → Prop} {l l' : List α}
    (h : ∀ i : Nat, OptAlike P l[i]? l'[i]?) : LAlike P l l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => exact .nil
    | cons b t =>
      have k := h 0
      simp only [List.getElem?_nil, List.getElem?_cons_zero] at k
      cases k
  | cons a l ih =>
    cases l' with
    | nil =>
      have k := h 0
      simp only [List.getElem?_nil, List.getElem?_cons_zero] at k
      cases k
    | cons b t =>
      refine .cons ?_ (ih fun i => ?_)
      · have k := h 0
        simp only [List.getElem?_cons_zero] at k
        cases k
        assumption
      · have k := h (i + 1)
        simpa only [List.getElem?_cons_succ] using k

theorem ArrAlike.toList {α : Type} {P : α → α → Prop} {a b : Array α} (h : ArrAlike P a b) :
    LAlike P a.toList b.toList :=
  LAlike.of_get fun i => by
    have k := h i
    rwa [← Array.getElem?_toList, ← Array.getElem?_toList] at k

theorem LAlike.map {α β : Type} {P : α → α → Prop} {P' : β → β → Prop} {l l' : List α}
    {f g : α → β} (h : LAlike P l l') (hf : ∀ a b, P a b → P' (f a) (g b)) :
    LAlike P' (l.map f) (l'.map g) := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons (hf _ _ a) ih

theorem LAlike.isEmpty_eq {α : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l') :
    l.isEmpty = l'.isEmpty := by
  cases h <;> rfl

theorem OptAlike.isNone_eq {α : Type} {P : α → α → Prop} {x y : Option α} (h : OptAlike P x y) :
    x.isNone = y.isNone := by
  cases h <;> rfl

/-- Two starts: equal but for the given sources in the book. -/
structure StartAlike (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop) (s s' : Start) :
    Prop where
  entries : s.entries = s'.entries
  samples : s.samples = s'.samples
  firstTree : s.firstTree = s'.firstTree
  st : s.st = s'.st
  book : BookAlike G s.book s'.book

/-- Two views: equal but for the digests drawn. -/
structure ViewAlike (v v' : Fmt.View) : Prop where
  rounds : LAlike RVAlike v.rounds v'.rounds
  opened : v.opened = v'.opened

theorem Carries.runNamed {α : Type} {Q : α → α → Prop} {b b' : Blk α}
    (h : Carries (Alike G d) Q b b') {s s' : Start} (hs : StartAlike G s s') (dry : Bool)
    {l l' : List Fmt.RoundView} (hl : LAlike RVAlike l l') (op : List (Nat × Nat × List UInt64))
    (keep : Bool) (hd : d = true → dry = true ∧ keep = false) :
    Out (Alike G d) Q (b.runNamed s dry l op keep) (b'.runNamed s' dry l' op keep) := by
  unfold Blk.runNamed
  rw [← hs.st]
  split
  · exact h _ _ ⟨rfl, hs.firstTree, hs.samples, hs.entries, hl, .none, rfl, rfl, rfl, rfl, rfl,
      ArrAlike.empty _, rfl, hs.book, rfl, rfl, rfl, hd⟩
  · exact Out.err _

/-- Two results of a run on a view: one failure, or values in Q. -/
inductive ExAlike {α : Type} (Q : α → α → Prop) : Except Failure α → Except Failure α → Prop
  | ok {a b : α} : Q a b → ExAlike Q (.ok a) (.ok b)
  | error (e : Failure) : ExAlike Q (.error e) (.error e)

theorem settled_eq {c c' : Ctx} (h : Alike G d c c') : c.ch.settled = c'.ch.settled := by
  unfold Chan.settled
  rw [h.last, h.askedRows]

/-- Law 2 at a whole run. -/
theorem Carries.runOn {α : Type} {Q : α → α → Prop} {b b' : Blk α}
    (h : Carries (Alike G false) Q b b') {s s' : Start} (hs : StartAlike G s s')
    {v v' : Fmt.View} (hv : ViewAlike v v') : ExAlike Q (b.runOn s v) (b'.runOn s' v') := by
  have k := h.runNamed hs false hv.rounds v.opened false (fun e => nomatch e)
  unfold Blk.runOn
  rw [← hv.opened]
  generalize b.runNamed s false v.rounds v.opened = x at k
  generalize b'.runNamed s' false v'.rounds v.opened = y at k
  cases x with
  | error e =>
    cases y with
    | error f => cases k; exact .error _
    | ok q => exact k.elim
  | ok p =>
    cases y with
    | error f => exact k.elim
    | ok q =>
      obtain ⟨a, c⟩ := p
      obtain ⟨a', c'⟩ := q
      obtain ⟨hq, hc⟩ := k
      dsimp only at hq hc ⊢
      rw [hc.failed, hc.entries, settled_eq hc, hc.cur.isNone_eq, hc.opened, hc.left.isEmpty_eq]
      split
      · exact .error _
      · split
        · exact .error _
        · split
          · exact .ok hq
          · exact .error _

/-- A round of a description with its stored trees: equal but for given sources. -/
structure RoundAlike (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop)
    (x y : Fmt.Round × List Fmt.Stored) : Prop where
  entry : x.1.entry = y.1.entry
  kind : x.1.kind = y.1.kind
  items : x.1.items = y.1.items
  opens : LAlike (OpenAlike G) x.1.opens y.1.opens
  stored : x.2 = y.2

/-- Law 1 at a whole dry run. -/
theorem Carries.dryRun {α : Type} {Q : α → α → Prop} {b b' : Blk α}
    (h : Carries (Alike G true) Q b b') {s s' : Start} (hs : StartAlike G s s') :
    OptAlike (fun x y => LAlike (RoundAlike G) x.1 y.1 ∧ Q x.2 y.2) (b.dryRun s)
      (b'.dryRun s') := by
  have k := h.runNamed hs true .nil [] false (fun _ => ⟨rfl, rfl⟩)
  unfold Blk.dryRun Blk.dryRunNamed
  generalize b.runNamed s true [] [] = x at k
  generalize b'.runNamed s' true [] [] = y at k
  cases x with
  | error e =>
    cases y with
    | error f => exact .none
    | ok q => exact k.elim
  | ok p =>
    cases y with
    | error f => exact k.elim
    | ok q =>
      obtain ⟨a, c⟩ := p
      obtain ⟨a', c'⟩ := q
      obtain ⟨hq, hc⟩ := k
      dsimp only at hq hc ⊢
      rw [hc.entries, hc.items, settled_eq hc]
      split
      · exact .some ⟨hc.noted.toList.map fun _ _ n =>
          ⟨n.entry, n.kind, n.items, n.opens, n.stored⟩, hq⟩
      · exact .none

/-- The G that no two given sources meet. -/
def NoGiven : ByteArray → ByteArray → ByteArray → ByteArray → Prop := fun _ _ _ _ => False

theorem LAlike.eq_of {α : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l')
    (hp : ∀ a b, P a b → a = b) : l = l' := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [hp _ _ a, ih]

theorem openAlike_eq {x y : Fmt.Shape × Fmt.Src} (h : OpenAlike NoGiven x y) : x = y := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h1
  cases h2 with
  | own n => rfl
  | given k => exact k.elim

/-- Where no given source is met, rounds that are alike are equal. -/
theorem roundAlike_eq {x y : Fmt.Round × List Fmt.Stored} (h : RoundAlike NoGiven x y) : x = y := by
  obtain ⟨⟨e, k, i, o⟩, s⟩ := x
  obtain ⟨⟨e', k', i', o'⟩, s'⟩ := y
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h5
  rw [h4.eq_of fun _ _ => openAlike_eq]

end OnBytes.TwoLaws
