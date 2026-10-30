-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawDry.lean: law 1 ("the descriptions are constants") where the two texts differ:
two blocks that are one routine at two arguments that hold values (a table's key; a reply). The
relation on contexts is `Alike G true` (OnBytes/TypedOracleCompiler/Laws/LawAlike.lean): both runs are dry and keep
no intermediate values.

Main names.
  `Dry G b b'`     the class: `Carries (Alike G true) Eq b b'`: from dry contexts that are alike the
                   two texts fail alike, or return equal values and leave contexts that are alike:
                   so they have noted the same rounds (but for given sources, which go together
                   under G)
  `dry_same`       one text (from the walk of law 2, which holds for every d)
  `dry_test`, `check`, `onView`, `getOnView`, `testOnView`, `checkOnView`, `note`, `noteBy`,
  `requireRows`, `addRowsOnView`   the ten calls of OnBytes/Iop/Ground.lean in which a dry run does
                   not look at an argument: the two texts may differ there at will
  `dry_addRow`     a dry run reads the row's kind alone
  `lock`           the tactic: instances, else a binder, a bind, a match or an if, a let
  `KeyAlike`       two keys of a table: one item, records of one size, as many seeds, points of one
                   length. What a dry run does read of a key.
  `dry_foldeqVerify`, `dry_linSharedVerify`, `carries_sharedBlock_dry`
  `carries_firstBlock_dry`   the frame of a proof's first chain, over a hypothesis that the real
                   links do not meet by this file's means: `Dry` asks equal values at every bind,
                   and in the layers' first link the values hang on the request's words
                   (OnBytes/Model/Layer.lean). For a proof file this file gives the shared chain's
                   rounds and, in pieces, the second chain's; nothing of the first chain's.
  `second_rounds_alike`, `rounds_renamed`   the second chain's rounds, in pieces
  `shared_dryRun_eq`   the shared chain's description and what its dry run returns are equal at two
                   keys that are alike

Not claimed. Nothing on a run on a view. Nothing on the caller's links but as a hypothesis.

-/
import OnBytes.TypedOracleCompiler.Laws.LawTail
import OnBytes.Proof.File

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Proof

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop}

/-- Two texts in a dry run: alike in failing, equal in value, alike in what they leave. -/
class Dry {α : Type} (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop) (b b' : Blk α) :
    Prop where
  out : Carries (Alike G true) Eq b b'

instance dry_same {α : Type} (b : Blk α) [h : Same (Alike G true) b] : Dry G b b := ⟨h.out⟩

theorem Dry.bind {α β : Type} {b b' : Blk α} {f f' : α → Blk β} (hb : Dry G b b')
    (hf : ∀ x, Dry G (f x) (f' x)) : Dry G (b >>= f) (b' >>= f') :=
  ⟨Carries.bind hb.out fun x _ e => e ▸ (hf x).out⟩

instance dry_bind {α β : Type} (b b' : Blk α) (f f' : α → Blk β) [hb : Dry G b b']
    [hf : ∀ x, Dry G (f x) (f' x)] : Dry G (b >>= f) (b' >>= f') := Dry.bind hb hf

instance dry_ite {α : Type} (p : Prop) [Decidable p] (a a' b b' : Blk α) [ha : Dry G a a']
    [hb : Dry G b b'] : Dry G (if p then a else b) (if p then a' else b') :=
  ⟨Carries.ite Iff.rfl ha.out hb.out⟩

-- dry_prim: for a call that is a function of the context, in a dry run that keeps no notes.
set_option hygiene false in
macro "dry_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨?_⟩
      alike_open
      obtain ⟨hd1, hd2⟩ := hd rfl
      subst hd1 hd2
      unfold $d
      simp only [Bool.or_true, Bool.true_or, ↓reduceIte, Bool.false_eq_true]
      repeat' split
      all_goals first
        | exact Out.err _
        | exact Out.ok rfl (by
            constructor <;> first | rfl | assumption | exact fun _ => ⟨rfl, rfl⟩)))

instance dry_test (b b' : Bool) (n : String) : Dry G (Blk.test b n) (Blk.test b' n) := by
  dry_prim Blk.test
instance dry_check (n : String) (b b' : Bool) : Dry G (Blk.check n b) (Blk.check n b') := by
  dry_prim Blk.check
instance dry_onView {α : Type} (x : α) (f f' : Unit → α) :
    Dry G (Blk.onView x f) (Blk.onView x f') := by
  dry_prim Blk.onView
instance dry_getOnView {α : Type} (x : α) (f f' : Unit → Option α) (n : String) :
    Dry G (Blk.getOnView x f n) (Blk.getOnView x f' n) := by
  dry_prim Blk.getOnView
instance dry_testOnView (f f' : Unit → Bool) (n : String) :
    Dry G (Blk.testOnView f n) (Blk.testOnView f' n) := by
  dry_prim Blk.testOnView
instance dry_checkOnView (n : String) (f f' : Unit → Bool) :
    Dry G (Blk.checkOnView n f) (Blk.checkOnView n f') := by
  dry_prim Blk.checkOnView
instance dry_note (w : String) (v v' : E) : Dry G (Blk.note w v) (Blk.note w v') := by
  dry_prim Blk.note
instance dry_noteBy (w : String) (v v' : Unit → E) : Dry G (Blk.noteBy w v) (Blk.noteBy w v') := by
  dry_prim Blk.noteBy
instance dry_requireRows (r r' : Nat) : Dry G (Blk.requireRows r) (Blk.requireRows r') := by
  dry_prim Blk.requireRows

/-- In a dry run the flag says so. -/
theorem carries_isDry :
    Carries (Alike G true) (fun x y => x = true ∧ y = true) Blk.isDry Blk.isDry := by
  alike_open
  obtain ⟨hd1, hd2⟩ := hd rfl
  subst hd1 hd2
  exact Out.ok ⟨rfl, rfl⟩ (by
    constructor <;> first | rfl | assumption | exact fun _ => ⟨rfl, rfl⟩)

/-- Two texts that take the book and go on alike from books that are alike. -/
theorem dry_of_theBook {β : Type} {f f' : TreeBook → Blk β}
    (hf : ∀ B B', BookAlike G B B' → Dry G (f B) (f' B')) :
    Dry G (Blk.theBook >>= f) (Blk.theBook >>= f') :=
  ⟨Carries.bind carries_theBook fun B B' h => (hf B B' h).out⟩

/-- Two texts that close a round and go on without the digest. -/
theorem dry_of_close {β : Type} (n : String) (k : Fmt.Kind) (nz : Nat) {f f' : Fmt.Drawn → Blk β}
    (hf : ∀ e p t g g', Dry G (f ⟨e, p, t, g⟩) (f' ⟨e, p, t, g'⟩)) :
    Dry G (Blk.close n k nz >>= f) (Blk.close n k nz >>= f') :=
  ⟨Carries.bind (carries_close n k nz) fun x x' h => by
    obtain ⟨e, p, t, g⟩ := x
    obtain ⟨e', p', t', g'⟩ := x'
    obtain ⟨h1, h2, h3⟩ := h
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    exact (hf _ _ _ _ _).out⟩

/-- The tactic for two texts in a dry run. -/
macro "lock" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | (with_reducible refine dry_of_close _ _ _ (fun _ _ _ _ _ => ?_); try dsimp only)
      | (with_reducible refine dry_of_theBook (fun _ _ hB => ?_); simp only [linAlone_alike hB])
      | with_reducible apply Dry.bind
      | split
      | dsimp only)

/-- A dry run reads the kind of a new row, and no more of it. -/
theorem dry_addRow (g : Nat) {r r' : Row} (h : r.kind = r'.kind) :
    Dry G (Blk.addRow g r) (Blk.addRow g r') := by
  refine ⟨?_⟩
  unfold Blk.addRow
  rw [h]
  refine Carries.bind_same fun S => ?_
  refine Carries.bind_same fun Gr => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind carries_isDry fun x y hxy => ?_
  obtain ⟨rfl, rfl⟩ := hxy
  simp only [↓reduceIte]
  exact Carries.pure rfl

instance dry_addRowsOnView (g : Nat) (r r' : Unit → Option (List Row)) :
    Dry G (Blk.addRowsOnView g r) (Blk.addRowsOnView g r') := by
  unfold Blk.addRowsOnView; lock

/-! ## A table's key -/

/-- What a dry run reads of a key. -/
structure KeyAlike (k k' : TableKey) : Prop where
  item : k.item = k'.item
  record : k.record.size = k'.record.size
  seeds : LAlike (fun a b : SampleSeed => a.z.length = b.z.length) k.seeds k'.seeds

theorem LAlike.length_eq {α : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l') :
    l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem LAlike.all_eq {α : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l')
    (f : α → Bool) (hf : ∀ a b, P a b → f a = f b) : l.all f = l'.all f := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.all_cons, hf _ _ a, ih]

theorem KeyAlike.fits {k k' : TableKey} (h : KeyAlike k k') (s : Params.IndexShape) :
    k.fits s = k'.fits s := by
  unfold TableKey.fits
  rw [h.record, h.seeds.length_eq, h.seeds.all_eq _ fun a b e => by rw [e]]

/-- Of the key, foldeqJoined hands seeds and record to rows that only a run on a view computes. -/
instance dry_foldeqJoined (S : Params.FoldeqShape) (k k' : TableKey) (e : Array E) (o g : Nat) :
    Dry G (foldeqJoined S k e o g) (foldeqJoined S k' e o g) := by
  unfold foldeqJoined; lock

section key
variable {k k' : TableKey} (hk : KeyAlike k k')
include hk

theorem dry_foldeqRequire (S : Params.FoldeqShape) :
    Dry G (foldeqRequire k S) (foldeqRequire k' S) := by
  unfold foldeqRequire
  rw [hk.fits]
  lock

theorem dry_foldeqColumnsVerify (S : Params.FoldeqShape) (e : Array E) (pos : Positions)
    (first : Nat) (u : FoldedRow) (g : Nat) :
    Dry G (foldeqColumnsVerify k S e pos first u g) (foldeqColumnsVerify k' S e pos first u g) := by
  have h : foldeqColumnsVerify k S e pos first u g = foldeqColumnsVerify k' S e pos first u g := by
    unfold foldeqColumnsVerify
    rw [hk.item]
  rw [h]
  infer_instance

theorem dry_foldeqVerify (S : Params.FoldeqShape) (gamma : List E) (g : Nat)
    (others : Array OracleNotice) :
    Dry G (foldeqVerify k S gamma g others) (foldeqVerify k' S gamma g others) := by
  have i1 := dry_foldeqRequire (G := G) hk
  have i3 := dry_foldeqColumnsVerify (G := G) hk
  unfold foldeqVerify
  obtain ⟨it, re, se⟩ := k
  obtain ⟨it', re', se'⟩ := k'
  have hs := hk.seeds
  dsimp only at hs
  cases hs <;> simp only [List.head?_nil, List.head?_cons] <;> lock

theorem dry_linSharedVerify (S : Params.LinShape) :
    Dry G (linSharedVerify S k) (linSharedVerify S k') := by
  have i1 := dry_foldeqVerify (G := G) hk
  unfold linSharedVerify
  lock

/-- Law 1 at the shared chain's block: two keys that are alike. -/
theorem carries_sharedBlock_dry (S : Params.LinShape) :
    Carries (Alike G true) (SharedEndAlike G) (sharedBlock S k) (sharedBlock S k') := by
  unfold sharedBlock
  refine Carries.bind (dry_linSharedVerify hk S).out fun x _ e => ?_
  subst e
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind (carries_close _ _ _) fun _ _ _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind carries_handOver fun h h' hh => ?_
  exact Carries.pure ⟨hh.1, hh.2, rfl⟩

end key

/-! ## Where no given source is met, "alike" is "equal" -/

theorem treeAlike_eq {a b : Tree} (h : TreeAlike NoGiven a b) : a = b := by
  obtain ⟨sh, nu, sr, pa, ol, li⟩ := a
  obtain ⟨sh', nu', sr', pa', ol', li'⟩ := b
  obtain ⟨e1, e2, hs, e4, e5, e6⟩ := h
  dsimp only at e1 e2 hs e4 e5 e6
  subst e1 e2 e4 e5 e6
  cases hs with
  | own n => rfl
  | given k => exact k.elim

theorem bookAlike_eq {A B : TreeBook} (h : BookAlike NoGiven A B) : A = B := by
  obtain ⟨t, p⟩ := A
  obtain ⟨t', p'⟩ := B
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h2
  have e : t = t' := by
    apply Array.toList_inj.1
    exact h1.toList.eq_of fun _ _ => treeAlike_eq
  rw [e]

theorem sharedEndAlike_eq {a b : SharedEnd} (h : SharedEndAlike NoGiven a b) : a = b := by
  obtain ⟨s, bk, l⟩ := a
  obtain ⟨s', bk', l'⟩ := b
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  subst h1 h3
  rw [bookAlike_eq h2]

/-- Law 1 at the shared chain, whole: at two keys that are alike the dry run of the shared chain's
block gives one list of rounds and one value (or fails at both). -/
theorem shared_dryRun_eq (p : TailPublic) {k k' : TableKey} (hk : KeyAlike k k') :
    (sharedBlock p.lin k).dryRun (sharedStart p) = (sharedBlock p.lin k').dryRun (sharedStart p) := by
  have s2 : StartAlike NoGiven (sharedStart p) (sharedStart p) :=
    ⟨rfl, rfl, rfl, rfl, ⟨ArrAlike.empty _, rfl⟩⟩
  have h := (carries_sharedBlock_dry (G := NoGiven) hk p.lin).dryRun s2
  generalize (sharedBlock p.lin k).dryRun (sharedStart p) = x at h
  generalize (sharedBlock p.lin k').dryRun (sharedStart p) = y at h
  cases h with
  | none => rfl
  | some q =>
    rename_i a b
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    obtain ⟨q1, q2⟩ := q
    dsimp only at q1 q2
    rw [q1.eq_of fun _ _ => roundAlike_eq, sharedEndAlike_eq q2]

/-! ## The second chain: its description at a renaming of the sources -/

/-- What a dry run of the second chain's block reads of what the first part has passed on: the four
numbers. The claim reaches a row that only a run on a view computes. -/
structure LinFirstAlike (a b : LinFirst) : Prop where
  w : a.w = b.w
  split : a.split = b.split
  own : a.own = b.own
  mask : a.mask = b.mask

/-- What the dry run of a first chain's block returns, as far as a later dry run reads it. -/
structure FirstEndDry (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop)
    (a b : FirstEnd) : Prop where
  st : a.st = b.st
  book : BookAlike G a.book b.book
  lin : LinFirstAlike a.lin b.lin

theorem carries_secondBlock_dry (S : Params.LinShape) {f f' : LinFirst} (hf : LinFirstAlike f f')
    {e e' : SharedEnd} (he : SharedEndAlike G e e') :
    Carries (Alike G true) Eq (secondBlock S f e) (secondBlock S f' e') := by
  obtain ⟨w, sp, ow, ma, cl⟩ := f
  obtain ⟨w', sp', ow', ma', cl'⟩ := f'
  obtain ⟨h1, h2, h3, h4⟩ := hf
  dsimp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  unfold secondBlock linSecondVerify linSecondTestsVerify
  rw [he.st, he.lin]
  dsimp only
  refine Carries.bind (P := Eq)
    (Carries.bind (P := Eq) (carries_linAdopt _ he.book _ _) fun o _ h => ?_) fun x _ h => ?_
  · subst h
    exact (by lock : Dry G _ _).out
  · subst h
    exact Carries.of_same (by walk)

/-- Law 1 at the second chain, whole. Two dry runs of the first chain's block whose values are alike
as far as a dry run reads them; two readings of the first and of the shared chain whose trees' names
go together under G, tree by tree, and that have as many roots on the first chain. Then the two
descriptions of the second chain are both missing, or are alike round by round: equal but for the
given sources of the openings, which go together under G. -/
theorem second_rounds_alike (p : TailPublic) {dry dry' : FirstEnd} (hd : FirstEndDry G dry dry')
    {end2 end2' : SharedEnd} (he : SharedEndAlike G end2 end2')
    (first first' shared shared' : ChainRead)
    (h1 : ∀ n, SrcAlike G (treesOf first n) (treesOf first' n))
    (h2 : ∀ n, SrcAlike G (treesOf shared n) (treesOf shared' n))
    (hn : first.roots.length = first'.roots.length) :
    OptAlike (LAlike (RoundAlike G))
      ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
      ((secondBlock p.lin dry'.lin (end2'.goesOn shared')).rounds (secondStart p dry' first')) := by
  have q : SharedEndAlike G (end2.goesOn shared) (end2'.goesOn shared') :=
    ⟨he.st, he.book.goesOn h2, he.lin⟩
  have s3 : StartAlike G (secondStart p dry first) (secondStart p dry' first') :=
    ⟨rfl, rfl, by unfold secondStart secondFirstTree; rw [hn], hd.st, hd.book.goesOn h1⟩
  have h := (carries_secondBlock_dry p.lin hd.lin q).dryRun s3
  unfold Blk.rounds
  generalize (secondBlock p.lin dry.lin (end2.goesOn shared)).dryRun _ = x at h
  generalize (secondBlock p.lin dry'.lin (end2'.goesOn shared')).dryRun _ = y at h
  cases h with
  | none => exact .none
  | some k => exact .some k.1

/-! ## From one G to another; a renaming -/

theorem SrcAlike.mono {G' : ByteArray → ByteArray → ByteArray → ByteArray → Prop}
    (hg : ∀ r s r' s', G r s r' s' → G' r s r' s') {a b : Fmt.Src} (h : SrcAlike G a b) :
    SrcAlike G' a b := by
  cases h with
  | own n => exact .own n
  | given k => exact .given (hg _ _ _ _ k)

/-- A book without a given source (alike to another under NoGiven) is alike to it under every G. -/
theorem BookAlike.of_noGiven {A B : TreeBook} (h : BookAlike NoGiven A B) : BookAlike G A B :=
  ⟨fun i => by
    have k := h.trees i
    generalize A.trees[i]? = x at k
    generalize B.trees[i]? = y at k
    cases k with
    | none => exact .none
    | some t => exact .some ⟨t.shape, t.number, t.src.mono (fun _ _ _ _ f => f.elim), t.parts,
        t.oneList, t.lists⟩, h.place⟩

/-- The graph of a renaming of given sources. -/
def Renames (φ : ByteArray → ByteArray → ByteArray × ByteArray) :
    ByteArray → ByteArray → ByteArray → ByteArray → Prop :=
  fun r s r' s' => (r', s') = φ r s

/-- A source, renamed. -/
def renameSrc (φ : ByteArray → ByteArray → ByteArray × ByteArray) : Fmt.Src → Fmt.Src
  | .own n => .own n
  | .given r s => .given (φ r s).1 (φ r s).2

/-- A round of a description, with the given sources of its openings renamed. -/
def renameRound (φ : ByteArray → ByteArray → ByteArray × ByteArray)
    (x : Fmt.Round × List Fmt.Stored) : Fmt.Round × List Fmt.Stored :=
  ({ x.1 with opens := x.1.opens.map fun o => (o.1, renameSrc φ o.2) }, x.2)

theorem LAlike.eq_map {α : Type} {P : α → α → Prop} {l l' : List α} (h : LAlike P l l')
    (f : α → α) (hp : ∀ a b, P a b → b = f a) : l' = l.map f := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [List.map_cons, ← hp _ _ a, ← ih]

/-- "The constant notes, made at tags, with each tag replaced": rounds that are alike under the
graph of a renaming are the first ones, renamed. -/
theorem rounds_renamed {φ : ByteArray → ByteArray → ByteArray × ByteArray}
    {l l' : List (Fmt.Round × List Fmt.Stored)} (h : LAlike (RoundAlike (Renames φ)) l l') :
    l' = l.map (renameRound φ) := by
  refine h.eq_map _ fun x y k => ?_
  obtain ⟨⟨e, kd, i, o⟩, s⟩ := x
  obtain ⟨⟨e', kd', i', o'⟩, s'⟩ := y
  obtain ⟨h1, h2, h3, h4, h5⟩ := k
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h5
  unfold renameRound
  dsimp only
  rw [h4.eq_map (fun o => (o.1, renameSrc φ o.2)) fun a b hab => ?_]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨q1, q2⟩ := hab
  dsimp only at q1 q2 ⊢
  subst q1
  cases q2 with
  | own n => rfl
  | given k =>
    unfold Renames at k
    show (_, Fmt.Src.given _ _) = (_, Fmt.Src.given (φ _ _).1 (φ _ _).2)
    rw [← k]

/-! ## The frame of a proof's first chain -/

/-- Law 1 at firstBlock's frame: two replies at will; two texts of the caller's links that go
together in a dry run with equal values. -/
theorem carries_firstBlock_dry (p : Params.First) {links links' : Blk LinksResult}
    (hl : Dry G links links') (reply reply' : E) :
    Carries (Alike G true) (FirstEndAlike G) (firstBlock p links reply)
      (firstBlock p links' reply') := by
  unfold firstBlock
  refine Carries.bind hl.out fun r _ e => ?_
  subst e
  refine Carries.bind_same fun got => ?_
  refine Carries.bind (dry_check _ _ _).out fun _ _ _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun lin => ?_
  exact carries_firstEnd lin

/-- Law 2 at firstBlock's frame: one text of the caller's links that is blind. -/
theorem carries_firstBlock {d : Bool} (p : Params.First) {links : Blk LinksResult}
    (hl : Same (Alike G d) links) (reply : E) :
    Carries (Alike G d) (FirstEndAlike G) (firstBlock p links reply) (firstBlock p links reply) := by
  unfold firstBlock
  refine Carries.bind_same fun r => ?_
  refine Carries.bind_same fun got => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun lin => ?_
  exact carries_firstEnd lin

#print axioms shared_dryRun_eq
#print axioms second_rounds_alike
#print axioms rounds_renamed
#print axioms carries_firstBlock_dry
#print axioms carries_firstBlock

end OnBytes.TwoLaws
