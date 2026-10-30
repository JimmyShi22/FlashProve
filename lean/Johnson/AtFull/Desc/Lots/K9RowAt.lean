-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K9RowAt.lean: THE ROW OF KIND K9's LOT, PART 2: AT HYPOTHESES BY FIELD. The
  lot's skeleton (k9_row, Johnson/AtFull/Desc/Lots/K9Row.lean) reads the stretches of the declared
  rounds; of a declared round it reads the ENTRY alone. Here stands the twin on entries, the law
  "twin = the text" at every list, and the row under four hypotheses, each on one thing that the lot
  reads of Z.
  General in the four values: no written value stands here.
  Definitions with code, statements and proofs.

THE NAMES.
rootsE, rootsE_eq: the roots that a list of entries sends, counted so that Lean's kernel keeps the
  carried number a numeral (Johnson.G.force).
stretchedE, stretched_entries: ProofFile.stretched on entries; it is that text's value with each round cut
  to its entry.
toE: a stretch cut to its entries. k9WhereE, k10ParE, k9LinksE: the lot's three readers on entries;
  k9Where_eq, k10ParG_eq, k9Links_eq: each is the text's value.
k9SkE: the lot's skeleton as a function of the groups, the stretches of ENTRIES and one Bool a
  segment. k9Sk_eq.
k9_row_at: **(hs : ProofFile.spotsOf Z.cuts = some ps) (he : Z.D.1.map (·.entry) = es) (hg :
  Z.s₀.check.frame.groups = groups) (ht : ∀ l ∈ ls, (K9.testsWhere Z.p.X l 0).isSome = tw l) ⊢
  (lotSk G (k9Ninth Z)).cut ls = (k9SkE groups (stretchedE ps es 0) tw).cut ls**: the form in which
  back_of_skel_cut takes a lot's row. THERE ls IS linksOf B.spots (SkelTab.lean):
  here it is a letter: WHOEVER LAYS THE ROW IN TAKES ls := linksOf ps AT THE VERY ps OF hs, not a
  list of its own.

Limits. Equations of terms. THE FOUR HYPOTHESES ARE PREMISES: nothing here shows that they hold at
  any public files. WHO IS TO GIVE THEM, AS FAR AS IS KNOWN HERE: hs: another file's spots_written
  (282 places; a trial file so far) behind "Z.cuts is the written table of steps" · he: the same
  equation on entries that K4's row takes · hg, ht: nobody known here. STILL OWED BEHIND THIS FILE
  (a part 3): closed facts by Lean's kernel at the written values, with negative lines. A LotSk has
  three fields that are functions (batch, each, tests): so "this lot's cut skeleton is the written
  one" is no equation that the kernel can decide as it stands: the closed facts must be
  back_of_skel_cut's own four Bools over the list of skeletons, or equations at the written places
  and numbers one by one. Nothing is evaluated. Nothing on soundness.
-/
import Johnson.AtFull.Desc.Lots.K9Row
import Johnson.Desc.ProofFile.Law.Skel.SkelTab
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.Lots
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (Where atS)
open ProofFile ProofFile.Sk

/-- The places with their stretches of declared rounds and the roots in front; the like on entries.
-/
abbrev XsD : Type := List (Spot × List Fmt.DeclaredRound × Nat)
abbrev XsE : Type := List (Spot × List Fmt.Entry × Nat)

/-! ### the stretches, on entries -/

/-- a plus the roots that the entries send; the carried number is forced at each step. -/
def rootsE : Nat → List Fmt.Entry → Nat
  | a, [] => a
  | a, e :: es => Johnson.G.force (a + e.roots) fun b => rootsE b es

theorem rootsE_eq : ∀ (ds : List Fmt.DeclaredRound) (a : Nat),
    rootsE a (ds.map (·.entry)) = ds.foldl (fun a d => a + d.entry.roots) a
  | [], _ => rfl
  | d :: ds, a => by
    show Johnson.G.force (a + d.entry.roots) (fun b => rootsE b (ds.map (·.entry))) = _
    rw [Johnson.G.force_eq, rootsE_eq ds]
    rfl

theorem foldl_from (ds : List Fmt.DeclaredRound) : ∀ a n : Nat,
    n + ds.foldl (fun a d => a + d.entry.roots) a =
      ds.foldl (fun a d => a + d.entry.roots) (n + a) := by
  induction ds with
  | nil => intro a n; rfl
  | cons d ds ih =>
    intro a n
    show n + ds.foldl _ (a + d.entry.roots) = ds.foldl _ (n + a + d.entry.roots)
    rw [ih, Nat.add_assoc]

/-- `ProofFile.stretched` on entries. -/
def stretchedE : List Spot → List Fmt.Entry → Nat → XsE
  | [], _, _ => []
  | p :: ps, es, n =>
    let k := p.cuts.foldl (fun a c => a + c.take) 0
    (p, es.take k, n) :: stretchedE ps (es.drop k) (rootsE n (es.take k))

/-- A stretch cut to its entries. -/
def toE (x : Spot × List Fmt.DeclaredRound × Nat) : Spot × List Fmt.Entry × Nat :=
  (x.1, x.2.1.map (·.entry), x.2.2)

theorem stretched_entries : ∀ (ps : List Spot) (ds : List Fmt.DeclaredRound) (n : Nat),
    (stretched ps ds n).map toE = stretchedE ps (ds.map (·.entry)) n
  | [], _, _ => rfl
  | p :: ps, ds, n => by
    have e : n + (ds.take (p.cuts.foldl (fun a c => a + c.take) 0)).foldl
        (fun a d => a + d.entry.roots) 0 =
        rootsE n ((ds.map (·.entry)).take (p.cuts.foldl (fun a c => a + c.take) 0)) := by
      rw [← List.map_take, rootsE_eq, foldl_from, Nat.add_zero]
    show toE (p, ds.take _, n) :: (stretched ps (ds.drop _) _).map toE =
      (p, (ds.map (·.entry)).take _, n) :: stretchedE ps ((ds.map (·.entry)).drop _) _
    rw [stretched_entries ps, e, List.map_drop, ← List.map_take]
    rfl

/-! ### the lot's three readers, on entries -/

def k9WhereE (xs : XsE) (l : Nat) : Option Where :=
  (xs.find? fun x =>
      x.1.place.kind == .K9 && !x.1.cuts.isEmpty && x.1.place.link == some l).bind fun x =>
    x.2.1.head?.map fun e =>
      { chain := 1, link := l, piece := x.1.place.piece, pieceEq := x.1.place.piece + 2
        rows := e.rows, work := e.work, sent := x.2.2 }

def k10ParE (groups : Array OnBytes.ReqGroup) (xs : XsE) (p : Where) : Option Par :=
  (xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).bind fun x =>
    (groups[p.link]?).bind fun Gr =>
      match x.2.1 with
      | bat :: _ :: round :: _ =>
        some { link := p.link, piece := p.pieceEq + 1, k := Gr.k, h := Gr.h
               rows := bat.rows, workField := bat.work
               workClose := round.work, sent := List.range x.2.2 }
      | _ => none

def k9LinksE (xs : XsE) : List Nat :=
  xs.filterMap fun x =>
    if x.1.place.kind == .K9 && !x.1.cuts.isEmpty then x.1.place.link else none

theorem k9Where_eq (xs : XsD) (l : Nat) : k9Where xs l = k9WhereE (xs.map toE) l := by
  unfold k9Where k9WhereE
  rw [List.find?_map]
  show (xs.find? fun x =>
      x.1.place.kind == .K9 && !x.1.cuts.isEmpty && x.1.place.link == some l).bind _ =
    ((xs.find? fun x =>
      x.1.place.kind == .K9 && !x.1.cuts.isEmpty && x.1.place.link == some l).map toE).bind _
  cases xs.find? fun x =>
      x.1.place.kind == .K9 && !x.1.cuts.isEmpty && x.1.place.link == some l with
  | none => rfl
  | some x =>
    show x.2.1.head?.map _ = (x.2.1.map (·.entry)).head?.map _
    cases x.2.1 <;> rfl

theorem k10ParG_eq (groups : Array OnBytes.ReqGroup) (xs : XsD) (p : Where) :
    k10ParG groups xs p = k10ParE groups (xs.map toE) p := by
  unfold k10ParG k10ParE
  rw [List.find?_map]
  show (xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).bind _ =
    ((xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).map toE).bind _
  cases xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link with
  | none => rfl
  | some x =>
    show (groups[p.link]?).bind _ = (groups[p.link]?).bind _
    cases groups[p.link]? with
    | none => rfl
    | some Gr =>
      show (match x.2.1 with
        | bat :: _ :: round :: _ => some _
        | _ => none) = (match x.2.1.map (·.entry) with
        | bat :: _ :: round :: _ => some _
        | _ => none)
      rcases x.2.1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

theorem k9Links_eq (xs : XsD) : k9Links xs = k9LinksE (xs.map toE) := by
  unfold k9Links k9LinksE
  rw [List.filterMap_map]
  rfl

/-! ### the lot's skeleton, on entries -/

def k9WsE (xs : XsE) : List (Nat × Option Where) :=
  (k9LinksE xs).map fun l => (l, k9WhereE xs l)

def k9CloseSkAtE (groups : Array OnBytes.ReqGroup) (xs : XsE) (w : Nat × Option Where) :
    List Skel :=
  match w.2.bind fun p => (k10ParE groups xs p).map fun P => (p, P) with
  | some (p, P) => (closeSk p P).map Skel.retype
  | none => [(refuserSk s!"link {w.1}: the closing" ⟨1, some w.1, 0, .K10⟩).retype]

def k9BatchSkE (xs : XsE) (a : Place) : Option Skel :=
  match a.kind, a.link with
  | .K9, some l =>
    (((k9WsE xs).lookup l).bind id).bind fun p =>
      if p.piece == a.piece then some (batchSk p) else none
  | _, _ => none

/-- **The lot's skeleton, as a function of the groups, the stretches of entries and one Bool a
segment.** -/
def k9SkE (groups : Array OnBytes.ReqGroup) (xs : XsE) (tw : Nat → Bool) : LotSk :=
  { name := "K9: the batching at the gatherer; each; tests; the closing as three blocks"
    letters := false, still := [], blocks := (k9WsE xs).flatMap (k9CloseSkAtE groups xs)
    batch := k9BatchSkE xs, each := tw, tests := tw }

theorem k9Ws_eq (xs : XsD) : k9Ws xs = k9WsE (xs.map toE) := by
  unfold k9Ws k9WsE
  rw [k9Links_eq]
  exact List.map_congr_left fun l _ => by rw [k9Where_eq]

theorem k9CloseSkAt_eq (groups : Array OnBytes.ReqGroup) (xs : XsD) :
    k9CloseSkAt groups xs = k9CloseSkAtE groups (xs.map toE) := by
  funext w
  unfold k9CloseSkAt k9CloseSkAtE
  have e : (fun p => (k10ParG groups xs p).map fun P => (p, P)) =
      fun p => (k10ParE groups (xs.map toE) p).map fun P => (p, P) :=
    funext fun p => by rw [k10ParG_eq]
  rw [e]
  rfl

theorem k9BatchSk_eq (xs : XsD) : k9BatchSk xs = k9BatchSkE (xs.map toE) := by
  funext a
  unfold k9BatchSk k9BatchSkE
  rw [k9Ws_eq]
  rfl

theorem k9Sk_eq (groups : Array OnBytes.ReqGroup) (xs : XsD) (tw : Nat → Bool) :
    k9Sk groups xs tw = k9SkE groups (xs.map toE) tw := by
  unfold k9Sk k9SkE k9BlocksSk
  rw [k9Ws_eq, k9CloseSkAt_eq, k9BatchSk_eq]

/-- Two skeletons that part in each | tests outside ls alone are one behind the cut. -/
theorem cut_congr (ls : List Nat) (k : LotSk) (tw tw' : Nat → Bool)
    (h : ∀ l ∈ ls, tw l = tw' l) :
    ({ k with each := tw, tests := tw } : LotSk).cut ls =
      ({ k with each := tw', tests := tw' } : LotSk).cut ls := by
  have e : (fun l => ls.contains l && tw l) = fun l => ls.contains l && tw' l := by
    funext l
    by_cases hl : l ∈ ls
    · rw [h l hl]
    · have : ls.contains l = false := by
        rw [List.contains_eq_mem]
        exact decide_eq_false hl
      rw [this, Bool.false_and, Bool.false_and]
  unfold LotSk.cut
  simp only [e]

/-- **THE ROW, AT HYPOTHESES BY FIELD.** -/
theorem k9_row_at (Z : Pub) (G : Ground) {ps : List Spot} {es : List Fmt.Entry}
    {groups : Array OnBytes.ReqGroup} {tw : Nat → Bool} (ls : List Nat)
    (hs : spotsOf Z.cuts = some ps) (he : Z.D.1.map (·.entry) = es)
    (hg : Z.s₀.check.frame.groups = groups)
    (ht : ∀ l ∈ ls, (K9.testsWhere Z.p.X l 0).isSome = tw l) :
    (lotSk G (k9Ninth Z)).cut ls = (k9SkE groups (stretchedE ps es 0) tw).cut ls := by
  have ex : (k9Stretches Z).map toE = stretchedE ps es 0 := by
    unfold k9Stretches
    rw [hs, ← he]
    exact stretched_entries ps Z.D.1 0
  rw [k9_row, k9Sk_eq, ex, hg]
  exact cut_congr ls (k9SkE groups (stretchedE ps es 0) tw) _ _ ht

end Johnson.AtFull.Desc.Lots

#print axioms Johnson.AtFull.Desc.Lots.rootsE_eq
#print axioms Johnson.AtFull.Desc.Lots.foldl_from
#print axioms Johnson.AtFull.Desc.Lots.stretched_entries
#print axioms Johnson.AtFull.Desc.Lots.k9Where_eq
#print axioms Johnson.AtFull.Desc.Lots.k10ParG_eq
#print axioms Johnson.AtFull.Desc.Lots.k9Links_eq
#print axioms Johnson.AtFull.Desc.Lots.k9Ws_eq
#print axioms Johnson.AtFull.Desc.Lots.k9CloseSkAt_eq
#print axioms Johnson.AtFull.Desc.Lots.k9BatchSk_eq
#print axioms Johnson.AtFull.Desc.Lots.k9Sk_eq
#print axioms Johnson.AtFull.Desc.Lots.cut_congr
#print axioms Johnson.AtFull.Desc.Lots.k9_row_at
