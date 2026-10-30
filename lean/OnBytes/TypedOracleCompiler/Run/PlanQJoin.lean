-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean.
TWO: cutRD BELOW IS NOT THE CUT OF a file of this project that is not in this library (cutRound: its
first half has the items
up to the first root, WITH it, and the entry { name, roots := 1 }; its second half { r.entry with
roots := 1 } and the items behind): cutRD's first piece has NO item and its second the round's own
entry and all items. Of the tie between that cut and a round of two roots TypedOracleCompiler/Slice/CarryOne.lean
has the maps (firstOf, joined); the tie itself is not shown in this library. joinRD stands and
is used there.

OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean: FROM THE LIBRARY's ROUNDS' DATA (one tree a round at most) TO
OnBytes/TypedOracleCompiler's, AND TWO NEIGHBOURING ROUNDS AS ONE. NEW. rdsKey stays
over the library's RD, with the round of two roots CUT in two; here are the maps by which its lists
become lists with the JOINED round.
  ofLib d          the library's round's data as OnBytes/TypedOracleCompiler's: tree.toList
  treeSh_ofLib     the trees keep their numbers and shapes: treeSh (ds.map ofLib) = the library's
                   treeSh ds
  wanted_ofLib     and so what the drawn positions ask for is the library's
  joinRD e d₁ d₂   two rounds as one: THE ENTRY e IS GIVEN (it has to be the program's own entry of
                   the joined
                   round; nothing is made up here); the second's kind; items, trees and openings one
                   behind the other
  treeSh_join      THE NUMBERS OF THE TREES IN THE WHOLE DO NOT MOVE: they are counted through the
                   rounds, a round's in
                   their order
  wanted_join      WHAT THE DRAWN POSITIONS ASK FOR IS KEPT IF THE FIRST ROUND OPENS NOTHING
                   (d₁.opens = []); without that it is FALSE in general: a round's openings stand
                   behind THAT round's draws, and the joined round has the second's draws alone
  joinAt e i ds    the two rounds number i and i + 1 of a list as one; treeSh_joinAt
  cutRD, join_cut  THE CUT (the first round is of its own making:
                   kind "nothing", no item, no opening, the first tree; the second carries THE
                   PLAN's ENTRY, all items and the other trees): joinRD d.entry (cut d) = d: THE
                   JOINED ROUND's ENTRY IS THE PROGRAM's OWN; the cut loses nothing of d. (rdsKey:
                   a file of this project that is not in this library, not checked here: that its
                   clause IS cutRD is owed.) THE CUT
                   LIST CANNOT BE SPELLED: its two rounds have not as many items "root" as trees (a
                   tree and no item; all items and one tree fewer): toRoots refuses both: meant so:
                   the cut is for the protocol's analysis, the joined round for the bytes. The join
                   loses d₁.entry, d₁.kind, d₂.entry. joinAt out of range hands the list back; there
                   is no wanted_joinAt.
  rdsFrom_ofLib    at descriptions with at most one root a round OnBytes/TypedOracleCompiler's rounds' data ARE the
                   library's, through
                   ofLib
  inlT, inrT, posSplit   PosT (ts₁ ++ ts₂) ≃ PosT ts₁ ⊕ PosT ts₂ (the library's recut has the joined
                         round's
                   positions as a sum)
  symL, symR       with the alphabets along it: the symbols at inlT p are those at p; the same for
                   inrT
  treeT_inlT …     tree and place along it: the left trees keep their numbers; the right ones are
                   counted on
  colT_symL …      the column as a list, and the fixed symbol 0, along symL | symR
WHAT IS NOT HERE: that the joined PROTOCOL is the cut one recut (an isomorphism of protocols:
positions, symbols, plain parts, one verifier message dropped): the walk on variables is in
a file of this project that is not in this library (not checked here); what is left is not here;
PlainOf (items₁ ++ items₂)
against the pair of plain parts.
ALSO OWED FOR THAT ISOMORPHISM: the verifier message's TYPE (joined: at e; cut: at d₂.entry: one
type where e = d₂.entry, as after cutRD); work and nonce (one GPlain against two); that ChalUnif |
DrawnFits | work ≤ 64 pass from the cut list to the joined (they are asked at e; after cutRD e is
d₂'s own entry, so they do); nTrees, nOpen, maxDepth, posAtT along the join.
"THE LIBRARY's LISTS ARE A CASE" IS SHOWN FOR treeSh, wanted AND rds ALONE: at ofLib d the ROUND is
isomorphic to the library's, not equal (Fin (2 ^ s.a) ⊕ Empty against Fin (posN (some s))): no
statement ties roundS | PSof | wireS there to the library's or to Tagged.ofRB.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open _root_.Iop _root_.Run.PQ

/-! ## The library's data as OnBytes/TypedOracleCompiler's -/

def ofLib (d : _root_.Run.PQ.RD) : RD := ⟨d.entry, d.kind, d.items, d.tree.toList, d.opens⟩

theorem treeSh_ofLib : ∀ (ds : List _root_.Run.PQ.RD) (n : ℕ),
    treeSh (ds.map ofLib) n = _root_.Run.PQ.treeSh ds n
  | [], _ => rfl
  | d :: ds, n => by
      obtain ⟨e, k, it, t, o⟩ := d
      cases t with
      | none =>
          show (if n < 0 then _ else treeSh (ds.map ofLib) (n - 0)) = _root_.Run.PQ.treeSh ds n
          rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, treeSh_ofLib ds n]
      | some s =>
          show (if n < 1 then [s][n]? else treeSh (ds.map ofLib) (n - 1)) =
            if n = 0 then some s else _root_.Run.PQ.treeSh ds (n - 1)
          by_cases hn : n = 0
          · subst hn
            rfl
          · rw [if_neg (by omega), if_neg hn, treeSh_ofLib ds (n - 1)]

theorem wantedL_ofLib (all : List _root_.Run.PQ.RD) :
    ∀ (ds : List _root_.Run.PQ.RD) (Ds : List _root_.Fmt.Drawn),
      wantedL (all.map ofLib) (ds.map ofLib) Ds = _root_.Run.PQ.wantedL all ds Ds
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, D :: Ds => by
      show (d.opens.flatMap fun n =>
          match treeSh (all.map ofLib) n with
          | none => []
          | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++
            wantedL (all.map ofLib) (ds.map ofLib) Ds = _
      simp only [treeSh_ofLib, wantedL_ofLib all ds Ds]
      rfl

theorem wanted_ofLib (ds : List _root_.Run.PQ.RD) (Ds : List _root_.Fmt.Drawn) :
    wanted (ds.map ofLib) Ds = _root_.Run.PQ.wanted ds Ds := wantedL_ofLib ds ds Ds

/-! ## Two rounds as one -/

def joinRD (e : _root_.Fmt.Entry) (d₁ d₂ : RD) : RD :=
  ⟨e, d₂.kind, d₁.items ++ d₂.items, d₁.trees ++ d₂.trees, d₁.opens ++ d₂.opens⟩

theorem treeSh_join_head (e : _root_.Fmt.Entry) (d₁ d₂ : RD) (B : List RD) (n : ℕ) :
    treeSh (joinRD e d₁ d₂ :: B) n = treeSh (d₁ :: d₂ :: B) n := by
  show (if n < (d₁.trees ++ d₂.trees).length then (d₁.trees ++ d₂.trees)[n]?
      else treeSh B (n - (d₁.trees ++ d₂.trees).length)) =
    if n < d₁.trees.length then d₁.trees[n]?
    else if n - d₁.trees.length < d₂.trees.length then d₂.trees[n - d₁.trees.length]?
    else treeSh B (n - d₁.trees.length - d₂.trees.length)
  rw [List.length_append]
  by_cases h1 : n < d₁.trees.length
  · rw [if_pos (by omega), if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : n - d₁.trees.length < d₂.trees.length
    · rw [if_pos (by omega), if_pos h2, List.getElem?_append_right (by omega)]
    · rw [if_neg (by omega), if_neg h2, Nat.sub_add_eq]

/-- The numbers of the trees in the whole do not move. -/
theorem treeSh_join (e : _root_.Fmt.Entry) (d₁ d₂ : RD) (B : List RD) :
    ∀ (A : List RD) (n : ℕ), treeSh (A ++ joinRD e d₁ d₂ :: B) n = treeSh (A ++ d₁ :: d₂ :: B) n
  | [], n => treeSh_join_head e d₁ d₂ B n
  | a :: A, n => by
      show (if n < a.trees.length then a.trees[n]?
          else treeSh (A ++ joinRD e d₁ d₂ :: B) (n - a.trees.length)) =
        if n < a.trees.length then a.trees[n]?
        else treeSh (A ++ d₁ :: d₂ :: B) (n - a.trees.length)
      rw [treeSh_join e d₁ d₂ B A]

/-- what is wanted hangs on the list in which trees are counted through treeSh alone -/
theorem wantedL_congr (all all' : List RD) (h : ∀ n, treeSh all n = treeSh all' n) :
    ∀ (ds : List RD) (Ds : List _root_.Fmt.Drawn), wantedL all ds Ds = wantedL all' ds Ds
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, D :: Ds => by
      show (d.opens.flatMap fun n =>
          match treeSh all n with
          | none => []
          | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x)) ++
            wantedL all ds Ds = _
      simp only [h, wantedL_congr all all' h ds Ds]
      rfl

theorem wantedL_join (all : List RD) (e : _root_.Fmt.Entry) (d₁ d₂ : RD) (h₁ : d₁.opens = [])
    (B : List RD) (D₁ D : _root_.Fmt.Drawn) (DB : List _root_.Fmt.Drawn) :
    ∀ (A : List RD) (DA : List _root_.Fmt.Drawn), DA.length = A.length →
      wantedL all (A ++ joinRD e d₁ d₂ :: B) (DA ++ D :: DB) =
        wantedL all (A ++ d₁ :: d₂ :: B) (DA ++ D₁ :: D :: DB)
  | [], [], _ => by
      show ((d₁.opens ++ d₂.opens).flatMap _) ++ wantedL all B DB =
        (d₁.opens.flatMap _) ++ ((d₂.opens.flatMap _) ++ wantedL all B DB)
      rw [h₁]
      rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: A, Da :: DA, h => by
      show _ ++ wantedL all (A ++ joinRD e d₁ d₂ :: B) (DA ++ D :: DB) =
        _ ++ wantedL all (A ++ d₁ :: d₂ :: B) (DA ++ D₁ :: D :: DB)
      rw [wantedL_join all e d₁ d₂ h₁ B D₁ D DB A DA (Nat.succ.inj h)]

/-- What the drawn positions ask for is kept, if the first of the two rounds opens nothing. D₁: what
the first round draws (with one verifier message: nothing that matters); D: what the second, and the
joined round, draws. -/
theorem wanted_join (e : _root_.Fmt.Entry) (d₁ d₂ : RD) (h₁ : d₁.opens = []) (A B : List RD)
    (D₁ D : _root_.Fmt.Drawn) (DA DB : List _root_.Fmt.Drawn) (hA : DA.length = A.length) :
    wanted (A ++ joinRD e d₁ d₂ :: B) (DA ++ D :: DB) =
      wanted (A ++ d₁ :: d₂ :: B) (DA ++ D₁ :: D :: DB) :=
  (wantedL_congr _ _ (treeSh_join e d₁ d₂ B A) _ _).trans
    (wantedL_join _ e d₁ d₂ h₁ B D₁ D DB A DA hA)

/-- the rounds number i and i + 1 as one -/
def joinAt (e : _root_.Fmt.Entry) : ℕ → List RD → List RD
  | 0, d₁ :: d₂ :: B => joinRD e d₁ d₂ :: B
  | i + 1, d :: ds => d :: joinAt e i ds
  | _, ds => ds

theorem treeSh_joinAt (e : _root_.Fmt.Entry) : ∀ (i : ℕ) (ds : List RD) (n : ℕ),
    treeSh (joinAt e i ds) n = treeSh ds n
  | 0, [], _ => rfl
  | 0, [_], _ => rfl
  | 0, d₁ :: d₂ :: B, n => treeSh_join_head e d₁ d₂ B n
  | _ + 1, [], _ => rfl
  | i + 1, d :: ds, n => by
      show (if n < d.trees.length then d.trees[n]? else treeSh (joinAt e i ds)
          (n - d.trees.length)) =
        if n < d.trees.length then d.trees[n]? else treeSh ds (n - d.trees.length)
      rw [treeSh_joinAt e i ds]

/-- The cut of a round that sends the tree s and then the trees ts: a first round of one's own
making (the entry e₁ is given: a name and a number of roots), of the kind "nothing", without item
and opening, with the tree s; and the round itself with the other trees. -/
def cutRD (e₁ : _root_.Fmt.Entry) (d : RD) (s : _root_.Fmt.Shape)
    (ts : List _root_.Fmt.Shape) : RD × RD :=
  (⟨e₁, .nothing, [], [s], []⟩, ⟨d.entry, d.kind, d.items, ts, d.opens⟩)

/-- Joined again, under the round's own entry, the cut round is the round. -/
theorem join_cut (e₁ : _root_.Fmt.Entry) (d : RD) (s : _root_.Fmt.Shape)
    (ts : List _root_.Fmt.Shape)
    (h : d.trees = s :: ts) : joinRD d.entry (cutRD e₁ d s ts).1 (cutRD e₁ d s ts).2 = d := by
  obtain ⟨e, k, it, tr, o⟩ := d
  have h' : tr = s :: ts := h
  subst h'
  rfl

theorem cut_opens (e₁ : _root_.Fmt.Entry) (d : RD) (s : _root_.Fmt.Shape)
    (ts : List _root_.Fmt.Shape) :
    (cutRD e₁ d s ts).1.opens = [] := rfl

/-! ## The rounds' data of a description -/

theorem rdsFrom_ofLib (S : _root_.Fmt.Spec) : ∀ (rs : List _root_.Fmt.Round) (sent : ℕ),
    (∀ r ∈ rs, r.entry.roots ≤ 1) → rdsFrom S sent rs = (_root_.Run.PQ.rdsFrom S sent rs).map ofLib
  | [], _, _ => rfl
  | r :: rs, sent, h => by
      have hr : r.entry.roots ≤ 1 := h r List.mem_cons_self
      have ih := rdsFrom_ofLib S rs (sent + r.entry.roots) fun x hx =>
          h x (List.mem_cons_of_mem _ hx)
      show (⟨r.entry, r.kind, r.items,
            (List.range r.entry.roots).map fun k =>
              (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k)),
            r.opens.filterMap ownNo⟩ : RD) :: rdsFrom S (sent + r.entry.roots) rs =
        ofLib ⟨r.entry, r.kind, r.items,
            if r.entry.roots = 0 then none
            else some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent)),
            r.opens.filterMap ownNo⟩ :: (_root_.Run.PQ.rdsFrom S (sent + r.entry.roots) rs).map
                ofLib
      rw [ih]
      congr 1
      by_cases h0 : r.entry.roots = 0
      · simp [ofLib, h0]
      · have h1 : r.entry.roots = 1 := by omega
        simp [ofLib, h1]

theorem rds_ofLib (S : _root_.Fmt.Spec) (h : ∀ r ∈ S.rounds, r.entry.roots ≤ 1) :
    rds S = (_root_.Run.PQ.rds S).map ofLib := rdsFrom_ofLib S S.rounds 0 h

/-! ## The positions of two lists of trees, one behind the other -/

def inlT : (ts₁ ts₂ : List _root_.Fmt.Shape) → PosT ts₁ → PosT (ts₁ ++ ts₂)
  | _ :: _, _, .inl x => .inl x
  | _ :: ts₁, ts₂, .inr p => .inr (inlT ts₁ ts₂ p)

def inrT : (ts₁ ts₂ : List _root_.Fmt.Shape) → PosT ts₂ → PosT (ts₁ ++ ts₂)
  | [], _, p => p
  | _ :: ts₁, ts₂, p => .inr (inrT ts₁ ts₂ p)

def splitT : (ts₁ ts₂ : List _root_.Fmt.Shape) → PosT (ts₁ ++ ts₂) → PosT ts₁ ⊕ PosT ts₂
  | [], _, p => .inr p
  | _ :: _, _, .inl x => .inl (.inl x)
  | _ :: ts₁, ts₂, .inr p => (splitT ts₁ ts₂ p).map .inr id

theorem splitT_inlT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₁),
    splitT ts₁ ts₂ (inlT ts₁ ts₂ p) = .inl p
  | _ :: _, _, .inl _ => rfl
  | _ :: ts₁, ts₂, .inr p => by
      show (splitT ts₁ ts₂ (inlT ts₁ ts₂ p)).map Sum.inr id = _
      rw [splitT_inlT ts₁ ts₂ p]
      rfl

theorem splitT_inrT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₂),
    splitT ts₁ ts₂ (inrT ts₁ ts₂ p) = .inr p
  | [], _, _ => rfl
  | _ :: ts₁, ts₂, p => by
      show (splitT ts₁ ts₂ (inrT ts₁ ts₂ p)).map Sum.inr id = _
      rw [splitT_inrT ts₁ ts₂ p]
      rfl

theorem elim_splitT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT (ts₁ ++ ts₂)),
    (splitT ts₁ ts₂ p).elim (inlT ts₁ ts₂) (inrT ts₁ ts₂) = p
  | [], _, _ => rfl
  | _ :: _, _, .inl _ => rfl
  | s :: ts₁, ts₂, .inr p => by
      have ih := elim_splitT ts₁ ts₂ p
      show ((splitT ts₁ ts₂ p).map Sum.inr id).elim (inlT (s :: ts₁) ts₂) (inrT (s :: ts₁) ts₂) = _
      cases h : splitT ts₁ ts₂ p with
      | inl q =>
          rw [h] at ih
          exact congrArg Sum.inr ih
      | inr q =>
          rw [h] at ih
          exact congrArg Sum.inr ih

/-- The positions split. -/
def posSplit (ts₁ ts₂ : List _root_.Fmt.Shape) : PosT (ts₁ ++ ts₂) ≃ PosT ts₁ ⊕ PosT ts₂ where
  toFun := splitT ts₁ ts₂
  invFun := fun q => q.elim (inlT ts₁ ts₂) (inrT ts₁ ts₂)
  left_inv := elim_splitT ts₁ ts₂
  right_inv := fun q => by
    cases q with
    | inl p => exact splitT_inlT ts₁ ts₂ p
    | inr p => exact splitT_inrT ts₁ ts₂ p

/-- the alphabet at a left position is that of the left list -/
def symL : (ts₁ ts₂ : List _root_.Fmt.Shape) → (p : PosT ts₁) →
    SymT ts₁ p ≃ SymT (ts₁ ++ ts₂) (inlT ts₁ ts₂ p)
  | _ :: _, _, .inl _ => Equiv.refl _
  | _ :: ts₁, ts₂, .inr p => symL ts₁ ts₂ p

/-- the alphabet at a right position is that of the right list -/
def symR : (ts₁ ts₂ : List _root_.Fmt.Shape) → (p : PosT ts₂) →
    SymT ts₂ p ≃ SymT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p)
  | [], _, _ => Equiv.refl _
  | _ :: ts₁, ts₂, p => symR ts₁ ts₂ p

theorem treeT_inlT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₁),
    treeT (ts₁ ++ ts₂) (inlT ts₁ ts₂ p) = treeT ts₁ p
  | _ :: _, _, .inl _ => rfl
  | _ :: ts₁, ts₂, .inr p => congrArg (· + 1) (treeT_inlT ts₁ ts₂ p)

theorem placeT_inlT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₁),
    placeT (ts₁ ++ ts₂) (inlT ts₁ ts₂ p) = placeT ts₁ p
  | _ :: _, _, .inl _ => rfl
  | _ :: ts₁, ts₂, .inr p => placeT_inlT ts₁ ts₂ p

theorem treeT_inrT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₂),
    treeT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p) = ts₁.length + treeT ts₂ p
  | [], _, _ => (Nat.zero_add _).symm
  | _ :: ts₁, ts₂, p => by
      show treeT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p) + 1 = ts₁.length + 1 + treeT ts₂ p
      rw [treeT_inrT ts₁ ts₂ p]
      omega

theorem placeT_inrT : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₂),
    placeT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p) = placeT ts₂ p
  | [], _, _ => rfl
  | _ :: ts₁, ts₂, p => placeT_inrT ts₁ ts₂ p

theorem colT_symL : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₁) (c : SymT ts₁ p),
    colT (ts₁ ++ ts₂) (inlT ts₁ ts₂ p) (symL ts₁ ts₂ p c) = colT ts₁ p c
  | _ :: _, _, .inl _, _ => rfl
  | _ :: ts₁, ts₂, .inr p, c => colT_symL ts₁ ts₂ p c

theorem colT_symR : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₂) (c : SymT ts₂ p),
    colT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p) (symR ts₁ ts₂ p c) = colT ts₂ p c
  | [], _, _, _ => rfl
  | _ :: ts₁, ts₂, p, c => colT_symR ts₁ ts₂ p c

theorem zeroT_symL : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₁),
    symL ts₁ ts₂ p (zeroT ts₁ p) = zeroT (ts₁ ++ ts₂) (inlT ts₁ ts₂ p)
  | _ :: _, _, .inl _ => rfl
  | _ :: ts₁, ts₂, .inr p => zeroT_symL ts₁ ts₂ p

theorem zeroT_symR : ∀ (ts₁ ts₂ : List _root_.Fmt.Shape) (p : PosT ts₂),
    symR ts₁ ts₂ p (zeroT ts₂ p) = zeroT (ts₁ ++ ts₂) (inrT ts₁ ts₂ p)
  | [], _, _ => rfl
  | _ :: ts₁, ts₂, p => zeroT_symR ts₁ ts₂ p

end TypedOracleCompiler.Run.PQ
