-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SWhole.lean: THE FORESTS' HALF AT THE BATCH's SKELETON:
Run/WholePaths.lean's GoodAt HOLDS AT D's WIRES, AT BODIES MADE BY D.embSS AND OPENINGS MADE BY
D.opSS, FROM ONE HYPOTHESIS ON THE TABLE OF OPENINGS; AND FROM THE TYPING's TABLE BACK TO THE
OPENING OF THE FILE THAT A ROW CAME FROM. Lemmas with proofs.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Wanted: "afterB's forests at assembleF's string say yes … for one tree first, then for the
forest". WholePaths' checks_yes asks GoodAt round by round, tree by tree, over the shape. The typing
(Slice/Batch3STyping.lean) speaks of "tree n in the whole, place x". Here the two are joined, by
recursion on the rounds' data.
  Enc1 B, liftT e1         a way of writing ONE tree's columns (the tree's form, place, column ↦
    body), and the way for a round's list of trees that it gives. (A symbol's type at a position of
    a list of trees is its own tree's column's by recursion alone: so the join is stated for ways of
    this make. That ownT (StringsList.lean) is one is not shown in this library.)
  at_tree                  a position that the maker's posAtT ts k j names, with its opening by opTS
    look n ts: it is look (n + k) s ⟨j, _⟩ at the k-th form s; body, salt and path agree
  LookGood P e1 Fm Rt look THE ONE HYPOTHESIS: if tree n has the form s (Fm n s) and the root c
    (Rt n c) and look n s x = some op, then P holds of the check ⟨⟨e1 s x op.sym, op.salt⟩, x,
    op.path, c, s.a⟩
  FormsOn Fm n ds          the trees of the rounds ds, counted from n, have their forms under Fm;
    allT, formsOn_all; BD.allT, BD.FormIs, BD.forms: so it is, at all three stretches, at "the
    n-th of all trees' forms, counted through, is s"
  RtsLo | RtsSh | RtsL Rt …   the roots that a run's record rts holds for a local | shared stretch
    before a tail | a last local stretch, counted from n, stand under Rt
  comp_round               one written round's component
  goodAt_lo | goodAt_sh | goodAt_L | goodAt_seam     a local | shared stretch before a skeleton
    tail; a last stretch; a seam in front
  BD.RtsOk Rt rts, BD.goodAt     at D.shS, D.annS, D.wiresS K chal o, D.embSS (liftT e1) ef,
    D.opSS of look: from LookGood, the front's CompGood and RtsOk
  lookF_some               what a yes of the typing's lookF says: the row in the table; the column;
    the typed salt; the path
  tabOf_lookup, rowsOf_mem a row of the typing's table comes from an opening of the file: op ∈
    ops, num op = n, x is listed in op.xs with that column and salt, and the path is pathFrom
    op.sh.a op.out.seen x
WHAT IS NOT SAID. LookGood AT THE TYPING's lookF: it wants, for the opening that a row came from:
RowOk (Run/WholePaths.lean: from the library's opening_paths at the twin's yes), "its form is D's
form of tree n", "the root in which its walk ended is the root sent for tree n", and the row law at
its leaf: THE TWIN's FACTS AND THE PAGE's: nobody's yet. RtsOk at the chain's record (the chain's
half). The stored string (checksExt_all asks its like directly). That a read position has an
opening.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3STyping
import OnBytes.TypedOracleCompiler.Run.WholePaths

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom)

/-! ## A way of writing one tree's columns -/

/-- the tree's form, place, column ↦ body -/
abbrev Enc1 (B : Type) : Type := (s : _root_.Fmt.Shape) → Fin (2 ^ s.a) → (Fin s.W → UInt64) → B

/-- the way for a round's list of trees -/
def liftT {B : Type} (e1 : Enc1 B) : (ts : List _root_.Fmt.Shape) → (p : PQ.PosT ts) →
    PQ.SymT ts p → B
  | s :: _, .inl x, col => e1 s x col
  | _ :: ts, .inr p, col => liftT e1 ts p col

/-- a position named by (tree, leaf), with its opening: it is the table's at the tree's number -/
theorem at_tree {B : Type} {lam : ℕ} (e1 : Enc1 B) (look : Look lam) :
    ∀ (ts : List _root_.Fmt.Shape) (n k j : ℕ) (p : PQ.PosT ts) (op : Opening lam (PQ.SymT ts p)),
      PQ.posAtT ts k j = some p → opTS look n ts p = some op →
      ∃ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (o : Opening lam (Fin s.W → UInt64)),
        ts[k]? = some s ∧ x.val = j ∧ look (n + k) s x = some o ∧
        liftT e1 ts p op.sym = e1 s x o.sym ∧ op.salt = o.salt ∧ op.path = o.path
  | [], _, _, _, p, _, _, _ => p.elim
  | s :: _, n, 0, j, p, op, hp, ho => by
      simp only [PQ.posAtT] at hp
      split at hp
      · rename_i hj
        obtain rfl := Option.some.inj hp
        exact ⟨s, ⟨j, hj⟩, op, rfl, rfl, ho, rfl, rfl, rfl⟩
      · cases hp
  | _ :: ts, n, k + 1, j, p, op, hp, ho => by
      simp only [PQ.posAtT] at hp
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
      obtain ⟨s, x, o, h1, h2, h3, h4⟩ := at_tree e1 look ts (n + 1) k j p' op hp' ho
      exact ⟨s, x, o, by simpa using h1, h2, by rwa [show n + (k + 1) = n + 1 + k by omega], h4⟩

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (P : Check 256 L → Prop) (e1 : Enc1 (Body L))
  (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop) (look : Look 256)

/-- The one hypothesis on the table of openings. -/
def LookGood : Prop :=
  ∀ (n : ℕ) (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (op : Opening 256 (Fin s.W → UInt64))
      (c : Dig 256),
    Fm n s → Rt n c → look n s x = some op → P ⟨⟨e1 s x op.sym, op.salt⟩, x.val, op.path, c, s.a⟩

/-- the trees of the rounds ds, counted from n, have their forms under Fm -/
def FormsOn : ℕ → List PQ.RD → Prop
  | _, [] => True
  | n, d :: ds => (∀ k s, d.trees[k]? = some s → Fm (n + k) s) ∧ FormsOn (n + d.trees.length) ds

/-- all trees' forms of a list of rounds, in order -/
def allT (ds : List PQ.RD) : List _root_.Fmt.Shape := ds.flatMap (·.trees)

theorem length_allT : ∀ ds : List PQ.RD, (allT ds).length = nTrees ds
  | [] => rfl
  | d :: ds => by
      show (d.trees ++ allT ds).length = d.trees.length + nTrees ds
      rw [List.length_append, length_allT ds]

/-- at "the n-th of a list of forms is s", if the rounds' trees stand in that list from n on -/
theorem formsOn_all (all : List _root_.Fmt.Shape) :
    ∀ (ds : List PQ.RD) (n : ℕ), (∀ k s, (allT ds)[k]? = some s → all[n + k]? = some s) →
      FormsOn (fun n s => all[n]? = some s) n ds
  | [], _, _ => trivial
  | d :: ds, n, h =>
    ⟨fun k s hk => h k s (by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hk
        show (d.trees ++ allT ds)[k]? = some s
        rw [List.getElem?_append_left hlt]
        exact hk),
      formsOn_all all ds (n + d.trees.length) fun k s hk => by
        have := h (d.trees.length + k) s (by
          show (d.trees ++ allT ds)[d.trees.length + k]? = some s
          rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hk)
        rwa [← Nat.add_assoc] at this⟩

variable {P e1 Fm Rt look}

/-- one written round's component: its trees are counted from n; rt holds their roots -/
theorem comp_round (H : LookGood P e1 Fm Rt look) (C : PQ.CK) (d : PQ.RD) (n : ℕ)
    (hF : ∀ k s, d.trees[k]? = some s → Fm (n + k) s) (rt : List (Dig 256))
    (hR : ∀ k c, rt[k]? = some c → Rt (n + k) c) (isRead : PQ.PosT d.trees → Bool) :
    CompGood (r := (PQ.roundS C d).up) P (PQ.posAtT d.trees) (d.trees.map (·.a))
        (liftT e1 d.trees) rt isRead
      (opTS look n d.trees) := fun k dep c hd hc j p op _ hp _ ho => by
  obtain ⟨s, x, o, h1, h2, h3, h4, h5, h6⟩ := at_tree e1 look d.trees n k j p op hp ho
  have hdep : dep = s.a := by
    rw [List.getElem?_map, h1] at hd
    exact (Option.some.inj hd).symm
  subst hdep
  subst h2
  have := H (n + k) s x o c (hF k s h1) (hR k c hc) h3
  rw [show liftT e1 d.trees p op.sym = e1 s x o.sym from h4, h5, h6]
  exact this

/-- a component without a tree -/
theorem comp_none {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : List (Dig 256)) (isRead : r.Pos → Bool) (f : (p : r.Pos) →
        Option (Opening 256 (r.Sym p))) :
    CompGood P posAt [] emb rt isRead f := fun _ _ _ hd => by simp at hd

end

/-! ## Stretches -/

section
variable (Rt : ℕ → Dig 256 → Prop) (C : PQ.CK) (T : List RS)

/-- the roots of a local stretch before a tail, counted from n, stand under Rt; the tail's record
meets Tl -/
def RtsLo (Tl : RootsOfChain 256 (_root_.Run.Twin.up T) → Prop) : ℕ → (ds : List PQ.RD) →
    RootsOfChain 256 (shA C T ds) → Prop
  | _, [], rts => Tl rts
  | n, d :: ds, (rt, rts) => (∀ k c, (rt.2.getD [])[k]? = some c → Rt (n + k) c) ∧
      RtsLo Tl (n + d.trees.length) ds rts

/-- the same for a shared stretch -/
def RtsSh (Tl : RootsOfChain 256 (_root_.Run.Twin.up T) → Prop) : ℕ → (ds : List PQ.RD) →
    RootsOfChain 256 (shA C T ds) → Prop
  | _, [], rts => Tl rts
  | n, d :: ds, (rt, rts) => (∀ k c, (rt.1.getD [])[k]? = some c → Rt (n + k) c) ∧
      RtsSh Tl (n + d.trees.length) ds rts

/-- the same for a local stretch with nothing behind it -/
def RtsL : ℕ → (ds : List PQ.RD) → RootsOfChain 256 (PQ.uL C ds) → Prop
  | _, [], _ => True
  | n, d :: ds, (rt, rts) => (∀ k c, (rt.2.getD [])[k]? = some c → Rt (n + k) c) ∧
      RtsL (n + d.trees.length) ds rts

end

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {P : Check 256 L → Prop} {e1 : Enc1 (Body L)}
  {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} {look : Look 256}
  (H : LookGood P e1 Fm Rt look) (C : PQ.CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (T : List RS)
include H

/-- A local stretch before a skeleton tail. -/
theorem goodAt_lo (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → Body L)
    (ot : (p : OPos (_root_.Run.Twin.up T)) → Option (Opening 256 (OSym (_root_.Run.Twin.up T) p)))
    (Tl : RootsOfChain 256 (_root_.Run.Twin.up T) → Prop)
    (hT : ∀ rts isRead, Tl rts → GoodAt P (_root_.Run.Twin.up T) At Wt et rts isRead ot) :
    ∀ (ds : List PQ.RD) (n : ℕ) (rts : RootsOfChain 256 (shA C T ds)) (isRead : OPos (shA C T ds) → Bool),
      FormsOn Fm n ds → RtsLo Rt C T Tl n ds rts →
      GoodAt P (shA C T ds) (annLoS C T At ds) (wLoS C K chal T At Wt ds)
          (embAS T C (liftT e1) et ds) rts isRead
        (opAS T C look ot n ds)
  | [], _, rts, isRead, _, hr => hT rts isRead hr
  | d :: ds, n, (_, rts), _, hf, hr =>
    ⟨comp_none _ _ _ _ _, comp_round H C d n hf.1 _ hr.1 _,
      goodAt_lo At Wt et ot Tl hT ds (n + d.trees.length) rts _ hf.2 hr.2⟩

/-- A shared stretch before a skeleton tail. -/
theorem goodAt_sh (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → Body L)
    (ot : (p : OPos (_root_.Run.Twin.up T)) → Option (Opening 256 (OSym (_root_.Run.Twin.up T) p)))
    (Tl : RootsOfChain 256 (_root_.Run.Twin.up T) → Prop)
    (hT : ∀ rts isRead, Tl rts → GoodAt P (_root_.Run.Twin.up T) At Wt et rts isRead ot) :
    ∀ (ds : List PQ.RD) (n : ℕ) (rts : RootsOfChain 256 (shA C T ds)) (isRead : OPos (shA C T ds) → Bool),
      FormsOn Fm n ds → RtsSh Rt C T Tl n ds rts →
      GoodAt P (shA C T ds) (annShS C T At ds) (wShS C K chal T At Wt ds)
          (embAS T C (liftT e1) et ds) rts isRead
        (opAS T C look ot n ds)
  | [], _, rts, isRead, _, hr => hT rts isRead hr
  | d :: ds, n, (_, rts), _, hf, hr =>
    ⟨comp_round H C d n hf.1 _ hr.1 _, comp_none _ _ _ _ _,
      goodAt_sh At Wt et ot Tl hT ds (n + d.trees.length) rts _ hf.2 hr.2⟩

/-- A local stretch with nothing behind it. -/
theorem goodAt_L :
    ∀ (ds : List PQ.RD) (n : ℕ) (rts : RootsOfChain 256 (PQ.uL C ds)) (isRead : OPos (PQ.uL C ds) → Bool),
      FormsOn Fm n ds → RtsL Rt C n ds rts →
      GoodAt P (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds)
          (embLS C (liftT e1) ds) rts
        isRead (opLS C look n ds)
  | [], _, _, _, _, _ => trivial
  | d :: ds, n, (_, rts), _, hf, hr =>
    ⟨comp_none _ _ _ _ _, comp_round H C d n hf.1 _ hr.1 _,
        goodAt_L ds (n + d.trees.length) rts _ hf.2 hr.2⟩

end

/-! ## At the batch's skeleton -/

namespace BD
variable (D : BD)

/-- the roots that a run's record holds for the three stretches' trees, counted through, stand under
Rt -/
def RtsOk (Rt : ℕ → Dig 256 → Prop) (rts : RootsOfChain 256 D.shS) : Prop :=
  RtsLo Rt D.G.C D.SJ
    (fun r => RtsSh Rt D.G.C D.S₃ (fun r' => RtsL Rt D.G.C
        (nTrees D.G.ds₁ + nTrees D.G.ds₂) D.G.ds₃ r'.2)
      (nTrees D.G.ds₁) D.G.ds₂ r.2)
    0 D.G.ds₁ rts.2

/-- all trees' forms of the three stretches, counted through -/
def allT (D : BD) : List _root_.Fmt.Shape := Slice.allT D.G.ds₁ ++
    (Slice.allT D.G.ds₂ ++ Slice.allT D.G.ds₃)

/-- "tree n in the whole has the form s" -/
def FormIs (D : BD) (n : ℕ) (s : _root_.Fmt.Shape) : Prop := D.allT[n]? = some s

/-- the three stretches' trees have their forms -/
theorem forms : FormsOn D.FormIs 0 D.G.ds₁ ∧ FormsOn D.FormIs (nTrees D.G.ds₁) D.G.ds₂ ∧
    FormsOn D.FormIs (nTrees D.G.ds₁ + nTrees D.G.ds₂) D.G.ds₃ := by
  refine ⟨formsOn_all D.allT _ _ fun k s hk => ?_, formsOn_all D.allT _ _ fun k s hk => ?_,
    formsOn_all D.allT _ _ fun k s hk => ?_⟩
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hk
    unfold allT
    rw [Nat.zero_add, List.getElem?_append_left hlt]
    exact hk
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hk
    unfold allT
    rw [← length_allT, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hlt]
    exact hk
  · unfold allT
    rw [← length_allT, ← length_allT, Nat.add_assoc,
        List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_right (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
    exact hk

/-- GoodAt at the batch's wires, bodies and openings. -/
theorem goodAt {I X : Type} {L : BatchProtocolWithLeafBody I X} {P : Check 256 L → Prop} {e1 : Enc1 (Body L)}
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} {look : Look 256}
        (H : LookGood P e1 Fm Rt look)
    (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (ef : (p : D.F.r.Pos) → D.F.r.Sym p → Body L) (of : (p : D.F.r.Pos) →
        Option (Opening 256 (D.F.r.Sym p)))
    (rts : RootsOfChain 256 D.shS) (isRead : OPos D.shS → Bool)
    (f₁ : FormsOn Fm 0 D.G.ds₁) (f₂ : FormsOn Fm (nTrees D.G.ds₁) D.G.ds₂)
    (f₃ : FormsOn Fm (nTrees D.G.ds₁ + nTrees D.G.ds₂) D.G.ds₃)
    (hF : CompGood (r := D.F.r) P D.F.posAt D.F.depths ef (rts.1.2.getD [])
        (fun p => isRead (.inl p)) of)
    (hR : D.RtsOk Rt rts) :
    GoodAt P D.shS D.annS (D.wiresS K chal o) (D.embSS (liftT e1) ef) rts isRead (D.opSS of look) :=
  ⟨comp_none _ _ _ _ _, hF,
    goodAt_lo H D.G.C K chal D.SJ D.annSJ (D.wSJ K chal o) _ _ _
      (fun r _ hr => ⟨comp_none _ _ _ _ _, comp_none _ _ _ _ _,
        goodAt_sh H D.G.C K chal D.S₃ D.annS₃ (D.wS₃ K chal o) _ _ _
          (fun r' _ hr' => ⟨comp_none _ _ _ _ _, comp_none _ _ _ _ _,
            goodAt_L H D.G.C K chal D.G.ds₃ _ r'.2 _ f₃ hr'⟩)
          D.G.ds₂ _ r.2 _ f₂ hr⟩)
      D.G.ds₁ 0 rts.2 _ f₁ hR⟩

end BD

/-! ## From the typing's table back to the file -/

/-- what a yes of the typing's table of openings says -/
theorem lookF_some {runOf : ℕ → ByteArray} {tab : List ((ℕ × ℕ) × Row)} {n : ℕ}
    {s : _root_.Fmt.Shape}
    {x : Fin (2 ^ s.a)} {op : Opening 256 (Fin s.W → UInt64)}
        (h : lookF runOf tab n s x = some op) :
    ∃ col salt, tab.lookup (n, x.val) = some (col, salt, op.path) ∧ List.ofFn op.sym = col ∧
      op.salt = leafSalt (runOf n) salt := by
  unfold lookF at h
  split at h
  · cases h
  · rename_i col salt path hl
    split at h
    · rename_i hw
      obtain rfl := Option.some.inj h
      refine ⟨col, salt, hl, ?_, rfl⟩
      apply List.ext_getElem
      · rw [List.length_ofFn, hw]
      · intro i h1 h2
        rw [List.getElem_ofFn]
    · cases h

/-- what a list made member by member holds comes from a member -/
theorem mem_of_mapM {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ y ∈ l', ∃ z ∈ l, f z = some y
  | [], l', h, y, hy => by
      obtain rfl : [] = l' := Option.some.inj h
      cases hy
  | a :: l, l', h, y, hy => by
      rw [List.mapM_cons] at h
      cases hb : f a with
      | none => rw [hb] at h; cases h
      | some b =>
        cases hbs : l.mapM f with
        | none => rw [hb, hbs] at h; cases h
        | some bs =>
          rw [hb, hbs] at h
          obtain rfl : b :: bs = l' := Option.some.inj h
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨a, List.mem_cons_self, hb⟩
          · obtain ⟨z, hz, hf⟩ := mem_of_mapM f l bs hbs y hy
            exact ⟨z, List.mem_cons_of_mem _ hz, hf⟩

/-- what a look-up finds stands in the list -/
theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k', v') :: l, k, v, h => by
      rw [List.lookup_cons] at h
      split at h
      · rename_i hk
        obtain rfl := Option.some.inj h
        rw [eq_of_beq hk]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_lookup l k v h)

/-- a row of one opening: its place is listed, with that column and salt; the path is looked up in
the opening's own record -/
theorem rowsOf_mem {op : OpAt} {l : List (ℕ × Row)} (h : rowsOf op = some l) {x : ℕ} {row : Row}
    (hx : (x, row) ∈ l) :
    (x, row.1, row.2.1) ∈ op.xs.zip (op.out.cols.zip op.out.salts) ∧
      pathFrom op.sh.a op.out.seen x = some row.2.2 := by
  unfold rowsOf at h
  obtain ⟨z, hz, hf⟩ := mem_of_mapM _ _ _ h _ hx
  obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 hf
  cases e
  exact ⟨hz, hp⟩

/-- A row of the typing's table comes from an opening of the file. -/
theorem tabOf_lookup {num : OpAt → ℕ} {ops : List OpAt} {tab : List ((ℕ × ℕ) × Row)}
    (h : tabOf num ops = some tab)
    {n x : ℕ} {row : Row} (hl : tab.lookup (n, x) = some row) :
    ∃ op ∈ ops, num op = n ∧ (x, row.1, row.2.1) ∈ op.xs.zip (op.out.cols.zip op.out.salts) ∧
      pathFrom op.sh.a op.out.seen x = some row.2.2 := by
  unfold tabOf at h
  obtain ⟨ls, hls, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨l', hl', hm⟩ := List.mem_flatten.1 (mem_of_lookup _ _ _ hl)
  obtain ⟨op, hop, hf⟩ := mem_of_mapM _ _ _ hls _ hl'
  obtain ⟨l, hrows, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
  cases e
  exact ⟨op, hop, rfl, rowsOf_mem hrows hz⟩

end TypedOracleCompiler.Slice
