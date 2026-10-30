-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean: THE TYPING OF AN ENTRY FILE, ITS PURE HALF: FROM THE ONE CHAIN
AS THE STRICT READER (OR ITS TWIN) RETURNS IT TO WHAT THE JUDGE judgeEL (Slice/JudgeE.lean) TAKES
(OutE): assembleE; WITH WHOLE REAL PATHS. Definitions that hash nothing; equations.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Wanted: assembleE, "what was read ↦ OutE", with whole real paths. The judge judgeEL runs the
LAX verifier: each opened position is climbed alone along its own path. The sibling's toBPrfX lays
OpenB.paths (made from the pruned set of given digests alone, without a hash): by a reading of its
name and of the library's Run/ParseFull.lean's head these are no real paths where the walk computes
a sibling. Here each path is looked up in the opening's own record of vertices met (the library's
pathFrom), as Slice/Batch3STyping.lean does for a proof file.
  whichOf D op           which stored table an opening is of: by its place in the file: the op.k-th
    stored opening of round op.round is of D.stored's table there; 1 if that table's item is 1, else
    0 (as D.xs has it). [The strict reader lays a round's stored openings FIRST, in D.stored's
    order: OnBytes/Tie/StoredRead.lean: joined.]
  lookE run tab          the table of own openings, keyed BY THE FORM's OWN NUMBER s.tree (as the
    sibling's placeSL | opensB): column as a symbol; typed salt := the chain's run, then the file's
    salt; the whole path
  extE a cfg tx          the two stored tables' openings: symbol (place, column); typed salt := cfg,
    then the file's salt; the whole path
  assembleS D dec o : Option (OneProtocolProof 256 (PSXE D dec).up)     THE STRING, AT THE SKELETON: salt :=
    bits run; roots := the chain's; plains := ((), PQ.plainsSL …) as the sibling's TYX; opens, ext
    as above; no request tree
  assembleE D dec r0 r1 x o   ([dig r0, dig r1], x, ofPS (the string)): Option (List (Dig 256) ×
    X × OneProtocolProof 256 (ofProto (LinkX D dec))): AT X := A × Sd THIS TYPE IS OutE (ZXE …) BY UNFOLDING:
    assembleEZ says so by its type
  assembleS_some         what a yes says, field by field
  assembleE_roots, assembleE_x, assembleE_str     the two roots are what went in; the instance
    is what went in; the string is ofPS of assembleS's
  assembleE_keeps, assembleE_ok     KeepsE Z R π, if R keeps (place, (place, column), cfg then
    salt) at every listed place of every stored opening; with the two roots: J.ok
  assembleS_isSome, assembleE_isSome     it IS some: the chain has a run value; as many rounds
    as D.ds, each round's values of its items' kinds; every listed place's path stands in its
    opening's record (from ReadAs | FactsAs: Batch3SRead(2).lean: paths_of_read | paths_of_facts,
    with ops1_all)
WHAT IS NOT SAID. That the judge accepts. That an opening is stored iff its form says so (had from
S.ok: storedOk asks t.sh.stored; Round.ok asks !stored of own trees; an entry's chain takes no tree
over). A place that two openings show: the first in the file is typed. The instance x and the two
roots are the caller's.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryPS
import OnBytes.TypedOracleCompiler.Slice.Batch3SRead2

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf)
open _root_.Run.PQ (View SgX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

/-- which stored table an opening is of -/
def whichOf (D : XD) (op : OpAt) : ℕ :=
  match (D.stored[op.round]?).bind (·[op.k]?) with
  | some t => if t.item == 1 then 1 else 0
  | none => 0

/-- the table of own openings, keyed by the form's own number -/
def lookE (run : ByteArray) (tab : List ((ℕ × ℕ) × Row)) : Look 256 := fun _ s x =>
    lookF (fun _ => run) tab s.tree s x

/-- the two stored tables' openings -/
def extE (a : ℕ) (cfg : ByteArray) (tx : List ((ℕ × ℕ) × Row)) :
    Fin (2 ^ a) ⊕ Fin (2 ^ a) → Option (Opening 256 SgX)
  | .inl q => (tx.lookup (0, q.val)).map fun z => ⟨(q.val, z.1), leafSalt cfg z.2.1, z.2.2⟩
  | .inr q => (tx.lookup (1, q.val)).map fun z => ⟨(q.val, z.1), leafSalt cfg z.2.1, z.2.2⟩

variable {X : Type} (D : XD) (dec : X → View → Bool)

/-- The string, at the skeleton. -/
def assembleS (o : _root_.Fmt.ChainOut) : Option (OneProtocolProof 256 (PSXE D dec).up) :=
  match o.run, PQ.plainsSL D.C D.ds o.rounds.toList,
    tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored),
    tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) with
  | some run, some pl, some tab, some tx =>
    some
      { salt := bytesToBits run
        roots := (rootsB o).map bytesToDig
        plains := ((), pl)
        opens := fun p => match p with
          | .inl e => e.elim
          | .inr q => opLS D.C (lookE run tab) 0 D.ds q
        ext := extE D.a D.base.cfg tx
        rtreq := fun _ => false
        slot := 0
        path := []
        rsalt := [] }
  | _, _, _, _ => none

/-- What was read ↦ what the judge takes. -/
def assembleE (r0 r1 : ByteArray) (x : X) (o : _root_.Fmt.ChainOut) :
    Option (List (Dig 256) × X × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) :=
  (assembleS D dec o).map fun π => ([bytesToDig r0, bytesToDig r1], x, ofPS D dec π)

/-- What a yes says. -/
theorem assembleS_some {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    (h : assembleS D dec o = some π) :
    ∃ run pl tab tx, o.run = some run ∧ PQ.plainsSL D.C D.ds o.rounds.toList = some pl ∧
      tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) = some tab ∧
      tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) = some tx ∧
      π.salt = bytesToBits run ∧ π.roots = (rootsB o).map bytesToDig ∧ π.plains = ((), pl) ∧
      (∀ q, π.opens (.inr q) = opLS D.C (lookE run tab) 0 D.ds q) ∧ π.ext = extE D.a D.base.cfg tx ∧
      π.rtreq = (fun _ => false) ∧ π.slot = 0 ∧ π.path = [] ∧ π.rsalt = [] := by
  unfold assembleS at h
  split at h
  · rename_i run pl tab tx h1 h2 h3 h4
    obtain rfl := Option.some.inj h
    exact ⟨run, pl, tab, tx, h1, h2, h3, h4, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

section
variable {D dec} {r0 r1 : ByteArray} {x : X} {o : _root_.Fmt.ChainOut}
  {out : List (Dig 256) × X × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))}

theorem assembleE_str (h : assembleE D dec r0 r1 x o = some out) :
    ∃ π, assembleS D dec o = some π ∧ out = ([bytesToDig r0, bytesToDig r1], x, ofPS D dec π) := by
  obtain ⟨π, hπ, e⟩ := Option.map_eq_some_iff.1 h
  exact ⟨π, hπ, e.symm⟩

/-- the two roots are what went in -/
theorem assembleE_roots (h : assembleE D dec r0 r1 x o = some out) :
    out.1 = [bytesToDig r0, bytesToDig r1] := by
  obtain ⟨π, -, rfl⟩ := assembleE_str h
  rfl

/-- the instance is what went in -/
theorem assembleE_x (h : assembleE D dec r0 r1 x o = some out) : out.2.1 = x := by
  obtain ⟨π, -, rfl⟩ := assembleE_str h
  rfl

end

/-- what an opening of a stored table in the string is: a row of a stored opening of the file -/
theorem extE_some {a : ℕ} {cfg : ByteArray} {num : OpAt → ℕ} {ops : List OpAt}
    {tx : List ((ℕ × ℕ) × Row)}
    (ht : tabOf num ops = some tx) {p : Fin (2 ^ a) ⊕ Fin (2 ^ a)} {op : Opening 256 SgX}
        (h : extE a cfg tx p = some op) :
    ∃ o ∈ ops, ∃ z ∈ o.xs.zip (o.out.cols.zip o.out.salts),
        num o = Sum.elim (fun _ => 0) (fun _ => 1) p ∧
      z.1 = (Sum.elim id id p : Fin (2 ^ a)).val ∧ op.sym = (z.1, z.2.1) ∧
          op.salt = leafSalt cfg z.2.2 ∧
      pathFrom o.sh.a o.out.seen z.1 = some op.path := by
  cases p with
  | inl q =>
    obtain ⟨row, hl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨o, ho, hn, hz, hp⟩ := tabOf_lookup ht hl
    exact ⟨o, ho, _, hz, hn, rfl, rfl, rfl, hp⟩
  | inr q =>
    obtain ⟨row, hl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨o, ho, hn, hz, hp⟩ := tabOf_lookup ht hl
    exact ⟨o, ho, _, hz, hn, rfl, rfl, rfl, hp⟩

/-! ## It is some -/

theorem assembleS_isSome (o : _root_.Fmt.ChainOut) (h1 : o.run.isSome = true)
    (hp : List.Forall₂ (fun d r => (_root_.Run.PQ.PlainOf.ofGots d.items r.vals).isSome = true) D.ds
        o.rounds.toList)
    (hs : ∀ op ∈ opsOf 1 o, ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      (pathFrom op.sh.a op.out.seen z.1).isSome = true) :
    (assembleS D dec o).isSome = true := by
  obtain ⟨run, h1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨pl, e2⟩ := Option.isSome_iff_exists.1 (plainsSL_isSome D.C _ _ hp)
  obtain ⟨tab, e3⟩ := Option.isSome_iff_exists.1 (tabOf_isSome (fun op => op.sh.tree)
    (ops := (opsOf 1 o).filter fun op => !op.sh.stored) fun op hop =>
        hs op (List.mem_of_mem_filter hop))
  obtain ⟨tx, e4⟩ := Option.isSome_iff_exists.1 (tabOf_isSome (whichOf D)
    (ops := (opsOf 1 o).filter fun op => op.sh.stored) fun op hop =>
        hs op (List.mem_of_mem_filter hop))
  unfold assembleS
  rw [h1, e2, e3, e4]
  rfl

theorem assembleE_isSome (r0 r1 : ByteArray) (x : X) (o : _root_.Fmt.ChainOut)
    (h1 : o.run.isSome = true)
    (hp : List.Forall₂ (fun d r => (_root_.Run.PQ.PlainOf.ofGots d.items r.vals).isSome = true) D.ds
        o.rounds.toList)
    (hs : ∀ op ∈ opsOf 1 o, ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      (pathFrom op.sh.a op.out.seen z.1).isSome = true) :
    (assembleE D dec r0 r1 x o).isSome = true := by
  unfold assembleE
  rw [Option.isSome_map]
  exact assembleS_isSome D dec o h1 hp hs

/-- a property of every opening of every round of the chain holds of every member of the typing's
list -/
theorem ops1_all (Q : _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut → Prop)
    (o : _root_.Fmt.ChainOut)
    (h : ∀ r ∈ o.rounds.toList, ∀ y ∈ r.opens, Q y) : ∀ op ∈ opsOf 1 o, Q (op.sh, op.xs, op.out) :=
        fun op hop => by
  obtain ⟨-, r, hr, hy⟩ := mem_opsOf hop
  exact h r hr _ hy

/-! ## At the written protocol of Slice/EntryX.lean -/

section
variable {A Sd : Type} (decE : A × Sd → View → Bool) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D)
    (early : A × Sd → A × Sd)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX)) (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- assembleE, at the type that the judge takes. -/
def assembleEZ (r0 r1 : ByteArray) (x : A × Sd) (o : _root_.Fmt.ChainOut) :
    Option (OutE (ZXE D decE B E early T wT eT pT)) :=
  assembleE D decE r0 r1 x o

/-- The external openings are kept by a reading, if it keeps every listed place of every stored
opening of the file. -/
theorem assembleE_keeps (R : Reading (LXE (Bd := Bd) D early T) B.embE)
    {r0 r1 : ByteArray} {x : A × Sd}
    {o : _root_.Fmt.ChainOut} {out : OutE (ZXE D decE B E early T wT eT pT)}
    (h : assembleEZ D decE B E early T wT eT pT r0 r1 x o = some out)
    (hk : ∀ op ∈ opsOf 1 o, op.sh.stored = true → ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      ∀ q : Fin (2 ^ D.a), q.val = z.1 → R.keeps q (z.1, z.2.1) (leafSalt D.base.cfg z.2.2)) :
    KeepsE (ZXE D decE B E early T wT eT pT) R out.2.2 := by
  obtain ⟨π, hπ, rfl⟩ := assembleE_str h
  obtain ⟨run, pl, tab, tx, -, -, -, e4, -, -, -, -, hext, -⟩ := assembleS_some D decE hπ
  intro p op hop
  have hop' : extE D.a D.base.cfg tx p = some op := by rw [← hext]; exact hop
  obtain ⟨o', ho', z, hz, -, hq, hs, hsalt, -⟩ := extE_some e4 hop'
  rw [hs, hsalt]
  exact hk o' (List.mem_of_mem_filter ho') (by simpa using (List.mem_filter.1 ho').2) z hz _ hq.symm

/-- J.ok: two roots; the external openings kept. -/
theorem assembleE_ok (R : Reading (LXE (Bd := Bd) D early T) B.embE)
    {r0 r1 : ByteArray} {x : A × Sd}
    {o : _root_.Fmt.ChainOut} {out : OutE (ZXE D decE B E early T wT eT pT)}
    (h : assembleEZ D decE B E early T wT eT pT r0 r1 x o = some out)
    (hk : ∀ op ∈ opsOf 1 o, op.sh.stored = true → ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      ∀ q : Fin (2 ^ D.a), q.val = z.1 → R.keeps q (z.1, z.2.1) (leafSalt D.base.cfg z.2.2)) :
    out.1.length = (ext2R (LXE (Bd := Bd) D early T)).k ∧
        KeepsE (ZXE D decE B E early T wT eT pT) R out.2.2 :=
  ⟨by rw [assembleE_roots h]; rfl, assembleE_keeps D decE B E early T wT eT pT R h hk⟩

end

end TypedOracleCompiler.Slice
