-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SRead.lean: FROM "THE FORMAT's READER OF AN OPENING SAID YES" TO WHAT THE
FORESTS' HALF ASKS OF THAT OPENING (Slice/Batch3SWholeF.lean: Climbs, OwnOk, StoOk); AND: THE
TYPING's PURE HALF SUCCEEDS (assemble3 … is some) FROM FACTS ON WHAT WAS READ. Lemmas with proofs.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. OwnOk | StoOk are hypotheses. Their heaviest clause (each whole path, climbed alone, ends in
the walk's root) is THE LIBRARY's THEOREM Run/WalkPaths.lean: opening_paths, at a yes of
Fmt.readOpeningW. Here it is applied; what is then still owed is written down as small facts on the
reading, so that whoever owns the laws on the port's reader sees them in letters.
  leafAtH h sh start x col salt     the leaf's digest as the format's reader computes it
    (Fmt.leafW's call: the number 164 | 174 by "stored", the label's word with the tree's number,
    the column's and the salt's words, 2 ^ depth + place, the start, column and salt as bytes)
  mem_zip_leafV                     a listed place with its column and salt stands, with that
    digest, in the library's list of the leaves' digests
  ReadAs h cfg start op         WHAT IS ASKED OF THE READER, OPENING BY OPENING: op.out is what
    Fmt.readOpeningW (at Id) returns at op's own form and list, at SOME field, salt's length, bytes
    and place, at the configuration's digest cfg and the start "start"; the given digests have 32
    bytes
  climbs_of_read                ReadAs, h's answers of the format's lengths ⇒ every listed place
    Climbs, at vert := the vertex call 166 under cfg, with lf := leafAtH
  ownOk_of_read                 ReadAs AT THE START runOf (num op) (THE SENDER's RUN), (depth),
    (root), and the page's row law at leaves (g at ⟨e1 s x sym, the sender's run then the salt⟩ is
    leafAtH … as a digest) ⇒ OwnOk
  stoOk_of_read                 ReadAs at the start cfg, depth a, the outer root, the row law at
    stored leaves ⇒ StoOk
  mapM_isSome, plainsSL_isSome, rowsOf_isSome, tabOf_isSome
  assemble3_isSome              the three chains have run values; each stretch's rounds are
    there and each round's values are of its items' kinds (Forall₂ … ofGots … isSome); every
    opening's every listed place has its whole path in the opening's record ⇒ assemble3 … is some
  paths_of_read                     the last clause from ReadAs
WHAT IS NEEDED OF THE PORT's READER, IN LETTERS (for r : Proof.TailRead returned by the strict
reader or its twin at a hash h with answers of the format's lengths; c = 1, 2, 3; o_c the chain's
ChainOut):
  (a) o_c.run = some run_c.
  (b) o_c.rounds has at least |ds_c| rounds, and for the i-th of them, with D's i-th datum d:
    PlainOf.ofGots d.items (its vals) is some [the reader reads a message item by item by the
    description's items: with "the description's rounds are D's"].
  (c) for each round and each (sh, xs, oo) of its opens: ∃ field, salt's length, bytes, place:
    Fmt.readOpeningW h cfg field salt sh start xs b i = some oo, WHERE start = the run of the chain
    THAT SENT the tree (own: this chain's run; taken over: the "given" start, which the port makes
    of the sender's ChainRead.tree) or, at a stored tree, cfg; and every given digest has 32 bytes
    [rdDigest reads 32].
  (d) oo.root = the root that was sent for that tree (the strict reader compares), as bytes.
  (e) sh.a = the depth of D's form of that tree ("the description's rounds are D's" again).
WHAT IS NOT SAID. (a) to (e) themselves. The row laws at any family. RtsOk; the front; that every
read position is opened. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SWholeF

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom)

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- the leaf's digest as the format's reader computes it -/
def leafAtH (sh : _root_.Fmt.Shape) (start : ByteArray) (x : ℕ) (col : List UInt64)
    (salt : ByteArray) : ByteArray :=
  h (_root_.Fmt.leafNo sh.stored) (_root_.Fmt.leafPlace sh.tree col.length (salt.size / 8))
      (2 ^ sh.a + x) start
    (_root_.Fmt.leafBytes col salt)

theorem mem_zip_leafV (sh : _root_.Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)) (z : ℕ × List UInt64 × ByteArray),
        z ∈ xs.zip cs →
      (z.1, leafAtH h sh start z.1 z.2.1 z.2.2) ∈ xs.zip (_root_.Run.WalkTie.leafV h sh start xs cs)
  | [], _, _, hz => by simp at hz
  | _ :: _, [], _, hz => by simp at hz
  | x :: xs, c :: cs, z, hz => by
      rw [List.zip_cons_cons] at hz
      show _ ∈ (x, leafAtH h sh start x c.1 c.2) ::
          xs.zip (_root_.Run.WalkTie.leafV h sh start xs cs)
      rcases List.mem_cons.1 hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_zip_leafV sh start xs cs z hz)

/-- What is asked of the reader, opening by opening. -/
structure ReadAs (cfg start : ByteArray) (op : OpAt) : Prop where
  read : ∃ (f : _root_.Fmt.Fld) (salt : ℕ) (b : ByteArray) (i : ℕ),
    _root_.Fmt.readOpeningW (m := Id) h cfg f salt op.sh start op.xs b i = some op.out
  given32 : ∀ g ∈ op.out.given, g.size = 32

variable {h}

/-- Every listed place climbs. -/
theorem climbs_of_read (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg start : ByteArray}
    {op : OpAt} (R : ReadAs h cfg start op) :
    ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      Climbs (fun l r => h 166 0 0 cfg (l ++ r)) op z.1 (leafAtH h op.sh start z.1 z.2.1 z.2.2) :=
          fun z hzm => by
  obtain ⟨f, salt, b, i, e⟩ := R.read
  obtain ⟨hl, -⟩ := _root_.Run.WalkTie.reader_seen h cfg f salt op.sh start op.xs b i op.out e
  refine ⟨(_root_.Run.WalkTie.listOK_spec op.sh.a op.xs hl).2.2 z.1 (List.of_mem_zip hzm).1, ?_,
    _root_.Run.WalkTie.opening_paths h hz cfg f salt op.sh start op.xs b i op.out e R.given32 _
      (mem_zip_leafV h op.sh start op.xs _ z hzm)⟩
  unfold leafAtH
  rw [hz]
  unfold _root_.Fmt.dlen _root_.Fmt.leafNo
  cases op.sh.stored <;> rfl

end

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X} {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)}
  {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray}

/-- An opening of a tree of the prover's. -/
theorem ownOk_of_read (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg : ByteArray}
    {e1 : Enc1 (Body L)} {D : BD} {num : OpAt → ℕ} {runOf : ℕ → ByteArray}
        {Rt : ℕ → Dig 256 → Prop} {op : OpAt}
    (R : ReadAs h cfg (runOf (num op)) op) (hd : ∀ s, D.FormIs (num op) s → s.a = op.sh.a)
    (hr : ∀ c, Rt (num op) c → c = bytesToDig op.out.root)
    (hleaf : ∀ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64)
        (salt : ByteArray),
      D.FormIs (num op) s →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 s x sym, leafSalt (runOf (num op)) salt⟩ :
                          LeafIn L) : Dig 256) =
        bytesToDig (leafAtH h op.sh (runOf (num op)) x.val (List.ofFn sym) salt)) :
    OwnOk g (fun l r => h 166 0 0 cfg (l ++ r)) e1 D num runOf Rt op :=
  ⟨hd, hr, fun z hzm => ⟨_, climbs_of_read hz R z hzm, fun s x sym hF hx hs => by
    rw [hleaf s x sym z.2.2 hF, hx, hs]⟩⟩

/-- An opening of the stored copy. -/
theorem stoOk_of_read (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg : ByteArray}
    {embE : PQ.SgX → Body L} {a : ℕ} {cm : Dig 256} {op : OpAt} (R : ReadAs h cfg cfg op)
        (hd : op.sh.a = a)
    (hr : cm = bytesToDig op.out.root)
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨embE (x, col), leafSalt cfg salt⟩ : LeafIn L) :
          Dig 256) =
        bytesToDig (leafAtH h op.sh cfg x col salt)) :
    StoOk g (fun l r => h 166 0 0 cfg (l ++ r)) embE a cfg cm op :=
  ⟨hd, hr, fun z hzm => ⟨_, climbs_of_read hz R z hzm, hleaf z.1 z.2.1 z.2.2⟩⟩

end

/-! ## The typing succeeds -/

theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ z ∈ l, (f z).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | a :: l, hl => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hl a List.mem_cons_self)
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1
          (mapM_isSome f l fun z hz => hl z (List.mem_cons_of_mem _ hz))
      rw [List.mapM_cons, hb, hbs]
      rfl

theorem plainsSL_isSome (C : PQ.CK) : ∀ (ds : List PQ.RD) (os : List _root_.Fmt.RoundOut),
    List.Forall₂ (fun d o => (_root_.Run.PQ.PlainOf.ofGots d.items o.vals).isSome = true) ds os →
      (PQ.plainsSL C ds os).isSome = true
  | [], [], _ => rfl
  | d :: ds, o :: os, hf => by
      cases hf with
      | cons h1 h2 =>
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h1
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (plainsSL_isSome C ds os h2)
        simp only [PQ.plainsSL, hp, hr]
        rfl

theorem rowsOf_isSome {op : OpAt}
    (hp : ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
        (pathFrom op.sh.a op.out.seen z.1).isSome = true) :
    (rowsOf op).isSome = true :=
  mapM_isSome _ _ fun z hz => by
    obtain ⟨p, e⟩ := Option.isSome_iff_exists.1 (hp z hz)
    rw [e]
    rfl

theorem tabOf_isSome (num : OpAt → ℕ) {ops : List OpAt}
    (hp : ∀ op ∈ ops, ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      (pathFrom op.sh.a op.out.seen z.1).isSome = true) : (tabOf num ops).isSome = true := by
  unfold tabOf
  rw [Option.isSome_map]
  exact mapM_isSome _ _ fun op hop => by
    rw [Option.isSome_map]
    exact rowsOf_isSome (hp op hop)

/-- The typing's pure half succeeds. -/
theorem assemble3_isSome {Xi : Type} (D : BD)
    (dec : Xi → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
    (num : OpAt → ℕ) (w : Own D) (q : Req) (d cfg : ByteArray) (o₁ o₂ o₃ : _root_.Fmt.ChainOut)
    (h1 : o₁.run.isSome = true) (h2 : o₂.run.isSome = true) (h3 : o₃.run.isSome = true)
    (p₁ : List.Forall₂ (fun d o => (_root_.Run.PQ.PlainOf.ofGots d.items o.vals).isSome = true)
        D.G.ds₁
      (o₁.rounds.toList.take D.G.ds₁.length))
    (p₂ : List.Forall₂ (fun d o => (_root_.Run.PQ.PlainOf.ofGots d.items o.vals).isSome = true)
        D.G.ds₂
      (o₂.rounds.toList.take D.G.ds₂.length))
    (p₃ : List.Forall₂ (fun d o => (_root_.Run.PQ.PlainOf.ofGots d.items o.vals).isSome = true)
        D.G.ds₃
      (o₃.rounds.toList.take D.G.ds₃.length))
    (hp : ∀ op ∈ opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃),
        ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      (pathFrom op.sh.a op.out.seen z.1).isSome = true) :
    (assemble3 D dec num w q d cfg o₁ o₂ o₃).isSome = true := by
  obtain ⟨run₁, h1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨run₂, h2⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨run₃, h3⟩ := Option.isSome_iff_exists.1 h3
  obtain ⟨a₁, e1⟩ := Option.isSome_iff_exists.1 (plainsSL_isSome D.G.C _ _ p₁)
  obtain ⟨a₂, e2⟩ := Option.isSome_iff_exists.1 (plainsSL_isSome D.G.C _ _ p₂)
  obtain ⟨a₃, e3⟩ := Option.isSome_iff_exists.1 (plainsSL_isSome D.G.C _ _ p₃)
  obtain ⟨tab, e4⟩ := Option.isSome_iff_exists.1 (tabOf_isSome num
    (ops := (opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter fun op => !op.sh.stored)
    fun op hop => hp op (List.mem_of_mem_filter hop))
  obtain ⟨tx, e5⟩ := Option.isSome_iff_exists.1 (tabOf_isSome (fun _ => 0)
    (ops := (opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter fun op => op.sh.stored)
    fun op hop => hp op (List.mem_of_mem_filter hop))
  unfold assemble3
  rw [h1, h2, h3]
  dsimp only
  rw [e1, e2, e3, e4, e5]
  rfl

/-- the last clause from the reader's yes, opening by opening -/
theorem paths_of_read {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray}
    (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
        {cfg start : ByteArray} {op : OpAt}
    (R : ReadAs h cfg start op) :
    ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
        (pathFrom op.sh.a op.out.seen z.1).isSome = true := fun z hzm => by
  obtain ⟨-, -, p, e, -⟩ := climbs_of_read hz R z hzm
  rw [e]
  rfl

end TypedOracleCompiler.Slice
