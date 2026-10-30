-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SRead2.lean: EVERY LISTED PLACE OF AN OPENING CLIMBS
(Slice/Batch3SWholeF.lean: Climbs), FROM FACTS ON THE OPENING IN THE PLACE OF THE READER's EQUATION;
AND FROM FACTS "ROUND BY ROUND" TO FACTS "FOR EVERY OPENING OF THE TYPING's LIST". Lemmas with
proofs.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Slice/Batch3SRead.lean's ReadAs asks the equation Fmt.readOpeningW … = some op.out. What the
trace of OnBytes/Tie/TraceStrict.lean gives of an opening is FACTS (the library's OpenFacts |
StoredFact of OnBytes/Tie/; the walk's end), and nothing on its record "seen". The library's
opening_paths uses its equation only through reader_seen's six clauses. So here the same conclusion
is had from these six, five of which the trace's facts give; the sixth is the law of "seen".
  FactsAs h cfg start op   (okl) the list is sorted, without repeats, not empty, within the
    tree; (cols | salts) as many columns and salts as places; (need) as many given digests as the
    pruned walk takes; (walk) op.out.root is the end of the library's pruned walk from the leaves'
    digests at "start"; (seen) op.out.seen = metAll … ++ noteAll …: ALL THAT THE WALK HAS PASSED
    AND NOTED: THE CLAUSE THAT THE TRACE LACKS; (given32)
  factsAs_of_read              the reader's equation gives them (the library's reader_seen): so
    FactsAs is the weaker asking
  climbs_of_facts          FactsAs, h's answers of the format's lengths ⇒ every listed place
    Climbs. THE PROOF IS THE LIBRARY's opening_paths' OWN TEXT behind its first line
  ownOk_of_facts, stoOk_of_facts, paths_of_facts     Batch3SRead's three, from FactsAs
  mem_opsOf                    an opening of the typing's list stands in a round of its chain: op ∈
    opsOf c o → op.chain = c ∧ ∃ r ∈ o.rounds.toList, (op.sh, op.xs, op.out) ∈ r.opens
  ops_all                  a property of every opening of every round of the three chains holds
    of every member of the typing's list
WHAT IS NOT SAID. That any reading has FactsAs. All that Batch3SRead.lean's head leaves open.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SRead

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom)
open _root_.Run.WalkTie Octopus

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- Facts on an opening, in the place of the reader's equation. -/
structure FactsAs (cfg start : ByteArray) (op : OpAt) : Prop where
  okl : _root_.Fmt.listOK op.sh.a op.xs = true
  cols : op.out.cols.length = op.xs.length
  salts : op.out.salts.length = op.xs.length
  need : op.out.given.length = Octopus.need op.sh.a op.xs
  walk : op.out.root = (octF (fun l r => h 166 0 0 cfg (l ++ r)) op.sh.a op.xs
    (leafV h op.sh start op.xs (op.out.cols.zip op.out.salts)) op.out.given).headD default
  seen : op.out.seen = metAll (fun l r => h 166 0 0 cfg (l ++ r)) op.sh.a op.xs
      (leafV h op.sh start op.xs (op.out.cols.zip op.out.salts)) op.out.given ++
    noteAll op.sh.a op.xs op.out.given
  given32 : ∀ g ∈ op.out.given, g.size = 32

variable {h}

/-- the reader's equation gives them -/
theorem factsAs_of_read {cfg start : ByteArray} {op : OpAt} (R : ReadAs h cfg start op) :
    FactsAs h cfg start op := by
  obtain ⟨f, salt, b, i, e⟩ := R.read
  obtain ⟨hl, r1, r2, r3, r4, r5⟩ := reader_seen h cfg f salt op.sh start op.xs b i op.out e
  exact ⟨hl, r1, r2, r3, r4, r5, R.given32⟩

/-- Every listed place climbs. -/
theorem climbs_of_facts (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg start : ByteArray}
    {op : OpAt} (F : FactsAs h cfg start op) :
    ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
      Climbs (fun l r => h 166 0 0 cfg (l ++ r)) op z.1 (leafAtH h op.sh start z.1 z.2.1 z.2.2) :=
          fun z hzm => by
  obtain ⟨hl, r1, r2, r3, r4, r5, hg⟩ := F
  obtain ⟨-, hp, hb⟩ := listOK_spec op.sh.a op.xs hl
  have hu1 := listOK_one op.sh.a op.xs hl
  have hlen : (leafV h op.sh start op.xs (op.out.cols.zip op.out.salts)).length = op.xs.length :=
    length_leafV h op.sh start op.xs _ (by rw [List.length_zip, r1, r2, Nat.min_self])
  have hn : Octopus.need op.sh.a op.xs ≤ op.out.given.length := le_of_eq r3.symm
  have hc := mem_zip_leafV h op.sh start op.xs _ z hzm
  have hmem : ∀ x,
      x ∈ op.out.seen ↔
      InLv (fun l r => h 166 0 0 cfg (l ++ r)) op.sh.a op.xs
          (leafV h op.sh start op.xs (op.out.cols.zip op.out.salts))
        op.out.given x.1 (x.2.1, x.2.2) :=
    fun x => by rw [r5]; exact mem_seen_iff _ _ _ _ _ x
  obtain ⟨p, h1, h2, h3⟩ := paths_ind (fun l r => h 166 0 0 cfg (l ++ r)) op.out.seen
    (fun y hy y' hy' e1 e2 =>
      InLv_unique _ op.sh.a op.xs _ op.out.given hp hlen hn hu1 y.1 (y.2.1, y.2.2) (y'.2.1, y'.2.2)
        ((hmem y).1 hy) (by rw [e1]; exact (hmem y').1 hy') e2)
    op.sh.a op.xs _ op.out.given hp hlen hn (fun d' e' hi => (hmem (d', e'.1, e'.2)).2 hi) _ hc
  refine ⟨hb z.1 (List.of_mem_zip hzm).1, ?_, p, h1, PathOK_length _ _ _ _ _ _ p h2,
      fun q hq => ?_, ?_⟩
  · unfold leafAtH
    rw [hz]
    unfold _root_.Fmt.dlen _root_.Fmt.leafNo
    cases op.sh.stored <;> rfl
  · obtain ⟨d', k, hk⟩ := h3 q hq
    exact InLv_all (fun l r => h 166 0 0 cfg (l ++ r)) (fun x => x.size = 32)
      (fun a b => hz 166 0 0 cfg (a ++ b))
      (_root_.Run.TieTree.size_stepF _ (fun a b => hz 166 0 0 cfg (a ++ b))) op.sh.a op.xs _
          op.out.given hn
      (leafV_size h hz op.sh start op.xs _) hg d' (k, q) ((hmem (d', k, q)).1 hk)
  · rw [climb_ok _ op.sh.a op.xs _ op.out.given hp hlen hn hu1 _ _ p hc h2, r4]

theorem paths_of_facts (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg start : ByteArray}
    {op : OpAt} (F : FactsAs h cfg start op) :
    ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
        (pathFrom op.sh.a op.out.seen z.1).isSome = true := fun z hzm => by
  obtain ⟨-, -, p, e, -⟩ := climbs_of_facts hz F z hzm
  rw [e]
  rfl

end

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X} {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)}
  {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray}

theorem ownOk_of_facts (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg : ByteArray}
    {e1 : Enc1 (Body L)} {D : BD} {num : OpAt → ℕ} {runOf : ℕ → ByteArray}
        {Rt : ℕ → Dig 256 → Prop} {op : OpAt}
    (F : FactsAs h cfg (runOf (num op)) op) (hd : ∀ s, D.FormIs (num op) s → s.a = op.sh.a)
    (hr : ∀ c, Rt (num op) c → c = bytesToDig op.out.root)
    (hleaf : ∀ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64)
        (salt : ByteArray),
      D.FormIs (num op) s →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 s x sym, leafSalt (runOf (num op)) salt⟩ :
                          LeafIn L) : Dig 256) =
        bytesToDig (leafAtH h op.sh (runOf (num op)) x.val (List.ofFn sym) salt)) :
    OwnOk g (fun l r => h 166 0 0 cfg (l ++ r)) e1 D num runOf Rt op :=
  ⟨hd, hr, fun z hzm => ⟨_, climbs_of_facts hz F z hzm, fun s x sym hF hx hs => by
    rw [hleaf s x sym z.2.2 hF, hx, hs]⟩⟩

theorem stoOk_of_facts (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg : ByteArray}
    {embE : PQ.SgX → Body L} {a : ℕ} {cm : Dig 256} {op : OpAt} (F : FactsAs h cfg cfg op)
        (hd : op.sh.a = a)
    (hr : cm = bytesToDig op.out.root)
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨embE (x, col), leafSalt cfg salt⟩ : LeafIn L) :
          Dig 256) =
        bytesToDig (leafAtH h op.sh cfg x col salt)) :
    StoOk g (fun l r => h 166 0 0 cfg (l ++ r)) embE a cfg cm op :=
  ⟨hd, hr, fun z hzm => ⟨_, climbs_of_facts hz F z hzm, hleaf z.1 z.2.1 z.2.2⟩⟩

end

/-! ## From rounds to the typing's list -/

theorem fst_mem_zipIdx {α : Type} : ∀ (l : List α) (n : ℕ) (x : α × ℕ), x ∈ l.zipIdx n → x.1 ∈ l
  | [], _, _, hx => by simp at hx
  | a :: l, n, x, hx => by
      rw [List.zipIdx_cons] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (fst_mem_zipIdx l (n + 1) x hx)

/-- an opening of the typing's list stands in a round of its chain -/
theorem mem_opsOf {c : ℕ} {o : _root_.Fmt.ChainOut} {op : OpAt} (hop : op ∈ opsOf c o) :
    op.chain = c ∧ ∃ r ∈ o.rounds.toList, (op.sh, op.xs, op.out) ∈ r.opens := by
  unfold opsOf at hop
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.1 hop
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  subst e
  exact ⟨rfl, r.1, fst_mem_zipIdx _ _ _ hr, fst_mem_zipIdx _ _ _ hx⟩

/-- A property of every opening of every round holds of every member of the typing's list. -/
theorem ops_all (Q : ℕ → _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut → Prop)
    (o₁ o₂ o₃ : _root_.Fmt.ChainOut)
    (h₁ : ∀ r ∈ o₁.rounds.toList, ∀ y ∈ r.opens, Q 1 y)
        (h₂ : ∀ r ∈ o₂.rounds.toList, ∀ y ∈ r.opens, Q 2 y)
    (h₃ : ∀ r ∈ o₃.rounds.toList, ∀ y ∈ r.opens, Q 3 y) :
    ∀ op ∈ opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃), Q op.chain (op.sh, op.xs, op.out) :=
        fun op hop => by
  rcases List.mem_append.1 hop with hop | hop
  · obtain ⟨e, r, hr, hy⟩ := mem_opsOf hop
    rw [e]
    exact h₁ r hr _ hy
  · rcases List.mem_append.1 hop with hop | hop
    · obtain ⟨e, r, hr, hy⟩ := mem_opsOf hop
      rw [e]
      exact h₂ r hr _ hy
    · obtain ⟨e, r, hr, hy⟩ := mem_opsOf hop
      rw [e]
      exact h₃ r hr _ hy

end TypedOracleCompiler.Slice
