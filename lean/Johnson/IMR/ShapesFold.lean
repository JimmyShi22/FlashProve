-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesFold.lean (kind-free): FoldFacts' FIELD
"K12.msgShapes": AT EVERY STATE THAT THE FOLD REACHES THE SHAPES OF THE STATEMENT's ORACLE MESSAGES
ARE THE FIRST OF THE SHAPES THAT ALL SENDINGS ANNOUNCE: the fold, from one debt a sub-protocol.
Theorems, proved.

Compiled with the whole library.

ON WORDS: "the state" is the verifier's state: the value of type S that the fold carries from
sub-protocol (block) to sub-protocol.

CALLED, NOT TYPED: ReachedAt, fold_last (Johnson/IMR/SendsFold.lean: the like fold for the book's
places and trees' shapes); msgShapesB, atFirstShapes (Johnson/Desc/K12/Door/MsgShapes.lean); Grows
(Johnson/Desc/Grows.lean).

  shapesOf st   the shapes of a statement's oracle messages, in the order of their numbers.
  noticesOf snd   the shapes of the notices of a list of sendings, in turn.
  ShapesOn ft G snd b   THE DEBT OF ONE SUB-PROTOCOL, asked at the states of G alone: an accepting
    step appends noticesOf snd to the shapes and turns none.
  shapes_alongR   along the fold, the debt at number j asked at the states that the fold reaches in
    front of j.
  shapes_at_cutR   AT A CHAIN, from a first state without an oracle message: the Door's own Bool
    atFirstShapes at noticesOf of all sendings of the table sn; and the shapes at the cut k are
    noticesOf of the sendings in front of k.
  stay_of_grows   a statement that has grown (Grows) and has as many oracle messages has the same
    shapes. shapes_of_grows: so a sub-protocol each of whose accepting decisions lets the statement
    grow and leaves that number owes nothing more: ShapesOn ft G [] b.
  shapes_of_sent   by the text of the plain change stSent: one prover's message appends its notices'
    shapes.
  ShapesOn.mono   a debt at more states pays the debt at fewer.

OBJECT: foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out. USER: IMR/ShapesCalm.lean; meant:
FoldFacts' field msgShapes. LETTERS: sn j: the list of sendings of the sub-protocol number j: free;
meant: the same table as at Johnson/IMR/SendsFold.lean's seats_at_cutR.

What is not claimed. ShapesOn at any sub-protocol. That noticesOf of the table's sendings is the
list that the field names (the planner's side). No soundness.
-/
import Johnson.IMR.SendsFold
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.Grows

set_option autoImplicit false

namespace IM

open OnBytes (OracleNotice OracleShape Statement)
open VerifiableInference.Desc (Block Chain foldBlocks OpenedColumn Grows)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The shapes of a statement's oracle messages, in the order of their numbers. -/
def shapesOf (st : Statement) : List OracleShape := st.oracles.toList.map (·.shape)

/-- The shapes of the notices of a list of sendings, in turn. -/
def noticesOf (snd : List (Array OracleNotice)) : List OracleShape :=
  (snd.flatMap (·.toList)).map (·.shape)

theorem noticesOf_nil : noticesOf [] = [] := rfl

theorem noticesOf_append (a b : List (Array OracleNotice)) :
    noticesOf (a ++ b) = noticesOf a ++ noticesOf b := by
  unfold noticesOf
  rw [List.flatMap_append, List.map_append]

theorem shapesOf_length (st : Statement) : (shapesOf st).length = st.oracles.size := by
  unfold shapesOf
  rw [List.length_map, Array.length_toList]

/-- **The debt of one sub-protocol, asked at the states of G alone**: an accepting step appends the
shapes of the notices snd to the statement's messages' shapes, and turns none. -/
def ShapesOn (ft : ℕ) (G : S → Prop) (snd : List (Array OracleNotice)) (b : Block S Cl) : Prop :=
  ∀ (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ), G s →
    b.step ft s rs cols = .ok (s', n) → shapesOf s'.st = shapesOf s.st ++ noticesOf snd

/-- **Along the fold, each debt asked at the states that the fold reaches in front of it.** -/
theorem shapes_alongR {ft : ℕ} {sn : ℕ → List (Array OracleNotice)} {bs : List (Block S Cl)}
    {s₀ : S} (h : ∀ j b, bs[j]? = some b → ShapesOn ft (ReachedAt ft bs s₀ j) (sn j) b) :
    ∀ (k : ℕ), k ≤ bs.length → ∀ (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft (bs.take k) s₀ rs cols = .ok out →
      shapesOf out.1.st = shapesOf s₀.st ++ noticesOf ((List.range k).flatMap sn)
  | 0, _, rs, cols, out, hf => by
    rw [List.take_zero] at hf
    obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s₀ rs cols out hf
    show shapesOf s₀.st = shapesOf s₀.st ++ noticesOf []
    rw [noticesOf_nil, List.append_nil]
  | k + 1, hk, rs, cols, out, hf => by
    have hb := List.getElem?_eq_getElem (l := bs) (i := k) (by omega)
    obtain ⟨t, rs', cols', n, h1, h2⟩ := fold_last hb hf
    have a1 := shapes_alongR h k (by omega) rs cols _ h1
    have a2 := h k _ hb t out.1 _ _ n ⟨rs, cols, _, h1, rfl⟩ h2
    rw [a2, a1, List.range_succ, List.flatMap_append, List.flatMap_singleton, noticesOf_append,
      List.append_assoc]

/-- A list is the first of itself with more behind. -/
theorem shapesB_of_prefix {st : Statement} {post : List OracleShape} :
    VerifiableInference.Desc.K12.Door.msgShapesB (shapesOf st ++ post) st = true := by
  unfold VerifiableInference.Desc.K12.Door.msgShapesB
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · show shapesOf st = (shapesOf st ++ post).take st.oracles.size
    rw [← shapesOf_length st, List.take_left']
    rfl
  · rw [List.length_append, shapesOf_length]
    omega

/-- **AT A CHAIN**: from a first state without an oracle message: at every state that the fold
reaches the messages' shapes are the first of what all sendings of the table sn announce: the
Door's own Bool. -/
theorem shapes_at_cutR {ft : ℕ} {sn : ℕ → List (Array OracleNotice)} {c : Chain S Cl} {s₀ : S}
    (h : ∀ j b, c.blocksInOrder[j]? = some b → ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ j) (sn j) b)
    (h0 : s₀.st.oracles = #[]) {k : ℕ} (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstShapes
      (noticesOf ((List.range c.blocksInOrder.length).flatMap sn)) out.1 = true ∧
      shapesOf out.1.st = noticesOf ((List.range k).flatMap sn) := by
  have a := shapes_alongR h k hk rs cols out hf
  have e0 : shapesOf s₀.st = [] := by
    unfold shapesOf
    rw [h0]
    rfl
  rw [e0, List.nil_append] at a
  have hsplit : (List.range c.blocksInOrder.length).flatMap sn =
      (List.range k).flatMap sn ++ (List.range' k (c.blocksInOrder.length - k)).flatMap sn := by
    have e : List.range' 0 c.blocksInOrder.length =
        List.range' 0 k ++ List.range' (0 + k) (c.blocksInOrder.length - k) := by
      rw [List.range'_append_1, Nat.add_sub_cancel' hk]
    rw [Nat.zero_add] at e
    rw [← List.flatMap_append, List.range_eq_range', List.range_eq_range', e]
  refine ⟨?_, a⟩
  unfold VerifiableInference.Desc.K12.Door.atFirstShapes
  rw [hsplit, noticesOf_append, ← a]
  exact shapesB_of_prefix

/-! ## Where nothing is sent: from the relation "a statement only grows" -/

/-- **A statement that has grown and has as many oracle messages has the same shapes.** -/
theorem stay_of_grows {T T' : Statement} (g : Grows T T')
    (e : T'.oracles.size = T.oracles.size) : shapesOf T' = shapesOf T := by
  apply List.ext_getElem?
  intro i
  unfold shapesOf
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  cases hx : T.oracles[i]? with
  | none =>
    have hi : T.oracles.size ≤ i := Array.getElem?_eq_none_iff.1 hx
    rw [Array.getElem?_eq_none_iff.2 (by omega)]
  | some x =>
    obtain ⟨x', h1, h2, -⟩ := g.2.2 i x hx
    rw [h1]
    show some x'.shape = some x.shape
    rw [h2]

/-- A sub-protocol each of whose accepting decisions lets the statement grow and leaves the number
of its oracle messages owes nothing more. -/
theorem shapes_of_grows {ft : ℕ} {G : S → Prop} {b : Block S Cl}
    (h : ∀ s rs gs s', b.decide s rs gs = .ok s' →
      Grows s.st s'.st ∧ s'.st.oracles.size = s.st.oracles.size) : ShapesOn ft G [] b := by
  intro s s' rs cols n _ hy
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft b s s' rs cols n hy
  obtain ⟨g, e⟩ := h s _ _ s' hd
  rw [stay_of_grows g e, noticesOf_nil, List.append_nil]

/-! ## Where one prover's message is received -/

/-- By the text of the plain change "oracle messages are sent". -/
theorem shapes_of_sent (T : Statement) (sent : Array OracleNotice) :
    shapesOf (OnBytes.Slice.stSent T sent) = shapesOf T ++ noticesOf [sent] := by
  unfold shapesOf noticesOf OnBytes.Slice.stSent
  simp

/-- A debt at more states pays the debt at fewer. -/
theorem ShapesOn.mono {ft : ℕ} {G G' : S → Prop} {snd : List (Array OracleNotice)}
    {b : Block S Cl} (hG : ∀ s, G' s → G s) (h : ShapesOn ft G snd b) : ShapesOn ft G' snd b :=
  fun s s' rs cols n hg hy => h s s' rs cols n (hG s hg) hy

end IM

#print axioms IM.shapes_alongR
#print axioms IM.shapes_at_cutR
#print axioms IM.stay_of_grows
#print axioms IM.shapes_of_grows
#print axioms IM.shapes_of_sent
#print axioms IM.ShapesOn.mono
