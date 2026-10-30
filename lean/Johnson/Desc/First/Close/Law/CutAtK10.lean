-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CutAtK10.lean: THE PIECE THAT THE RULE OF COMPOSITION's OWN MAKER MAKES
OF A BLOCK THAT DECLARES K10's ROUNDS HAS JUST THE DATA OF WHICH K10's LAW SPEAKS. Definitions,
statements and proofs. After the form of Johnson/Desc/First/Batch/Law/CutAt.lean, which does the
like for a block with one round; its general lemmas (`cut_piece`, `forall₂_at`, `data_at₁`) are
called.

Why. K10's law stands at a piece whose rounds' data are dB :: dE :: k times dR, under three
premises: these data have the entry, the kind and the items of the format's rounds "BAT", "FOLD
epsilon", "FOLD round" (`IsRd`). A piece puts out nothing unless what is shown fits its block's
declared rounds (`Piece.out_decide`, Johnson/Desc/Sound/PieceOut.lean: `roundsFit`): so at data that
do not fit them the law would hold idly [by a reading, not shown here]. So a
term must tie the law's data to the block's declared rounds.
  `dOf r`; `dBat rows`, `dEps`, `dTwo`: the road's data (`rdtOf`, `Three.rdOf`) of a written
    round that sends no root, opens nothing and has no stored part; at the three rounds. `dBat_is`,
    `dEps_is`, `dTwo_is`: THE LAW's THREE PREMISES ON ITS ROUNDS HOLD OF THEM. `rd_bat`, `rd_eps`,
    `rd_two`: the road's data of these rounds do not hang on the trees' numbers. `rd_at`: the two
    lists, place by place.
  `decl_at_j`: the declared round number j of block k, in the chain's row of declared rounds.
    `drop_take_of`: a stretch of a list, from its members.
  `k10_cut`: the chain's declared rounds written out as R₁ (`WrittenAs`, OF THE WHOLE CHAIN: the
    road's own premise); block k (not the last) declares the rounds of `kind Q`; Q's two
    numbers of proof of work are 0; K10's rounds are not the chain's last: THEN THE MAKER's PIECE
    NUMBER k (`cutRow`, Johnson/Desc/Sound/Tiles.lean) IS `pieceOf` of that block at dBat Q.rows ::
    dEps :: Q.k times dTwo, nothing put back. General in the blocks' state.
  `k10_cut_held`: AT THE ROW THAT A DESCRIPTION HAS: its pieces are cut of `held b`
    (Johnson/Desc/Sound/PaidAtDesc.lean: b under the words' test, lifted over the pair of what was
    handed to the chain and the verifier's state): the premises are asked of the description's own
    blocks b₀ :: l; the maker's piece number k is `pieceOf (held b)` at these data.
  `k10_cut_on`: OVER THE BARE STATE: in a row of blocks over the first chain's state alone, where
    block k is `below b`: the maker's piece is `pieceOn b` (AtAny.lean, beside this file), the piece
    at which K10's law is typed, at these data and Q.k. No description has such a row.
Limits. BETWEEN `pieceOf (held b)` AND `pieceOn b` (the lifted piece and the law's) NOTHING IS TYPED
HERE: the two have one base, one list of data and nothing put back; to carry a law or a tie from the
one to the other is other files' rule. Not claimed: that a description's data are `dataOf` of its
written rounds (its `data` has to return). The number of the first tree (base') stands under "there
is". The two numbers of proof of work are premises. That the law's typed number of fold rounds is
Q.k, and its number of batched rows Q.rows, is not here. Nothing on soundness.
No description has a row with the piece over the bare state: see
`k10_cut_held`.

-/
import Johnson.Desc.First.Batch.Law.CutAt
import Johnson.Desc.First.Close.Law.RoundsOfPar
import Johnson.Desc.First.Close.Law.AtAny
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc.Sound VerifiableInference.Desc.K9L
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open OnBytes.Params (Rounds)

/-- The data of a written round that sends no root, opens nothing and has no stored part. -/
def dOf (r : Fmt.Round) : RDT := rdtOf (Three.rdOf [] 0 0 0 0 0 (r, []) 0)

/-- The three data of K10's rounds. -/
def dBat (rows : ℕ) : RDT := dOf (Fmt.M2.rBatN rows)
def dEps : RDT := dOf (Fmt.M1.rEps "FOLD epsilon")
def dTwo : RDT := dOf (Fmt.M1.rTwo "FOLD round")

theorem dBat_is (rows : ℕ) : IsRd (toRD (dBat rows)) (Fmt.M2.rBatN rows) := ⟨rfl, rfl, rfl⟩
theorem dEps_is : IsRd (toRD dEps) (Fmt.M1.rEps "FOLD epsilon") := ⟨rfl, rfl, rfl⟩
theorem dTwo_is : IsRd (toRD dTwo) (Fmt.M1.rTwo "FOLD round") := ⟨rfl, rfl, rfl⟩

/-- The road's data of these three written rounds do not hang on the trees' numbers. -/
theorem rd_bat (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first sent rows : ℕ) :
    rdtOf (Three.rdOf all t₁ t₂ here base first (Fmt.M2.rBatN rows, []) sent) = dBat rows := rfl

theorem rd_eps (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first sent : ℕ) :
    rdtOf (Three.rdOf all t₁ t₂ here base first (Fmt.M1.rEps "FOLD epsilon", []) sent) = dEps :=
  rfl

theorem rd_two (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first sent : ℕ) :
    rdtOf (Three.rdOf all t₁ t₂ here base first (Fmt.M1.rTwo "FOLD round", []) sent) = dTwo := rfl

/-- The law's list of data, against the format's list of rounds, place by place. -/
theorem rd_at (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ sent rows k : ℕ) :
    ∀ (j : ℕ) (x : Fmt.Round × List Fmt.Stored), (roundsOf rows k)[j]? = some x →
      (dBat rows :: dEps :: List.replicate k dTwo)[j]? =
        some (rdtOf (Three.rdOf all t₁ t₂ 0 0 0 x sent))
  | 0, x, h => by
    obtain rfl : _ = x := Option.some.inj h
    rfl
  | 1, x, h => by
    obtain rfl : _ = x := Option.some.inj h
    rfl
  | j + 2, x, h => by
    have h' : (List.replicate k (Fmt.M1.rTwo "FOLD round", ([] : List Fmt.Stored)))[j]? =
        some x := h
    show (List.replicate k dTwo)[j]? = _
    rw [List.getElem?_replicate] at h' ⊢
    split at h'
    · rename_i hj
      obtain rfl : _ = x := Option.some.inj h'
      rw [if_pos hj]
      rfl
    · cases h'

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- The declared round number j of block k stands, in the chain's row of declared rounds, j places
behind the rounds of the blocks in front. -/
theorem decl_at_j : ∀ (bs : List (Block S Cl)) (k : ℕ) (bk : Block S Cl) (j : ℕ)
    (d : Fmt.DeclaredRound), bs[k]? = some bk → bk.rounds[j]? = some d →
    (bs.flatMap (·.rounds))[roundsBefore bs k + j]? = some d
  | [], _, _, _, _, h, _ => nomatch h
  | b :: l, 0, bk, j, d, h, hr => by
    obtain rfl : b = bk := Option.some.inj h
    have hj : j < b.rounds.length := (List.getElem?_eq_some_iff.1 hr).1
    simp only [roundsBefore, List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
      List.flatMap_cons]
    rw [List.getElem?_append_left hj]
    exact hr
  | b :: l, k + 1, bk, j, d, h, hr => by
    rw [roundsBefore_succ, List.flatMap_cons, Nat.add_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact decl_at_j l k bk j d h hr

/-- A stretch of a list, from its members. -/
theorem drop_take_of {α : Type} (l L : List α) (n : ℕ)
    (h : ∀ j, j < L.length → l[n + j]? = L[j]?) : (l.drop n).take L.length = L := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take]
  split
  · rename_i hj
    rw [List.getElem?_drop]
    exact h j hj
  · rename_i hj
    exact (List.getElem?_eq_none (Nat.le_of_not_lt hj)).symm

/-- **THE MAKER's PIECE AT A BLOCK THAT DECLARES K10's ROUNDS.** -/
theorem k10_cut {Cl' : Type} (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (i base a : ℕ) (R₁ R₂ R₃ : Rounds)
    (e : List (List ByteArray × ByteArray)) (b : Block S Cl) (l : List (Block S Cl)) (k : ℕ)
    (bk : Block S Cl) (Q : Par) (h1 : Q.workField = 0) (h2 : Q.workClose = 0)
    (hW : WrittenAs e ((b :: l).flatMap (·.rounds)) R₁) (hk : (b :: l)[k]? = some bk)
    (hlast : k < l.length) (hr : bk.rounds = (kind (Cl := Cl') Q).rounds)
    (hseal : roundsBefore (b :: l) k + (2 + Q.k) < R₁.length) :
    ∃ base', ((cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).1 ::
        (cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).2)[k]? =
      some (pieceOf bk base' (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (rest (i + k) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) := by
  obtain ⟨base', j, ds', rfl, e1, h⟩ :=
    cut_piece rest putBack k i base (dataOf a R₁ R₂ R₃).ds₁ b l bk hk hlast
  have hlen : (dBat Q.rows :: dEps :: List.replicate Q.k dTwo).length = bk.rounds.length := by
    rw [hr, kind_rounds_length]
    simp only [List.length_cons, List.length_replicate]
    omega
  have e2 : ds' = dBat Q.rows :: dEps :: List.replicate Q.k dTwo := by
    rw [e1, ← hlen]
    refine drop_take_of _ _ _ fun j hj => ?_
    have hj' : j < 2 + Q.k := by
      rw [hlen, hr, kind_rounds_length] at hj
      exact hj
    -- the declared round number j, and the format's round of it
    obtain ⟨d, hd⟩ : ∃ d, bk.rounds[j]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by rw [hr, kind_rounds_length]; exact hj')⟩
    obtain ⟨x0, hx0, g1, g2⟩ := forall₂_at (kind_written (Cl := Cl') Q e h1 h2) j d (hr ▸ hd)
    obtain ⟨x, hx, f1, f2⟩ := forall₂_at hW _ _ (decl_at_j (b :: l) k bk j d hk hd)
    obtain rfl : x = x0 :=
      Prod.ext (Option.some.inj (f1.symm.trans g1)) (f2.trans g2.symm)
    obtain ⟨all, t₁, t₂, sent, hdat⟩ := data_at₁ a R₁ R₂ R₃ _ _ hx (by omega)
    rw [hdat]
    exact (rd_at all t₁ t₂ sent Q.rows Q.k j x hx0).symm
  subst e2
  exact ⟨base', h⟩

/-- **OVER THE BARE STATE**: in a row of blocks over the first chain's state alone, where the block
in the maker's list is a block b under the words' test, the maker's piece is pieceOn b at these
three data, at Q.k fold rounds, with the maker's own extractor and errors; and the three data meet
the law's three premises on its rounds. NO DESCRIPTION HAS SUCH A ROW: see k10_cut_held. -/
theorem k10_cut_on {Cl' Cl₀ W₀ : Type} {F₀ : Frame}
    (rest : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) F₀ VerifiableInference.Desc.First.S W₀ ds)
    (putBack : List Fmt.RoundView) (i base a : ℕ) (R₁ R₂ R₃ : Rounds)
    (e : List (List ByteArray × ByteArray)) (b₀ : Block VerifiableInference.Desc.First.S Cl₀)
    (l : List (Block VerifiableInference.Desc.First.S Cl₀)) (k : ℕ)
    (b : Block VerifiableInference.Desc.First.S Cl₀) (Q : Par) (h1 : Q.workField = 0)
    (h2 : Q.workClose = 0) (hW : WrittenAs e ((b₀ :: l).flatMap (·.rounds)) R₁)
    (hk : (b₀ :: l)[k]? = some (below b)) (hlast : k < l.length)
    (hr : b.rounds = (kind (Cl := Cl') Q).rounds)
    (hseal : roundsBefore (b₀ :: l) k + (2 + Q.k) < R₁.length) :
    ∃ base', ((cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b₀ l).1 ::
        (cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b₀ l).2)[k]? =
      some (pieceOn b base' (dBat Q.rows) dEps dTwo Q.k
        (rest (i + k) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo)).ext
        (rest (i + k) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo)).err) ∧
      IsRd (toRD (dBat Q.rows)) (Fmt.M2.rBatN Q.rows) ∧
      IsRd (toRD dEps) (Fmt.M1.rEps "FOLD epsilon") ∧
      IsRd (toRD dTwo) (Fmt.M1.rTwo "FOLD round") := by
  obtain ⟨base', h⟩ := k10_cut (Cl' := Cl') rest putBack i base a R₁ R₂ R₃ e b₀ l k (below b) Q h1
    h2 hW hk hlast hr hseal
  exact ⟨base', h, dBat_is Q.rows, dEps_is, dTwo_is⟩

/-- **AT THE ROW THAT A DESCRIPTION HAS**: its pieces are cut of the blocks held b: b under the
words' test, lifted over the pair (what was handed to the chain, the verifier's state)
(Johnson/Desc/Sound/PaidAtDesc.lean: held, piecesAt). The maker's piece at held b has the law's
data. -/
theorem k10_cut_held {Cl' P₀ : Type}
    (rest : (i : ℕ) → (ds : List RDT) → Rest C F (P₀ × S) W ds) (putBack : List Fmt.RoundView)
    (i base a : ℕ) (R₁ R₂ R₃ : Rounds) (e : List (List ByteArray × ByteArray))
    (b₀ : Block S Cl) (l : List (Block S Cl)) (k : ℕ) (b : Block S Cl) (Q : Par)
    (h1 : Q.workField = 0) (h2 : Q.workClose = 0)
    (hW : WrittenAs e ((b₀ :: l).flatMap (·.rounds)) R₁) (hk : (b₀ :: l)[k]? = some b)
    (hlast : k < l.length) (hr : b.rounds = (kind (Cl := Cl') Q).rounds)
    (hseal : roundsBefore (b₀ :: l) k + (2 + Q.k) < R₁.length) :
    ∃ base', ((cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ (held b₀) (l.map held)).1 ::
        (cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ (held b₀) (l.map held)).2)[k]? =
      some (pieceOf (held b) base' (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (rest (i + k) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) := by
  have hf : ∀ L : List (Block S Cl),
      (L.map (held (P := P₀))).flatMap (·.rounds) = L.flatMap (·.rounds) := by
    intro L
    induction L with
    | nil => rfl
    | cons x L ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rfl
  have hrb : roundsBefore (held (P := P₀) b₀ :: l.map held) k = roundsBefore (b₀ :: l) k := by
    unfold roundsBefore
    rw [← List.map_cons, ← List.map_take, hf]
  refine k10_cut (Cl' := Cl') rest putBack i base a R₁ R₂ R₃ e (held b₀) (l.map held) k (held b) Q
    h1 h2 ?_ ?_ (by rw [List.length_map]; exact hlast) hr (by rw [hrb]; exact hseal)
  · rw [← List.map_cons, hf]
    exact hW
  · rw [← List.map_cons, List.getElem?_map, hk]
    rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_cut_held
#print axioms VerifiableInference.Desc.First.Close.k10_cut_on
#print axioms VerifiableInference.Desc.First.Close.rd_at
#print axioms VerifiableInference.Desc.First.Close.decl_at_j
#print axioms VerifiableInference.Desc.First.Close.k10_cut
