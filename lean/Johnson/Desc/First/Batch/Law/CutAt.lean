-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/CutAt.lean
(kind K9's soundness lemma): THEOREMS: THE PIECE THAT THE RULE OF COMPOSITION's OWN MAKER (cutRow,
Johnson/Desc/Sound/Tiles.lean) MAKES OF A BLOCK THAT DECLARES K9's ONE ROUND HAS JUST K9's ROUND AS
ITS DATA: the premises hds and hbk of K9's row (Law/RowAtS.lean, Law/RowSteps.lean, the joining's
JoinAsks) AT THAT FUNCTION, where the chain's data are made of the blocks' own declared rounds by
the road (declared rounds written out: WrittenAs; the data of written rounds: dataOf).
  roundsBefore bs k   the number of rounds that the blocks in front of block k declare.
  cut_piece     the maker's piece number k (not the last) holds block k, nothing put back, and of
                the chain's data the stretch behind roundsBefore, as long as block k declares.
  written_at    declared rounds written out, round by round: the written round at a place.
  decl_at       the declared round at roundsBefore bs k is block k's own, where it declares one.
  data_at₁      the first chain's data at a place (not the last written round) are that written
                round's (rdOf, rdtOf): entry, kind, items and stored parts field for field; the
                trees and the openings UP TO THE TREES' NUMBERS (the four letters behind "there are"
                are tied to nothing in the statement).
  k9Decl_roundE K9's declared round, written out, whatever the earlier chains' roots are.
  rd_k9         the data of that written round are k9Round p: by rfl: it sends no root and opens
                nothing, so the trees' numbers play no part.
  k9_cut        **the maker's piece at a block with rounds = [k9Decl p] is
                pieceOf bk base' [k9Round p] [] (rest (i + k) [k9Round p])**: so hds and hbk hold by
                rfl; hextb and hcap are then sentences on the family "rest" at the block's own
                number i + k and at [k9Round p].
  capRest, k9_cut_asks   at the family that hands the witness on and carries the cap 128: hds, hbk,
                hextb and hcap together.
  below_rounds, lift_rounds   the words' test and a lift leave a block's declared rounds. (That K9's
                batching declares [k9Decl p]: Law/ConditionAt.lean: batch_rounds.)
hseal: K9's round is not the chain's last written round (the seal, which the data leave out).
Not claimed: that a description's first chain is cut by this maker (Three.IsCut); THAT WHOEVER CALLS
THE RULE OF COMPOSITION LAYS THE FAMILY capRest: it is a family of our own writing, to show that the
four premises can be had together at the maker's piece.

-/
import Johnson.Desc.Sound.TilesCutProofs
import OnBytes.Maker.ReadSpecs
import Johnson.Desc.First.Batch.Law.ConditionAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open OnBytes.Params (Rounds)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- The number of rounds that the blocks in front of block k declare. -/
def roundsBefore (bs : List (Block S Cl)) (k : ℕ) : ℕ := ((bs.take k).flatMap (·.rounds)).length

theorem roundsBefore_succ (b : Block S Cl) (l : List (Block S Cl)) (k : ℕ) :
    roundsBefore (b :: l) (k + 1) = b.rounds.length + roundsBefore l k := by
  simp [roundsBefore]

/-- **The maker's piece number k.** -/
theorem cut_piece (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView) :
    ∀ (k i base : ℕ) (ds : List RDT) (b : Block S Cl) (l : List (Block S Cl)) (bk : Block S Cl),
      (b :: l)[k]? = some bk → k < l.length →
      ∃ (base' j : ℕ) (ds' : List RDT), j = i + k ∧
        ds' = (ds.drop (roundsBefore (b :: l) k)).take bk.rounds.length ∧
        ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[k]? =
          some (pieceOf bk base' ds' [] (rest j ds'))
  | _, _, _, _, _, [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | 0, i, base, ds, b, b' :: l, bk, hb, _ => by
    obtain rfl : b = bk := Option.some.inj hb
    exact ⟨base, i, ds.take b.rounds.length, rfl, by simp [roundsBefore],
      by rw [cutRow_cons]; rfl⟩
  | k + 1, i, base, ds, b, b' :: l, bk, hb, hk => by
    obtain ⟨base', j, ds', ej, e, h⟩ := cut_piece rest putBack k (i + 1)
      (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) b' l bk hb
      (Nat.lt_of_succ_lt_succ hk)
    refine ⟨base', j, ds', by omega, ?_, ?_⟩
    · rw [e, roundsBefore_succ, List.drop_drop]
    · rw [cutRow_cons]
      exact h

/-- Two lists related member by member: the partner at a place. -/
theorem forall₂_at {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {R : List β},
    List.Forall₂ P l R → ∀ (n : ℕ) (a : α), l[n]? = some a → ∃ b, R[n]? = some b ∧ P a b
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons h0 _, 0, a, h => by
    obtain rfl := Option.some.inj h
    exact ⟨_, rfl, h0⟩
  | _, _, .cons _ ht, n + 1, a, h => forall₂_at ht n a h

/-- The declared round at roundsBefore bs k is block k's own, where it declares one round. -/
theorem decl_at : ∀ (bs : List (Block S Cl)) (k : ℕ) (bk : Block S Cl) (d : Fmt.DeclaredRound),
    bs[k]? = some bk → bk.rounds = [d] →
    (bs.flatMap (·.rounds))[roundsBefore bs k]? = some d
  | [], _, _, _, h, _ => nomatch h
  | b :: l, 0, bk, d, h, hr => by
    obtain rfl : b = bk := Option.some.inj h
    simp [roundsBefore, hr]
  | b :: l, k + 1, bk, d, h, hr => by
    rw [roundsBefore_succ, List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact decl_at l k bk d h hr

theorem drop_take_one {α : Type} : ∀ (l : List α) (n : ℕ) (x : α), l[n]? = some x →
    (l.drop n).take 1 = [x]
  | [], _, _, h => nomatch h
  | a :: l, 0, x, h => by
    obtain rfl := Option.some.inj h
    rfl
  | a :: l, n + 1, x, h => drop_take_one l n x h

/-- **The first chain's data at a place are that written round's**, up to the trees' numbers. -/
theorem data_at₁ (a : ℕ) (R₁ R₂ R₃ : Rounds) (n : ℕ) (r : Fmt.Round × List Fmt.Stored)
    (hr : R₁[n]? = some r) (hn : n + 1 < R₁.length) :
    ∃ all t₁ t₂ sent, (dataOf a R₁ R₂ R₃).ds₁[n]? =
      some (rdtOf (Three.rdOf all t₁ t₂ 0 0 0 r sent)) := by
  have hl : (Three.sentBefore R₁).length = R₁.length := sentBefore_length R₁
  obtain ⟨s, hs⟩ : ∃ s, (Three.sentBefore R₁)[n]? = some s :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  refine ⟨Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 0 R₁ ++
    (Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 1 R₂ ++
      Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 2 R₃),
    Three.rootsIn R₁, Three.rootsIn R₂, s, ?_⟩
  show ((Three.Whole.of R₁ R₂ R₃).stretch₁.map rdtOf)[n]? = _
  rw [List.getElem?_map]
  unfold Three.Whole.stretch₁ Three.Whole.of Three.rdsFromL
  simp only [List.getElem?_dropLast, List.length_zipWith, hl, Nat.min_self, List.getElem?_zipWith,
    hr, hs]
  rw [if_pos (by omega)]
  rfl

/-- K9's declared round, written out, whatever the earlier chains' roots are. -/
theorem k9Decl_roundE (e : List (List ByteArray × ByteArray)) (p : K9.Where) :
    (k9Decl p).round e = some { entry := K9.entry p, kind := .elems } := by
  have hk : Fmt.kindOf (k9Decl p).entry.name = some .elems := kindOf_sigma
  have ho : (k9Decl p).opens = [] := rfl
  have hi : (k9Decl p).items = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, k9Decl, K9.entry]
  unfold Fmt.DeclaredRound.round
  rw [hk, ho, hi]
  simp [k9Decl]

/-- The data of that written round are K9's round. -/
theorem rd_k9 (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first sent : ℕ)
    (p : K9.Where) :
    rdtOf (Three.rdOf all t₁ t₂ here base first
      ({ entry := K9.entry p, kind := .elems }, []) sent) = k9Round p := rfl

/-- **The maker's piece at a block that declares K9's one round.** -/
theorem k9_cut (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (i base a : ℕ) (R₁ R₂ R₃ : Rounds) (e : List (List ByteArray × ByteArray))
    (b : Block S Cl) (l : List (Block S Cl)) (k : ℕ) (bk : Block S Cl) (p : K9.Where)
    (hW : WrittenAs e ((b :: l).flatMap (·.rounds)) R₁) (hk : (b :: l)[k]? = some bk)
    (hlast : k < l.length) (hr : bk.rounds = [k9Decl p])
    (hseal : roundsBefore (b :: l) k + 1 < R₁.length) :
    ∃ base', ((cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).1 ::
        (cutRow rest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).2)[k]? =
      some (pieceOf bk base' [k9Round p] [] (rest (i + k) [k9Round p])) := by
  obtain ⟨base', j, ds', rfl, e1, h⟩ :=
    cut_piece rest putBack k i base (dataOf a R₁ R₂ R₃).ds₁ b l bk hk hlast
  obtain ⟨x, hx, h1, h2⟩ := forall₂_at hW _ _ (decl_at (b :: l) k bk (k9Decl p) hk hr)
  rw [k9Decl_roundE] at h1
  have ex : x = ({ entry := K9.entry p, kind := .elems }, []) :=
    Prod.ext (Option.some.inj h1).symm h2
  rw [ex] at hx
  obtain ⟨all, t₁, t₂, sent, hd⟩ := data_at₁ a R₁ R₂ R₃ _ _ hx hseal
  rw [rd_k9] at hd
  have e2 : ds' = [k9Round p] := by
    rw [e1, hr]
    exact drop_take_one _ _ _ hd
  subst e2
  exact ⟨base', h⟩

/-- The family "rest" at which every piece hands the witness on and carries the cap. -/
noncomputable def capRest (_ : ℕ) (ds : List RDT) : Rest C F S W ds :=
  ⟨fun _ _ w => w, _root_.Iop.Err.cap 128 (uLT C ds)⟩

/-- **hds, hbk, hextb, hcap together**, at the maker's piece, at that family. -/
theorem k9_cut_asks (putBack : List Fmt.RoundView) (i base a : ℕ) (R₁ R₂ R₃ : Rounds)
    (e : List (List ByteArray × ByteArray)) (b : Block S Cl) (l : List (Block S Cl)) (k : ℕ)
    (bk : Block S Cl) (p : K9.Where)
    (hW : WrittenAs e ((b :: l).flatMap (·.rounds)) R₁) (hk : (b :: l)[k]? = some bk)
    (hlast : k < l.length) (hr : bk.rounds = [k9Decl p])
    (hseal : roundsBefore (b :: l) k + 1 < R₁.length) :
    ∃ pc : Piece C F S Cl W,
      ((cutRow capRest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).1 ::
        (cutRow capRest putBack i base (dataOf a R₁ R₂ R₃).ds₁ b l).2)[k]? = some pc ∧
      pc.b = bk ∧ pc.ds = [k9Round p] ∧ pc.back = [] ∧ (∀ x τ w, pc.ext x τ w = w) ∧
      pc.err = _root_.Iop.Err.cap 128 (uLT C pc.ds) := by
  obtain ⟨base', h⟩ :=
    k9_cut (W := W) capRest putBack i base a R₁ R₂ R₃ e b l k bk p hW hk hlast hr hseal
  exact ⟨_, h, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩

/-! ## Which blocks declare K9's one round -/

theorem below_rounds (b : Block S Cl) : (below b).rounds = b.rounds := rfl

theorem lift_rounds {T : Type} (get : T → S) (set : T → S → T) (b : Block S Cl) :
    (b.lift get set).rounds = b.rounds := rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k9_cut_asks
#print axioms VerifiableInference.Desc.K9L.cut_piece
#print axioms VerifiableInference.Desc.K9L.data_at₁
#print axioms VerifiableInference.Desc.K9L.k9_cut
