-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RunIsDecide.lean: WHAT A BLOCK'S YES ON ITS OWN STRETCH IS, IN THE BLOCK'S OWN
WORDS; and that a stretch leaves the earlier trees as they are.

The setting. The rule of composition (Johnson/Desc/Sound/ChainRule.lean) speaks of a block through
`Piece.run`: the frame's own fold at the list that holds this one block; and through the reduction
`Piece.ior`. A kind's files know its block by the field `decide`. Whoever proves a law of a block
has to get from the first to the second.

What is said.
  `foldRun_one`: the fold at one block says yes, with the record s', IF AND ONLY IF the stretch
    shows just as many rounds as the block declares; the rounds have the declared shapes
    (`roundsFit`); the opened leaves shown are, in key, position and width, just those that the
    declared rounds read; and `decide`, at the rounds without the sealed digest and the leaves laid
    in groups, returns s'.
  `Piece.out_iff`: the same of the block's reduction at a statement and a transcript: the stage's
    own tests pass, the four clauses hold at what the verifier is shown, and the statement behind is
    the record that `decide` returns with the oracles that the stage leaves.
  `posL_self`, `sLeft_old`: where no two trees of the frame's list have one number, a
    stretch leaves the stored table, and every tree with a number below the stretch's first own
    tree, as they are.
  `ReadsBelow c rd`: a reading of statements that reads, of the oracles, the stored table and the
    trees with a number below c alone. `ReadsBelow.imp`: such a reading gives the same in front of
    and behind a stretch whose first own tree has the number c or a larger one.

Limits. Facts on the frame, general in the block. Nothing on any kind's `decide`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StageCut
import Johnson.Desc.Sound.FoldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 1 One block's yes -/

/-- What a block's yes asks of what it is shown, beside `decide`: R: the rounds; c: the opened
leaves.
-/
def Shown (ft : ℕ) (b : Block S Cl) (R : List Fmt.RoundView) (c : List OpenedColumn) : Prop :=
  R.length = b.rounds.length ∧ roundsFit b.rounds R = true ∧
    c.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf ft b.rounds (R.map (·.drawn))).flatMap id

/-- The opened leaves laid in the groups in which `decide` is handed them. -/
def groupsAt (ft : ℕ) (b : Block S Cl) (R : List Fmt.RoundView) (c : List OpenedColumn) :
    List (List (ℕ × List UInt64)) :=
  regroup ((groupsOf ft b.rounds (R.map (·.drawn))).map (·.length)) c

theorem step_ok_iff (ft : ℕ) (b : Block S Cl) (s s' : S) (R : List Fmt.RoundView) (c : List OpenedColumn) (k : ℕ) :
    b.step ft s R c = .ok (s', k) ↔
      roundsFit b.rounds R = true ∧
      (c.take k).map (fun x => (x.1, x.2.1, x.2.2.length)) =
        (groupsOf ft b.rounds (R.map (·.drawn))).flatMap id ∧
      k = ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length ∧
      b.decide s (R.map noDigest) (groupsAt ft b R (c.take k)) = .ok s' := by
  rw [Block.step_eq]
  constructor
  · intro h
    split at h
    · rename_i h1
      split at h
      · rename_i h2
        have hk := bind_pair_ok _ _ _ _ h
        subst hk
        refine ⟨h1, eq_of_beq h2, rfl, ?_⟩
        unfold groupsAt
        cases hd : b.decide s (R.map noDigest)
            (regroup ((groupsOf ft b.rounds (R.map (·.drawn))).map (·.length))
              (c.take ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length)) with
        | error e =>
          rw [hd] at h
          cases h
        | ok t =>
          rw [hd] at h
          have h' : (Except.ok (t, ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length) :
            Except String (S × ℕ)) = .ok (s', _) := h
          cases h'
          rfl
      · cases h
    · cases h
  · rintro ⟨h1, h2, rfl, h4⟩
    unfold groupsAt at h4
    rw [if_pos h1, if_pos (by rw [h2]; exact beq_self_eq_true _), h4]
    rfl

/-- **The fold at one block says yes just where the block's own four clauses hold.** -/
theorem foldRun_one (F : Frame) (name : String) (b : Block S Cl) (back : List Fmt.RoundView) (s s' : S)
    (v : Fmt.View) :
    foldRun F name [b] back s v = some s' ↔
      Shown F.ft b (v.rounds ++ back) v.opened ∧
        b.decide s ((v.rounds ++ back).map noDigest)
          (groupsAt F.ft b (v.rounds ++ back) v.opened) = .ok s' := by
  unfold foldRun
  rw [chainAt_toOption]
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
  generalize v.rounds ++ back = R
  generalize v.opened = c
  constructor
  · intro h
    by_cases hle : b.rounds.length ≤ R.length
    · have hlen : (R.take b.rounds.length).length = b.rounds.length := by
        rw [List.length_take]
        omega
      cases hs : b.step F.ft s (R.take b.rounds.length) c with
      | error e =>
        have e1 := foldBlocks_error F.ft b [] s _ (R.drop b.rounds.length) c hlen e hs
        rw [List.take_append_drop] at e1
        rw [e1] at h
        cases h
      | ok x =>
        obtain ⟨s1, k⟩ := x
        have e1 := foldBlocks_ok F.ft b [] s _ (R.drop b.rounds.length) c hlen s1 k hs
        rw [List.take_append_drop] at e1
        rw [e1] at h
        have h' : endOk (.ok (s1, R.drop b.rounds.length, c.drop k)) = some s' := h
        cases hR : R.drop b.rounds.length with
        | cons _ _ =>
          rw [hR] at h'
          cases h'
        | nil =>
          rw [hR] at h'
          cases hc : c.drop k with
          | cons _ _ =>
            rw [hc] at h'
            cases h'
          | nil =>
            rw [hc] at h'
            obtain rfl : s1 = s' := Option.some.inj h'
            have hRt : R.take b.rounds.length = R := by
              have := List.take_append_drop b.rounds.length R
              rw [hR, List.append_nil] at this
              exact this
            have hct : c.take k = c := by
              have := List.take_append_drop k c
              rw [hc, List.append_nil] at this
              exact this
            rw [hRt] at hs hlen
            obtain ⟨h1, h2, -, h4⟩ := (step_ok_iff F.ft b s s1 R c k).1 hs
            rw [hct] at h2 h4
            exact ⟨⟨hlen, h1, h2⟩, h4⟩
    · rw [foldBlocks_short F.ft b [] s R c hle] at h
      cases h
  · rintro ⟨⟨hlen, h1, h2⟩, h4⟩
    have hk : c.length = ((groupsOf F.ft b.rounds (R.map (·.drawn))).flatMap id).length := by
      rw [← h2, List.length_map]
    have hs : b.step F.ft s R c = .ok (s', c.length) :=
      (step_ok_iff F.ft b s s' R c c.length).2
        ⟨h1, by rw [List.take_length]; exact h2, hk, by rw [List.take_length]; exact h4⟩
    have e1 := foldBlocks_ok F.ft b [] s R [] c hlen s' c.length hs
    rw [List.append_nil, List.drop_length] at e1
    rw [e1]
    rfl

/-- **The block's reduction puts out just where the stage's own tests pass and the block's four
clauses hold at what the verifier is shown**; what it puts out is the record that `decide` returns,
with the oracles that the stage leaves. -/
theorem Piece.out_iff (p : Piece C F S Cl W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) :
    p.ior.red.out a τ = some a' ↔
      sTests C p.stage a.2 τ = true ∧
      Shown F.ft p.b ((sView C p.stage a.2 τ).rounds ++ p.back) (sView C p.stage a.2 τ).opened ∧
      p.b.decide a.1 (((sView C p.stage a.2 τ).rounds ++ p.back).map noDigest)
        (groupsAt F.ft p.b ((sView C p.stage a.2 τ).rounds ++ p.back)
          (sView C p.stage a.2 τ).opened) = .ok a'.1 ∧
      a'.2 = p.ior.imp a.2 τ := by
  show ((if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none).map
    fun xo => (xo, p.ior.imp a.2 τ)) = some a' ↔ _
  obtain ⟨s', y'⟩ := a'
  by_cases ht : sTests C p.stage a.2 τ = true
  · rw [if_pos ht, Option.map_eq_some_iff]
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨h1, h2⟩ := (foldRun_one F p.b.name p.b p.back a.1 x _).1 hx
      exact ⟨ht, h1, h2, rfl⟩
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨s', (foldRun_one F p.b.name p.b p.back a.1 s' _).2 ⟨h1, h2⟩,
        congrArg (Prod.mk s') (show y' = _ from h3).symm⟩
  · rw [if_neg ht]
    constructor
    · intro h
      cases h
    · rintro ⟨h, -⟩
      exact absurd h ht

/-! ## 2 A stretch leaves the earlier trees as they are -/

/-- Where no two trees of a list have one number, `posL` finds each position at its own tree's
number and its own leaf. -/
theorem posL_self (L : List LeftT) (hnd : (L.map (·.no)).Nodup) (p : PosL L) :
    posL L (L.get p.1).no p.2.val = some p := by
  obtain ⟨q, hq⟩ := posL_isSome L _ _ (L.get p.1) (List.get_mem L p.1) rfl p.2.isLt
  obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hq
  have hg : L.get q.1 = L.get p.1 :=
    List.inj_on_of_nodup_map hnd (List.get_mem L q.1) (List.get_mem L p.1) h1
  have hi : q.1 = p.1 := (List.nodup_iff_injective_get.1 hnd.of_map) hg
  rw [hq]
  obtain ⟨qi, qx⟩ := q
  obtain ⟨pi, px⟩ := p
  obtain rfl : qi = pi := hi
  obtain rfl : qx = px := Fin.ext h2
  rfl

/-- **A stretch leaves a tree with a number below its first own tree's as it is.** -/
theorem sLeft_old (hnd : (F.all.map (·.no)).Nodup) (xs : List RDT) (c : ℕ) (y : F.E.Str)
    (τ : Iop.Tr (uLT C xs)) (p : PosL F.all) (h : (F.all.get p.1).no < c) :
    sLeft C (stg F c xs) y τ p = y.2 p := by
  show (sCol C (stg F c xs) y τ (.tree (F.all.get p.1).no p.2.val)).getD [] = _
  rw [sCol_eq, if_pos h, posL_self F.all hnd p]
  rfl

/-- A reading of statements that reads, of the oracles, the stored table and the trees with a number
below c alone. -/
def ReadsBelow {α : Type} (c : ℕ) (rd : S × F.E.Str → α) : Prop :=
  ∀ (s : S) (y y' : F.E.Str), y.1 = y'.1 →
    (∀ p : PosL F.all, (F.all.get p.1).no < c → y.2 p = y'.2 p) → rd (s, y) = rd (s, y')

/-- Such a reading gives the same at the oracles in front of and behind a stretch whose first own
tree has the number c or a larger one. -/
theorem ReadsBelow.imp {α : Type} {c : ℕ} {rd : S × F.E.Str → α} (h : ReadsBelow c rd)
    (hnd : (F.all.map (·.no)).Nodup) (p : Piece C F S Cl W) (hc : c ≤ p.base) (s : S) (y : F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) : rd (s, p.ior.imp y τ) = rd (s, y) :=
  h s _ _ rfl fun q hq => sLeft_old hnd p.ds p.base y τ q (Nat.lt_of_lt_of_le hq hc)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.step_ok_iff
#print axioms VerifiableInference.Desc.Sound.foldRun_one
#print axioms VerifiableInference.Desc.Sound.Piece.out_iff
#print axioms VerifiableInference.Desc.Sound.posL_self
#print axioms VerifiableInference.Desc.Sound.sLeft_old
#print axioms VerifiableInference.Desc.Sound.ReadsBelow.imp
