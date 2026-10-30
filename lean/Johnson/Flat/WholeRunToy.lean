-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WholeRunToy.lean: a control of Johnson/Flat/WholeRun.lean: the law `RunMeets` is met at
a file with a round that has proof of work, by a run that says yes somewhere, at a typed protocol
that is sound with a count below the number of its verifier's messages.

Why. A theorem from hypotheses says nothing if they can never be met together. A chain's view does
not show a round's bits of proof of work, so this law's first test is a round that has some.

The toy. One written round, in the first chain: the prover sends one word; one bit of proof of work;
the verifier draws one position below 2. The two other chains are empty. The typed protocol has one
round: the prover sends a number, the verifier draws the format's typed values of that round, and
accepts if the position drawn is the number sent: the prover has to guess. Its language is empty: no
statement is true, so soundness bounds the prover's luck at every statement.

Definitions, statements and proofs.
  `toyD`, `toyR`, `toyM`: the file's data; the typed round; the maps (the word's value; the typed
    values as they are).
  `toyAcc`: the typed decision. `toyRun`: the decision on the three views: the first view has one
    round, which sent one word, and drew one position, the word's value.
  `toy_meets`: `RunMeets` there.
  `toyTr u b w`: a transcript: hash blocks u, the bit of work b, the word w. `toy_out`: what the
    file's verifier says there. `toy_poss`: the position that a view shows is the one that the
    blocks give.
  `toy_yes`: the file's verifier says yes at all hash blocks, where the bit of work is 0 and the
    word is the position drawn.
  `toy_no`, `toy_views`: with the bit of work turned it says no, though a view shows the same
    rounds: so the law, which stands under the verifier's yes, asks nothing there.
  `toy_typed_sound`, `toy_card`: the typed protocol is round-by-round sound for the empty language
    at the count 1: whatever the prover sends, at most one of the 2 verifier's messages lets it win.
  `toy_sound`: so the file's protocol is sound: `wholeRun_sound` with every premise paid.
  `toy_below`: the written counts are shares of at most 1/2: by the rule `below_whole_pow`,
    from two comparisons of natural numbers (`toy_heldN`).
  `toy_rule_needs_work`: the rule's second comparison holds there through its factor 2 ^ work alone:
    with that factor left out it fails at every choice of the rule's two numbers.

Does not show: anything on a file of the format. That the bound 1/2 itself fails at a round without
work: `toy_rule_needs_work` is on the rule's premise, not on the counts: so this toy is no ground
for "with the work counted" beyond that rule. `keySound_of_runMeets` has no control here: no
`filesOf`, no shared chain's count. No tree is sent and nothing is opened: the law's side on opened
columns is not controlled. One chain alone has a round, and no round inside a chain is skipped. The
typed values are taken as they are: no field element. The instance, the stored table, the language's
translation and the three silent rounds are idle.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WholeRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.WholeRunToy
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice OnBytes.Flat

/-- The written round's entry: one bit of work, one position below 2. -/
def toyE : Fmt.Entry := { name := "guess", work := 1, poss := 1, logN := 1 }

/-- The written round: it sends one word and no tree, and opens nothing. -/
def toyRD : RDT := { entry := toyE, kind := .positions, items := [.word], trees := [], opens := [],
                     stored := [] }

/-- The file's data: that one round in the first chain. -/
def toyD : WholeD := ⟨0, [toyRD], [], [], id, id, id⟩

/-- The round's draws. -/
theorem toy_ds : Fmt.dsOf toyE .positions = [.pos 1, .trits 0] := rfl

/-- The typed round: a number; the format's typed values of the written round. -/
def toyR : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := ℕ
  Chal := Vals .two (Fmt.dsOf toyRD.entry toyRD.kind)
  dOrc := ()
  dPlain := 0

/-- How the written round is read: the word's value; the typed values as they are. -/
def toyRM : RMap toyRD toyR :=
  ⟨fun m => ((), (GPlain.old (W := ℕ) (b := 1) (P := UInt64 × Unit) m.2).1.toNat), id⟩

/-- The first chain's maps. -/
def toyM : Maps toyD.ds₁ [toyR] := .step toyRM .nil

theorem toyM_ok : toyM.OK := ⟨⟨fun _ _ h => h, by decide⟩, trivial⟩

/-- The typed decision: the position drawn is the number sent. -/
def toyAcc (_ : Unit) (_ : (oneExternalString (2 ^ toyD.a) SgX).Str) (τ : Tr ([toyR] ++ ([] ++ []))) : Bool :=
  possV (Fmt.dsOf toyRD.entry toyRD.kind) τ.2.1 == [τ.1.2]

/-- The decision on the three views: yes, if the first view has one round, which sent one word and
drew one position, and the position is the word's value. -/
def toyRun (_ : Unit) (v₁ _ _ : View) : Bool :=
  match v₁.rounds with
  | [rv] =>
    match rv.vals with
    | [.word w] => rv.drawn.poss == [w.toNat]
    | _ => false
  | _ => false

/-- The silent rounds send nothing that is tested. -/
def toySil (_ : Unit) (_ _ _ : Unit) : Bool := true

/-- **The law holds at the toy.** -/
theorem toy_meets :
    RunMeets toyD () () () toyM .nil .nil toySil toyRun id id toyAcc := by
  intro x y τ h
  have h2 := (Option.ite_none_right_eq_some.1 h).1
  simp only [Bool.and_eq_true] at h2
  have hr := h2.2
  obtain ⟨mF, cF, ⟨o, pl⟩, c, rest⟩ := τ
  have hr' : (((ckP .two).dr toyRD.entry toyRD.kind (GChal.old (b := 1) c)).poss ==
      [(GPlain.old (W := ℕ) (b := 1) (P := UInt64 × Unit) pl).1.toNat]) = true := hr
  show (possV (Fmt.dsOf toyRD.entry toyRD.kind) (valsOf (toRD toyRD) c) ==
      [(GPlain.old (W := ℕ) (b := 1) (P := UInt64 × Unit) pl).1.toNat]) = true
  rw [← collect_poss]
  exact hr'

/-- The word whose value is a position below 2. -/
def toyW (i : Fin (2 ^ 1)) : UInt64 := if i.val = 0 then 0 else 1

theorem toyW_toNat (i : Fin (2 ^ 1)) : (toyW i).toNat = i.val := by
  revert i
  decide

/-- A transcript of the file: hash blocks u, the bit of work b, the word w. -/
def toyTr (u : Fin (bsRound .two toyE .positions).b → Dig 256) (b : Bool) (w : UInt64) :
    Tr (chainsOf (ckP .two) toyD () () ()).sh :=
  (((), ()), (), ((zeroT [], ((w, ()), 0)), (u, fun _ => b), (((), ()), (), (((), ()), (), ()))))

/-- What the file's verifier says there: the bit of work is 0, and the position drawn is the word's
value. -/
theorem toy_out (y : (oneExternalString (2 ^ toyD.a) SgX).Str)
    (u : Fin (bsRound .two toyE .positions).b → Dig 256) (b : Bool) (w : UInt64) :
    (reductionOfWholeFile (ckP .two) toyD () () () toySil toyRun).out () y (toyTr u b w) =
      if (GChal.pass (b := 1) (C := Fin (bsRound .two toyE .positions).b → Dig 256)
          (u, fun _ => b) && true && true && true && true && true && true && true && true &&
          (((ckP .two).dr toyE .positions u).poss == [w.toNat])) = true
      then some () else none := rfl

/-- The position that hash blocks give is the one that the view shows. -/
theorem toy_poss (u : Fin (bsRound .two toyE .positions).b → Dig 256) :
    ((ckP .two).dr toyE .positions u).poss = [((bsRound .two toyE .positions).φ u).1.val] := by
  show (Fmt.collect (outAll .two (Fmt.dsOf toyE .positions)
    ((bsRound .two toyE .positions).φ u))).poss = _
  rw [collect_poss]
  rfl

/-- **The file's verifier says yes somewhere**: at all hash blocks, where the bit of work is 0 and
the word is the position drawn. -/
theorem toy_yes (y : (oneExternalString (2 ^ toyD.a) SgX).Str)
    (u : Fin (bsRound .two toyE .positions).b → Dig 256) :
    (reductionOfWholeFile (ckP .two) toyD () () () toySil toyRun).out () y
      (toyTr u false (toyW ((bsRound .two toyE .positions).φ u).1)) = some () := by
  rw [toy_out, toy_poss, toyW_toNat]
  have hp : GChal.pass (b := 1) (C := Fin (bsRound .two toyE .positions).b → Dig 256)
      (u, fun _ => false) = true := GChal.pass_zero 1 u
  rw [hp, beq_self_eq_true]
  rfl

/-- **With the bit of work turned it says no**, at the same blocks and the same word. -/
theorem toy_no (y : (oneExternalString (2 ^ toyD.a) SgX).Str)
    (u : Fin (bsRound .two toyE .positions).b → Dig 256) (w : UInt64) :
    (reductionOfWholeFile (ckP .two) toyD () () () toySil toyRun).out () y (toyTr u true w) = none := rfl

/-- A view shows the same rounds, whatever the bit of work is. -/
theorem toy_views (u : Fin (bsRound .two toyE .positions).b → Dig 256) (w : UInt64) :
    rvT (ckP .two) toyD.ds₁ ((chainsOf (ckP .two) toyD () () ()).tr₁ (toyTr u true w)) =
      rvT (ckP .two) toyD.ds₁ ((chainsOf (ckP .two) toyD () () ()).tr₁ (toyTr u false w)) := rfl

/-- **The typed protocol is sound for the empty language at the count 1.** -/
theorem toy_typed_sound :
    (⟨[toyR] ++ ([] ++ []), fun _ => true, fun _ _ => ∅, fun _ _ _ => ∅, toyAcc⟩ :
      InteractiveOracleProof Unit (oneExternalString (2 ^ toyD.a) SgX)).Sound (fun _ _ => False)
      (Err.app ((1, ()) : Err [toyR]) (Err.app (() : Err []) (() : Err []))) := by
  intro x y _ m
  show cnt (fun c : Vals .two (Fmt.dsOf toyRD.entry toyRD.kind) =>
    ¬ (toyAcc x y (m, c, ()) = false)) ≤ 1
  unfold cnt
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ?_⟩
  have ha : possV (Fmt.dsOf toyRD.entry toyRD.kind) a.1 = [m.2] := by
    have := a.2
    simpa [toyAcc] using this
  have hb : possV (Fmt.dsOf toyRD.entry toyRD.kind) b.1 = [m.2] := by
    have := b.2
    simpa [toyAcc] using this
  exact vals_inj _ (show PlainDraws [.pos 1, .trits 0] from ⟨rfl, trivial⟩) a.1 b.1 rfl
    (ha.trans hb.symm)

/-- The typed round has 2 verifier's messages. -/
theorem toy_card : Nat.card toyR.Chal = 2 :=
  (card_vals_all (Fmt.dsOf toyRD.entry toyRD.kind)).trans rfl

/-- **The file's protocol is sound**: `wholeRun_sound` with every premise paid. -/
theorem toy_sound :
    (reductionOfWholeFile (ckP .two) toyD () () () toySil toyRun).toInteractiveOracleProof.Sound (fun _ _ => False)
      (wholeErr toyD () () () toyM .nil .nil ((1, ()) : Err [toyR]) () ()) :=
  wholeRun_sound toyD () () () toyM .nil .nil toySil toyRun id id toyAcc toy_meets (fun _ => true)
    (fun _ _ => ∅) (fun _ _ _ => ∅) toyM_ok trivial trivial ((1, ()) : Err [toyR]) () ()
    (fun _ _ => False) (fun _ _ => False) (fun _ _ h => h) toy_typed_sound

/-- The two comparisons of natural numbers at the one step: the typed share is 1/2; with the
sampler's bias and one bit of work it is at most 1/2. -/
theorem toy_heldN : toyM.HeldN 1 ((1, ()) : Err [toyR]) :=
  ⟨⟨1, 2, by decide, by decide, by decide⟩, trivial⟩

/-- **The written counts are shares of at most 1/2.** -/
theorem toy_below :
    Err.Below (wholeErr toyD () () () toyM .nil .nil ((1, ()) : Err [toyR]) () ())
      ((2 : ENNReal)⁻¹ ^ 1) :=
  below_whole_pow toyD () () () (M₁ := toyM) (M₂ := .nil) (M₃ := .nil) toyM_ok trivial trivial
    toy_heldN trivial trivial

/-- **The rule's second comparison needs the bit of work**: with the factor 2 ^ work left out it
fails, whatever the two numbers n, D with 0 < D (`hD`) that meet the first comparison (`h1`). -/
theorem toy_rule_needs_work (n D : ℕ) (hD : 0 < D) (h1 : 1 * D ≤ n * 2) :
    ¬ ((2 ^ 128 + 1) ^ (bsRound .two toyE .positions).b * n * 2 ^ 1 ≤
      (2 ^ 128) ^ (bsRound .two toyE .positions).b * D) := by
  intro h
  have hb : (bsRound .two toyE .positions).b ≠ 0 := by decide
  have hlt : (2 ^ 128) ^ (bsRound .two toyE .positions).b <
      (2 ^ 128 + 1) ^ (bsRound .two toyE .positions).b :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self _) hb
  have hn : 0 < n * 2 := by omega
  have a1 : (2 ^ 128) ^ (bsRound .two toyE .positions).b * D ≤
      (2 ^ 128) ^ (bsRound .two toyE .positions).b * (n * 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have a2 : (2 ^ 128) ^ (bsRound .two toyE .positions).b * (n * 2) <
      (2 ^ 128 + 1) ^ (bsRound .two toyE .positions).b * (n * 2) :=
    Nat.mul_lt_mul_of_pos_right hlt hn
  have a3 : (2 ^ 128 + 1) ^ (bsRound .two toyE .positions).b * n * 2 ^ 1 =
      (2 ^ 128 + 1) ^ (bsRound .two toyE .positions).b * (n * 2) := by
    rw [pow_one, Nat.mul_assoc]
  rw [a3] at h
  exact absurd (lt_of_lt_of_le a2 h) (not_lt.2 a1)

end OnBytes.Flat.WholeRunToy

#print axioms OnBytes.Flat.WholeRunToy.toy_meets
#print axioms OnBytes.Flat.WholeRunToy.toy_yes
#print axioms OnBytes.Flat.WholeRunToy.toy_no
#print axioms OnBytes.Flat.WholeRunToy.toy_views
#print axioms OnBytes.Flat.WholeRunToy.toy_card
#print axioms OnBytes.Flat.WholeRunToy.toy_sound
#print axioms OnBytes.Flat.WholeRunToy.toy_below
#print axioms OnBytes.Flat.WholeRunToy.toy_rule_needs_work
