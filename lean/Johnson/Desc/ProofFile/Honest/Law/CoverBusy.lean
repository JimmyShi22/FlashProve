-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverBusy.lean: one lemma that gives `DebtAt`, the bound that one
sub-protocol of a chain has to meet, in exactly the form in which the chain's lemma takes it. The
hypotheses are statements about single falls and marks, each made for all data that fit the
sub-protocol's declared rounds. No sub-protocol of the protocol is named here.

`localDebts_seated` (Honest/Law/CoverSeated.lean) takes `DebtAt` for each busy sub-protocol, at that
sub-protocol's own share of the chain's data and at numbers written as sums. `debt_join_near`
(Honest/Law/CoverNear.lean) proves `DebtAt` from statements about the falls near the sub-protocol
and the marks at its place. Whoever proves such a statement does not know the chain's data.
`kindFits_at` (Honest/Law/CoverFitAt.lean) says that the share of the data fits the declared rounds.
This lemma combines the three.

Three words. The gated sub-protocols of a chain (`bs`) are those that get a number of their own; in
the first chain these are all but the last. A fall is near a sub-protocol if it is at that
sub-protocol's place, or at the place of one of the sub-protocols without a round that follow it
directly, up to the next one that has a round (`groupOf`, Honest/Law/CoverNone.lean). Busy is
defined in Honest/Law/CoverSeated.lean; this lemma does not use it.

  1  `debt_busy`   the bound for a sub-protocol that has a gated sub-protocol after it

The hypotheses of `debt_busy`. `hfit`: the chain's data fit its declared rounds one by one
(`KindFits`, Honest/Law/Due.lean); for a description's own data this is `kindFits_first` and its two
neighbours (Honest/Law/CoverData.lean). `hM`, `hF`: the statements about the marks and about the
counted falls. `hin`: each fall of the chain's list that is near the sub-protocol has its event
inside the event of a counted fall. `hPM`, `hfront`: what the earlier challenges and the verifier's
state before the sub-protocol provide. `hp`: the numbers add up to at most the sub-protocol's
number.

Limits.
  * The lemma does not cover the last gated sub-protocol of a chain.
  * It is applied to no description here, and none of its hypotheses is proved here.
  * No number follows from them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNear
import Johnson.Desc.ProofFile.Honest.Law.CoverFitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- The bound for a sub-protocol `b` that has a gated sub-protocol `b'` after it. `A`: the gated
sub-protocols before `b`; `B`: those after `b'`; `rest`: the chain's sub-protocols after the gated
ones. -/
theorem debt_busy (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds))) {A : List (Block S Cl)}
    {b b' : Block S Cl} {B : List (Block S Cl)} (e : bs = A ++ b :: b' :: B) {ft : Nat}
    (PM : List Fmt.Drawn → Prop) (P : List Fmt.Drawn → S → Prop) (qM : Mark → ℝ≥0∞)
    (qF : Fall S → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb PM (qM mk))
    (reps : List (Fall S))
    (hF : ∀ g ∈ reps, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g ft b (b' :: B ++ rest) dsb [] P (qF g))
    (hin : ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ rest), f.place = d.place) →
      ∃ g ∈ reps, ∀ fr s' own, P fr s' → localFall [f] ft (b :: (b' :: B ++ rest)) s' own →
        localFall [g] ft (b :: (b' :: B ++ rest)) s' own)
    (hPM : ∀ fr, skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → PM fr)
    (hfront : ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' →
      z.todo = b :: (b' :: B ++ rest) ∧ z.own = [] ∧ (X (fr.take skip)).lay.firstTree = ft ∧
        P fr s')
    (hp : ((ms.filter fun m => m.place == b.place).map qM).sum + (reps.map qF).sum ≤
      p (0 + A.length)) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
      (0 + (A.flatMap (·.rounds)).length)
      ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
      (if (b' :: B).isEmpty then tail else []) (b' :: B).isEmpty := by
  have hj : bs[0 + A.length]? = some b := by
    rw [Nat.zero_add, e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hn : 0 + (A.flatMap (·.rounds)).length =
      ((bs.take (0 + A.length)).flatMap (·.rounds)).length := by
    rw [Nat.zero_add, Nat.zero_add, e, List.take_left' rfl]
  have hk := kindFits_at ds A (b' :: B) b (by rw [← e]; exact hfit)
  have ht : (if (b' :: B).isEmpty then tail else ([] : List Fmt.Drawn)) = [] := rfl
  rw [ht]
  exact debt_join_near C all fs ms skip X p bs hj hn hk.length_eq PM P qM qF
    (fun mk hmk => hM mk hmk _ hk) reps (fun g hg => hF g hg _ hk) hin hPM hfront hp

end ProofFile.Honest

#print axioms ProofFile.Honest.debt_busy
