-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDotItem.lean: the item (Dot) at the last thread's start, at the library's filling of the
letter: `dotI` (Johnson/Desc/Third/Law/Row0DotOm.lean), the shared chain's words read off the second
half of the last witness.

Why. `door_items` (E2E/KeyDoorPairs.lean) leaves (Dot) as the premise `hdot`. The library's `dot_at`
(Johnson/Desc/K14/Honest/ItemsHold.lean) has (Dot)'s equation at the honest words, at a number and
a point of its own. This file says what joins the two.

Main names.
  `dot_omega`: `DotOmAt` at a state of the shared chain, from `dot_at` and three equations on that
    state: Omega's number, the codes, the point; and the words at that number.
  `words_at_two`: the words that the last witness holds at number 2 are the honest words there.
  `dotFill`: a meaning whose (Dot) is `dotI`.
  `dot_item`: the item, at the last witness, under the premises named.

Premises that stay. `hnum`, `hcodes`, `hpsi`: the three equations on the state. `hpt`: the point's
length. `hV`: the half on W (`VIs`), at the letters `g`, `wv`. `hP`: the plan's facts; `two`: number 2 is
of `Ours`.

What stays open. `g` and `wv` are letters: which weights and which reader of W are meant is not laid
here. Nothing here reads a run. The three equations at the state where the shared chain ends are
`end_at_key` and `codes_at_key` (E2E/KeyEndAtKey.lean), wherever the thread stands there.

NOT IN FRONT OF A LAW OVER COINS: `dot_omega` and `dot_item` bear this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `hV` reads the hidden matrix through
`H.Rw`, of the second kind, and ties `g`, `wv` where `H` and the words move with a run's coins, of the
first kind too. None
of these is the term that the committer makes. None: the bar is flat. `words_at_two` keeps the letter
`holds`; `dotFill` is a definition.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyDoorItems
import Johnson.Desc.K14.Honest.ItemsHold
import Johnson.Desc.K14.Law.PointGood
import Johnson.Desc.Third.Law.Row0DotOm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyDotItem
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (rdE GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Shared (MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.Third.Law (dotI)
open _root_.Desc.K14 (St P14 first drawn)
open _root_.Desc.K14.Law (DotEq DotOmAt VIs omegaOf)
open _root_.Desc.K14.Honest (PlanFacts Inputs omegaAt words2 dot_at)

/-- **(Dot)'s equation at a state of the shared chain**, from `dot_at`, at a first state with no
message, where the state's number, codes and point are the honest ones and the words at that number
are the honest words.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem dot_omega {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hP : PlanFacts P.par P.codes sentU layO) (key : TableKey) (e : St) (r1 : Fmt.RoundView) (H : Inputs)
    (hpt : (drawn r1).length = P.par.S.kCol) (g W : Nat → GE) (hV : VIs P.par.S g H.Rw W)
    (hnum : e.loc.oOmega = 2) (hcodes : e.st.codes = P.codes) (hpsi : e.loc.psiSh = drawn r1)
    (m : Words GE)
    (hm : ∀ part i, m 2 part i = words2 P sentU (first P.codes key) r1 H 2 part i) :
    DotOmAt P.par.S g e m W := by
  have h := dot_at hP (first P.codes key) r1 H hpt g W hV
  have e1 : omegaOf e.loc (linLayOmega e.st.codes P.par.S) m =
      omegaAt P (first P.codes key) (words2 P sentU (first P.codes key) r1 H) := by
    funext y
    show m e.loc.oOmega .main ((linLayOmega e.st.codes P.par.S).index y) =
      words2 P sentU (first P.codes key) r1 H (0 + 2) .main ((linLayOmega P.codes P.par.S).index y)
    rw [hnum, hcodes, hm]
  unfold DotOmAt
  rw [e1, hpsi]
  exact h

section
variable {Bk : ProverCoinCounts} {W₀ Rc Wt : Type}

/-- **The honest words stand at number 2 of the shared thread's witness.** -/
theorem words_at_two (ℓ : WitLens Wt) (Q : P14) (sentU : Array OracleNotice)
    (two : Ours Q sentU 2) (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) (part : OnBytes.Part) (i : Nat) :
    ℓ.get (witL ℓ Q sentU holds rest k w h) 2 part i =
      words2 Q sentU (first Q.codes w.key) (firstRv h) (holds k w) 2 part i := by
  rw [get_witL]
  unfold witAll
  exact words2_ours Q sentU _ _ _ _ 2 two part i

end

/-- A meaning whose (Dot) is the library's filling, at words read off the second half. -/
def dotFill {Wt₁ : Type} (S : LinShape) (g : Xi × FirstState → Nat → GE)
    (wv : Xi × FirstState → Wt₁ × Words GE → Nat → GE)
    (D : MeaningS St (Xi × FirstState) (Wt₁ × Words GE)) :
    MeaningS St (Xi × FirstState) (Wt₁ × Words GE) :=
  { D with dot := dotI S g (fun _ u => u.2) wv }

/-- **The item (Dot)** at a pair whose second half holds the honest words at number 2.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem dot_item {Wt₁ : Type} {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hP : PlanFacts P.par P.codes sentU layO) (key : TableKey) (e : St) (r1 : Fmt.RoundView) (H : Inputs)
    (hpt : (drawn r1).length = P.par.S.kCol) (g : Xi × FirstState → Nat → GE)
    (wv : Xi × FirstState → Wt₁ × Words GE → Nat → GE)
    (D : MeaningS St (Xi × FirstState) (Wt₁ × Words GE)) (p : Xi × FirstState) (y : Strs)
    (u : Wt₁ × Words GE) (hV : VIs P.par.S (g p) H.Rw (wv p u))
    (hnum : e.loc.oOmega = 2) (hcodes : e.st.codes = P.codes) (hpsi : e.loc.psiSh = drawn r1)
    (hm : ∀ part i, u.2 2 part i = words2 P sentU (first P.codes key) r1 H 2 part i) :
    (dotFill P.par.S g wv D).dot p e y u :=
  dot_omega hP key e r1 H hpt (g p) (wv p u) hV hnum hcodes hpsi u.2 hm

end AtPublicFiles.KeyDotItem

#print axioms AtPublicFiles.KeyDotItem.dot_omega
#print axioms AtPublicFiles.KeyDotItem.words_at_two
#print axioms AtPublicFiles.KeyDotItem.dot_item
