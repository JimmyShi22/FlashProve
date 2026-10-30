-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BasePart.lean: the last part of the proximity test's block (`baseJ5`,
Johnson/Desc/K12/JoinGuarded.lean) says yes, from eight public clauses on the record in front, a yes of
`baseDecide` and the columns' places; with three small things beside
Johnson/Prover/Link/Base.lean.

Main names (namespace `Johnson.Prover.Link`).
  `BaseFront p j cur t row L c cl m star a`   what the part asks of the record in front, guard by
      guard: what is handed on is a claim · the stage is in the plan · the claim can be written
      out · its form fits · the last group has one member m · the masking message star has come ·
      the codes and the two messages are the place's, star unspent · the two stand alone in the
      declared tree a, unopened
  `baseJ5_yes`   `BaseFront` · `baseDecide` returns the claim · the columns stand at the list of the
      drawn positions: then the part returns the record with star spent, the tree a counted as
      opened, nothing handed on and no mask
  `ranged_yes`   guard (z) in front of a part: where every drawn position is in its round's range
      the guarded part decides as the part
  `find_of_list`   a group of columns that stands at the list of the drawn positions has a column
      at each drawn position, found by `find?`
  `baseDecide_cols`   `baseDecide_written` with its premise on `find?` paid so
  `lt_words12`   the twelve words of a written column are below the prime
  `baseChecks_turned`   a test that can fail: with another element in the first round, all else as
      an honest prover writes it, `baseChecks` = false

Limits. `BaseFront` is asked, not shown here: `baseFront_behind`
(Johnson/Prover/Link/BaseBehindSwitch.lean) has it behind the last switch, under its own premises.
Nothing above the part: the row of parts, `Block.step`'s
tests on form, the tie of the columns to a written oracle. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.Base
import Johnson.Desc.K12.JoinGuarded
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12

/-- What the last part asks of the record in front. -/
structure BaseFront (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (cl : BaseClaim) (m star a : ℕ) : Prop where
  pass : t.pass = .claim row L
  stage : stageAt p j cur = some c
  claim : claimAt t.st.codes c row = some cl
  fits : ((t.st.codes.base[c.code]?).any fun k =>
    Own.formFits (row.c.fixLow [zeroE]) (ceilLog2 k.ell)) = true
  member : lastMember L = some m
  mask : t.mask = some star
  pair : lastPairOk (basePar p cur) t.st c m star = true
  tree : lastTree (basePar p cur) t.book m star = some a

/-- **The last part says yes.** -/
theorem baseJ5_yes (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (d₁ d₂ : Fmt.DeclaredRound) (t : T12)
    (row : GroupRow) (L : GroupLayout) (c : IoppStage) (cl : BaseClaim) (m star a : ℕ)
    (rL rB : Fmt.RoundView) (g : List (ℕ × List UInt64))
    (hF : BaseFront p j cur t row L c cl m star a)
    (hD : baseDecide (basePar p cur) cl [rL, rB] [g] = .ok cl)
    (hg : g.map (·.1) = Fmt.listOf rB.drawn.poss) :
    (baseJ5 p j cur [d₁, d₂]).decide t [rL, rB] [g] = .ok { t with
      st :=
        { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
      book :=
        { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
      pass := .nothing, mask := none } := by
  unfold baseJ5
  simp only [hF.pass, hF.stage, hF.claim, hF.fits, hD, hg, hF.member, hF.mask, hF.pair, hF.tree,
    named, need, beq_self_eq_true, if_true, bind, Except.bind, pure, Except.pure]

/-- Guard (z): in range, the guarded part decides as the part. -/
theorem ranged_yes (cut : List Fmt.DeclaredRound) (X : K12.Part T12) (t : T12) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : inRange cut rs = true) :
    (ranged cut X).decide t rs gs = X.decide t rs gs := by
  unfold ranged
  simp only [h, need, if_true, bind, Except.bind]

/-- A group that stands at the list of the drawn positions has a column at each of them. -/
theorem find_of_list (g : List (ℕ × List UInt64)) (poss : List ℕ)
    (hg : g.map (·.1) = Fmt.listOf poss) (x : ℕ) (hx : x ∈ poss) :
    ∃ y, g.find? (·.1 == x) = some y ∧ y ∈ g ∧ y.1 = x := by
  have hm : x ∈ g.map (·.1) := by
    rw [hg]
    exact (Fmt.listOf_mem poss x).2 hx
  obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
  cases hf : g.find? (·.1 == x) with
  | none =>
    have := List.find?_eq_none.1 hf z hz
    rw [e] at this
    exact absurd (beq_self_eq_true x) this
  | some y =>
    exact ⟨y, rfl, List.mem_of_find?_eq_some hf, by
      have := List.find?_some hf
      exact eq_of_beq this⟩

/-- **The decision returns the claim**, at a group that stands at the list of the drawn positions
and holds, at each of its places, the written column. -/
theorem baseDecide_cols (P : BasePar) (s : BaseClaim) (rL rB : Fmt.RoundView)
    (g : List (ℕ × List UInt64)) (lam : Fmt.M1.E) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE)
    (hc : s.c.size = P.C.l) (hd : s.d.size = P.Z.l)
    (hcl : formG P.C.l s.c m0 + formG P.Z.l s.d m1 = toE s.tau)
    (hL : rL.vals = [Fmt.ItemValue.e (tauSW P.C P.Z s.c s.d h0 h1)]) (hlam : rL.drawn.elems = [lam])
    (hB : rB.vals = (shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).map Fmt.ItemValue.e)
    (hg : g.map (·.1) = Fmt.listOf rB.drawn.poss)
    (hw : ∀ y ∈ g, y.2 = words12 (baseColW P.C P.Z m0 r0 m1 r1 h0 s0 h1 s1 y.1)) :
    baseDecide P s [rL, rB] [g] = .ok s :=
  baseDecide_written P s rL rB g lam m0 r0 m1 r1 h0 s0 h1 s1 hc hd hcl hL hlam hB fun x hx => by
    obtain ⟨y, hy, hm, e⟩ := find_of_list g _ hg x hx
    exact ⟨y, hy, by rw [hw y hm, e]⟩

/-- A written word is below the prime. -/
theorem lt_ofF (x : Cb.Gl.F) : ofF x < fieldPrimeWord := by
  have h := ok_ofF x
  unfold Fmt.Fld.ok at h
  rw [UInt64.lt_iff_toNat_lt, show fieldPrimeWord.toNat = Fmt.Fld.two.p by decide]
  exact of_decide_eq_true h

/-- The twelve words of a written column are below the prime. -/
theorem lt_words12 (C Z : Fmt.M1.Code) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) (x : ℕ) :
    ∀ w ∈ words12 (baseColW C Z m0 r0 m1 r1 h0 s0 h1 s1 x), w < fieldPrimeWord := by
  intro w hw
  simp only [words12, baseColW, ofE, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> exact lt_ofF _

/-- **A test that can fail**: another element in the first round, all else as written: no. -/
theorem baseChecks_turned (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (tau lam tauS : Fmt.M1.E)
    (xs : List ℕ) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE)
    (hcl : formG C.l c m0 + formG Z.l d m1 = toE tau)
    (hne : toE tauS ≠ formG C.l c h0 + formG Z.l d h1) :
    baseChecks C Z c d tau tauS lam
      (wr C.l fun j => h0 j + toE lam * m0 j) (wr Z.l fun j => h1 j + toE lam * m1 j)
      (wr C.r fun q => s0 q + toE lam * r0 q) (wr Z.r fun q => s1 q + toE lam * r1 q) xs
      (fun x => some (baseColW C Z m0 r0 m1 r1 h0 s0 h1 s1 x)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [baseChecks_eq, baseOK_iff_parts] at h
  have e1 := (baseB1_iff c d tau tauS lam _ _ C.l Z.l (le_of_eq (length_wr _ _))
    (le_of_eq (length_wr _ _))).1 h.2.1
  have e2 : formG C.l c (lst (wr C.l fun j => h0 j + toE lam * m0 j)) +
      formG Z.l d (lst (wr Z.l fun j => h1 j + toE lam * m1 j)) =
      toE tauS + toE lam * toE tau := e1
  rw [formG_congr C.l c _ _ (fun j hj => lst_wr _ _ j hj),
    formG_congr Z.l d _ _ (fun j hj => lst_wr _ _ j hj), formG_line, formG_line, ← hcl] at e2
  apply hne
  have e3 : formG C.l c h0 + formG Z.l d h1 +
      toE lam * (formG C.l c m0 + formG Z.l d m1) =
      toE tauS + toE lam * (formG C.l c m0 + formG Z.l d m1) := by
    rw [← e2]
    ring
  exact (add_right_cancel e3).symm

end Johnson.Prover.Link
