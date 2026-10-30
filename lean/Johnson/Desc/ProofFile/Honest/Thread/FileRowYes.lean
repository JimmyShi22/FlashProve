-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileRowYes.lean: a toy example that meets the hypotheses of the
rule for a file's acceptance (Honest/Thread/FileYes.lean, `file_accepts`): at the toy example's own
description `Fy`, book `By` and prover `Hy`, at the three `Thread`s of Honest/Thread/FileRow.lean:
the acceptance is met at each of the ten sub-protocols, with no fall at all; the second chain's
start and the last test accept: so the rule's hypotheses can be met together, and it gives that the
description accepts the views of the run of `runC`. Theorems about these files' own made-up objects,
but for three general lemmas. None is one of the library's goals.

  1  general: `accepted_of_saysYes`, `accepted_of_runs`, `fallFree_noFall`
  2  the acceptance at the ten sub-protocols: `yes₁`, `yes₂`, `yes₃`
  3  `door_yes_row`, `fin_yes_row`   the second chain's start and the last test
  4  `accepts_by_threads`   the rule, applied

Limits.
  * A toy example: ten small sub-protocols; no stop, no fall, no item; the second chain's start and
    the last test ask nothing.
  * It proves that the hypotheses of `file_accepts` can be met together at one toy description,
    with no fall, no stop and no item; it proves nothing of a description of the protocol.
  * No part of the example reads what it is handed as `Seen`, so none reads the field `opened`: what
    the hypotheses here ask of that field is met for free. Of a prover with a part that reads the
    columns nothing is shown here.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `quiet_runs`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileRow
import Johnson.Desc.ProofFile.Honest.Thread.FileYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

/-! ## 1 Three general lemmas -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **`Accepted` from `SaysYes`.** A lemma on this folder's own definitions. Hypotheses: the
invariant at the border gives `A` (`hA`); where `fall b` is silent, so is `fl` (`hf`). -/
theorem accepted_of_saysYes {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} {fl : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W X → Env → Prop} (hblk : T.bs[b]? = some blk)
    (h : SaysYes T.φ Bk T.chain T.ft T.hs blk fl A)
    (hA : ∀ k s m E, Thr T b k s m E → A k s m E)
    (hf : ∀ s ds, fall b s ds = none → fl s ds = none) : Accepted T fall b := by
  intro blk' hblk' k s m E ds y cols hThr hd hst hn hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨s', n, hs⟩ := h k s m E ds l y cols (hA k s m E hThr) hd hst (hf s ds hn) hl hy hc
  have hn' : n = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hn'
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hMv, hs⟩

/-- **`Accepted` from "whatever `Step`s are prepared for the sub-protocol: it is played, read and
stepped".** A lemma on this folder's own definitions. -/
theorem accepted_of_runs {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (h : ∀ k s m E ds l, Thr T b k s m E → drawsFit blk.rounds ds = true →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
        .ok l →
      ∃ (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S), play l ds [] m = .ok y ∧
        fillCols (readsOf T.chain T.ft (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
          .ok cols ∧ blk.step T.ft s (roundsOf y.1) cols = .ok (s', cols.length)) :
    Accepted T fall b := by
  intro blk' hblk' k s m E ds y cols hThr hd _ _ hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨y', cols', s', hy', hc', hs'⟩ := h k s m E ds l hThr hd hl
  have ey : y' = y := Except.ok.inj (hy'.symm.trans hy)
  subst ey
  have ec : cols' = cols := Except.ok.inj (hc'.symm.trans hc)
  subst ec
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hMv, hs'⟩

end

/-- Where there is no fall, none fires. -/
theorem fallFree_noFall {S Cl : Type} (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn), fallFree ft bs (fun _ _ _ => none) s rs cols
  | [], _, _, _ => trivial
  | _ :: l, _, _, _ => ⟨rfl, fun s' _ _ => fallFree_noFall ft l s' _ _⟩

namespace Toy
open VerifiableInference.Desc.BlockToy (St send₃ sealB frontQ endQ)

/-! ## 2 The acceptance at the ten sub-protocols -/

/-- A sub-protocol without a round that asks nothing: played, read and stepped. -/
theorem quiet_runs {V W Pb : Type} {φ : Face V W Pb} {hs : List (Placed V W Nat)}
    {blk : Block St Nat} {chain ft : Nat} (hr : blk.rounds = [])
    (hstep : ∀ s, blk.step ft s [] [] = .ok (s, 0)) {k : Coins By} {s : St} {m : Mid W Nat}
    {E : Env} {ds : List Fmt.Drawn} {l : List (Step W Nat)}
    (hd : drawsFit blk.rounds ds = true)
    (hl : chainSteps By (By.rowsOf chain) (k.look chain) (φ.sees m.st.input) [blk] hs = .ok l) :
    ∃ (y : List Played × Mid W Nat) (cols : List OpenedColumn) (s' : St), play l ds [] m = .ok y ∧
      fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
        .ok cols ∧ blk.step ft s (roundsOf y.1) cols = .ok (s', cols.length) := by
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  refine ⟨([], m), [], s, rfl, ?_, hstep s⟩
  rw [hr]
  rfl

/-- The first chain. -/
theorem yes₁ (w : L) : Yes (T₁y w) (fun _ _ _ => none) := by
  intro b hb
  match b, hb with
  | 0, _ =>
    exact accepted_of_runs (T₁y w) (b := 0) rfl fun _ _ _ _ _ _ _ hd hl =>
      quiet_runs rfl (fun _ => rfl) hd hl
  | 1, _ =>
    refine accepted_of_runs (T₁y w) (b := 1) (blk := sealB) rfl fun k s m E ds l _ hd hl => ?_
    have el := steps_one_none (b := sealB) rfl hl
    subst el
    have hd' : drawsFit [{ entry := { name := "SEAL" } }] ds = true := hd
    obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
    refine ⟨_, [], s, rfl, rfl, ?_⟩
    exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  | n + 2, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 2 n))

/-- The shared chain. -/
theorem yes₂ (w : L₀) : Yes (T₂y w) (fun _ _ _ => none) := by
  intro b hb
  match b, hb with
  | 0, _ =>
    exact accepted_of_runs (T₂y w) (b := 0) rfl fun _ _ _ _ _ _ _ hd hl =>
      quiet_runs rfl (fun _ => rfl) hd hl
  | 1, _ =>
    exact accepted_of_saysYes (T₂y w) (b := 1) rfl (yes_of_good (good_look (pre := [])) rfl)
      (fun _ _ _ _ h => (parts₂ h).2) fun _ _ _ => rfl
  | 2, _ =>
    refine accepted_of_runs (T₂y w) (b := 2) (blk := storeY) rfl fun k s m E ds l hA hd hl => ?_
    have el := steps_one_none (b := storeY) rfl hl
    subst el
    have hd' : drawsFit storeY.rounds ds = true := hd
    obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
    obtain ⟨p, hp⟩ := one_of_length (poss_of_drawFit h₀)
    obtain ⟨el, ps, tr, dg⟩ := R
    have hp' : ps = [p] := hp
    subst hp'
    obtain ⟨u, hu, hlen⟩ := (parts₂ hA).1 (p % 2 ^ 3)
    obtain ⟨u₀, u₁, rfl⟩ : ∃ a b, u = [a, b] := by
      match u, hlen with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    refine ⟨_, [(Fmt.storedKey 0, p % 2 ^ 3, [u₀, u₁])], s, rfl, ?_, ?_⟩
    · show fillCols [⟨Fmt.storedKey 0, p % 2 ^ 3, some 0, none, none, E.stored 0 (p % 2 ^ 3), 2⟩]
        [] = _
      rw [hu]
      rfl
    · exact VerifiableInference.Desc.Block.step_ok.2
        ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
          by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  | n + 3, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 3 n))

/-- The second chain. -/
theorem yes₃ (w : L) : Yes (T₃y w) (fun _ _ _ => none) := by
  intro b hb
  match b, hb with
  | 0, _ =>
    exact accepted_of_runs (T₃y w) (b := 0) rfl fun _ _ _ _ _ _ _ hd hl =>
      quiet_runs rfl (fun _ => rfl) hd hl
  | 1, _ =>
    exact accepted_of_saysYes (T₃y w) (b := 1) rfl (yes_of_good (good_send (pre := [])) rfl)
      (fun _ _ _ _ h => (parts₃ h).2) fun _ _ _ => rfl
  | 2, _ =>
    refine accepted_of_runs (T₃y w) (b := 2) (blk := tellB) rfl fun k s m E ds l hA hd hl => ?_
    obtain ⟨y, cols, hy, hc, hs⟩ := runs_tell₃ hA hd l hl
    exact ⟨y, cols, s, hy, hc, hs⟩
  | 3, _ =>
    exact accepted_of_saysYes (T₃y w) (b := 3) rfl (yes_of_good (good_carry (pre := [])) rfl)
      (fun _ _ _ _ _ => trivial) fun _ _ _ => rfl
  | 4, _ =>
    exact accepted_of_runs (T₃y w) (b := 4) rfl fun _ _ _ _ _ _ _ hd hl =>
      quiet_runs rfl (fun _ => rfl) hd hl
  | n + 5, hb => exact absurd hb (Nat.not_lt.2 (Nat.le_add_left 5 n))

/-! ## 3 The second chain's start and the last test -/

theorem door_yes_row (w : L) (w' : L₀) (x : Nat) (k : Coins By) :
    DoorYes Fy (T₁y w) (T₂y w') x k := fun _ _ _ _ _ _ _ _ => ⟨_, rfl⟩

theorem fin_yes_row (w : L) (w' : L₀) (x : Nat) (k : Coins By) :
    FinYes Fy (T₁y w) (T₂y w') (T₃y w) x k := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-! ## 4 The rule, applied -/

/-- **The description accepts the views of the run of `runC` at the example, from the hypotheses at
the sub-protocols and the conditions where the chains begin and meet**: `file_runs` and
`file_accepts`, with every hypothesis met at the inputs of `RelY`, at all coins, at every list of
challenges that has its rounds' shapes (`Draws.due`). -/
theorem accepts_by_threads : ∀ w₀ rc x, RelY w₀ rc x → ∀ (k : Coins By) ρ', ρ'.due Fy = true →
    ∃ r, runC Fy By Hy w₀ rc x k ρ' = .ok r ∧
      Fy.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  intro w₀ rc x h k ρ' hρ
  obtain ⟨r, hr⟩ := runs_by_threads w₀ rc x h k ρ' hρ
  obtain ⟨R, hR, -, -, -⟩ := ready_row w₀ rc x k h
  refine ⟨r, hr, ?_⟩
  exact (file_accepts (sits_row R.own R.common) (by with_unfolding_all rfl) rfl (owes₁ R.own)
    (owes₂ R.common) (owes₃ R.own) (yes₁ R.own) (yes₂ R.common) (yes₃ R.own) hR hρ
    (silent_row w₀ rc x ρ') (enters₁_row hR) (enters₂_row hR) door_row
    (door_yes_row R.own R.common x k) (fin_yes_row R.own R.common x k) hr
    (fallFree_noFall _ _ _ _ _) (fallFree_noFall _ _ _ _ _)
    fun _ _ _ _ _ _ => fallFree_noFall _ _ _ _ _).2

end Toy
end ProofFile.Honest

#print axioms ProofFile.Honest.accepted_of_saysYes
#print axioms ProofFile.Honest.accepted_of_runs
#print axioms ProofFile.Honest.fallFree_noFall
#print axioms ProofFile.Honest.Toy.quiet_runs
#print axioms ProofFile.Honest.Toy.yes₁
#print axioms ProofFile.Honest.Toy.yes₂
#print axioms ProofFile.Honest.Toy.yes₃
#print axioms ProofFile.Honest.Toy.door_yes_row
#print axioms ProofFile.Honest.Toy.fin_yes_row
#print axioms ProofFile.Honest.Toy.accepts_by_threads
