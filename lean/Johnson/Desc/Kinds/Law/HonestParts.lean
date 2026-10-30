-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HonestParts.lean.
WHAT IT DOES NOT SHOW. All that Law/HonestHear.lean says it does not show: that a kind's own
summand, start form and end term meet what is asked; that the verifier's ledger is Fresh; what the
prover's program sends. Nothing on soundness, on probabilities or on hiding.
WHAT IT IS. heardBy_honest (Law/HonestHear.lean) at HeadParts.lean's two callers. Both
hand on Shaped, against their own tables of rounds.
  publicPart_claimed   behind the laying of one scalar c0 the one slot's form has the public part
                       tgt c0: so a sumcheck's start form asks no premise.
  sumcheck_honest      "sumcheck z n": the claimed sum's shown scalar c0 is a letter.
  level_honest         "level z start": the start form's public part T in front is a premise; the
                       last round LINE draws the given element.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HonestHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open Came (bind_eq)
open OnBytes.Desc.First.P1 (Chain honest hid psiProd)
open Part.MaskedSum (Var Call Ends readAll leadScalars ownSlots movesOf rowForm challenges rvOf
  shown_returns)

theorem hidOf_one (j : Nat) (c0 : E) :
    (hidOf j [c0]).getD 0 {} = { var := Aff.slot (j + 0), shown := c0 } := by
  simp [hidOf]

/-- Behind the laying of one scalar the one slot's form has a public part. -/
theorem publicPart_claimed {F : Fork} {m : Nat} (hW : WellLaid F) (c0 : E)
    (hF : Fresh F ([c0].length + m)) (Fa : Fork)
    (h : hide [c0] F [] = some (hidOf F.next [c0], Fa, [])) :
    Fa.publicPart ((hidOf F.next [c0]).getD 0 {}).var = some (tgt c0) := by
  obtain ⟨run, _⟩ := hide_unfold h
  obtain ⟨_, _, _, w4, _⟩ := hideRun_frame
    (F := ({ F with next := F.next + [c0].length } : Fork)) hW run
  obtain ⟨G, g0, _, g2, _, g4⟩ := hide_returns [c0] hF []
  have hG : G = Fa := by
    rw [h] at g0
    simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and] at g0
    exact g0.symm
  subst hG
  have hlt : F.next < G.ns := by
    rw [g2]
    have := hF.1
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hs : G.shown (F.next + 0) = some c0 := by
    rw [Nat.add_zero, shown_returns hlt (by
      rw [g4, if_pos ⟨le_refl _, by simp⟩]), w4, if_pos ⟨le_refl _, by simp⟩]
    simp
  rw [hidOf_one]
  show ((G.shown (F.next + 0)).map fun y => addE zeroE (mulE oneE y)).bind pure = some (tgt c0)
  rw [hs]
  rfl

/-- **THE HONEST ROUNDS OF "sumcheck z n".** -/
theorem sumcheck_honest (z : Point) {n : Nat} (hn : 1 ≤ n) {F : Fork} {m : Nat} (hW : WellLaid F)
    (c0 : E) (hF : Fresh F ([c0].length + (ownSlots (callOf 1 z n).all + n + m)))
    (hcoef : ℕ → K) (S : List K → K) (sigma muT : K) (tq : K → List K → K[X])
    (hCh : ∀ (eps : K) (rs : List K),
      rs.length = ((callOf 1 z n).all.map (Var.wt Reading.gl)).length →
      Chain ((callOf 1 z n).all.map (Var.wt Reading.gl)) (honest (tq eps) [] rs)
        (muT + eps * Reading.gl.val (tgt c0))
        (hid ((callOf 1 z n).all.map (Var.wt Reading.gl)) hcoef rs + eps * S rs +
          eps * (Reading.gl.val (tgt c0) - sigma) *
            psiProd ((callOf 1 z n).all.map (Var.wt Reading.gl)) rs))
    (eps : E) (rsE values : List E) (hr : rsE.length = z.size + 1) (hv : values.length = n)
    (okc : okE c0 = true) (oke : okE eps = true) (okr : ∀ x ∈ rsE, okE x = true)
    (okv : ∀ x ∈ values, okE x = true) :
    ∃ (t : List Fmt.RoundView) (l : List (List E × E)),
      Shaped (eps :: rsE) t (sumcheck.rounds z.size n) ∧ t.length = z.size + 3 ∧ Canonical t ∧
      readAll (callOf 1 z n) t = some ⟨ofK muT, eps, l, values⟩ ∧
      leadScalars (callOf 1 z n) t = some [c0] ∧ l.map (·.2) = rsE ∧
      movesOf Reading.gl (callOf 1 z n).all l (addE (ofK muT) (mulE eps (tgt c0))) =
        honest (tq (Reading.gl.val eps)) [] (rsE.map Reading.gl.val) ∧
      (∀ rest, ∃ (Sm : Sum) (F1 : Fork), sumcheck z n F (t ++ rest) = some (Sm, F1, rest) ∧
        Sm.psc = some (heardRec ((hidOf F.next [c0]).getD 0 {}).var (tgt c0)
          ⟨ofK muT, eps, l, values⟩ (callOf 1 z n) (F.next + [c0].length)) ∧
        F1.next = F.next + [c0].length + ownSlots (callOf 1 z n).all + n ∧ F1.ns = F.ns ∧
        Fresh F1 m) ∧
      ∀ (W : World K) (S0 : E) (kept : Form),
        (((hidOf F.next [c0]).getD 0 {}).var).value Reading.gl W = sigma →
        (∀ i, i < ownSlots (callOf 1 z n).all → W.slot (F.next + [c0].length + i) = hcoef i) →
        S (rsE.map Reading.gl.val) = Reading.gl.val S0 + kept.value Reading.gl W →
        (rowForm (heardRec ((hidOf F.next [c0]).getD 0 {}).var (tgt c0)
          ⟨ofK muT, eps, l, values⟩ (callOf 1 z n) (F.next + [c0].length)) S0 kept).value
            Reading.gl W = 0 := by
  obtain ⟨t, l, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := heardBy_honest 1
    (fun c => (c.getD 0 {}).var) z hn [c0] rfl hF (tgt c0)
    (fun Fa h => publicPart_claimed hW c0 hF Fa h) hcoef S sigma muT tq hCh eps rsE values hr hv
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact okc) oke okr okv
  refine ⟨t, l, a0, a1, a2, a3, a4, a5, a6, fun rest => ?_, a8⟩
  obtain ⟨es, Fa, F1, _, b2, b3, b4, b5⟩ := a7 rest
  refine ⟨{ r := (challenges (callOf 1 z n) (heardRec ((hidOf F.next [c0]).getD 0 {}).var (tgt c0)
        ⟨ofK muT, eps, l, values⟩ (callOf 1 z n) (F.next + [c0].length))).toArray,
            ends := es,
            psc := some (heardRec ((hidOf F.next [c0]).getD 0 {}).var (tgt c0)
              ⟨ofK muT, eps, l, values⟩ (callOf 1 z n) (F.next + [c0].length)),
            claimed := (hidOf F.next [c0]).getD 0 {} }, F1, ?_, rfl, b3, b4, b5⟩
  unfold sumcheck
  rw [bind_eq b2]
  rfl

/-- **THE HONEST ROUNDS OF "level z start".** down: the element of its last round. -/
theorem level_honest (z : Point) (start : Form) {F : Fork} {m : Nat}
    (hF : Fresh F (([] : List E).length + (ownSlots (callOf 0 z 2).all + 2 + m))) (T : E)
    (hT : F.publicPart start = some T)
    (hcoef : ℕ → K) (S : List K → K) (sigma muT : K) (tq : K → List K → K[X])
    (hCh : ∀ (eps : K) (rs : List K),
      rs.length = ((callOf 0 z 2).all.map (Var.wt Reading.gl)).length →
      Chain ((callOf 0 z 2).all.map (Var.wt Reading.gl)) (honest (tq eps) [] rs)
        (muT + eps * Reading.gl.val T)
        (hid ((callOf 0 z 2).all.map (Var.wt Reading.gl)) hcoef rs + eps * S rs +
          eps * (Reading.gl.val T - sigma) *
            psiProd ((callOf 0 z 2).all.map (Var.wt Reading.gl)) rs))
    (eps down : E) (rsE values : List E) (hr : rsE.length = z.size + 1) (hv : values.length = 2)
    (oke : okE eps = true) (okd : okE down = true) (okr : ∀ x ∈ rsE, okE x = true)
    (okv : ∀ x ∈ values, okE x = true) :
    ∃ (t : List Fmt.RoundView) (l : List (List E × E)),
      Shaped (down :: eps :: rsE) (t ++ [rvOf [] [down]]) (level.rounds z.size) ∧
      t.length = z.size + 3 ∧ Canonical (t ++ [rvOf [] [down]]) ∧
      readAll (callOf 0 z 2) t = some ⟨ofK muT, eps, l, values⟩ ∧ l.map (·.2) = rsE ∧
      movesOf Reading.gl (callOf 0 z 2).all l (addE (ofK muT) (mulE eps T)) =
        honest (tq (Reading.gl.val eps)) [] (rsE.map Reading.gl.val) ∧
      (∀ rest, ∃ (Sm : Sum) (F1 : Fork),
        level z start F (t ++ [rvOf [] [down]] ++ rest) = some (Sm, F1, rest) ∧
        Sm.psc = some (heardRec start T ⟨ofK muT, eps, l, values⟩ (callOf 0 z 2)
          (F.next + ([] : List E).length)) ∧
        F1.next = F.next + ([] : List E).length + ownSlots (callOf 0 z 2).all + 2 ∧
        F1.ns = F.ns ∧ Fresh F1 m) ∧
      ∀ (W : World K) (S0 : E) (kept : Form),
        start.value Reading.gl W = sigma →
        (∀ i, i < ownSlots (callOf 0 z 2).all →
          W.slot (F.next + ([] : List E).length + i) = hcoef i) →
        S (rsE.map Reading.gl.val) = Reading.gl.val S0 + kept.value Reading.gl W →
        (rowForm (heardRec start T ⟨ofK muT, eps, l, values⟩ (callOf 0 z 2)
          (F.next + ([] : List E).length)) S0 kept).value Reading.gl W = 0 := by
  obtain ⟨t, l, a0, a1, a2, a3, _, a5, a6, a7, a8⟩ := heardBy_honest 0 (fun _ => start) z
    (by omega : 1 ≤ 2) [] rfl hF T
    (fun Fa h => by
      obtain ⟨run, _⟩ := hide_unfold h
      have h0 : ({ F with next := F.next + ([] : List E).length } : Fork).hideRun F.next
          ([] : List E).toArray oneE =
          some ({ F with next := F.next + ([] : List E).length } : Fork) := by
        simp [Fork.hideRun]
      rw [h0] at run
      rw [← Option.some.inj run]
      exact hT) hcoef S sigma muT tq hCh eps rsE values hr hv (by simp) oke okr okv
  have eL : level.rounds z.size = (⟨"PSC epsilon", 0 + 1, 1, false, 0⟩ ::
      (List.replicate z.size ⟨"PSC round", 2, 1, false, 0⟩ ++
        [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", 2, 0, false, 0⟩])) ++
      [⟨"LINE", 0, 1, false, 0⟩] := by simp [level.rounds]
  refine ⟨t, l, eL ▸ (a0.mono fun x hx => List.mem_cons_of_mem _ hx).append
    ((shaped_one [] [down] ⟨"LINE", 0, 1, false, 0⟩ rfl rfl).mono fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact List.mem_cons_self ..), a1, ?_, a3, a5, a6, fun rest => ?_, a8⟩
  · intro r hr'
    rcases List.mem_append.mp hr' with h | h
    · exact a2 r h
    · rw [List.mem_singleton.mp h]
      refine ⟨fun x hx => by simp [rvOf] at hx, fun x hx => ?_⟩
      have hx' : x = down.triple := by simpa [rvOf] using hx
      rw [hx', E.ofTriple_triple]
      exact okd
  · obtain ⟨es, Fa, F1, _, b2, b3, b4, b5⟩ := a7 (rvOf [] [down] :: rest)
    refine ⟨{ r := (challenges (callOf 0 z 2) (heardRec start T ⟨ofK muT, eps, l, values⟩
          (callOf 0 z 2) (F.next + ([] : List E).length))).toArray,
              ends := es,
              psc := some (heardRec start T ⟨ofK muT, eps, l, values⟩ (callOf 0 z 2)
                (F.next + ([] : List E).length)),
              down := down }, F1, ?_, rfl, b3, b4, b5⟩
    unfold level
    rw [List.append_assoc, List.singleton_append, bind_eq b2]
    dsimp only
    rw [bind_eq (show Hear.round 0 1 F1 (rvOf [] [down] :: rest) = some (([], [down]), F1, rest)
      from round_returns [] [down] F1 rest)]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law
