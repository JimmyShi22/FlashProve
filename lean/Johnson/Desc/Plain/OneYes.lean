-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/OneYes.lean: WHAT A BLOCK's YES SAYS IN A FILE OF ONE CHAIN, BY GROUP, FROM WHAT
THE VIEW SHOWS BY KEY. The library says what the written link's view shows BY KEY AND POSITION
(`viewX`); a kind's `decide` is handed its columns BY GROUP, behind `Block.step`'s `groupsOf` and
`regroup`. Here the two meet.

  `readG L g`: a group's columns, each looked up by its key and position.
  `regroup_colsFor`: the columns that `colsFor` looks up, regrouped, ARE the groups read by `readG`.
  `opiece_decides`: where a piece (Johnson/Desc/Plain/OneChain.lean) puts out u: the rounds' work
    has passed; every word of its rounds and columns is below the prime; `roundsFit` has said yes;
    and THE BLOCK's decide WENT ON TO u's RECORD ON THE TRANSCRIPT's OWN ROUNDS (without the sealed
    digests) AND ON THE DECLARED GROUPS READ BY KEY in the two stored tables, the trees sent before,
    and the block's own.
  `Walk`, `rowOut_walk`: where the blocks in a row put out: the statements at all the boundaries,
    each block's yes on its own cut of the transcript.
  `run_walk`: so WHERE THE CHAIN's FOLD SAYS YES ON THE WRITTEN LINK's VIEW, there is such a walk
    (by `fold_row` and `view_true`, Johnson/Desc/Plain/OneFile.lean).
No game: all of it holds at every transcript.
Nearest kin: `shownFrom_of_keys` (Johnson/Desc/Link/LinkShown.lean; not compared): by its name the
same step by another road; also `shows_many`, `view_rounds_many` (OnBytes/Slice/ManyView.lean).

-/
import Johnson.Desc.Plain.OneFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Plain.One
open TypedOracleCompiler.Run.PQ (viewX skeletonOverBothExternalStrings SOf)
open OnBytes.Maker (RDT toRDs uLT rvT rhoT passT colAtST)
open Fo.Peel (joinR fstR sndR joinR_split fstR_join sndR_join rvT_join rvT_length passT_join)
open _root_.Run.PQ (CK SgX XO)
open _root_.Iop (Tr twoExternalStrings)

/-- A group's columns, each with its position, looked up by key and position. -/
def readG (L : ℕ → ℕ → Option (List UInt64)) (g : List (ℕ × ℕ × ℕ)) : List (ℕ × List UInt64) :=
  g.map fun w => (w.2.1, (L w.1 w.2.1).getD [])

theorem colsFor_append (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (g r : List (ℕ × ℕ × ℕ)) (cs : List OpenedColumn), colsFor L (g ++ r) = some cs →
      ∃ c₁ c₂, colsFor L r = some c₂ ∧ cs = c₁ ++ c₂ ∧ c₁.length = g.length ∧
        c₁.map (fun c => (c.2.1, c.2.2)) = readG L g
  | [], _, cs, h => ⟨[], cs, h, rfl, rfl, rfl⟩
  | w :: g, r, cs, h => by
      have h' : (match L w.1 w.2.1, colsFor L (g ++ r) with
        | some c, some cs => some ((w.1, w.2.1, c) :: cs)
        | _, _ => none) = some cs := h
      cases hL : L w.1 w.2.1 with
      | none => rw [hL] at h'; cases h'
      | some c =>
        cases hr : colsFor L (g ++ r) with
        | none => rw [hL, hr] at h'; cases h'
        | some cs' =>
          rw [hL, hr] at h'
          obtain rfl := Option.some.inj h'
          obtain ⟨c₁, c₂, k1, k2, k3, k4⟩ := colsFor_append L g r cs' hr
          refine ⟨(w.1, w.2.1, c) :: c₁, c₂, k1, by rw [k2]; rfl, by simp [k3], ?_⟩
          show (w.2.1, c) :: c₁.map (fun c => (c.2.1, c.2.2)) =
            (w.2.1, (L w.1 w.2.1).getD []) :: readG L g
          rw [k4, hL]
          rfl

/-- **By key ⟹ by group.** -/
theorem regroup_colsFor (L : ℕ → ℕ → Option (List UInt64)) :
    ∀ (groups : List (List (ℕ × ℕ × ℕ))) (cs : List OpenedColumn),
      colsFor L (groups.flatMap id) = some cs →
      regroup (groups.map (·.length)) cs = groups.map (readG L)
  | [], _, _ => rfl
  | g :: gs, cs, h => by
      have h' : colsFor L (g ++ gs.flatMap id) = some cs := h
      obtain ⟨c₁, c₂, k1, rfl, k3, k4⟩ := colsFor_append L g _ cs h'
      show ((c₁ ++ c₂).take g.length).map (fun c => (c.2.1, c.2.2)) ::
        regroup (gs.map (·.length)) ((c₁ ++ c₂).drop g.length) = readG L g :: gs.map (readG L)
      rw [← k3, List.take_left' rfl, List.drop_left' rfl, k4, regroup_colsFor L gs c₂ k1]

section
variable {C : CK} {S Cl : Type} (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (ft : ℕ)

/-- **What a piece's yes says.** -/
theorem opiece_decides (p : OPiece C S Cl) (t u : Stm S) (σ : Tr (uLT C p.ds))
    (h : p.out a y ft t σ = some u) :
    passT C p.ds (rhoT C p.ds σ) = true ∧ roundsFit p.b.rounds (rvT C p.ds σ) = true ∧
      p.b.decide t.1 ((rvT C p.ds σ).map noDigest)
        ((groupsOf ft p.b.rounds ((rvT C p.ds σ).map (·.drawn))).map
          (readG (lookY a y (lookOn p t.2.1 t.2.2 σ)))) = .ok u.1 ∧
      u.2.1 = lookOn p t.2.1 t.2.2 σ ∧ u.2.2 = t.2.2 + nT p.ds ∧
      ∃ cs, colsFor (lookY a y (lookOn p t.2.1 t.2.2 σ)) (wantOf ft p.b (rvT C p.ds σ)) = some cs ∧
        viewWordsBelowPrime ⟨rvT C p.ds σ, cs⟩ = true := by
  have h0 : (if passT C p.ds (rhoT C p.ds σ) = true then
      (colsFor (lookY a y (lookOn p t.2.1 t.2.2 σ)) (wantOf ft p.b (rvT C p.ds σ))).bind fun cs =>
        if viewWordsBelowPrime ⟨rvT C p.ds σ, cs⟩ = true then
          (p.b.step ft t.1 (rvT C p.ds σ) cs).toOption.map fun r =>
            (r.1, lookOn p t.2.1 t.2.2 σ, t.2.2 + nT p.ds)
        else none
      else none) = some u := h
  by_cases hpw : passT C p.ds (rhoT C p.ds σ) = true
  swap
  · rw [if_neg hpw] at h0
    cases h0
  rw [if_pos hpw] at h0
  obtain ⟨cs, hcs, h2⟩ := Option.bind_eq_some_iff.1 h0
  by_cases hwd : viewWordsBelowPrime ⟨rvT C p.ds σ, cs⟩ = true
  swap
  · rw [if_neg hwd] at h2
    cases h2
  rw [if_pos hwd] at h2
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h2
  refine ⟨hpw, ?_, ?_, rfl, rfl, cs, hcs, hwd⟩
  · cases hs : p.b.step ft t.1 (rvT C p.ds σ) cs with
    | error e => rw [hs] at hr; cases hr
    | ok r' =>
      unfold Block.step at hs
      obtain ⟨_, h1, _⟩ := bindOk hs
      exact needOk h1
  have hst : p.b.step ft t.1 (rvT C p.ds σ) cs = .ok r := by
    cases hs : p.b.step ft t.1 (rvT C p.ds σ) cs with
    | error e => rw [hs] at hr; cases hr
    | ok r' => rw [hs] at hr; exact congrArg Except.ok (Option.some.inj hr)
  obtain ⟨hk, _⟩ := step_cols ft (s' := r.1) (k := r.2) hst
  have hlen : cs.length = (wantOf ft p.b (rvT C p.ds σ)).length := by
    obtain ⟨c₁, c₂, k1, k2, k3, _⟩ := colsFor_append _ (wantOf ft p.b (rvT C p.ds σ)) [] cs
      (by rw [List.append_nil]; exact hcs)
    have : c₂ = [] := (Option.some.inj k1).symm
    rw [k2, this, List.append_nil, k3]
  unfold Block.step at hst
  obtain ⟨_, _, hst⟩ := bindOk hst
  obtain ⟨_, _, hst⟩ := bindOk hst
  obtain ⟨s', hd, hst⟩ := bindOk hst
  have e : s' = r.1 := congrArg Prod.fst (Except.ok.inj hst)
  have htake : cs.take ((groupsOf ft p.b.rounds ((rvT C p.ds σ).map (·.drawn))).flatMap id).length =
      cs := List.take_of_length_le (le_of_eq hlen)
  rw [htake, regroup_colsFor _ _ cs hcs, e] at hd
  exact hd

/-- The statements at all the boundaries, each block's yes on its own cut of the transcript. -/
def Walk : (l : List (OPiece C S Cl)) → Stm S → Tr (uLT C (rowDs l)) → Stm S → Prop
  | [], t, _, e => t = e
  | p :: l, t, τ, e =>
    ∃ u, p.out a y ft t (fstR C p.ds (rowDs l) τ) = some u ∧
      Walk l u (sndR C p.ds (rowDs l) τ) e

theorem rowOut_walk : ∀ (l : List (OPiece C S Cl)) (t : Stm S) (τ : Tr (uLT C (rowDs l))) (e : Stm
    S),
    rowOut a y ft l t τ = some e → Walk a y ft l t τ e
  | [], _, _, _, h => Option.some.inj h
  | p :: l, t, τ, e, h => by
      obtain ⟨u, hu, hr⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨u, hu, rowOut_walk l u _ e hr⟩

/-- **Where the chain's fold says yes on the written link's view, there is such a walk**, from the
first statement (no tree is sent) to the fold's end. -/
theorem run_walk (xs : List XO) (l : List (OPiece C S Cl)) (name : String) (s e : S)
    (τ : Tr (uLT C (rowDs l))) (lens : ∀ p ∈ l, p.ds.length = p.b.rounds.length)
    (back : OpensBack ft 0 l) (hpw : passT C (rowDs l) (rhoT C (rowDs l) τ) = true)
    (hwd : viewWordsBelowPrime (viewX C (toRDs (rowDs l)) a xs y τ) = true)
    (h : chainAt name ft (l.map (·.b)) s (viewX C (toRDs (rowDs l)) a xs y τ) = .ok e) :
    ∃ t, Walk a y ft l (s, fun _ _ => none, 0) τ t ∧ t.1 = e := by
  obtain ⟨t, ht, hte⟩ := fold_row a y ft (colAtST C (rowDs l) τ) l s (fun _ _ => none) 0 τ _ e lens
    hpw hwd (chainOk h) (view_true a y (rowDs l) xs τ) (fun n _ hn => absurd hn (Nat.not_lt_zero n))
    (fun _ _ _ => rfl) back
  exact ⟨t, rowOut_walk a y ft l _ τ t ht, hte⟩

end

end VerifiableInference.Desc.Plain.One

#print axioms VerifiableInference.Desc.Plain.One.regroup_colsFor
#print axioms VerifiableInference.Desc.Plain.One.opiece_decides
#print axioms VerifiableInference.Desc.Plain.One.run_walk
