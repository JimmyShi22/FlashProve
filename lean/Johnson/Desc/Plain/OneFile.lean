-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/OneFile.lean: the second half of the rule for a file of one unsealed chain
(Johnson/Desc/Plain/OneChain.lean, whose head says all): where the fold says yes on the whole view,
the blocks in a row put out (`fold_row`); the written link is sound (`linkW_sound`); `SoundAt`
(`soundAt_of_chain`).
Nearest kin in the library: `view_true`: `opened_stored` (OnBytes/Slice/WrittenView.lean:165),
`shows_many` (OnBytes/Slice/ManyView.lean:142) (rounds with one tree); `Err.Below.zero`
(Iop/Compose.lean:195), called; the top that takes `SoundAt`: `linkSib_sound`
(OnBytes/Flat/LinkSib.lean).
Limits. A rule: `linkW_sound` and `soundAt_of_chain` are said under the hypotheses that stand in
their statements, which this comment does not list; it is no claim that they hold. No probability is
evaluated to a number here: the error is rowErr l, the pieces' own errors in a row
(Johnson/Desc/Plain/OneChain.lean); that it lies below κ is a premise (below). Nothing on
acceptance.

-/
import Johnson.Desc.Plain.OneChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Plain.One
open TypedOracleCompiler.Run.PQ (viewX skeletonOverBothExternalStrings SOf)
open OnBytes.Maker (RDT toRDs uLT rvT rhoT passT colAtST)
open Fo.Peel (joinR fstR sndR joinR_split fstR_join sndR_join rvT_join rvT_length passT_join)
open _root_.Run.PQ (CK SgX XO storedKey xPos)
open _root_.Iop (Reduction Err Shape Doomed Tr twoExternalStrings)
open _root_.Prob (cnt cnt_mono cnt_false)
open OnBytes.Flat (linkProtocolOfRoundData SoundAt)

/-! ## 3 Where the fold says yes, the blocks in a row put out -/

/-- Every column is the oracle's column at its key and position. -/
def ColsTrue (L : ℕ → ℕ → Option (List UInt64)) (cols : List OpenedColumn) : Prop :=
  ∀ c ∈ cols, L c.1 c.2.1 = some c.2.2

section Step
variable {S Cl : Type} (ft : ℕ)

/-- A FURTHER TEXT of a three-line lemma that the library holds several times (so `needTrue`,
Johnson/Desc/First/StartsSized.lean): kept, so that this file need not import a file on the first
chain's start. -/
theorem needOk {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  unfold need at h
  split at h
  · assumption
  · exact nomatch h

/-- What a step's yes says of the columns. -/
theorem step_cols {b : Block S Cl} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {s' : S} {k : ℕ}
    (H : b.step ft s rs cols = .ok (s', k)) :
    k = (wantOf ft b rs).length ∧
      (cols.take k).map (fun c => (c.1, c.2.1, c.2.2.length)) = wantOf ft b rs := by
  unfold Block.step at H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨_, h2, H⟩ := bindOk H
  obtain ⟨t, _, H⟩ := bindOk H
  have e : (wantOf ft b rs).length = k := congrArg Prod.snd (Except.ok.inj H)
  refine ⟨e.symm, ?_⟩
  rw [← e]
  exact eq_of_beq (needOk h2)

/-- A step reads of the columns only as many as it asks. -/
theorem step_take (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    b.step ft s rs (cols.take (wantOf ft b rs).length) = b.step ft s rs cols := by
  unfold Block.step wantOf
  simp only [List.take_take, Nat.min_self]

theorem colsFor_true (L : ℕ → ℕ → Option (List UInt64)) : ∀ got : List OpenedColumn, ColsTrue L got →
    colsFor L (got.map fun c => (c.1, c.2.1, c.2.2.length)) = some got
  | [], _ => rfl
  | c :: got, h => by
      have h1 : L c.1 c.2.1 = some c.2.2 := h c List.mem_cons_self
      have h2 := colsFor_true L got fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
      show (match L c.1 c.2.1, colsFor L (got.map fun c => (c.1, c.2.1, c.2.2.length)) with
        | some x, some cs => some ((c.1, c.2.1, x) :: cs)
        | _, _ => none) = some (c :: got)
      rw [h1, h2]

/-- The words' test on a view holds of its cuts. -/
theorem okView_cut {r₁ r₂ : List Fmt.RoundView} {cols : List OpenedColumn} (k : ℕ)
    (h : viewWordsBelowPrime ⟨r₁ ++ r₂, cols⟩ = true) :
    viewWordsBelowPrime ⟨r₁, cols.take k⟩ = true ∧ viewWordsBelowPrime ⟨r₂, cols.drop k⟩ = true := by
  unfold viewWordsBelowPrime at h ⊢
  dsimp only at h ⊢
  rw [Bool.and_eq_true, List.all_append, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, hc⟩ := h
  have hc' := List.all_eq_true.1 hc
  exact ⟨Bool.and_eq_true_iff.2 ⟨h1, List.all_eq_true.2 fun o ho => hc' o (List.mem_of_mem_take
      ho)⟩,
    Bool.and_eq_true_iff.2 ⟨h2, List.all_eq_true.2 fun o ho => hc' o (List.mem_of_mem_drop ho)⟩⟩

end Step

section Fold
variable {C : CK} {S Cl : Type} (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (ft : ℕ)

/-- A block opens no tree that is sent behind it. -/
def OpensBack : ℕ → List (OPiece C S Cl) → Prop
  | _, [] => True
  | base, p :: l =>
    (∀ rs, ∀ w ∈ wantOf ft p.b rs,
      w.1 = storedKey false ∨ w.1 = storedKey true ∨ w.1 < base + nT p.ds) ∧
      OpensBack (base + nT p.ds) l

theorem lookY_congr (L L' : Look) (k p : ℕ)
    (h : k ≠ storedKey false → k ≠ storedKey true → L k p = L' k p) :
    lookY a y L k p = lookY a y L' k p := by
  unfold lookY
  by_cases h0 : k = storedKey false
  · rw [if_pos h0, if_pos h0]
  · by_cases h1 : k = storedKey true
    · rw [if_neg h0, if_neg h0, if_pos h1, if_pos h1]
    · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, h h0 h1]

/-- **Where the fold says yes on rounds and columns of which every column is true, the blocks in a
row put out, and end at the fold's end.** Lw: the chain's own trees, all. -/
theorem fold_row (Lw : Look) : ∀ (l : List (OPiece C S Cl)) (s : S) (look : Look) (base : ℕ)
    (τ : Tr (uLT C (rowDs l))) (cols : List OpenedColumn) (e : S),
    (∀ p ∈ l, p.ds.length = p.b.rounds.length) →
    passT C (rowDs l) (rhoT C (rowDs l) τ) = true →
    viewWordsBelowPrime ⟨rvT C (rowDs l) τ, cols⟩ = true →
    foldBlocks ft (l.map (·.b)) s (rvT C (rowDs l) τ) cols = .ok (e, [], []) →
    ColsTrue (lookY a y Lw) cols →
    (∀ n x, n < base → Lw n x = look n x) →
    (∀ n x, base ≤ n → Lw n x = colAtST C (rowDs l) τ (n - base) x) →
    OpensBack ft base l →
    ∃ t', rowOut a y ft l (s, look, base) τ = some t' ∧ t'.1 = e
  | [], s, look, base, _, _, e, _, _, _, H, _, _, _, _ =>
      ⟨_, rfl, congrArg Prod.fst (Except.ok.inj H)⟩
  | p :: l, s, look, base, τ, cols, e, hlen, hpass, hwords, H, htrue, hlo, hhi, hback => by
      have hτ := joinR_split C p.ds (rowDs l) τ
      generalize fstR C p.ds (rowDs l) τ = τ₁ at hτ
      generalize sndR C p.ds (rowDs l) τ = τ₂ at hτ
      subst hτ
      have hhi' : ∀ n x, base ≤ n →
          Lw n x = colAtST C (p.ds ++ rowDs l) (joinR C p.ds (rowDs l) τ₁ τ₂) (n - base) x := hhi
      have hpass' : (passT C p.ds (rhoT C p.ds τ₁) &&
          passT C (rowDs l) (rhoT C (rowDs l) τ₂)) = true := by
        rw [← passT_join]
        exact hpass
      obtain ⟨hp1, hp2⟩ := Bool.and_eq_true_iff.1 hpass'
      have hrv := rvT_join C p.ds (rowDs l) τ₁ τ₂
      have hn : (rvT C p.ds τ₁).length = p.b.rounds.length := by
        rw [rvT_length, hlen p List.mem_cons_self]
      have H' : foldBlocks ft (p.b :: l.map (·.b)) s (rvT C p.ds τ₁ ++ rvT C (rowDs l) τ₂) cols =
          .ok (e, [], []) := by
        rw [← hrv]
        exact H
      obtain ⟨s', k, hst, Hr⟩ := foldConsOk H'
      rw [← hn, List.take_left'  rfl] at hst
      rw [← hn, List.drop_left' rfl] at Hr
      obtain ⟨hk, hwant⟩ := step_cols ft hst
      have hwords' : viewWordsBelowPrime ⟨rvT C p.ds τ₁ ++ rvT C (rowDs l) τ₂, cols⟩ = true := by
        rw [← hrv]
        exact hwords
      obtain ⟨hw1, hw2⟩ := okView_cut k hwords'
      -- the columns that the step took are true of the trees behind the block
      have hgot : ColsTrue (lookY a y (lookOn p look base τ₁)) (cols.take k) := by
        intro c hc
        have hc0 := htrue c (List.mem_of_mem_take hc)
        rw [← hc0]
        refine (lookY_congr a y _ _ _ _ fun h0 h1 => ?_).symm
        have hw : (c.1, c.2.1, c.2.2.length) ∈ wantOf ft p.b (rvT C p.ds τ₁) := by
          rw [← hwant]
          exact List.mem_map_of_mem hc
        have hb : c.1 < base + nT p.ds := by
          rcases hback.1 _ _ hw with h | h | h
          · exact absurd h h0
          · exact absurd h h1
          · exact h
        unfold lookOn
        by_cases hcb : c.1 < base
        · rw [if_pos hcb, hlo _ _ hcb]
        · rw [if_neg hcb, hhi' _ _ (Nat.le_of_not_lt hcb), col_join, if_pos (by omega)]
      have hcols : colsFor (lookY a y (lookOn p look base τ₁)) (wantOf ft p.b (rvT C p.ds τ₁)) =
          some (cols.take k) := by
        rw [← hwant]
        exact colsFor_true _ _ hgot
      have hst' : p.b.step ft s (rvT C p.ds τ₁) (cols.take k) = .ok (s', k) := by
        rw [hk, step_take]
        rw [← hk]
        exact hst
      obtain ⟨t', ht', he'⟩ := fold_row Lw l s' (lookOn p look base τ₁) (base + nT p.ds) τ₂
        (cols.drop k) e (fun q hq => hlen q (List.mem_cons_of_mem _ hq)) hp2 hw2 Hr
        (fun c hc => htrue c (List.mem_of_mem_drop hc))
        (fun n x hnx => by
          unfold lookOn
          by_cases hcb : n < base
          · rw [if_pos hcb, hlo _ _ hcb]
          · rw [if_neg hcb, hhi' _ _ (Nat.le_of_not_lt hcb), col_join, if_pos (by omega)])
        (fun n x hnx => by
          rw [hhi' n x (by omega), col_join, if_neg (by omega), Nat.sub_sub])
        hback.2
      refine ⟨t', ?_, he'⟩
      show (p.out a y ft (s, look, base) (fstR C p.ds (rowDs l) (joinR C p.ds (rowDs l) τ₁
          τ₂))).bind
        (fun u => rowOut a y ft l u (sndR C p.ds (rowDs l) (joinR C p.ds (rowDs l) τ₁ τ₂))) = _
      rw [fstR_join, sndR_join]
      have hout : p.out a y ft (s, look, base) τ₁ =
          some (s', lookOn p look base τ₁, base + nT p.ds) := by
        show (if passT C p.ds (rhoT C p.ds τ₁) = true then
          (colsFor (lookY a y (lookOn p look base τ₁)) (wantOf ft p.b (rvT C p.ds τ₁))).bind _
          else none) = _
        rw [if_pos hp1, hcols]
        show (if viewWordsBelowPrime ⟨rvT C p.ds τ₁, cols.take k⟩ = true then
          ((p.b.step ft s (rvT C p.ds τ₁) (cols.take k)).toOption.map _) else none) = _
        rw [if_pos hw1, hst']
        rfl
      rw [hout]
      exact ht'

/-- Every column of the written link's view is the oracle's column at its key and position. -/
theorem view_true (ds : List RDT) (xs : List XO) (τ : Tr (uLT C ds)) :
    ColsTrue (lookY a y (colAtST C ds τ)) (viewX C (toRDs ds) a xs y τ).opened := by
  intro c hc
  obtain ⟨kx, _, hkx⟩ := List.mem_filterMap.1 hc
  unfold lookY
  by_cases h0 : kx.1 = storedKey false
  · rw [if_pos h0] at hkx
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hkx
    show (if kx.1 = storedKey false then _ else _) = _
    rw [if_pos h0, hq]
    rfl
  · rw [if_neg h0] at hkx
    by_cases h1 : kx.1 = storedKey true
    · rw [if_pos h1] at hkx
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hkx
      show (if kx.1 = storedKey false then _ else if kx.1 = storedKey true then _ else _) = _
      rw [if_neg h0, if_pos h1, hq]
      rfl
    · rw [if_neg h1] at hkx
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hkx
      show (if kx.1 = storedKey false then _ else if kx.1 = storedKey true then _ else _) = _
      rw [if_neg h0, if_neg h1]
      exact hq

end Fold

/-! ## 4 The file -/

section File
variable {C : CK} {S Cl X : Type} (a : ℕ) (ft : ℕ) (xs : List XO) (l : List (OPiece C S Cl))
  (name : String) (dec : X → Fmt.View → Bool) (pub : Prop) (okS : X → Prop) (start : X → S)
  (fin : X → S → Prop)

/-- The first statement: the first record; no tree is sent. -/
def first (x : X) : Stm S := (start x, fun _ _ => none, 0)

/-- **The written link at the decision is sound round by round for Lg**, at one instance. -/
theorem linkW_sound (x : X) (Lg : (twoExternalStrings (2 ^ a) SgX).Str → Prop)
    (on : (twoExternalStrings (2 ^ a) SgX).Str → ℕ → Stm S → Prop)
    (Q : (twoExternalStrings (2 ^ a) SgX).Str → ℕ → Stm S → Stm S → Prop)
    (hdec : ∀ v, dec x v = true → pub ∧ okS x ∧ viewWordsBelowPrime v = true ∧
      ∃ e, chainAt name ft (l.map (·.b)) (start x) v = .ok e ∧ fin x e)
    (lens : pub → ∀ p ∈ l, p.ds.length = p.b.rounds.length) (back : pub → OpensBack ft 0 l)
    (laws : pub → ∀ y, EachLeadsO a y ft (on y) (Q y) 0 l)
    (tie : pub → ∀ y (t : Stm S), okS x → fin x t.1 →
      (on y 0 (first start x) → chainRel (Q y) 0 l.length (first start x) t) → Lg y) :
    (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).Sound (fun _ y => Lg y)
      ((0, rowErr l) : ℕ × Err (uLT C (rowDs l))) := by
  intro u y hL m
  rw [cnt_false]
  intro c hc
  refine hc ?_
  have key : ∀ τ : Tr (uLT C (rowDs l)),
      (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).accept u y (m, c, τ) = true →
      pub ∧ okS x ∧ ∃ t, rowOut a y ft l (first start x) τ = some t ∧ fin x t.1 := by
    intro τ hacc
    have hd : dec x (viewX C (toRDs (rowDs l)) a xs y τ) = true := (Bool.and_eq_true_iff.1 hacc).2
    have hpw : passT C (rowDs l) (rhoT C (rowDs l) τ) = true :=
      (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hacc).1).1).1
    obtain ⟨hpub, ho, hwd, e, hch, hf⟩ := hdec _ hd
    obtain ⟨t, ht, hte⟩ := fold_row a y ft (colAtST C (rowDs l) τ) l (start x) (fun _ _ => none) 0 τ
      _ e (lens hpub) hpw hwd (chainOk hch) (view_true a y (rowDs l) xs τ)
      (fun n _ h => absurd h (Nat.not_lt_zero n)) (fun _ _ _ => rfl) (back hpub)
    exact ⟨hpub, ho, t, ht, hte ▸ hf⟩
  by_cases hpb : pub
  swap
  · refine Doomed.of_forall _ _ fun τ => ?_
    cases hacc : (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).accept u y (m, c, τ) with
    | false => exact hacc
    | true => exact absurd (key τ hacc).1 hpb
  by_cases ho : on y 0 (first start x)
  · refine Doomed.mono _ _ ?_ (one_chain a y ft (on y) (Q y) l 0 (first start x) ho (laws hpb y))
    intro τ hτ
    cases hacc : (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).accept u y (m, c, τ) with
    | false => exact hacc
    | true =>
      obtain ⟨_, hs, t, ht, hf⟩ := key τ hacc
      exact absurd (tie hpb y t hs hf fun _ => hτ t ht) hL
  · refine Doomed.of_forall _ _ fun τ => ?_
    cases hacc : (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).accept u y (m, c, τ) with
    | false => exact hacc
    | true =>
      obtain ⟨_, hs, t, _, hf⟩ := key τ hacc
      exact absurd (tie hpb y t hs hf fun h => absurd h ho) hL

end File

/-! ## 5 The condition that the top asks of the entry file's decision -/

section At
open OnBytes.Slice TypedOracleCompiler.Slice
variable {C : CK} {S Cl : Type} (T : Fmt.M1.Code) (v eM lg s : ℕ)
  (dec : XE AnsT lg s → Fmt.View → Bool) (κ : ℝ≥0∞) (a : ℕ) (ft : ℕ) (xs : List XO)
  (l : List (OPiece C S Cl)) (name : String) (pub : Prop) (okS : XE AnsT lg s → Prop)
  (start : XE AnsT lg s → S) (fin : XE AnsT lg s → S → Prop)

/-- **`SoundAt` from one plain law a block**: so `CompilerSoundnessConditionStatements.entrySound` (by the library's
`linkSib_sound`). -/
theorem soundAt_of_chain
    (on : XE AnsT lg s → (twoExternalStrings (2 ^ a) SgX).Str → ℕ → Stm S → Prop)
    (Q : XE AnsT lg s → (twoExternalStrings (2 ^ a) SgX).Str → ℕ → Stm S → Stm S → Prop)
    (hdec : ∀ x w, dec x w = true → pub ∧ okS x ∧ viewWordsBelowPrime w = true ∧
      ∃ e, chainAt name ft (l.map (·.b)) (start x) w = .ok e ∧ fin x e)
    (lens : pub → ∀ p ∈ l, p.ds.length = p.b.rounds.length) (back : pub → OpensBack ft 0 l)
    (laws : pub → ∀ x y, EachLeadsO a y ft (on x y) (Q x y) 0 l)
    (tie : pub → ∀ x y (t : Stm S), okS x → fin x t.1 →
      (on x y 0 (first start x) → chainRel (Q x y) 0 l.length (first start x) t) →
      DecR.LgE (D := decRec T v eM lg s) (Equiv.refl _) (anT v s) id (x.1.1, x.2.1)
        (x.1.2, x.2.2) y.1 y.2)
    (below : pub → Err.Below (rowErr l) κ) :
    SoundAt T v eM lg s dec κ C (toRDs (rowDs l)) a xs := by
  by_cases hp : pub
  · exact ⟨((0, rowErr l) : ℕ × Err (uLT C (rowDs l))),
      fun x => linkW_sound a ft xs l name dec pub okS start fin x _ (on x) (Q x) (hdec x) lens back
        (fun h y => laws h x y) (fun h => tie h x),
      ⟨by simp, below hp⟩⟩
  · refine ⟨((0, Err.zero (uLT C (rowDs l))) : ℕ × Err (uLT C (rowDs l))), fun x u y _ => ?_,
      ⟨by simp, Err.Below.zero _ κ⟩⟩
    refine Doomed.of_forall _ _ fun τ => ?_
    cases hacc : (linkProtocolOfRoundData C (toRDs (rowDs l)) a xs fun _ : Unit => dec x).accept u y τ with
    | false => rfl
    | true => exact absurd (hdec x _ (Bool.and_eq_true_iff.1 hacc).2).1 hp

end At

end VerifiableInference.Desc.Plain.One

#print axioms VerifiableInference.Desc.Plain.One.soundAt_of_chain
#print axioms VerifiableInference.Desc.Plain.One.fold_row
#print axioms VerifiableInference.Desc.Plain.One.view_true
#print axioms VerifiableInference.Desc.Plain.One.linkW_sound
