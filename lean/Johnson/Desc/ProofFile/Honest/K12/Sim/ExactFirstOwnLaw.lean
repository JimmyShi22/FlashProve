-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFirstOwnLaw.lean: a law on a text. The text is what a
proximity test's first part shows where the first fold sends its own fresh table: the round "BAT",
the fold's rounds, and the columns of the table's tree at the positions that are asked (`ownText`).
Its random values are the 2 k + 1 coefficients of the fold's hiding polynomial and the tails of the
table's 2 ^ h rows. The law: sampled over all of these, what is shown has the same distribution
whatever the claim's row and the rows' message are, if the positions asked are in range and at most
as many different ones as a row's tail has entries. Two more hypotheses, on public numbers: the
stage's k is h + g, and the depth of the fresh table's code is at most 32. Definitions, statements
and proofs.

  `tailShare`, `msgShare`, `symG_shares`, `tailShare_add`, `tailShare_congr`   a symbol is the
                 tail's share plus the message's share; the tail's share is additive
  `tail_onto`    where the code's depth is at most 32 and the positions lie in range: at no more
                 different positions than the tail has entries, the tail's share takes every pattern
  `takeUp`, `takeUp_spec`   a chosen tail with a given pattern
  `ownText`, `own_tr`, `freshCol_len`   the text, at a claim's row v and a message μ; its one tree
  `foldShown_of_vals`   the fold's rounds are fixed by its 2 k + 1 values
  `upOf`, `normal`, `normal_lo`, `normal_hi`, `normal_bij`   the change of the random values: a
                 coefficient becomes the fold's value of that number; a row's tail takes up the
                 share of the row's message at the positions asked. It is one to one and onto
  `own_key`      two values of the random values with one image under the change, each at its own
                 v and μ, show the same
  `own_law`      the law

By what. `ontoUpTo_gen` (Code/RS.lean) and `toF_point_inj` (OnBytes/Slice/Points.lean) for
`tail_onto`; `foldVals_inj`, `hideAt_inj`, `showRV_congr`, `valsOf_fst`, `valsOf_snd`
(Sim/FoldLaw.lean); `length_wordsOf` (Johnson/Prover/Link/SwitchCols.lean), `length_wr`
(Johnson/Prover/Link/Base.lean);
`shownFrom_congr` (Sim/CoreText.lean); `map_unif_of_bijective` (Prob/Linear.lean).

Grade. Theorems: the law within the bound (`own_law`, Sim/ExactFirstOwnLaw.lean); a member of the
sentence at the full size, under the library's head, at written letters (`meets_head_O`,
Sim/MeetsOwnAtHead.lean). Said here without a theorem: at one position more than the bound allows
the distribution is another; at as many positions as the bound allows no random value is to spare;
one random value fewer will not do.

Limits.
- A law on a text. No part, no play, no simulator and no job occurs here: Sim/ExactFirstOwn.lean.
- v, μ and the challenges are fixed and depend on none of the random values.
- It speaks of these rounds and of this tree's columns at the positions asked alone. By the book
  these coefficients and tails are meant to be carried by the test's second part; nothing is said on
  that here.
- `takeUp` is chosen by `Classical.choose`: no code.
- No file of this folder states a security property by itself. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FoldLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.CoreText
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row
import Code.RS
import OnBytes.Slice.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice Cb
open Fmt.M1 (Code point)
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## 1 The tail's share of a symbol -/

def tailShare (Z : Code) (x : ℕ) (r : ℕ → GE) : GE :=
  ∑ q ∈ Finset.range Z.r, algebraMap GF GE (toF (point Z.a x) ^ q) * r q

def msgShare (Z : Code) (x : ℕ) (m : ℕ → GE) : GE :=
  ∑ j ∈ Finset.range Z.l, algebraMap GF GE (toF (point Z.a x) ^ (Z.r + j)) * m j

theorem symG_shares (Z : Code) (x : ℕ) (m r : ℕ → GE) :
    symG Z x m r = tailShare Z x r + msgShare Z x m := rfl

theorem tailShare_add (Z : Code) (x : ℕ) (r r' : ℕ → GE) :
    tailShare Z x (fun q => r q + r' q) = tailShare Z x r + tailShare Z x r' := by
  unfold tailShare
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => mul_add _ _ _

theorem tailShare_congr (Z : Code) (x : ℕ) (r r' : ℕ → GE) (h : ∀ q, q < Z.r → r q = r' q) :
    tailShare Z x r = tailShare Z x r' :=
  Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.1 hq)]

/-- Where the code's depth is at most 32 and the positions lie in range: at no more different
positions than the tail has entries, its share takes every pattern. -/
theorem tail_onto (Z : Code) (ha : Z.a ≤ 32) (A : List ℕ) (hA : ∀ x ∈ A, x < 2 ^ Z.a)
    (hd : different A ≤ Z.r) (g : ℕ → GE) : ∃ d : ℕ → GE, ∀ x ∈ A, tailShare Z x d = g x := by
  classical
  have hx : Function.Injective
      (fun j : Fin (2 ^ Z.a) => algebraMap GF GE (toF (point Z.a j.val))) := fun i j h =>
    Fin.ext (toF_point_inj Z.a ha i.isLt j.isLt ((algebraMap GF GE).injective h))
  have hS : ((A.eraseDups.filterMap fun x =>
      if h : x < 2 ^ Z.a then some (⟨x, h⟩ : Fin (2 ^ Z.a)) else none).toFinset).card ≤ Z.r :=
    ((List.toFinset_card_le _).trans (List.length_filterMap_le _ _)).trans hd
  obtain ⟨t, ht⟩ := Code.RS.ontoUpTo_gen hx Z.r _ hS fun j => g j.val.val
  refine ⟨fun q => if h : q < Z.r then t ⟨q, h⟩ else 0, fun x hxA => ?_⟩
  have hlt := hA x hxA
  have hm : (⟨x, hlt⟩ : Fin (2 ^ Z.a)) ∈ (A.eraseDups.filterMap fun x =>
      if h : x < 2 ^ Z.a then some (⟨x, h⟩ : Fin (2 ^ Z.a)) else none).toFinset :=
    List.mem_toFinset.2 (List.mem_filterMap.2 ⟨x, List.mem_eraseDups.2 hxA, dif_pos hlt⟩)
  have h1 := congrFun ht ⟨⟨x, hlt⟩, hm⟩
  rw [Code.restr_apply, Code.RS.gen_apply] at h1
  rw [← h1]
  unfold tailShare
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  show algebraMap GF GE (toF (point Z.a x) ^ i.val) *
      (if h : i.val < Z.r then t ⟨i.val, h⟩ else 0) =
    t i * algebraMap GF GE (toF (point Z.a x)) ^ i.val
  rw [dif_pos i.isLt, map_pow, mul_comm]

/-- A chosen tail whose share at the positions of A is g; 0 where there is none. -/
def takeUp (Z : Code) (A : List ℕ) (g : ℕ → GE) : ℕ → GE :=
  open Classical in
  if h : ∃ d : ℕ → GE, ∀ x ∈ A, tailShare Z x d = g x then Classical.choose h else fun _ => 0

theorem takeUp_spec (Z : Code) (ha : Z.a ≤ 32) (A : List ℕ) (hA : ∀ x ∈ A, x < 2 ^ Z.a)
    (hd : different A ≤ Z.r) (g : ℕ → GE) (x : ℕ) (hx : x ∈ A) :
    tailShare Z x (takeUp Z A g) = g x := by
  unfold takeUp
  rw [dif_pos (tail_onto Z ha A hA hd g)]
  exact Classical.choose_spec (tail_onto Z ha A hA hd g) x hx

/-! ## 2 The text -/

/-- **The text.** st: the first stage. v: the claim's row. μ: the rows' message. c: the random
values, by number: the coefficients, then the tails. D: the challenges, "BAT" being round 0. -/
def ownText (st : Fmt.M1.Stage) (v μ : (sgOf st).cIn.J → GE) (c : ℕ → GE) (D : ℕ → Fmt.Drawn) :
    BOut :=
  let W := hideAt ((sgOf st).h + (sgOf st).g) c
  let P : PS := { zeroPS with fM := packedN (sgOf st) W, fT := tailsIn st c }
  let rf := foldShown (sgOf st) v μ W fun n => D (1 + n)
  ⟨⟨[], D 0⟩ :: rf, (fun _ => []) :: (rf.map fun _ _ => []).set 0 (freshCol (sgOf st) P), []⟩

theorem getD_const {α : Type} (l : List α) (j : ℕ) :
    (l.map fun (_ : α) (_ : ℕ) => ([] : List UInt64)).getD j (fun _ => []) = fun _ => [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-- The text's trees: one, at round 1. -/
theorem own_tr (st : Fmt.M1.Stage) (v μ : (sgOf st).cIn.J → GE) (c : ℕ → GE) (D : ℕ → Fmt.Drawn) :
    ∀ i : ℕ, (ownText st v μ c D).tr.getD i (fun _ => []) =
      if i = 1 then freshCol (sgOf st) { zeroPS with
        fM := packedN (sgOf st) (hideAt ((sgOf st).h + (sgOf st).g) c), fT := tailsIn st c }
      else fun _ => []
  | 0 => by rw [if_neg (by omega)]; rfl
  | 1 => by rw [if_pos rfl]; rfl
  | j + 2 => by
    rw [if_neg (by omega)]
    exact getD_const _ j

theorem freshCol_len (s : Sg) (P : PS) (x : ℕ) : (freshCol s P x).length = 3 * 2 ^ s.h := by
  unfold freshCol
  rw [length_wordsOf, length_wr]

/-- The fold's rounds are fixed by its 2 k + 1 values. -/
theorem foldShown_of_vals (s : Sg) (v μ v' μ' : s.cIn.J → GE) (D : ℕ → Fmt.Drawn)
    (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (h : ∀ n, n < 2 * (s.h + s.g) + 1 → foldVals s v μ D W n = foldVals s v' μ' D W' n) :
    foldShown s v μ W D = foldShown s v' μ' W' D := by
  unfold foldShown
  have h0 : hMu (sVars GE 2 (s.h + s.g)) W = hMu (sVars GE 2 (s.h + s.g)) W' := h 0 (by omega)
  rw [h0]
  refine congrArg _ (showRV_congr _ _ _ _ fun i hi => ?_)
  have h1 := h (1 + 2 * i) (by omega)
  have h2 := h (2 + 2 * i) (by omega)
  unfold foldVals at h1 h2
  rw [valsOf_fst, valsOf_fst] at h1
  rw [valsOf_snd, valsOf_snd] at h2
  exact Prod.ext h1 h2

/-! ## 3 The change of the random values -/

theorem cut_idx (r b q : ℕ) (hq : q < r) : (b * r + q) / r = b ∧ (b * r + q) % r = q := by
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hq
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hq, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

/-- What row b's tail takes up: a tail whose share at the positions of A is the share of the row's
message. -/
def upOf (st : Fmt.M1.Stage) (A : List ℕ) (W : HIdx (sVars GE 2 ((sgOf st).h + (sgOf st).g)) → GE)
    (b : ℕ) : ℕ → GE :=
  takeUp (sgOf st).Z A fun x => msgShare (sgOf st).Z x (packedN (sgOf st) W b)

/-- **The change.** A: the positions asked. -/
def normal (st : Fmt.M1.Stage) (v μ : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn) (A : List ℕ)
    (c : Cs ⟨0, dueFresh st⟩) : Cs ⟨0, dueFresh st⟩ :=
  ⟨c.f, fun i =>
    if i.val < 2 * st.k + 1 then
      foldVals (sgOf st) v μ D (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e) i.val
    else (stretchOf c).e i.val +
      upOf st A (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e)
        ((i.val - (2 * st.k + 1)) / st.Z.r) ((i.val - (2 * st.k + 1)) % st.Z.r)⟩

theorem stretch_at {d : Due} (c : Cs d) (n : ℕ) (hn : n < d.e) :
    (stretchOf c).e n = c.e ⟨n, hn⟩ := by
  show (if h : n < d.e then c.e ⟨n, h⟩ else 0) = _
  rw [dif_pos hn]

theorem normal_lo (st : Fmt.M1.Stage) (v μ : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn)
    (A : List ℕ) (c : Cs ⟨0, dueFresh st⟩) (n : ℕ) (hn : n < 2 * st.k + 1) :
    (stretchOf (normal st v μ D A c)).e n =
      foldVals (sgOf st) v μ D (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e) n := by
  have hN : n < (⟨0, dueFresh st⟩ : Due).e := by
    show n < 2 * st.k + 1 + 2 ^ st.h * st.Z.r
    omega
  rw [stretch_at _ n hN]
  show (if n < 2 * st.k + 1 then _ else _) = _
  rw [if_pos hn]

theorem tail_lt (st : Fmt.M1.Stage) (b q : ℕ) (hb : b < 2 ^ st.h) (hq : q < st.Z.r) :
    2 * st.k + 1 + b * st.Z.r + q < 2 * st.k + 1 + 2 ^ st.h * st.Z.r := by
  have h1 : (b + 1) * st.Z.r ≤ 2 ^ st.h * st.Z.r := Nat.mul_le_mul_right _ hb
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

theorem normal_hi (st : Fmt.M1.Stage) (v μ : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn)
    (A : List ℕ) (c : Cs ⟨0, dueFresh st⟩) (b q : ℕ) (hb : b < 2 ^ st.h) (hq : q < st.Z.r) :
    tailsIn st (stretchOf (normal st v μ D A c)).e b q = tailsIn st (stretchOf c).e b q +
      upOf st A (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e) b q := by
  have hN : 2 * st.k + 1 + b * st.Z.r + q < (⟨0, dueFresh st⟩ : Due).e := tail_lt st b q hb hq
  show (stretchOf (normal st v μ D A c)).e (2 * st.k + 1 + b * st.Z.r + q) = _
  rw [stretch_at _ _ hN]
  show (if 2 * st.k + 1 + b * st.Z.r + q < 2 * st.k + 1 then _ else _) = _
  rw [if_neg (by omega)]
  have e : 2 * st.k + 1 + b * st.Z.r + q - (2 * st.k + 1) = b * st.Z.r + q := by omega
  rw [e, (cut_idx st.Z.r b q hq).1, (cut_idx st.Z.r b q hq).2]
  rfl

theorem normal_bij (st : Fmt.M1.Stage) (hk : st.k = (sgOf st).h + (sgOf st).g)
    (v μ : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn) (A : List ℕ) :
    Function.Bijective (normal st v μ D A) := by
  refine Finite.injective_iff_bijective.1 fun c c' h => ?_
  have hW : hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e =
      hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c').e :=
    foldVals_inj (sgOf st) v μ D _ _ fun n hn => by
      rw [← hk] at hn
      rw [← normal_lo st v μ D A c n hn, h, normal_lo st v μ D A c' n hn]
  have hf : c.f = c'.f := by
    have := congrArg Cs.f h
    exact this
  have he : c.e = c'.e := funext fun i => by
    rw [← stretch_at c i.val i.isLt, ← stretch_at c' i.val i.isLt]
    by_cases hi : i.val < 2 * st.k + 1
    · exact hideAt_inj _ _ _ hW i.val (by rw [← hk]; exact hi)
    · have h1 := congrFun (congrArg Cs.e h) i
      have h2 : (stretchOf c).e i.val +
          upOf st A (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e)
            ((i.val - (2 * st.k + 1)) / st.Z.r) ((i.val - (2 * st.k + 1)) % st.Z.r) =
          (stretchOf c').e i.val +
          upOf st A (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c').e)
            ((i.val - (2 * st.k + 1)) / st.Z.r) ((i.val - (2 * st.k + 1)) % st.Z.r) := by
        have h3 : (if i.val < 2 * st.k + 1 then _ else _) =
            (if i.val < 2 * st.k + 1 then _ else _) := h1
        rwa [if_neg hi, if_neg hi] at h3
      rw [hW] at h2
      exact add_right_cancel h2
  cases c
  cases c'
  simp only at hf he
  rw [hf, he]

/-! ## 4 What is shown hangs on the image alone -/

/-- The positions asked of the table's tree. -/
def askedOf (asks : List (List (List ℕ))) : List ℕ := (((asks[1]?).getD [])[0]?).getD []

theorem own_key (st : Fmt.M1.Stage) (hk : st.k = (sgOf st).h + (sgOf st).g) (ha : st.Z.a ≤ 32)
    (v μ v' μ' : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ) (n : ℕ)
    (asks : List (List (List ℕ))) (hbud : budFirst st asks = true) (c c' : Cs ⟨0, dueFresh st⟩)
    (h : normal st v μ (fun n => D (1 + n)) (askedOf asks) c =
      normal st v' μ' (fun n => D (1 + n)) (askedOf asks) c') :
    shownFrom (ownText st v μ (stretchOf c).e D) dep n asks =
      shownFrom (ownText st v' μ' (stretchOf c').e D) dep n asks := by
  have hA : (∀ x ∈ askedOf asks, x < 2 ^ (sgOf st).Z.a) ∧
      different (askedOf asks) ≤ (sgOf st).Z.r := by
    unfold budFirst at hbud
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hbud
    exact hbud
  have hrf : foldShown (sgOf st) v μ (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e)
        (fun n => D (1 + n)) =
      foldShown (sgOf st) v' μ' (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c').e)
        fun n => D (1 + n) :=
    foldShown_of_vals (sgOf st) v μ v' μ' _ _ _ fun n hn => by
      rw [← hk] at hn
      rw [← normal_lo st v μ _ (askedOf asks) c n hn, h, normal_lo st v' μ' _ _ c' n hn]
  have hcol : ∀ q ∈ askedOf asks,
      freshCol (sgOf st) { zeroPS with
          fM := packedN (sgOf st) (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e)
          fT := tailsIn st (stretchOf c).e } q =
        freshCol (sgOf st) { zeroPS with
          fM := packedN (sgOf st) (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c').e)
          fT := tailsIn st (stretchOf c').e } q := fun q hq => by
    show wordsOf (wr _ (freshSym _ _ _ q)) = wordsOf (wr _ (freshSym _ _ _ q))
    refine congrArg wordsOf ?_
    unfold wr
    refine List.map_congr_left fun b hb => congrArg ofE ?_
    have hb' : b < 2 ^ st.h := List.mem_range.1 hb
    have hq' : q % 2 ^ (sgOf st).Z.a = q := Nat.mod_eq_of_lt (hA.1 q hq)
    show symG (sgOf st).Z (q % 2 ^ (sgOf st).Z.a) _ _ = symG (sgOf st).Z (q % 2 ^ (sgOf st).Z.a) _ _
    rw [hq', symG_shares, symG_shares,
      ← takeUp_spec (sgOf st).Z ha (askedOf asks) hA.1 hA.2
        (fun x => msgShare (sgOf st).Z x (packedN (sgOf st)
          (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c).e) b)) q hq,
      ← takeUp_spec (sgOf st).Z ha (askedOf asks) hA.1 hA.2
        (fun x => msgShare (sgOf st).Z x (packedN (sgOf st)
          (hideAt ((sgOf st).h + (sgOf st).g) (stretchOf c').e) b)) q hq,
      ← tailShare_add, ← tailShare_add]
    refine tailShare_congr _ _ _ _ fun j hj => ?_
    have e1 := normal_hi st v μ (fun n => D (1 + n)) (askedOf asks) c b j hb' hj
    have e2 := normal_hi st v' μ' (fun n => D (1 + n)) (askedOf asks) c' b j hb' hj
    rw [h] at e1
    exact (e1.symm.trans e2)
  refine shownFrom_congr _ _ dep n asks ?_ (fun i => ?_) fun i q hq => ?_
  · show (⟨[], D 0⟩ : Fmt.RoundView) :: _ = ⟨[], D 0⟩ :: _
    rw [hrf]
  · rw [own_tr, own_tr]
    by_cases hi : i = 1
    · rw [if_pos hi, if_pos hi, freshCol_len, freshCol_len]
    · rw [if_neg hi, if_neg hi]
  · rw [own_tr, own_tr]
    by_cases hi : i = 1
    · rw [if_pos hi, if_pos hi]
      subst hi
      exact hcol q hq
    · rw [if_neg hi, if_neg hi]

/-! ## 5 The law -/

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **The law**: what is shown has one distribution at all claims' rows and rows' messages.
`Prob.unif` is over the part's own random values alone, at fixed v, μ, v', μ', D and asks. Nothing
is said on what v or μ are. -/
theorem own_law (st : Fmt.M1.Stage) (hk : st.k = (sgOf st).h + (sgOf st).g) (ha : st.Z.a ≤ 32)
    (v μ v' μ' : (sgOf st).cIn.J → GE) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ) (n : ℕ)
    (asks : List (List (List ℕ))) (hbud : budFirst st asks = true) :
    (Prob.unif (Cs ⟨0, dueFresh st⟩)).map (fun c =>
        shownFrom (ownText st v μ (stretchOf c).e D) dep n asks) =
      (Prob.unif (Cs ⟨0, dueFresh st⟩)).map fun c =>
        shownFrom (ownText st v' μ' (stretchOf c).e D) dep n asks := by
  have hb := normal_bij st hk v μ (fun n => D (1 + n)) (askedOf asks)
  have hb' := normal_bij st hk v' μ' (fun n => D (1 + n)) (askedOf asks)
  have e : (fun c : Cs ⟨0, dueFresh st⟩ =>
      shownFrom (ownText st v μ (stretchOf c).e D) dep n asks) =
      (fun c => shownFrom (ownText st v' μ' (stretchOf c).e D) dep n asks) ∘
        ((Equiv.ofBijective _ hb').symm ∘ normal st v μ (fun n => D (1 + n)) (askedOf asks)) := by
    funext c
    exact own_key st hk ha v μ v' μ' D dep n asks hbud c _
      ((Equiv.ofBijective _ hb').apply_symm_apply _).symm
  rw [e, ← PMF.map_comp, Prob.map_unif_of_bijective ((Equiv.bijective _).comp hb)]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tailShare
#print axioms ProofFile.Honest.K12.Light.msgShare
#print axioms ProofFile.Honest.K12.Light.takeUp
#print axioms ProofFile.Honest.K12.Light.ownText
#print axioms ProofFile.Honest.K12.Light.upOf
#print axioms ProofFile.Honest.K12.Light.normal
#print axioms ProofFile.Honest.K12.Light.askedOf
#print axioms ProofFile.Honest.K12.Light.symG_shares
#print axioms ProofFile.Honest.K12.Light.tailShare_add
#print axioms ProofFile.Honest.K12.Light.tailShare_congr
#print axioms ProofFile.Honest.K12.Light.tail_onto
#print axioms ProofFile.Honest.K12.Light.takeUp_spec
#print axioms ProofFile.Honest.K12.Light.getD_const
#print axioms ProofFile.Honest.K12.Light.own_tr
#print axioms ProofFile.Honest.K12.Light.freshCol_len
#print axioms ProofFile.Honest.K12.Light.foldShown_of_vals
#print axioms ProofFile.Honest.K12.Light.cut_idx
#print axioms ProofFile.Honest.K12.Light.stretch_at
#print axioms ProofFile.Honest.K12.Light.normal_lo
#print axioms ProofFile.Honest.K12.Light.tail_lt
#print axioms ProofFile.Honest.K12.Light.normal_hi
#print axioms ProofFile.Honest.K12.Light.normal_bij
#print axioms ProofFile.Honest.K12.Light.own_key
#print axioms ProofFile.Honest.K12.Light.own_law
