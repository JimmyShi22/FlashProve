-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Attention.lean: the attention block of the array program (ArrayProgram,
IntegerModel/Runnable/ArrayModel.lean) compared with the library's Att.x' and Att.OK
(Inst/Model/Program.lean). attention_is: under Good P, TabRel and SameLayer the block gives some
(Att.x') if Att.OK holds, else none.
-/
import IntegerModel.Runnable.Small

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-! ## The program's text once more, cut into steps ("attention_eq": the same term, by unfolding alone) -/

section Steps
variable (S : ArrayProgram.Shape)
  (t : ArrayProgram.Tables) (s : ArrayProgram.LayerScales) (w : ArrayProgram.LayerWeights) (L : ℕ)

def qRow (ai : Array ℤ) (i : ℕ) : Option (Array ℤ) :=
  ArrayProgram.checked ((ArrayProgram.rotate
      S t L i (ArrayProgram.row (S.heads * S.headDim) fun c => ArrayProgram.dot ai (w.Wq · c))).map
    (ArrayProgram.shiftRound · s.kq))
def kRow (ai : Array ℤ) (i : ℕ) : Option (Array ℤ) :=
  ArrayProgram.checked ((ArrayProgram.rotate S t L i
      (ArrayProgram.row (S.kvHeads * S.headDim) fun c => ArrayProgram.dot ai (w.Wk · c))).map
    (ArrayProgram.shiftRound · s.kk))
def vRow (r : Array ℤ) : Option (Array ℤ) :=
  ArrayProgram.checked (ArrayProgram.project r w.Wv (S.kvHeads * S.headDim) s.kv)

def head2 (v : Array (Array ℤ)) (g : ℕ) (weight : Array ℤ) : Array ℤ :=
  ArrayProgram.row S.headDim fun n =>
    (2 * ArrayProgram.dot weight (fun j => ArrayProgram.at2 v j (S.headDim * g + n)) +
        weight.foldl (· + ·) 0) /
      (2 * weight.foldl (· + ·) 0)
def head1 (v : Array (Array ℤ)) (g : ℕ) (score : Array ℤ) : Array ℤ :=
  head2 S v g
    (score.map fun a =>
      if (score.foldl max score[0]! - a) / 2 ^ s.sh < t.expRows then
        t.exp ((score.foldl max score[0]! - a) / 2 ^ s.sh)
      else 0)
def head0 (q k v : Array (Array ℤ)) (i h : ℕ) : Array ℤ :=
  head1 S t s v (h / (S.heads / S.kvHeads))
    (ArrayProgram.row (i + 1) fun j =>
      (List.range S.headDim).foldl
        (fun a n =>
          a + ArrayProgram.at2 q i (S.headDim * h + n) *
              ArrayProgram.at2 k j (S.headDim * (h / (S.heads / S.kvHeads)) + n)) 0)
def attOut (x q k v : Array (Array ℤ)) (i : ℕ) : Array ℤ :=
  ArrayProgram.row S.d fun c =>
    ArrayProgram.at2 x i c +
      ArrayProgram.shiftRound
        (ArrayProgram.dot ((Array.range S.heads).flatMap fun h => head0 S t s q k v i h) (w.Wo · c))
        s.ko

theorem attention_eq (x : Array (Array ℤ)) : ArrayProgram.attention S t s w L x =
    (x.mapM (ArrayProgram.rmsNorm s.norm1)).bind fun a =>
      ((Array.range x.size).mapM fun i => qRow S t s w L a[i]! i).bind fun q =>
        ((Array.range x.size).mapM fun i => kRow S t s w L a[i]! i).bind fun k =>
          (a.mapM (vRow S s w)).bind fun v =>
            some ((Array.range x.size).map fun i => attOut S t s w x q k v i) := rfl

/-- the block's output depends on a layer's scales through six fields alone: norm1, kq, kk, kv, sh,
ko -/
theorem attention_scales (s' : ArrayProgram.LayerScales) (h1 : s.norm1 = s'.norm1)
    (h2 : s.kq = s'.kq) (h3 : s.kk = s'.kk) (h4 : s.kv = s'.kv) (h5 : s.sh = s'.sh)
    (h6 : s.ko = s'.ko) (x : Array (Array ℤ)) :
    ArrayProgram.attention S t s w L x = ArrayProgram.attention S t s' w L x := by
  have hv : vRow S s w = vRow S s' w := by funext r; simp only [vRow, h4]
  simp only [attention_eq, qRow, kRow, hv, attOut, head0, head1, h1, h2, h3, h5, h6]

end Steps

/-! ## Indices -/

theorem idx_lt {ch a h n : ℕ} (hh : h < a) (hn : n < ch) : ch * h + n < a * ch := by
  have h1 : ch * (h + 1) ≤ ch * a := Nat.mul_le_mul_left _ hh
  rw [Nat.mul_succ, Nat.mul_comm ch a] at h1
  omega

theorem kv_lt {P : Params} (hP : Good P) {h : ℕ} (hh : h < P.nq) : Att.kvOf P h < P.nkv := by
  obtain ⟨h0, m, hm⟩ := hP.kv
  unfold Att.kvOf
  rw [hm, Nat.mul_div_cancel_left m h0]
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hm]; exact hh)

theorem list_flatMap_congr {ι α : Type} {f g : ι → List α} :
    ∀ l : List ι, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
        list_flatMap_congr l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem tabl_flatMap' {α : Type} (n m : ℕ) (G : ℕ → Array α)
    (F : ℕ → ℕ → α) (h : ∀ a < n, G a = tabl m (F a)) :
    (Array.range n).flatMap G = tabl (n * m) fun c => F (c / m) (c % m) := by
  rw [← tabl_flatMap]
  apply Array.toList_inj.1
  rw [Array.toList_flatMap, Array.toList_flatMap]
  exact list_flatMap_congr _ fun a ha => by rw [h a (by simpa using ha)]

/-! ## The block -/

section Block
variable (P : Params) (hP : Good P) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec)

theorem Y'_def (i c : ℕ) :
    Att.Y' P tb w L x i c =
      if c % P.ch % 2 = 0 then
        tb.C L i (c % P.ch / 2) * Att.AY P w x i c -
          tb.S L i (c % P.ch / 2) * Att.AY P w x i (c + 1)
      else
        tb.S L i (c % P.ch / 2) * Att.AY P w x i (c - 1) +
            tb.C L i (c % P.ch / 2) * Att.AY P w x i c := rfl

theorem AY_lt {i c : ℕ} (h : c < Att.dq P) : Att.AY P w x i c = Att.Aq P w x i c := if_pos h
theorem AY_ge (i c : ℕ) : Att.AY P w x i (Att.dq P + c) = Att.Ak P w x i c := by
  unfold Att.AY
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

include hP in
theorem Y'_q {i c : ℕ} (hc : c < Att.dq P) :
    Att.Y' P tb w L x i c =
      if c % P.ch % 2 = 0 then
        tb.C L i (c % P.ch / 2) * Att.Aq P w x i c -
          tb.S L i (c % P.ch / 2) * Att.Aq P w x i (c + 1)
      else
        tb.S L i (c % P.ch / 2) * Att.Aq P w x i (c - 1) +
            tb.C L i (c % P.ch / 2) * Att.Aq P w x i c := by
  rw [Y'_def]
  by_cases he : c % P.ch % 2 = 0
  · rw [if_pos he, if_pos he, AY_lt P w x hc,
      AY_lt P w x (succ_lt_of_even hP.ch ⟨P.nq, Nat.mul_comm _ _⟩ hc he)]
  · rw [if_neg he, if_neg he, AY_lt P w x hc, AY_lt P w x (lt_of_le_of_lt (Nat.sub_le c 1) hc)]

theorem Y'_k (i c : ℕ) :
    Att.Y' P tb w L x i (Att.dq P + c) =
      if c % P.ch % 2 = 0 then
        tb.C L i (c % P.ch / 2) * Att.Ak P w x i c -
          tb.S L i (c % P.ch / 2) * Att.Ak P w x i (c + 1)
      else
        tb.S L i (c % P.ch / 2) * Att.Ak P w x i (c - 1) +
            tb.C L i (c % P.ch / 2) * Att.Ak P w x i c := by
  have hm : (Att.dq P + c) % P.ch = c % P.ch := by
    unfold Att.dq
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [Y'_def, hm]
  by_cases he : c % P.ch % 2 = 0
  · rw [if_pos he, if_pos he, AY_ge, Nat.add_assoc, AY_ge]
  · have h1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at he
      · exact h
    rw [if_neg he, if_neg he, AY_ge, Nat.add_sub_assoc h1, AY_ge]

variable (Tmax : ℕ) (t : ArrayProgram.Tables) (hT : TabRel t tb L P.expRows)
  (W : ArrayProgram.LayerWeights) (hW : SameLayer P L W w)

include hP hT hW in
theorem qRow_is (i : ℕ) :
    Is (qRow (shapeOf P Tmax) t (lsOf P) W L (tabl P.d (Att.a P x i)) i)
      (∀ c < Att.dq P, Fits16 (Att.qkw P tb w L x i c)) (tabl (Att.dq P) (Att.q P tb w L x i)) := by
  have e1 : (ArrayProgram.row ((shapeOf P Tmax).heads * (shapeOf P Tmax).headDim)
        fun c => ArrayProgram.dot (tabl P.d (Att.a P x i)) (W.Wq · c)) =
      tabl (Att.dq P) (Att.Aq P w x i) :=
    tabl_congr fun c hc => (dot_tabl _ _ _).trans (dot_congr fun j hj => hW.Wq j hj c hc)
  have e2 := rotate_tabl (shapeOf P Tmax) t tb L P.expRows hT hP.ch i (Att.dq P)
    ⟨P.nq, Nat.mul_comm _ _⟩ (Att.Aq P w x i)
  have e3 : (ArrayProgram.rotate (shapeOf P Tmax) t L i (tabl (Att.dq P) (Att.Aq P w x i))).map
        (ArrayProgram.shiftRound · (lsOf P).kq) =
      tabl (Att.dq P) (Att.qkw P tb w L x i) := by
    rw [e2, tabl_map]
    refine tabl_congr fun c hc => ?_
    unfold Att.qkw
    rw [if_pos hc, Y'_q P hP tb w L x hc]
    rfl
  unfold qRow
  rw [e1, e3]
  exact checked_is _ _

include hP hT hW in
theorem kRow_is (i : ℕ) :
    Is (kRow (shapeOf P Tmax) t (lsOf P) W L (tabl P.d (Att.a P x i)) i)
      (∀ c < P.nkv * P.ch, Fits16 (Att.qkw P tb w L x i (Att.dq P + c)))
      (tabl (P.nkv * P.ch) (Att.kx P tb w L x i)) := by
  have e1 : (ArrayProgram.row ((shapeOf P Tmax).kvHeads * (shapeOf P Tmax).headDim)
        fun c => ArrayProgram.dot (tabl P.d (Att.a P x i)) (W.Wk · c)) =
      tabl (P.nkv * P.ch) (Att.Ak P w x i) :=
    tabl_congr fun c hc => (dot_tabl _ _ _).trans (dot_congr fun j hj => hW.Wk j hj c hc)
  have e2 := rotate_tabl (shapeOf P Tmax) t tb L P.expRows hT hP.ch i (P.nkv * P.ch)
    ⟨P.nkv, Nat.mul_comm _ _⟩ (Att.Ak P w x i)
  have e3 : (ArrayProgram.rotate (shapeOf P Tmax) t L i (tabl (P.nkv * P.ch) (Att.Ak P w x i))).map
        (ArrayProgram.shiftRound · (lsOf P).kk) =
      tabl (P.nkv * P.ch) fun c => Att.qkw P tb w L x i (Att.dq P + c) := by
    rw [e2, tabl_map]
    refine tabl_congr fun c _ => ?_
    unfold Att.qkw
    rw [Y'_k, if_neg (show ¬ Att.dq P + c < Att.dq P by omega)]
    rfl
  unfold kRow
  rw [e1, e3]
  exact checked_is _ _

include hW in
theorem vRow_is (i : ℕ) :
    Is (vRow (shapeOf P Tmax) (lsOf P) W (tabl P.d (Att.a P x i)))
      (∀ c < P.nkv * P.ch, Fits16 (Att.vw P w x i c)) (tabl (P.nkv * P.ch) (Att.v P w x i)) := by
  have e : ArrayProgram.project (tabl P.d (Att.a P x i)) W.Wv
        ((shapeOf P Tmax).kvHeads * (shapeOf P Tmax).headDim) (lsOf P).kv =
      tabl (P.nkv * P.ch) (Att.vw P w x i) :=
    (project_tabl _ _ _ _ _).trans
      (tabl_congr fun c hc => congrArg (rhu · P.kv) (dot_congr fun j hj => hW.Wv j hj c hc))
  unfold vRow
  rw [e]
  exact checked_is _ _

include hP hT in
/-- one head at one position -/
theorem head0_eq {i h : ℕ} (hi : i < P.T) (hh : h < P.nq) :
    head0 (shapeOf P Tmax) t (lsOf P) (tabl P.T fun i => tabl (Att.dq P) (Att.q P tb w L x i))
        (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.kx P tb w L x i))
        (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.v P w x i)) i h =
      tabl P.ch fun n =>
        (2 * Att.ac P tb w L x h i n + Att.den P tb w L x h i) / (2 * Att.den P tb w L x h i) := by
  have hg := kv_lt hP hh
  have e1 : (ArrayProgram.row (i + 1) fun j =>
        (List.range (shapeOf P Tmax).headDim).foldl
          (fun a n =>
            a + ArrayProgram.at2 (tabl P.T fun i => tabl (Att.dq P) (Att.q P tb w L x i))
                  i ((shapeOf P Tmax).headDim * h + n) *
                ArrayProgram.at2 (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.kx P tb w L x i)) j
                  ((shapeOf P Tmax).headDim *
                      (h / ((shapeOf P Tmax).heads / (shapeOf P Tmax).kvHeads)) + n)) 0) =
      tabl (i + 1) (Att.sc P tb w L x h i) := by
    refine tabl_congr fun j hj => ?_
    rw [foldl_sum]
    exact Finset.sum_congr rfl fun n hn =>
      congrArg₂ (· * ·) (at2_tabl (Att.q P tb w L x) hi (idx_lt hh (Finset.mem_range.1 hn)))
        (at2_tabl (Att.kx P tb w L x) (Nat.lt_of_lt_of_le hj hi)
          (idx_lt hg (Finset.mem_range.1 hn)))
  have e2 : (tabl (i + 1) (Att.sc P tb w L x h i)).foldl
        max (tabl (i + 1) (Att.sc P tb w L x h i))[0]! =
      Att.mx P tb w L x h i := by
    rw [tabl_foldl, tabl_get _ (Nat.succ_pos i)]
    exact foldl_max _ i
  have e3 : ((tabl (i + 1) (Att.sc P tb w L x h i)).map fun a =>
        if (Att.mx P tb w L x h i - a) / 2 ^ (lsOf P).sh < t.expRows then
          t.exp ((Att.mx P tb w L x h i - a) / 2 ^ (lsOf P).sh)
        else 0) =
      tabl (i + 1) (Att.wt P tb w L x h i) := by
    rw [tabl_map, hT.exp, hT.rows]
    rfl
  have e4 : (tabl (i + 1) (Att.wt P tb w L x h i)).foldl (· + ·) 0 = Att.den P tb w L x h i := by
    rw [tabl_foldl]
    exact foldl_sum _ _
  unfold head0
  rw [e1]
  unfold head1
  rw [e2, e3]
  unfold head2
  rw [e4]
  refine tabl_congr (n := P.ch) fun n hn => ?_
  rw [dot_tabl]
  have e5 : dot (i + 1) (Att.wt P tb w L x h i) (fun j =>
        ArrayProgram.at2 (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.v P w x i)) j
          ((shapeOf P Tmax).headDim * (h / ((shapeOf P Tmax).heads / (shapeOf P Tmax).kvHeads)) +
            n)) =
      Att.ac P tb w L x h i n :=
    Finset.sum_congr rfl fun j hj =>
      congrArg (Att.wt P tb w L x h i j * ·)
        (at2_tabl (Att.v P w x) (Nat.lt_of_lt_of_le (Finset.mem_range.1 hj) hi) (idx_lt hg hn))
  rw [e5]

include hP hT hW in
/-- the block's output at one position -/
theorem attOut_eq {i : ℕ} (hi : i < P.T) :
    attOut (shapeOf P Tmax) t (lsOf P) W (tabl P.T fun i => tabl P.d (x i))
        (tabl P.T fun i => tabl (Att.dq P) (Att.q P tb w L x i))
        (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.kx P tb w L x i))
        (tabl P.T fun i => tabl (P.nkv * P.ch) (Att.v P w x i)) i =
      tabl P.d (Att.x' P tb w L x i) := by
  unfold attOut
  rw [show (shapeOf P Tmax).heads = P.nq from rfl,
    tabl_flatMap' P.nq P.ch _
      (fun h n =>
        (2 * Att.ac P tb w L x h i n + Att.den P tb w L x h i) / (2 * Att.den P tb w L x h i))
      fun h hh => head0_eq P hP tb w L x Tmax t hT hi hh]
  refine tabl_congr (n := P.d) fun c hc => ?_
  rw [at2_tabl _ hi hc, dot_tabl, dot_congr fun j hj => hW.Wo j hj c hc]
  rfl

include hP hT hW in
/-- The attention block: under hP, hT, hW the array program computes the library's formulas. -/
theorem attention_is :
    Is (ArrayProgram.attention (shapeOf P Tmax) t (lsOf P) W L (tabl P.T fun i => tabl P.d (x i)))
      (Att.OK P tb w L x) (tabl P.T fun i => tabl P.d (Att.x' P tb w L x i)) := by
  rw [attention_eq, tabl_size]
  have ha : Is ((tabl P.T fun i => tabl P.d (x i)).mapM (ArrayProgram.rmsNorm (lsOf P).norm1))
      (∀ i < P.T, NORM.OK P.n1 P.d (x i)) (tabl P.T fun i => tabl P.d (Att.a P x i)) :=
    Is.mapM_tabl fun i _ => rmsNorm_is P.n1 P.d (x i)
  have hq : Is
      ((Array.range P.T).mapM fun i =>
        qRow (shapeOf P Tmax) t (lsOf P) W L (tabl P.T fun i => tabl P.d (Att.a P x i))[i]! i)
      _ _ :=
    Is.mapM_range fun i hi => by rw [tabl_get _ hi]; exact qRow_is P hP tb w L x Tmax t hT W hW i
  have hk : Is
      ((Array.range P.T).mapM fun i =>
        kRow (shapeOf P Tmax) t (lsOf P) W L (tabl P.T fun i => tabl P.d (Att.a P x i))[i]! i)
      _ _ :=
    Is.mapM_range fun i hi => by rw [tabl_get _ hi]; exact kRow_is P hP tb w L x Tmax t hT W hW i
  have hv : Is
      ((tabl P.T fun i => tabl P.d (Att.a P x i)).mapM (vRow (shapeOf P Tmax) (lsOf P) W)) _ _ :=
    Is.mapM_tabl fun i _ => vRow_is P w L x Tmax W hW i
  refine Is.of ?_ (fun _ => ?_) (Is.bind ha (Is.bind hq (Is.bind hk (Is.bind hv (Is.pure _)))))
  · constructor
    · rintro ⟨a, b, c, d, -⟩ i hi
      refine ⟨a i hi, fun e he => ?_, d i hi⟩
      by_cases hlt : e < Att.dq P
      · exact b i hi e hlt
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
        exact c i hi k (by omega)
    · intro h
      exact ⟨fun i hi => (h i hi).1,
        fun i hi e he => (h i hi).2.1 e (by omega),
        fun i hi e he => (h i hi).2.1 _ (by omega),
        fun i hi => (h i hi).2.2,
        trivial⟩
  · exact tabl_congr fun i hi => attOut_eq P hP tb w L x Tmax t hT W hW hi

end Block

end IntegerModel.Runnable
