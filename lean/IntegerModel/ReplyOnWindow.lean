-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/ReplyOnWindow.lean: the definitions of IntegerModel/Reply.lean compared.
`holdsOnWindow_iff`: `HoldsOnWindow`, a sentence on one pass of the integer program over a request's
1,024 tokens, holds exactly if the request has its form, its reply is the model's (`IsReply`:
`programNextToken` run on the prefix that ends at each covered position) and `programNextToken` has
a value on all 1,024 tokens. `isReply_iff`: `IsReply` is `Says`. `holdsOnWindow_iff_RinfS`:
`HoldsOnWindow` is the relation `RinfS` of Inst/Model/ProgramR.lean. The step between a prefix and
the window is causality: at the positions below n the program on the first n tokens has the same
stream and logits as on the window, and no range condition fails on them if none fails on the window
(part 1).
-/
import IntegerModel.Reply
import Inst.Model.Causal

set_option autoImplicit false

open Inst.Model

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace IntegerModel

/-! ## 1. The first n tokens of a window -/

section Prefix
variable (P : Params) (n : ℕ) (hn : n ≤ P.T)
include hn

theorem Att.OK_prefix (tb : Tables) (w : LayerW) (L : ℕ) {x x' : ℕ → Vec} (h : ∀ i < n, x' i = x i)
    (H : Att.OK P tb w L x) : Att.OK { P with T := n } tb w L x' := by
  intro i hi
  have hi' : i < n := hi
  have e := h i hi'
  have K := H i (lt_of_lt_of_le hi' hn)
  have q : ∀ c, Att.qkw P tb w L x' i c = Att.qkw P tb w L x i c := fun c =>
      by simp only [Att.qkw, Att.Y', Att.AY, Att.Aq, Att.Ak, Att.a, e]
  have v : ∀ c, Att.vw P w x' i c = Att.vw P w x i c := fun c =>
      by simp only [Att.vw, Att.Av, Att.a, e]
  refine ⟨?_, fun c hc => ?_, fun c hc => ?_⟩
  · show NORM.OK P.n1 P.d (x' i)
    rw [e]
    exact K.1
  · show Fits16 (Att.qkw P tb w L x' i c)
    rw [q]
    exact K.2.1 c hc
  · show Fits16 (Att.vw P w x' i c)
    rw [v]
    exact K.2.2 c hc

theorem FF.OK_prefix (tb : Tables) (w : LayerW) (L : ℕ) {x x' : ℕ → Vec} (h : ∀ i < n, x' i = x i)
    (H : FF.OK P tb w L x) : FF.OK { P with T := n } tb w L x' := by
  intro i hi
  have hi' : i < n := hi
  have e := h i hi'
  have K := H i (lt_of_lt_of_le hi' hn)
  have hm : FF.m P x' i = FF.m P x i := by unfold FF.m; rw [e]
  have hlw : FF.lw P w x' i = FF.lw P w x i := by funext e; simp only [FF.lw, hm]
  have hl3 : FF.l3 P w x' i = FF.l3 P w x i := by funext e; simp only [FF.l3, hlw]
  have hly : FF.ly P w x' i = FF.ly P w x i := by funext e; simp only [FF.ly, hlw, hl3]
  have hlr : FF.lr P w x' i = FF.lr P w x i := by funext e; simp only [FF.lr, hly, hl3]
  have hes : FF.es P w x' i = FF.es P w x i := by simp only [FF.es, hlr]
  have hmr : FF.mr P w x' i = FF.mr P w x i := by simp only [FF.mr, hlr, hes]
  have hsc : FF.sc P tb w x' i = FF.sc P tb w x i := by simp only [FF.sc, hmr]
  have hxr : FF.xr P tb w x' i = FF.xr P tb w x i := by funext j; simp only [FF.xr, hsc, hm]
  have hz : ∀ j, FF.z P tb w L x' i j = FF.z P tb w L x i j := fun j => by simp only [FF.z, hxr, hm]
  have hwg : ∀ j, FF.wg P w L x' i j = FF.wg P w L x i j := fun j =>
      by funext t; simp only [FF.wg, hes]
  have hwu : ∀ j, FF.wu P w L x' i j = FF.wu P w L x i j := fun j =>
      by funext t; simp only [FF.wu, hes]
  refine ⟨?_, fun hE c hc => ?_, fun j hj => ?_⟩
  · show NORM.OK P.n2 P.d (x' i)
    rw [e]
    exact K.1
  · show Fits16 (FF.ly P w x' i c)
    rw [hly]
    exact K.2.1 hE c hc
  · show UNIT.OK P.d (FF.z P tb w L x' i j) (FF.wg P w L x' i j) (FF.wu P w L x' i j) (FF.kG P L j)
        (FF.kU P L j)
    rw [hz, hwg, hwu]
    exact K.2.2 j hj

variable (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (i : Inst.Model.Weights)
    (p : Fin P.T → Fin P.V) (p' : Fin n → Fin P.V)
  (h : ∀ t (ht : t < n), p' ⟨t, ht⟩ = p ⟨t, lt_of_lt_of_le ht hn⟩)
include h

/-- At the positions below n, the program on the first n tokens has the same residual stream (`XK`)
as on the window. -/
theorem XK_prefix : ∀ l pos, pos < n → XK { P with T := n } κ tbs i p' l pos = XK P κ tbs i p l pos
  | 0, pos, hp => by
      funext j
      show (if h : pos < n then i.Emb (p' ⟨pos, h⟩) j else 0) = if h : pos < P.T then i.Emb
          (p ⟨pos, h⟩) j else 0
      rw [dif_pos hp, dif_pos (lt_of_lt_of_le hp hn), h pos hp]
  | l + 1, pos, hp => by
      show (if l % 2 = 0 then Att.x' (P.at (κ (l / 2))) _ _ _ (XK { P with T := n } κ tbs i p' l)
          else FF.x'' (P.at (κ (l / 2))) _ _ _ (XK { P with T := n } κ tbs i p' l)) pos
        = (if l % 2 = 0 then Att.x' (P.at (κ (l / 2))) _ _ _ (XK P κ tbs i p l) else FF.x'' (P.at (κ
            (l / 2))) _ _ _ (XK P κ tbs i p l)) pos
      split
      · exact Att.x'_congr _ _ _ _ fun j hj => XK_prefix l j (lt_of_le_of_lt hj hp)
      · exact FF.x''_congr _ _ _ _ (XK_prefix l pos hp)

theorem lgK_prefix {pos : ℕ} (hp : pos < n) : lgK { P with T := n } κ nf tbs i p' pos = lgK P κ nf
    tbs i p pos := by
  funext v
  show dot P.d (NORM.out nf P.d (XK { P with T := n } κ tbs i p' (2 * P.layers) pos)) _ = dot P.d
      (NORM.out nf P.d (XK P κ tbs i p (2 * P.layers) pos)) _
  rw [XK_prefix P n hn κ tbs i p p' h _ pos hp]

/-- If no range condition fails on the window, none fails on its first n tokens. -/
theorem RunsK_prefix (H : RunsK P κ nf tbs i p) : RunsK { P with T := n } κ nf tbs i p' :=
  ⟨fun L hL => ⟨Att.OK_prefix (P.at (κ L)) n hn _ _ _ (fun j hj => XK_prefix P n hn κ tbs i p p' h _
      j hj) (H.1 L hL).1,
      FF.OK_prefix (P.at (κ L)) n hn _ _ _ (fun j hj => XK_prefix P n hn κ tbs i p p' h _ j hj)
          (H.1 L hL).2⟩,
    fun pos hp => by
      show NORM.OK nf P.d (XK { P with T := n } κ tbs i p' (2 * P.layers) pos)
      rw [XK_prefix P n hn κ tbs i p p' h _ pos hp]
      exact H.2 pos (lt_of_lt_of_le hp hn)⟩
end Prefix

theorem argTo_unique (f : Vec) (n a : ℕ) (ha : a ≤ n) (h1 : ∀ v ≤ n, f v ≤ f a)
    (h2 : ∀ v < a, f v < f a) : argTo f n = a := by
  obtain ⟨b0, b1, b2⟩ := argTo_spec f n
  rcases Nat.lt_trichotomy (argTo f n) a with h | h | h
  · exact absurd (b1 a ha) (not_le.2 (h2 _ h))
  · exact h
  · exact absurd (h1 _ b0) (not_le.2 (b2 a h))

/-- From a pass over a window to the model on a context. If `ctx` is a nonempty prefix of the
window, the program runs on the window, and y is the least token with the largest logit at the last
position of `ctx`, then `programNextToken m ctx = some y`. -/
theorem model_of_window (m : Committed) (toks : Fin ppref.T → Fin ppref.V) (ctx : List Token)
    (h0 : 0 < ctx.length) (hn : ctx.length ≤ ppref.T)
    (hget : ∀ t (ht : t < ctx.length), ctx.get ⟨t, ht⟩ = toks ⟨t, lt_of_lt_of_le ht hn⟩)
        (hr : RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks)
        (y : Token)
    (h1 : ∀ v < ppref.V, lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks
        (ctx.length - 1) v ≤ lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
        toks (ctx.length - 1) y)
    (h2 : ∀ v < y.val, lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks
        (ctx.length - 1) v < lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
        toks (ctx.length - 1) y) :
    programNextToken m ctx = some y := by
  have hV : 0 < ppref.V := by decide
  have e : lgK (arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
      (fun i => ctx.get i) (ctx.length - 1) = lgK ppref m.settings.kap m.settings.nf
      (fun _ => tbRef) m.weights.val toks (ctx.length - 1) :=
    lgK_prefix ppref ctx.length hn m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks
        (fun i => ctx.get i) hget (by omega)
  unfold programNextToken
  rw [if_pos ⟨h0, hn, RunsK_prefix ppref ctx.length hn m.settings.kap m.settings.nf (fun _ => tbRef)
      m.weights.val toks (fun i => ctx.get i) hget hr⟩]
  refine congrArg some (Fin.ext ?_)
  simp only [e]
  exact argTo_unique _ _ _ (by have := y.isLt; omega) (fun v hv => h1 v (by omega)) h2

theorem firstToks_succ (x : Request) (t : ℕ) : firstToks x (t + 1) ++ [⟨x.w t, x.w_lt t⟩] =
    firstToks x (t + 2) := by
  show _ = (List.range (t + 1 + 1)).map _
  rw [List.range_succ, List.map_append]
  rfl

theorem greedy_of_window (f : List Token → Option Token) (x : Request)
    (hf : ∀ t, x.r ≤ t → t < x.e → f (firstToks x (t + 1)) = some ⟨x.w t, x.w_lt t⟩) :
    ∀ k t, x.r ≤ t → t + k ≤ x.e → greedyOutput f (firstToks x (t + 1)) k = some
        ((List.range k).map fun j => ⟨x.w (t + j), x.w_lt _⟩)
  | 0, _, _, _ => rfl
  | k + 1, t, h1, h2 => by
      show (match f (firstToks x (t + 1)) with
        | none => none
        | some y => (greedyOutput f (firstToks x (t + 1) ++ [y]) k).map (y :: ·)) = _
      rw [hf t h1 (by omega)]
      show (greedyOutput f (firstToks x (t + 1) ++ [⟨x.w t, x.w_lt t⟩]) k).map _ = _
      rw [firstToks_succ, greedy_of_window f x hf k (t + 1) (by omega) (by omega),
          List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg some (congrArg₂ List.cons rfl (List.map_congr_left fun j _ => Fin.ext ?_))
      show x.w (t + 1 + j) = x.w (t + (j + 1))
      rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem firstToks_length (x : Request) (k : ℕ) : (firstToks x k).length = k := by simp [firstToks]

theorem firstToks_get (x : Request) (k : ℕ) (hk : k ≤ ppref.T) (t : ℕ)
    (ht : t < (firstToks x k).length) :
    (firstToks x k).get ⟨t, ht⟩ = x.prompt ⟨t, lt_of_lt_of_le (firstToks_length x k ▸ ht) hk⟩ := by
  have h2 : t < ppref.T := lt_of_lt_of_le (firstToks_length x k ▸ ht) hk
  refine Fin.ext ?_
  simp only [firstToks, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  show x.tok t = _
  unfold Instance.tok
  rw [dif_pos h2]

/-- `HoldsOnWindow` implies `Says`. -/
theorem says_of_holdsOnWindow {m : Committed} {x : Request}
    (h : HoldsOnWindow m.settings m.weights x) : Says m x :=
  ⟨h.1.1, fun t h1 h2 => by
    have hlen := firstToks_length x (t + 1)
    have he := h.1.2.1
    have e : (firstToks x (t + 1)).length - 1 = t := by omega
    exact model_of_window m x.prompt (firstToks x (t + 1)) (by omega) (by omega)
        (fun j hj => firstToks_get x (t + 1) (by omega) j hj) h.2.1 ⟨x.w t, x.w_lt t⟩
      (by rw [e]; exact (h.2.2 t h1 h2).1) (by rw [e]; exact (h.2.2 t h1 h2).2)⟩

theorem isReply_of_says (m : Committed) (x : Request) (h : Says m x) : IsReply m x :=
  ⟨h.1, greedy_of_window (programNextToken m) x h.2 (x.e - x.r) x.r le_rfl (by have := h.1; omega)⟩

theorem says_of_greedy (f : List Token → Option Token) (x : Request) : ∀ k t, greedyOutput f
    (firstToks x (t + 1)) k = some ((List.range k).map fun j => (⟨x.w (t + j), x.w_lt _⟩ : Token)) →
    ∀ j, j < k → f (firstToks x (t + j + 1)) = some ⟨x.w (t + j), x.w_lt _⟩
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, t, h, j, hj => by
      have h' : (match f (firstToks x (t + 1)) with
        | none => none
        | some y => (greedyOutput f (firstToks x (t + 1) ++ [y]) k).map (y :: ·)) = some
            ((List.range (k + 1)).map fun j => (⟨x.w (t + j), x.w_lt _⟩ : Token)) := h
      cases hf : f (firstToks x (t + 1)) with
      | none =>
        rw [hf] at h'
        exact absurd h' (by simp)
      | some y =>
        rw [hf] at h'
        have h'' : (greedyOutput f (firstToks x (t + 1) ++ [y]) k).map (y :: ·) = some
            ((List.range (k + 1)).map fun j => (⟨x.w (t + j), x.w_lt _⟩ : Token)) := h'
        cases hg : greedyOutput f (firstToks x (t + 1) ++ [y]) k with
        | none =>
          rw [hg] at h''
          exact absurd h'' (by simp)
        | some l =>
          rw [hg, List.range_succ_eq_map, List.map_cons, List.map_map] at h''
          have h3 : y :: l = (⟨x.w (t + 0), x.w_lt _⟩ : Token) :: (List.range k).map
              ((fun j => (⟨x.w (t + j), x.w_lt _⟩ : Token)) ∘ Nat.succ) := Option.some.inj h''
          obtain ⟨hy, hl⟩ := List.cons.inj h3
          cases j with
          | zero =>
            show f (firstToks x (t + 0 + 1)) = some ⟨x.w (t + 0), x.w_lt _⟩
            rw [← hy]
            exact hf
          | succ j =>
            have hy' : y = ⟨x.w t, x.w_lt t⟩ := hy
            have hrec : greedyOutput f (firstToks x (t + 1 + 1)) k = some
                ((List.range k).map fun j => (⟨x.w (t + 1 + j), x.w_lt _⟩ : Token)) := by
              rw [← firstToks_succ x t, ← hy', hg, hl]
              refine congrArg some (List.map_congr_left fun i _ => Fin.ext ?_)
              show x.w (t + (i + 1)) = x.w (t + 1 + i)
              rw [Nat.add_assoc, Nat.add_comm 1 i]
            have r := says_of_greedy f x k (t + 1) hrec j (by omega)
            have e : t + (j + 1) = t + 1 + j := by omega
            rw [e]
            exact r

theorem says_of_isReply (m : Committed) (x : Request) (h : IsReply m x) : Says m x :=
  ⟨h.1, fun t h1 h2 => by
    have g := says_of_greedy (programNextToken m) x (x.e - x.r) x.r h.2 (t - x.r) (by omega)
    have e : x.r + (t - x.r) = t := by omega
    rw [e] at g
    exact g⟩

theorem greedy_pos {f : List Token → Option Token} {ctx l : List Token} {n : ℕ} (hn : 0 < n)
    (h : greedyOutput f ctx n = some l) : f ctx ≠ none := by
  cases n with
  | zero => omega
  | succ k =>
    intro hf
    unfold greedyOutput at h
    rw [hf] at h
    cases h

/-! ## 2. From the model's answers back to the sentence on one pass over the window -/

section Back

/- Keep Lean from unfolding `firstToks x 1024` or `argTo f (ppref.V - 1)`. -/
attribute [local irreducible] Inst.Model.argTo Inst.Model.lgK Inst.Model.RunsK
    IntegerModel.firstToks

/-- What `programNextToken m ctx = some y` implies: the conditions on the length and the ranges, and
y is `argTo` of the logits at the last position. -/
theorem model_some {m : Committed} {ctx : List Token} {y : Token}
    (h : programNextToken m ctx = some y) :
    (0 < ctx.length ∧ ctx.length ≤ ppref.T ∧ RunsK (arch ctx.length) m.settings.kap m.settings.nf
        (fun _ => tbRef) m.weights.val (fun i => ctx.get i)) ∧
      argTo (lgK (arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val (fun
          i => ctx.get i) (ctx.length - 1)) (ppref.V - 1) = y.val := by
  unfold programNextToken at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc, rfl⟩
  · exact absurd h (by simp)

theorem form_of_requestWellFormed {x : Request} (h : requestWellFormed x = true) : x.r < x.e ∧ x.e ≤
    ppref.T ∧ (x.e < ppref.T → x.y.val = 0) := by
  unfold requestWellFormed at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
  exact ⟨h.1.1, h.1.2, fun hlt => h.2.resolve_left fun hn => hn hlt⟩

theorem requestWellFormed_of_form {x : Request}
    (h : x.r < x.e ∧ x.e ≤ ppref.T ∧ (x.e < ppref.T → x.y.val = 0)) : requestWellFormed x = true :=
    by
  unfold requestWellFormed
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  by_cases hlt : x.e < ppref.T
  · exact Or.inr (h.2.2 hlt)
  · exact Or.inl hlt

/-- If `ctx` has full length and holds the window's tokens, and no range condition fails at T := its
length, none fails on the window. `ctx` is a variable here, so that Lean does not evaluate a list of
1,024 tokens. -/
theorem runs_of_full (m : Committed) (toks : Fin ppref.T → Fin ppref.V) (ctx : List Token)
    (hlen : ctx.length = ppref.T)
    (hget : ∀ t (ht : t < ppref.T) (ht' : t < ctx.length), toks ⟨t, ht⟩ = ctx.get ⟨t, ht'⟩)
        (h : RunsK (arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
        (fun i => ctx.get i)) :
    RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks :=
  RunsK_prefix (arch ctx.length) ppref.T (le_of_eq hlen.symm) m.settings.kap m.settings.nf
      (fun _ => tbRef) m.weights.val (fun i => ctx.get i) toks (fun t ht => hget t ht _) h

/-- The converse direction. If the request has the required form, `programNextToken`'s answer on the
tokens up to each covered position is the checked token, and `programNextToken` answers on all 1,024
tokens, then `HoldsOnWindow` holds. -/
theorem holdsOnWindow_of_says {m : Committed} {x : Request} (hform : requestWellFormed x = true)
    (hS : Says m x) (hrun : (programNextToken m (firstToks x 1024)).isSome = true) : HoldsOnWindow
    m.settings m.weights x := by
  have hV : 0 < ppref.V := by decide
  have hT : ppref.T = 1024 := by decide
  obtain ⟨y0, hy0⟩ := Option.isSome_iff_exists.1 hrun
  have hc := (model_some hy0).1
  have hlen : (firstToks x 1024).length = 1024 := firstToks_length x 1024
  have hr : RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt :=
    runs_of_full m x.prompt (firstToks x 1024) (by omega)
        (fun t _ ht' => (firstToks_get x 1024 (by omega) t ht').symm) hc.2.2
  refine ⟨form_of_requestWellFormed hform, hr, fun t h1 h2 => ?_⟩
  obtain ⟨hc', ha⟩ := model_some (hS.2 t h1 h2)
  have hl : (firstToks x (t + 1)).length = t + 1 := firstToks_length x (t + 1)
  have hn : (firstToks x (t + 1)).length ≤ ppref.T := hc'.2.1
  have e : lgK (arch (firstToks x (t + 1)).length) m.settings.kap m.settings.nf (fun _ => tbRef)
      m.weights.val (fun i => (firstToks x (t + 1)).get i) ((firstToks x (t + 1)).length - 1)
      = lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt
          ((firstToks x (t + 1)).length - 1) :=
    lgK_prefix ppref _ hn m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt
        (fun i => (firstToks x (t + 1)).get i) (fun j hj => firstToks_get x (t + 1) (by omega) j hj)
        (by omega)
  have e1 : (firstToks x (t + 1)).length - 1 = t := by omega
  rw [e, e1] at ha
  have ha' : argTo (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt
      t) (ppref.V - 1) = x.w t := ha
  obtain ⟨-, b1, b2⟩ := argTo_spec
      (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt t)
      (ppref.V - 1)
  rw [ha'] at b1 b2
  exact ⟨fun v hv => b1 v (by omega), fun v hv => b2 v hv⟩

/-- Where the program runs on the window, `programNextToken` answers on every nonempty prefix of the
window (`ctx` is a variable, as in `runs_of_full`). -/
theorem model_isSome_of_window (m : Committed) (toks : Fin ppref.T → Fin ppref.V) (ctx : List Token)
    (h0 : 0 < ctx.length) (hn : ctx.length ≤ ppref.T)
    (hget : ∀ t (ht : t < ctx.length), ctx.get ⟨t, ht⟩ = toks ⟨t, lt_of_lt_of_le ht hn⟩)
        (hr : RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val toks) :
        (programNextToken m ctx).isSome = true := by
  unfold programNextToken
  rw [if_pos ⟨h0, hn, RunsK_prefix ppref ctx.length hn m.settings.kap m.settings.nf (fun _ => tbRef)
      m.weights.val toks (fun i => ctx.get i) hget hr⟩]
  rfl

theorem holdsOnWindow_iff_aux (m : Committed) (x : Request) :
    HoldsOnWindow m.settings m.weights x ↔
        (requestWellFormed x = true ∧ IsReply m x ∧ (programNextToken m (firstToks x 1024)).isSome =
        true) := by
  have hT : ppref.T = 1024 := by decide
  have hlen : (firstToks x 1024).length = 1024 := firstToks_length x 1024
  refine ⟨fun h => ⟨requestWellFormed_of_form h.1, isReply_of_says m x (says_of_holdsOnWindow h),
      ?_⟩, fun h => holdsOnWindow_of_says h.1 (says_of_isReply m x h.2.1) h.2.2⟩
  exact model_isSome_of_window m x.prompt (firstToks x 1024) (by omega) (by omega)
      (fun t ht => firstToks_get x 1024 (by omega) t ht) h.2.1

end Back

/-! ## 3. The statements -/

/-- The two forms of "the reply is the model's" are equivalent. -/
theorem isReply_iff (m : Committed) (x : Request) : IsReply m x ↔ Says m x :=
    ⟨says_of_isReply m x, isReply_of_says m x⟩

/-- `HoldsOnWindow` is equivalent to: the request has the required form, the reply is the
model's, and `programNextToken` answers on all 1,024 tokens of the window. So `IsReply` omits from
`HoldsOnWindow`: y = 0 where e < 1,024 (e ≤ 1,024 is in the request's type), and the range
conditions at the positions e .. 1,023 (none at e = 1,024). These two clauses do not follow from
`IsReply`. For `Cm.TrueAt`, which is this sentence (IntegerModel/TrueRequest.lean), `Cm.filler`
(Cm/RelTrueExp.lean) has two requests with the same r, e, y (r = 0, e = 1) and tokens 0 .. 1,022,
one true and one not, and `Cm.false_form` (Cm/RelTrue.lean) says that a request without its form is
not true; that `IsReply` reads only r, e and the tokens 0 .. e is seen from its definition, and no
theorem states it. -/
theorem holdsOnWindow_iff (m : Committed) (x : Request) :
    HoldsOnWindow m.settings m.weights x ↔
        (requestWellFormed x = true ∧ IsReply m x ∧ (programNextToken m (firstToks x 1024)).isSome =
        true) := holdsOnWindow_iff_aux m x

/-- `HoldsOnWindow` is the relation at exact match of Inst/Model/ProgramR.lean, which is written
without a policy. -/
theorem holdsOnWindow_iff_RinfS (pp : ScalesAndPolicy) (i : Index ppref) (x : Instance ppref) : HoldsOnWindow pp
    i x ↔ RinfS ppref pp.kap pp.nf (fun _ => tbRef) i x :=
  ⟨fun ⟨c, b, d⟩ => ⟨b, c, fun t h1 h2 => (gapOf_eq_zero_iff _ _ (x.w_lt t)).2 (d t h1 h2)⟩, fun
      ⟨b, c, d⟩ => ⟨c, b, fun t h1 h2 => (gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (d t h1 h2)⟩⟩

end IntegerModel
