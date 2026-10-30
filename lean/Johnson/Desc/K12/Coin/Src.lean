-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Src.lean: THE WRITTEN COLUMNS BEHIND THE OPENINGS OF A PROXIMITY TEST
(`srcFrom`, `srcFirst`, Johnson/Desc/K12/Law/Written.lean) ARE THE COLUMNS OF THE TREES THAT THE
DECLARED OPENINGS NAME. Statements and proofs.

P o x col: a letter: "col is the column at x of the tree that the declared opening o names". The
law's arithmetic deals written trees to the declared openings by counting. Here: under the test on
the plan that holds that arithmetic against the declared sources (`Dealt`,
Johnson/Desc/K12/Law/DealLaw.lean: stage j's one opening has the source "own", number
free + own + (j - 1)), whatever P says of opening number i is said of `srcFrom … i` |
`srcFirst … i`.

  `OwnCols P n c b`: along the chain: at every opening whose source is "own", number n, then n + 1,
    and so on, P's columns are those of the written oracle, in b, of the switch's first round.
  `dealt_one`: a stage j ≥ 1 has its one opening, whether it is the last or not.
  `srcFrom_src`: from a stage j ≥ 1 on. `srcFirst_src`: the whole test behind "BAT"; the first
    switch's openings are asked of the letter gT (`hfirst`).
The inductions follow `wideFrom` and `wideFirst` (Johnson/Desc/K12/Law/ViewWide.lean) step by step.
A tool.
-/
import Johnson.Desc.K12.Law.ViewWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.First (Dealt cutN OneAt nOpen_of_flat take_cut ownN)

abbrev ToldO : Type := Fmt.Shape × Fmt.TreeSource

/-- Along the chain: the tree of own number n is the first switch's, n + 1 the second's, … -/
def OwnCols (P : ToldO → ℕ → List UInt64 → Prop) :
    ℕ → {s : Sg} → (c : OnBytes.Slice.Chain s) → c.Bl → Prop
  | _, _, .last _ _ _ _ _ _ _ => fun _ => True
  | n, _, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun b =>
    (∀ o : ToldO, o.2 = .own n → ∀ x col, P o x col → col = colW dS b.2.1.1.1 x) ∧
      OwnCols P (n + 1) next b.2.2

theorem flat_cut (l : Laid) (k : ℕ) : (l.map (·.1)).flatMap (·.opens) =
    (cutF l k).flatMap (·.opens) ++ (cutS l k).flatMap (·.opens) ++
      ((l.drop (k + 3)).map (·.1)).flatMap (·.opens) := by
  rw [← List.flatMap_append, ← take_cut, ← List.flatMap_append, List.map_drop,
    List.take_append_drop]

theorem flat_nil (cut : List Fmt.DeclaredRound) (hst : ∀ d ∈ cut, d.stored = [])
    (h : nOpen cut = 0) : cut.flatMap (·.opens) = [] := by
  have := nOpen_of_flat cut hst
  rw [h] at this
  exact List.eq_nil_of_length_eq_zero this.symm

theorem mem_cutF (l : Laid) (k : ℕ) (x : Fmt.DeclaredRound) (hx : x ∈ cutF l k) : x ∈ l.map (·.1) := by
  unfold cutF at hx
  rw [List.map_take] at hx
  exact List.mem_of_mem_take hx

theorem dealt_one (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (h : Dealt p j cur rest l) (hj : j ≠ 0) : ∃ o, OneAt p j (cutN cur rest l) o := by
  cases rest with
  | nil => exact h.2.1
  | cons nxt rest => exact h.2.1 hj

theorem srcFrom_src (p : P12) (P : ToldO → ℕ → List UInt64 → Prop) :
    ∀ {s : Sg} (c : OnBytes.Slice.Chain s) (j : ℕ) (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid), stagesOf c = cur :: rest → j ≠ 0 → Dealt p j cur rest l →
    ∀ (d : PQ.RD) (o0 : ToldO), (cutN cur rest l).flatMap (·.opens) = [o0] →
    ∀ (o : (wRound d).Orc) (b : c.Bl), (∀ x col, P o0 x col → col = colW d o x) →
    OwnCols P (p.nums.free + (ownN p + j)) c b → (∀ x ∈ l.map (·.1), x.stored = []) →
    ∀ (i : ℕ) (oi : ToldO), ((l.map (·.1)).flatMap (·.opens))[i]? = some oi →
    ∀ x col, P oi x col → col = srcFrom c d o b l i x := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro j cur rest l hs _ _ d o0 h1 o b hd _ _ i oi hi x col hP
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    have h1' : (l.map (·.1)).flatMap (·.opens) = [o0] := h1
    rw [h1'] at hi
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      exact hd x col hP
    | succ i => simp at hi
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro j cur rest l hs hj hD d o0 h1 o b hd hO hst i oi hi x col hP
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, d2, d3⟩ := hD
      obtain ⟨oc, hoc⟩ := d2 hj
      have hk : s.st.k = s.h + s.g := rfl
      rw [hk] at d1 d3 hoc
      have hcut : cutN s.st (nxt :: rest') l = cutS l (s.h + s.g) := rfl
      rw [hcut] at h1
      have hnS : nOpen (cutS l (s.h + s.g)) = 1 := hoc.nOpen
      obtain ⟨o1, ho1⟩ := dealt_one p (j + 1) nxt rest' _ d3 (Nat.succ_ne_zero j)
      have hz : (cutF l (s.h + s.g)).flatMap (·.opens) = [] :=
        flat_nil _ (fun y hy => hst y (mem_cutF l _ y hy)) d1
      rw [flat_cut l (s.h + s.g), hz, h1, List.nil_append] at hi
      show col = if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then colW d o x
        else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
          (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x
      rw [d1, hnS]
      cases i with
      | zero =>
        rw [if_pos (by omega)]
        obtain rfl := Option.some.inj hi
        exact hd x col hP
      | succ i =>
        rw [if_neg (by omega)]
        have hi' : (((l.drop (s.h + s.g + 3)).map (·.1)).flatMap (·.opens))[i]? = some oi := hi
        have e : i + 1 - (0 + 1) = i := by omega
        rw [e]
        have hsrc : o1.2 = .own (p.nums.free + (ownN p + j)) := by
          rw [ho1.src, Nat.add_sub_cancel]
        exact ih (j + 1) nxt rest' (l.drop (s.h + s.g + 3)) hn (Nat.succ_ne_zero j) d3 dS o1
          ho1.one b.2.1.1.1 b.2.2 (hO.1 o1 hsrc) hO.2
          (fun y hy => hst y (by rw [List.map_drop] at hy; exact List.mem_of_mem_drop hy)) i oi hi'
          x col hP

theorem srcFirst_src (p : P12) (P : ToldO → ℕ → List UInt64 → Prop) {s : Sg}
    (c : OnBytes.Slice.Chain s) (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (hs : stagesOf c = cur :: rest) (hD : Dealt p 0 cur rest l) (ts : List ℕ)
    (gT : ℕ → ℕ → List UInt64)
    (hfirst : ∀ (i : ℕ) (o : ToldO) (x : ℕ) (col : List UInt64),
      ((cutS l cur.k).flatMap (·.opens))[i]? = some o → P o x col → col = gT (ts.getD i 0) x)
    (b : c.Bl) (hO : OwnCols P (p.nums.free + (ownN p + 0)) c b)
    (hst : ∀ x ∈ l.map (·.1), x.stored = []) (i : ℕ) (oi : ToldO)
    (hi : ((l.map (·.1)).flatMap (·.opens))[i]? = some oi) (x : ℕ) (col : List UInt64)
    (hP : P oi x col) : col = srcFirst c b l ts gT i x := by
  cases c with
  | last s e dL dB fu fs εb =>
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    exact absurd rfl hD.1
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, _, d3⟩ := hD
      have hk : s.st.k = s.h + s.g := rfl
      rw [hk] at d1 d3 hfirst
      obtain ⟨o1, ho1⟩ := dealt_one p 1 nxt rest' _ d3 (Nat.succ_ne_zero 0)
      have hz : (cutF l (s.h + s.g)).flatMap (·.opens) = [] :=
        flat_nil _ (fun y hy => hst y (mem_cutF l _ y hy)) d1
      have hstS : ∀ y ∈ cutS l (s.h + s.g), y.stored = [] := fun y hy => hst y (by
        have : y ∈ (l.map (·.1)).take (s.h + s.g + 3) := by
          rw [take_cut]
          exact List.mem_append_right _ hy
        exact List.mem_of_mem_take this)
      have hnS : nOpen (cutS l (s.h + s.g)) = ((cutS l (s.h + s.g)).flatMap (·.opens)).length :=
        nOpen_of_flat _ hstS
      rw [flat_cut l (s.h + s.g), hz, List.nil_append] at hi
      show col = if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
          gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) x
        else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
          (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x
      rw [d1, hnS, Nat.zero_add]
      by_cases hlt : i < ((cutS l (s.h + s.g)).flatMap (·.opens)).length
      · rw [if_pos hlt, Nat.sub_zero]
        rw [List.getElem?_append_left hlt] at hi
        exact hfirst i oi x col hi hP
      · rw [if_neg hlt]
        rw [List.getElem?_append_right (by omega)] at hi
        have hsrc : o1.2 = .own (p.nums.free + (ownN p + 0)) := by
          rw [ho1.src]
        exact srcFrom_src p P next 1 nxt rest' (l.drop (s.h + s.g + 3)) hn (Nat.succ_ne_zero 0) d3
          dS o1 ho1.one b.2.1.1.1 b.2.2 (hO.1 o1 hsrc) hO.2
          (fun y hy => hst y (by rw [List.map_drop] at hy; exact List.mem_of_mem_drop hy)) _ oi hi
          x col hP

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.srcFrom_src
#print axioms VerifiableInference.Desc.K12.Coin.srcFirst_src
