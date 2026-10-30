-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/NamesOwn.lean: the honest side of the kind "lookup" (K3):
from the hearing's return, on any rounds, at any face: every form of the lookup's runs of claims
names slots of the lookup's own window alone: the statement `NamesOwn`
(Honest/K3/GoodDrawsLaw.lean), at its own name. Theorems; four definitions.

Terms. Honest/K3/GLOSSARY.md: see there hearing, form, slot, row, run (of claims), sumcheck, key
tree, tie and leaves. In this file: the lookup's own window is the stretch of slots from the
ledger's count in front, as many as the face's slots.

What is shown.
  `In lo hi a`: every slot that the form a names lies from lo on and below hi.
  `AllIn`, `CarriedIn`, `TieIn`: the like of an array of rows; of what a run of levels carries; of
    what the tie's fold carries.
  `in_mono` to `in_onSlots`, `in_rowAff`, `in_stepDown`, `in_joinForm`: the makers of forms.
  `hear_names`, `row_names`, `whole_names`: the masked sumcheck's texts: where the structure's slots
    lie; the count behind; the row names its own slots and those of the form that it was given.
  `sumV_names`, `level_names`, `run_names`, `tieV_names`, `partsV_names`, `keysV_names`: the
    hearing's pieces.
  `heard_names`: what was heard: every row, every key tree's last form, the leaves' structure, the
    bits' slot.
  `namesOwn`: the statement `NamesOwn`.

Hypotheses that remain. The hearing's return alone, which stands inside `NamesOwn`, with the return
of the claims on the planes behind it: no course, no coin, and no hypothesis on the ledger's arrays.
`heard_names` has `h` (`messagesV` returns) and `h2`: two planes at least.
In the pieces: `h`, `hh`, `hr`, `hw`, `e`: the routine returns. `hC`, `hs`, `hk`, `hf`, `ha`, `hb`,
`hy`: `In` (or `AllIn`, `CarriedIn`) of what goes in. `hg`: (in `in_foldl`) the step g keeps `In`.
`hlo`, `hh`, `h1` to `h4`: bounds on lo, hi and the slots that come in. `hf`: (in `foldlM_keeps`,
`foldlM_count`) each step keeps the property, or counts one on. `h` has three more senses: `In` or
`AllIn` of what goes in (`in_mono`, `allIn_mono`, `allIn_push`), bounds on the planes' slots
(`in_joinForm`), a membership (`mem_push`).

Users. Honest/K3/Good/Coef.lean, Honest/K3/Law/Thread/PadNamesOf.lean [not in this library],
Honest/K3/Parts/NamesMarks.lean, Honest/K3/Parts/NoEntries.lean and Honest/K3/Shape/Window.lean
import this file.

Limits. It says which slots are named, not with which coefficient. Entries of virtual rows are not
spoken of here. Shown in: NoEntries.lean (`hearV_ne`, `planesV_ne`): the forms name none, from the
same two returns.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.GoodDrawsLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedWorth
import Johnson.Desc.First.K4.RunsCore
import Johnson.Desc.Part.MaskedSumJoint
import Johnson.Desc.Part.MaskedSumReady

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff orderDefault eqTab)
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV messagesV planesV Hr drawsV drawV sumV
  openV tieV partsV
  keysV noVar leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried stepDown level_spec)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Forward (joinForm)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {α β γ : Type}

/-! ## Forms that name slots of a window alone -/

/-- Every slot that the form names lies from lo on and below hi. -/
def In (lo hi : Nat) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, lo ≤ x.1 ∧ x.1 < hi

theorem in_mono {lo hi hi' : Nat} {a : Aff} (h : In lo hi a) (hh : hi ≤ hi') : In lo hi' a :=
  fun x hx => ⟨(h x hx).1, Nat.lt_of_lt_of_le (h x hx).2 hh⟩

theorem in_ofConst (lo hi : Nat) (v : E) : In lo hi (Aff.ofConst v) := by
  intro x hx
  simp [Aff.ofConst] at hx

theorem in_empty (lo hi : Nat) : In lo hi {} := by
  intro x hx
  simp at hx

theorem in_slot {lo hi j : Nat} (h1 : lo ≤ j) (h2 : j < hi) : In lo hi (Aff.slot j) := by
  intro x hx
  have e : x = (j, oneE) := by simpa [Aff.slot] using hx
  rw [e]
  exact ⟨h1, h2⟩

theorem in_addMul {lo hi : Nat} {a b : Aff} (ha : In lo hi a) (hb : In lo hi b) (k : E) :
    In lo hi (Aff.addMul a b k) := by
  intro x hx
  have hx' : x ∈ (b.slots.foldl (fun l y => l.push (y.1, mulE y.2 k)) a.slots).toList := hx
  rw [OnBytes.Model.foldl_push_toList (fun y : Nat × E => (y.1, mulE y.2 k))] at hx'
  rcases List.mem_append.1 hx' with h | h
  · exact ha x h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact hb y hy

theorem in_scale {lo hi : Nat} {a : Aff} (ha : In lo hi a) (k : E) : In lo hi (Aff.scale a k) :=
  in_addMul (in_empty lo hi) ha k

theorem in_add {lo hi : Nat} {a b : Aff} (ha : In lo hi a) (hb : In lo hi b) : In lo hi (a + b) :=
  in_addMul ha hb oneE

theorem in_sub {lo hi : Nat} {a b : Aff} (ha : In lo hi a) (hb : In lo hi b) : In lo hi (a - b) :=
  in_addMul ha hb (subE zeroE oneE)

theorem in_onFold {lo hi : Nat} : ∀ (u : List E) (first : Nat) (f : Aff), In lo hi f → lo ≤ first →
    first + u.length ≤ hi →
    In lo hi (u.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x))
      (first, f)).2
  | [], _, _, hf, _, _ => hf
  | x :: u, first, f, hf, h1, h2 => by
    rw [List.foldl_cons]
    have h2' : first + (u.length + 1) ≤ hi := h2
    exact in_onFold u (first + 1) _ (in_addMul hf (in_slot h1 (by omega)) x) (by omega) (by omega)

theorem in_onSlots {lo hi first : Nat} {f : Aff} {u : List E} (hf : In lo hi f) (h1 : lo ≤ first)
    (h2 : first + u.length ≤ hi) : In lo hi (MaskedSum.onSlots f first u) :=
  in_onFold u first f hf h1 h2

theorem in_rowAff {lo hi : Nat} (h : MaskedSum.Heard) (S0 : E) {kept : Aff} (hs : In lo hi h.start)
    (hk : In lo hi kept) (h1 : lo ≤ h.first)
    (h2 : h.first + (MaskedSum.hidingAt (h.vars.zip h.r)).1.length ≤ hi) :
    In lo hi (MaskedSum.rowAff h S0 kept) := by
  unfold MaskedSum.rowAff
  exact in_addMul (in_addMul (in_onSlots (in_ofConst _ _ _) h1 h2)
    (in_sub (in_ofConst _ _ _) hs) _) hk _

theorem in_stepDown {lo hi : Nat} (o : LevelOut) (h1 : lo ≤ o.sL) (h2 : o.sL < hi) (h3 : lo ≤ o.sR)
    (h4 : o.sR < hi) : In lo hi (stepDown o).2 :=
  in_add (in_scale (in_slot h1 h2) _) (in_scale (in_slot h3 h4) _)

theorem in_foldl {lo hi : Nat} (g : Aff → Nat → Aff) (hg : ∀ c j, In lo hi c → In lo hi (g c j)) :
    ∀ (l : List Nat) (c : Aff), In lo hi c → In lo hi (l.foldl g c)
  | [], _, hc => hc
  | j :: l, c, hc => in_foldl g hg l _ (hg c j hc)

theorem in_joinForm {lo hi : Nat} (f : LFace) (sG : Array Nat) (rho : Array E)
    (h : ∀ j, j < f.planes → lo ≤ sG.getD j 0 ∧ sG.getD j 0 < hi) :
    In lo hi (joinForm f sG rho) := by
  unfold joinForm
  refine in_foldl _ (fun c j hc => ?_) _ _ (in_ofConst _ _ _)
  by_cases hj : j < f.planes
  · simp only [if_pos hj]
    exact in_addMul hc (in_slot (h j hj).1 (h j hj).2) _
  · simp only [if_neg hj]
    exact in_add hc (in_ofConst _ _ _)

/-! ## The masked sumcheck's texts -/

theorem lens_len : ∀ {vs : List MaskedSum.Var} {l : List (List E × E)}, MaskedSum.Lens vs l →
    l.length = vs.length
  | [], [], _ => rfl
  | _ :: vs, _ :: l, h => by
    have h' := lens_len (vs := vs) (l := l) h.2.2
    simp [h']
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Where a hearing's structure's slots lie, and the count behind. -/
theorem hear_names {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) :
    h.start = C ∧ h.first = F.next ∧ h.sEnd = F.next + MaskedSum.ownSlots k.all ∧
      G.next = h.sEnd + k.endsN ∧
      (MaskedSum.hidingAt (h.vars.zip h.r)).1.length ≤ MaskedSum.ownSlots k.all := by
  obtain ⟨hs, T, R, _, hR, he, hG⟩ := MaskedSum.hear_spec hh
  have hn := (hideRun_core hG).next
  have hl := lens_len (MaskedSum.readAll_lens hs hR)
  have hle := MaskedSum.hidingAt_length_le (h.vars.zip h.r)
  have hfst : (h.vars.zip h.r).map (·.1) = k.all := by
    rw [he]
    exact List.map_fst_zip (by simp [hl])
  rw [hfst] at hle
  refine ⟨by rw [he], by rw [he], by rw [he], ?_, hle⟩
  rw [hn, he]
  show F.next + MaskedSum.ownSlots k.all + R.values.length = _
  rw [MaskedSum.readAll_values_len hR]

/-- A row names its sumcheck's own slots, and those of the form that the sumcheck was given and of
the kept term. -/
theorem row_names {lo hi : Nat} {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) (hs : In lo hi h.start) (hk : In lo hi kept)
    (h1 : lo ≤ h.first) (h2 : h.first + (MaskedSum.hidingAt (h.vars.zip h.r)).1.length ≤ hi) :
    In lo hi f ∧ G.next = F.next := by
  rw [MaskedSum.row_spec hr]
  exact ⟨in_rowAff h S0 hs hk h1 h2, (hideRun_core (MaskedSum.row_write hr)).next⟩

theorem whole_names {lo : Nat} {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) (hC : In lo F.next C)
    (hlo : lo ≤ F.next) :
    In lo G.next f ∧ F.next ≤ h.sEnd ∧ G.next = h.sEnd + k.endsN := by
  obtain ⟨_, G1, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_names hh
  obtain ⟨b1, b2⟩ := row_names (lo := lo) (hi := G1.next) hr
    (by rw [a1]; exact in_mono hC (by omega)) (in_empty _ _) (by omega) (by omega)
  rw [b2]
  exact ⟨b1, by omega, a4⟩

/-! ## The hearing's pieces -/

theorem sumV_names {lo : Nat} {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs rest : List Fmt.RoundView} {x : MaskedSum.Heard × Aff}
    (e : sumV C k endTerm F rs = some (x, G, rest)) (hC : In lo F.next C) (hlo : lo ≤ F.next) :
    In lo G.next x.2 ∧ F.next ≤ x.1.sEnd ∧ G.next = x.1.sEnd + k.endsN :=
  whole_names (sumV_whole e) hC hlo

/-- All rows of an array. -/
def AllIn (lo hi : Nat) (rows : Array Aff) : Prop := ∀ y ∈ rows.toList, In lo hi y

theorem allIn_mono {lo hi hi' : Nat} {rows : Array Aff} (h : AllIn lo hi rows) (hh : hi ≤ hi') :
    AllIn lo hi' rows := fun y hy => in_mono (h y hy) hh

theorem allIn_push {lo hi : Nat} {rows : Array Aff} {y : Aff} (h : AllIn lo hi rows)
    (hy : In lo hi y) : AllIn lo hi (rows.push y) := by
  intro z hz
  rw [Array.toList_push] at hz
  rcases List.mem_append.1 hz with h1 | h1
  · exact h z h1
  · obtain rfl : z = y := by simpa using h1
    exact hy

theorem level_names {lo m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest))
    (hC : In lo F.next C) (hlo : lo ≤ F.next) :
    In lo G.next o.row ∧ In lo G.next (stepDown o).2 ∧ F.next ≤ G.next := by
  obtain ⟨hd, line, s, hw, _, _, _, hL, hR⟩ := level_spec h
  obtain ⟨a, b, c⟩ := whole_names hw hC hlo
  have c' : G.next = hd.sEnd + 2 := c
  exact ⟨a, in_stepDown o (by omega) (by omega) (by omega) (by omega), by omega⟩

/-- What a run of levels carries. -/
def CarriedIn (lo : Nat) (c : Carried) (F : Fork) : Prop :=
  AllIn lo F.next c.rows ∧ In lo F.next c.form ∧ lo ≤ F.next

theorem turn_names {lo : Nat} {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest))
    (hs : CarriedIn lo s F) : CarriedIn lo s' G ∧ F.next ≤ G.next := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, _⟩ := e
  subst e1 e2
  obtain ⟨a, b, c⟩ := level_names hx hs.2.1 hs.2.2
  exact ⟨⟨allIn_push (allIn_mono hs.1 c) a, b, Nat.le_trans hs.2.2 c⟩, c⟩

theorem fold_names {lo : Nat} (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → CarriedIn lo x.1 x.2.1 →
    CarriedIn lo y.1 y.2.1 ∧ x.2.1.next ≤ y.2.1.next
  | [], x, y, h, hx => by
    obtain rfl : x = y := Option.some.inj h
    exact ⟨hx, Nat.le_refl _⟩
  | i :: l, x, y, h, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    obtain ⟨a, b⟩ := turn_names hz hx
    obtain ⟨c, d⟩ := fold_names m0 orders l _ y h a
    exact ⟨c, Nat.le_trans b d⟩

theorem run_names {lo m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : vRun m0 n orders s F rs = some (s', G, rest))
    (hs : CarriedIn lo s F) : CarriedIn lo s' G ∧ F.next ≤ G.next :=
  fold_names m0 orders _ (s, F, rs) (s', G, rest) h hs

/-- A fold of texts that hear keeps what each step keeps. -/
theorem foldlM_keeps {f : β → γ → Hr β} (P : β → Fork → Prop)
    (hf : ∀ s a F rs s' G rest, f s a F rs = some (s', G, rest) → P s F → P s' G) :
    ∀ (l : List γ) (s : β) (F : Fork) (rs : List Fmt.RoundView) (s' : β) (G : Fork) (rest : List Fmt.RoundView),
    l.foldlM f s F rs = some (s', G, rest) → P s F → P s' G
  | [], s, F, rs, s', G, rest, h, hp => by
    obtain ⟨a, b, _⟩ := pure_spec (a := s) h
    rw [a, b]
    exact hp
  | a :: l, s, F, rs, s', G, rest, h, hp => by
    have h' : (f s a >>= fun t => l.foldlM f t) F rs = some (s', G, rest) := h
    obtain ⟨t, F1, r1, h1, h2⟩ := bindHr_some h'
    exact foldlM_keeps P hf l t F1 r1 s' G rest h2 (hf s a F rs t F1 r1 h1 hp)

/-- A fold of texts that hear counts its steps, where each step counts one. -/
theorem foldlM_count {f : β → γ → Hr β} (c : β → Nat)
    (hf : ∀ s a F rs s' G rest, f s a F rs = some (s', G, rest) → c s' = c s + 1) :
    ∀ (l : List γ) (s : β) (F : Fork) (rs : List Fmt.RoundView) (s' : β) (G : Fork) (rest : List Fmt.RoundView),
    l.foldlM f s F rs = some (s', G, rest) → c s' = c s + l.length
  | [], s, F, rs, s', G, rest, h => by
    obtain ⟨a, _, _⟩ := pure_spec (a := s) h
    rw [a]
    rfl
  | a :: l, s, F, rs, s', G, rest, h => by
    have h' : (f s a >>= fun t => l.foldlM f t) F rs = some (s', G, rest) := h
    obtain ⟨t, F1, r1, h1, h2⟩ := bindHr_some h'
    rw [foldlM_count c hf l t F1 r1 s' G rest h2, hf s a F rs t F1 r1 h1, List.length_cons]
    omega

/-- What the tie's fold carries. -/
def TieIn (lo : Nat) (s : Array Aff × Nat × Array Nat) (F : Fork) : Prop :=
  AllIn lo F.next s.1 ∧ (lo ≤ s.2.1 ∧ s.2.1 < F.next) ∧
    (∀ j ∈ s.2.2.toList, lo ≤ j ∧ j < F.next) ∧ lo ≤ F.next

theorem mem_push {a : Array Nat} {y j : Nat} (h : j ∈ (a.push y).toList) : j ∈ a.toList ∨ j = y :=
    by
  rw [Array.toList_push] at h
  rcases List.mem_append.1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by simpa using h1)

theorem tieV_names {lo w : Nat} {a : E} {F G : Fork} {rs rest : List Fmt.RoundView} {rows : Array Aff}
    {sZ : Nat} {sG : Array Nat} (h : tieV w a F rs = some ((rows, sZ, sG), G, rest))
    (hlo : lo ≤ F.next) :
    AllIn lo G.next rows ∧ (lo ≤ sZ ∧ sZ < G.next) ∧ (∀ j ∈ sG.toList, lo ≤ j ∧ j < G.next) ∧
      sG.size = w - 2 + 2 ∧ F.next ≤ G.next := by
  unfold tieV at h
  obtain ⟨x, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨hg, hG, _⟩ := pure_spec h
  obtain ⟨a1, a2, a3⟩ := sumV_names (lo := lo) e1 (in_ofConst _ _ _) hlo
  have a3' : F1.next = x.1.sEnd + 3 := a3
  have P0 : TieIn lo (#[x.2], x.1.sEnd + 1, #[x.1.sEnd + 2]) F1 ∧ x.1.sEnd < F1.next ∧
      (#[x.1.sEnd + 2] : Array Nat).size = 1 + 0 := by
    refine ⟨⟨?_, ⟨by show lo ≤ x.1.sEnd + 1; omega, by show x.1.sEnd + 1 < F1.next; omega⟩, ?_,
      by omega⟩, by omega, rfl⟩
    · intro y hy
      obtain rfl : y = x.2 := by simpa using hy
      exact a1
    · intro j hj
      obtain rfl : j = x.1.sEnd + 2 := by simpa using hj
      exact ⟨by omega, by omega⟩
  have step := foldlM_keeps
    (fun (s : Array Aff × Nat × Array Nat) (F' : Fork) => TieIn lo s F' ∧ x.1.sEnd < F'.next)
    (by
      intro s _ F' rs' s' G' rest' hs hp
      obtain ⟨y, F3, r3, e3, hs⟩ := bindHr_some hs
      obtain ⟨q1, q2, _⟩ := pure_spec hs
      obtain ⟨⟨p1, p2, p3, p4⟩, p5⟩ := hp
      obtain ⟨b1, b2, b3⟩ := sumV_names (lo := lo) e3 (in_slot p2.1 p2.2) p4
      have b3' : F3.next = y.1.sEnd + 2 := b3
      rw [q1, q2]
      refine ⟨⟨allIn_push (allIn_mono p1 (by omega)) b1, ⟨by show lo ≤ y.1.sEnd; omega,
        by show y.1.sEnd < _; omega⟩, ?_, by omega⟩, by omega⟩
      intro j hj
      rcases mem_push hj with h1 | h1
      · exact ⟨(p3 j h1).1, by have := (p3 j h1).2; omega⟩
      · rw [h1]
        exact ⟨by omega, by omega⟩)
    _ _ _ _ _ _ _ e2 ⟨P0.1, P0.2.1⟩
  have hsz : s.2.2.size = 1 + (List.range (w - 2)).length :=
    foldlM_count (fun (s : Array Aff × Nat × Array Nat) => s.2.2.size)
      (by
        intro s _ F' rs' s' G' rest' hs
        obtain ⟨y, F3, r3, e3, hs⟩ := bindHr_some hs
        obtain ⟨q1, _, _⟩ := pure_spec hs
        rw [q1]
        simp)
      _ _ _ _ _ _ _ e2
  obtain ⟨⟨t1, t2, t3, t4⟩, t5⟩ := step
  simp only [Prod.mk.injEq] at hg
  obtain ⟨g1, g2, g3⟩ := hg
  subst g1 g2 g3
  rw [hG]
  have hF : F.next ≤ F2.next := by omega
  refine ⟨t1, ⟨by omega, t5⟩, ?_, ?_, hF⟩
  · intro j hj
    rcases mem_push hj with h1 | h1
    · exact t3 j h1
    · rw [h1]
      exact t2
  · rw [Array.size_push, hsz, List.length_range]
    omega

theorem partsV_names {lo : Nat} : ∀ (n : Nat) (rows : Array Aff) (C : Aff) (F : Fork)
    (rs : List Fmt.RoundView) (rows' : Array Aff) (roots : List Aff) (G : Fork) (rest : List Fmt.RoundView),
    partsV n rows C F rs = some ((rows', roots), G, rest) → AllIn lo F.next rows →
    In lo F.next C → lo ≤ F.next →
    AllIn lo G.next rows' ∧ (∀ y ∈ roots, In lo G.next y) ∧ F.next ≤ G.next
  | 0, rows, C, F, rs, rows', roots, G, rest, h, hr, hC, _ => by
    unfold partsV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b
    refine ⟨hr, fun y hy => ?_, Nat.le_refl _⟩
    obtain rfl : y = C := by simpa using hy
    exact hC
  | n + 1, rows, C, F, rs, rows', roots, G, rest, h, hr, hC, hlo => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨x, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    rw [b]
    obtain ⟨b1, b2, b3⟩ := sumV_names e1 hC hlo
    have b3' : F1.next = w.1.sEnd + 2 := b3
    obtain ⟨c1, c2, c3⟩ := partsV_names n _ _ F1 r1 x.1 x.2 F2 r2 e2
      (allIn_push (allIn_mono hr (by omega)) b1) (in_slot (by omega) (by omega)) (by omega)
    refine ⟨c1, fun y hy => ?_, by omega⟩
    rcases List.mem_cons.1 hy with h1 | h1
    · rw [h1]
      exact in_slot (by omega) (by omega)
    · exact c2 y h1

theorem keysV_names {lo : Nat} (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff)
    (rows : Array Aff) (F : Fork) (rs : List Fmt.RoundView) (rows' : Array Aff)
    (keys : List (Array E × Aff)) (G : Fork) (rest : List Fmt.RoundView),
    keysV f xs Cs rows F rs = some ((rows', keys), G, rest) → AllIn lo F.next rows →
    (∀ C ∈ Cs, In lo F.next C) → lo ≤ F.next →
    AllIn lo G.next rows' ∧ (∀ y ∈ keys, In lo G.next y.2) ∧ F.next ≤ G.next
  | [], _, rows, F, rs, rows', keys, G, rest, h, hr, _, _ => by
    unfold keysV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b
    exact ⟨hr, fun y hy => by simp at hy, Nat.le_refl _⟩
  | _ :: _, [], rows, F, rs, rows', keys, G, rest, h, hr, _, _ => by
    unfold keysV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2 b
    exact ⟨hr, fun y hy => by simp at hy, Nat.le_refl _⟩
  | x :: xs, C :: Cs, rows, F, rs, rows', keys, G, rest, h, hr, hC, hlo => by
    unfold keysV at h
    obtain ⟨k, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    rw [b]
    have e1' : vRun 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C } F rs =
        some (k, F1, r1) := e1
    obtain ⟨⟨k1, k2, k3⟩, k4⟩ := run_names (lo := lo) e1' ⟨hr, hC C (by simp), hlo⟩
    obtain ⟨c1, c2, c3⟩ := keysV_names f xs Cs k.rows F1 r1 y.1 y.2 F2 r2 e2 k1
      (fun D hD => in_mono (hC D (List.mem_cons_of_mem _ hD)) k4) k3
    refine ⟨c1, fun z hz => ?_, by omega⟩
    rcases List.mem_cons.1 hz with h1 | h1
    · rw [h1]
      exact in_mono k2 c3
    · exact c2 z h1

/-! ## What was heard -/

/-- **Of what was heard**, from the return, at a face with two planes at least (`h2`): every row,
every key tree's last form and the form that the leaves' sumcheck was given name slots of the
lookup's window alone; the leaves' own slots and the bits' end slot lie in it. -/
theorem heard_names {f : LFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV}
    (h2 : 2 ≤ f.planes) (h : messagesV f F rs = some (g, G, rest)) :
    AllIn F.next (F.next + f.slots) g.rows ∧
      (∀ y ∈ g.keys, In F.next (F.next + f.slots) y.2) ∧
      In F.next (F.next + f.slots) g.leaves.start ∧ F.next ≤ g.leaves.first ∧
      g.leaves.first + (MaskedSum.hidingAt (g.leaves.vars.zip g.leaves.r)).1.length ≤
        F.next + f.slots ∧
      F.next ≤ g.sBit ∧ g.sBit < F.next + f.slots := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  obtain ⟨s0, s0'⟩ := slot_spec e1
  have n6 : F.next ≤ F6.next := by
    have a1 := (GoesOn.later e1).next
    have a2 := (GoesOn.later e2).next
    have a3 := (GoesOn.later e3).next
    have a4 := (GoesOn.later e4).next
    have a5 := (GoesOn.later e5).next
    have a6 := (GoesOn.later e6).next
    omega
  obtain ⟨t1, t2, t3, t4, t5⟩ := tieV_names (lo := F.next) e7 n6
  obtain ⟨p1, p2, p3⟩ := partsV_names (lo := F.next) _ _ _ _ _ _ _ _ _ e8 t1
    (in_slot t2.1 t2.2) (by omega)
  have n9 := (GoesOn.later e9).next
  obtain ⟨k1, k2, k3⟩ := keysV_names (lo := F.next) f _ _ _ _ _ _ _ _ _ e10 (allIn_mono p1 n9)
    (fun C hC => in_mono (p2 C hC) n9) (by omega)
  have n11 := (GoesOn.later e11).next
  have hsG : ∀ j, j < f.planes → F.next ≤ sG.getD j 0 ∧ sG.getD j 0 < F11.next := by
    intro j hj
    have hlt : j < sG.size := by omega
    have hm : sG.getD j 0 ∈ sG.toList := by
      simp [Array.getD, hlt]
    exact ⟨(t3 _ hm).1, by have := (t3 _ hm).2; omega⟩
  have e12' : vRun f.mu f.d orderDefault
      { rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse } F11 r11 =
      some (table, F12, r12) := e12
  obtain ⟨⟨q1, q2, q3⟩, q4⟩ := run_names (lo := F.next) e12'
    ⟨allIn_mono k1 n11, in_joinForm f sG _ hsG, by omega⟩
  have n13 := (GoesOn.later e13).next
  obtain ⟨l1, l2, l3, l4, l5⟩ := hear_names (openV_hear e14)
  have l4' : F14.next = leaves.sEnd + 0 := l4
  have n15 := (GoesOn.later e15).next
  obtain ⟨b1, b2, b3⟩ := sumV_names (lo := F.next) e16 (in_ofConst _ _ _) (by omega)
  have b3' : F16.next = bits.1.sEnd + 1 := b3
  obtain ⟨s17, s17'⟩ := slot_spec e17
  have hm := (must_spec e18).1
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hm
  have hN : F16.next = F.next + f.slots := by
    rw [← s17, hm.1, s0]
  subst hg
  rw [← hN]
  refine ⟨allIn_push (allIn_mono q1 (by omega)) b1, fun y hy => in_mono (k2 y hy) (by omega), ?_,
    ?_, ?_, ?_, ?_⟩
  · show In _ _ leaves.start
    rw [l1]
    exact in_mono q2 (by omega)
  · show _ ≤ leaves.first
    omega
  · show leaves.first + _ ≤ _
    exact Nat.le_trans (Nat.add_le_add_left l5 _) (by omega)
  · show _ ≤ bits.1.sEnd
    omega
  · show bits.1.sEnd < _
    omega

/-- **The statement `NamesOwn` (Honest/K3/GoodDrawsLaw.lean), at its own name**: from the hearing's
return and the return of the claims on the planes behind it, on any rounds, at any face. No
hypothesis beside. -/
theorem namesOwn : NamesOwn := by
  intro f F G G' rs g pl hh hp r a ha x hx
  obtain ⟨hok, hm⟩ := hearV_messages hh
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := heard_names (two_le_planes_of_ok f hok) hm
  cases r with
  | objects => exact c1 a ha x hx
  | join =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact c2 y hy x hx
  | planes =>
    unfold planesV at hp
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hp
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, _⟩ := e
    subst e1
    have hy' : MaskedSum.row g.leaves oneE {} G = some (y.1, y.2) := hy
    obtain ⟨r1, _⟩ := row_names hy' c3 (in_empty _ _) c4 c5
    have ha' : a = y.1 ∨ a = Aff.slot g.sBit ∨
        a = Aff.ofConst (subE zeroE (OnBytes.Model.ofNat f.count)) := by
      simpa [formsOf] using ha
    rcases ha' with h1 | h1 | h1
    · rw [h1] at hx
      exact r1 x hx
    · rw [h1] at hx
      exact in_slot c6 c7 x hx
    · rw [h1] at hx
      exact in_ofConst _ _ _ x hx

#print axioms ProofFile.Honest.K3.Parts.in_mono
#print axioms ProofFile.Honest.K3.Parts.in_ofConst
#print axioms ProofFile.Honest.K3.Parts.in_empty
#print axioms ProofFile.Honest.K3.Parts.in_slot
#print axioms ProofFile.Honest.K3.Parts.in_addMul
#print axioms ProofFile.Honest.K3.Parts.in_scale
#print axioms ProofFile.Honest.K3.Parts.in_add
#print axioms ProofFile.Honest.K3.Parts.in_sub
#print axioms ProofFile.Honest.K3.Parts.in_onFold
#print axioms ProofFile.Honest.K3.Parts.in_onSlots
#print axioms ProofFile.Honest.K3.Parts.in_rowAff
#print axioms ProofFile.Honest.K3.Parts.in_stepDown
#print axioms ProofFile.Honest.K3.Parts.in_foldl
#print axioms ProofFile.Honest.K3.Parts.in_joinForm
#print axioms ProofFile.Honest.K3.Parts.lens_len
#print axioms ProofFile.Honest.K3.Parts.hear_names
#print axioms ProofFile.Honest.K3.Parts.row_names
#print axioms ProofFile.Honest.K3.Parts.whole_names
#print axioms ProofFile.Honest.K3.Parts.sumV_names
#print axioms ProofFile.Honest.K3.Parts.allIn_mono
#print axioms ProofFile.Honest.K3.Parts.allIn_push
#print axioms ProofFile.Honest.K3.Parts.level_names
#print axioms ProofFile.Honest.K3.Parts.turn_names
#print axioms ProofFile.Honest.K3.Parts.fold_names
#print axioms ProofFile.Honest.K3.Parts.run_names
#print axioms ProofFile.Honest.K3.Parts.foldlM_keeps
#print axioms ProofFile.Honest.K3.Parts.foldlM_count
#print axioms ProofFile.Honest.K3.Parts.mem_push
#print axioms ProofFile.Honest.K3.Parts.tieV_names
#print axioms ProofFile.Honest.K3.Parts.partsV_names
#print axioms ProofFile.Honest.K3.Parts.keysV_names
#print axioms ProofFile.Honest.K3.Parts.heard_names
#print axioms ProofFile.Honest.K3.Parts.namesOwn

end ProofFile.Honest.K3.Parts
