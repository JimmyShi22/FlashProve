-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Kit.lean: THE LAYERS' OWN ROUNDS (K4): TOOLS FOR "THE HEARING
RETURNS". General laws on the flat hearing functions (OnBytes/K/Kc/Flat.lean): nothing is evaluated.
This file and the seven that stand on it in a row (Norms, Terms, Stack, Gated, Merge, Whole, Points)
declare in the namespace OnBytes.Desc.First.K4.Rt.

  1 At, TapeOf    a tape has the shape of rows of K4's table (OnBytes/Desc/First/K4/Rounds.lean):
                  round by round the name, the number drawn other than 0, the batched rows, the
                  number sent, the number drawn. tape_nil, tape_cons, tape_append, tape_vars,
                  tape_masked open such a tape into the written form that the laws of
                  OnBytes/K/Kc/Returns/ ask.
  2 Head          from a return: a sumcheck's record keeps the drawn eps, the start form and the
                  first slot (pscRound_head, roundIn_head, pscEnds_head, tscLoop_head,
                  roundsFold_head); pscBegin_head: what the beginning lays.
  3 tscInD        THE TOKEN SUMCHECK AT ANY DEGREE IN THE FURTHER VARIABLE (the library's law is
                  stated at degree 2; K4's second token sumcheck has degree 1), with the drawn eps,
                  the start form and the number of challenges. claimsIn_tape, tscRounds_head.
  4 plainRounds_returns   K4's plain rounds (OnBytes/Desc/First/K4/Engine.lean).
    bindIte       a call made in one case alone, as the do-notation lays it.
  5 Shown         every slot of a form lies below the next slot and is filled; rules for the forms'
                  operations; Shown.public: such a form's public part returns.
  6 point_tape, claimsBatch_tape, levelIn_tape, tscIn_tape, row_tape   the engine's calls at a tape
                  of the table's shape, each with the room left, "nothing below has turned", the
                  next slot by number, and what is filled. levelIn_all: a layer of a product tree
                  fills every slot that it takes. tsc_marks: of the slots that a token sumcheck
                  takes just its own, from its first to its end values, are free behind it.

Limits. No test on values. Nothing on soundness, completeness or hiding.

-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.K.Kc.Returns.FlReturns8
import OnBytes.Desc.First.P1.Returns
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.Model OnBytes.K.Kc D6.Ret
open OnBytes.PscRun (Sized Filled)

/-! ## 1 A tape of the shape of rows of K4's table -/

/-- The round r has the row's name, numbers and lengths. -/
def At (d : Rd) (r : FlatRound) : Prop :=
  r.name = some d.name.name ∧ r.nz = d.notZero ∧ r.rows = d.rows ∧ r.sent.length = d.sent ∧
    r.drawn.length = d.drawn

/-- The tape has the rows' shape, round by round. -/
def TapeOf : List Rd → Tape → Prop
  | [], [] => True
  | d :: ds, r :: t => At d r ∧ TapeOf ds t
  | _, _ => False

/-- No row: no round. -/
theorem tape_nil {t : Tape} (h : TapeOf [] t) : t = [] := by
  cases t with
  | nil => rfl
  | cons _ _ => exact h.elim

/-- A row and the rest: a written round and the rest. -/
theorem tape_cons {d : Rd} {ds : List Rd} {t : Tape} (h : TapeOf (d :: ds) t) :
    ∃ s dr t', t = ⟨some d.name.name, d.notZero, d.rows, s, dr⟩ :: t' ∧ s.length = d.sent ∧
      dr.length = d.drawn ∧ TapeOf ds t' := by
  cases t with
  | nil => exact h.elim
  | cons r t' =>
    obtain ⟨⟨a1, a2, a3, a4, a5⟩, h2⟩ := h
    obtain ⟨nm, z, w, s, dr⟩ := r
    obtain rfl : nm = some d.name.name := a1
    obtain rfl : z = d.notZero := a2
    obtain rfl : w = d.rows := a3
    exact ⟨s, dr, t', rfl, a4, a5, h2⟩

/-- Rows behind rows: a tape behind a tape. -/
theorem tape_append : ∀ {ds₁ ds₂ : List Rd} {t : Tape}, TapeOf (ds₁ ++ ds₂) t →
    ∃ t₁ t₂, t = t₁ ++ t₂ ∧ TapeOf ds₁ t₁ ∧ TapeOf ds₂ t₂
  | [], _, t, h => ⟨[], t, rfl, trivial, h⟩
  | _ :: _, _, [], h => h.elim
  | d :: ds₁, ds₂, r :: t, h => by
    obtain ⟨t₁, t₂, e, h1, h2⟩ := tape_append (ds₁ := ds₁) (ds₂ := ds₂) h.2
    exact ⟨r :: t₁, t₂, by rw [e]; rfl, ⟨h.1, h1⟩, h2⟩

theorem len_zero {α : Type} {l : List α} (h : l.length = 0) : l = [] := List.length_eq_zero_iff.1 h

theorem len_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] :=
  List.length_eq_one_iff.1 h

/-- Rounds of a variable with two coefficients. -/
theorem tape_vars : ∀ {k : Nat} {t : Tape},
    TapeOf (List.replicate k { name := .pscRound, sent := 2 }) t →
      t.length = k ∧ ∀ x ∈ t, IsVar x
  | 0, t, h => by
    rw [tape_nil h]
    exact ⟨rfl, fun _ hx => by cases hx⟩
  | _ + 1, [], h => h.elim
  | k + 1, r :: t, h => by
    obtain ⟨⟨a1, a2, _, a4, a5⟩, h2⟩ := h
    obtain ⟨e, hv⟩ := tape_vars (k := k) h2
    refine ⟨by rw [List.length_cons, e], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨a1, a2, a4, a5⟩
    · exact hv x hx

/-- **A masked sumcheck's rounds, written out.** -/
theorem tape_masked {k first y ends : Nat} {t : Tape} (h : TapeOf (masked k first y ends) t) :
    ∃ (s0 : List E) (eps : E) (rs : List FlatRound) (sY : List E) (beta : E) (vals : List E),
      t = ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ ::
        (rs ++ [⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩,
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩]) ∧
      s0.length = first ∧ rs.length = k ∧ (∀ x ∈ rs, IsVar x) ∧ sY.length = y ∧
      vals.length = ends := by
  unfold masked at h
  rw [List.append_assoc] at h
  obtain ⟨s0, d0, t', rfl, a1, a2, h1⟩ := tape_cons (ds := _) h
  obtain ⟨eps, rfl⟩ := len_one a2
  obtain ⟨rs, t2, rfl, hr, h2⟩ := tape_append (ds₁ := List.replicate k _) h1
  obtain ⟨e, hv⟩ := tape_vars hr
  obtain ⟨sY, dY, t3, rfl, b1, b2, h3⟩ := tape_cons h2
  obtain ⟨beta, rfl⟩ := len_one b2
  obtain ⟨vals, dV, t4, rfl, c1, c2, h4⟩ := tape_cons h3
  obtain rfl := len_zero c2
  obtain rfl := tape_nil h4
  exact ⟨s0, eps, rs, sY, beta, vals, rfl, a1, e, hv, b1, c1⟩

/-! ## 2 What a sumcheck's record keeps, from a return -/

open OnBytes.Desc.First.P1 (bind_some pure_some must_some need_some onTape_some)

/-- q is p some rounds later: what stands at a sumcheck's head stays: the same drawn eps, the same
start form, the same first slot. -/
structure Head (p q : Psc) : Prop where
  eps : q.eps = p.eps
  start : q.start = p.start
  first : q.first = p.first

theorem Head.refl (p : Psc) : Head p p := ⟨rfl, rfl, rfl⟩

theorem Head.trans {p q r : Psc} (a : Head p q) (b : Head q r) : Head p r :=
  ⟨b.eps.trans a.eps, b.start.trans a.start, b.first.trans a.first⟩

theorem pscRound_head {p q : Psc} {w : OnBytes.Psc.Weight} {draw : Tape → Option (E × Tape)}
    {F G : Fork} {t u : Tape} {r : E} (h : Fl.pscRound p w draw F t = some ((r, q), G, u)) :
    Head p q := by
  unfold Fl.pscRound at h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨e, _, _⟩ := pure_some.mp h
  obtain rfl := congrArg Prod.snd e
  exact ⟨rfl, rfl, rfl⟩

theorem roundIn_head {form : RoundForm} {p q : Psc} {z : E} {d : Nat} {F G : Fork} {t u : Tape}
    {r : E} (h : Fl.roundIn form p z d F t = some ((r, q), G, u)) : Head p q := by
  unfold Fl.roundIn at h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  exact pscRound_head h

theorem pscEnds_head {p q : Psc} {dY n e : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.pscEnds p dY n F t = some ((e, q), G, u)) : Head p q := by
  unfold Fl.pscEnds at h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨⟨beta, p1⟩, _, _, h1, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨e, _, _⟩ := pure_some.mp h
  obtain rfl := congrArg Prod.snd e
  have a := pscRound_head h1
  exact ⟨a.eps, a.start, a.first⟩

/-- The token sumcheck's loop: the record's head stays; one challenge a coordinate is appended. -/
theorem tscLoop_head : ∀ {zs : List E} {r r' : Array E} {p q : Psc} {F G : Fork} {t u : Tape},
    Fl.tscLoop zs r p F t = some ((r', q), G, u) → Head p q ∧ r'.size = r.size + zs.length
  | [], r, r', p, q, F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨e, _, _⟩ := pure_some.mp h
    obtain rfl := congrArg Prod.fst e
    obtain rfl := congrArg Prod.snd e
    exact ⟨Head.refl _, rfl⟩
  | z :: zs, r, r', p, q, F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨⟨x, p1⟩, _, _, h1, h⟩ := bind_some.mp h
    obtain ⟨a, b⟩ := tscLoop_head h
    refine ⟨(roundIn_head h1).trans a, ?_⟩
    rw [b, Array.size_push, List.length_cons]
    omega

/-- The beginning, at a written round: the drawn eps and the start form are laid. -/
theorem pscBegin_head {C : Aff} {p : Psc} {F G : Fork} {w : Nat} {mu eps : E} {t u : Tape}
    (h : Fl.pscBegin C F (⟨some RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
      some (p, G, u)) : p.eps = eps ∧ p.start = C := by
  have hT : ∃ T, F.publicPart C = some T := by
    unfold Fl.pscBegin at h
    obtain ⟨T, _, _, h0, _⟩ := bind_some.mp h
    exact ⟨T, (OnBytes.Desc.First.P1.ask_some.mp h0).1⟩
  obtain ⟨T, hT⟩ := hT
  rw [OnBytes.Desc.First.P1.pscBegin_returns hT mu eps w t] at h
  obtain rfl := congrArg Prod.fst (Option.some.inj h)
  exact ⟨rfl, rfl⟩

/-! ## 3 The token sumcheck at any degree in the further variable -/

/-- Hidden values outside a sumcheck: what is left of the tape. -/
theorem claimsIn_tape {n j : Nat} {F G : Fork} {nm : Option String} {z w : Nat} {xs s d : List E}
    {t u : Tape} (hx : xs.length = n)
    (h : Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (j, G, u)) :
    u = ⟨nm, z, w, s, d⟩ :: t ∧ j = F.next := by
  unfold Fl.claimsIn at h
  obtain ⟨v, G1, u1, h1, h⟩ := bind_some.mp h
  rw [readR nm z w d t xs s n hx.symm F] at h1
  obtain ⟨rfl, rfl, rfl⟩ := OnBytes.Desc.First.P1.some_triple.mp h1
  obtain ⟨_, _, _, h2, h⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h2
  obtain ⟨_, _, _, h3, h⟩ := bind_some.mp h
  obtain ⟨rfl, rfl, rfl⟩ := OnBytes.Desc.First.P1.takeSlots_some.mp h3
  obtain ⟨_, _, _, h4, h⟩ := bind_some.mp h
  obtain ⟨_, rfl⟩ := OnBytes.Desc.First.P1.change_some.mp h4
  obtain ⟨rfl, _, rfl⟩ := pure_some.mp h
  exact ⟨rfl, rfl⟩

/-- The claimed sum, the beginning and the rounds: what the record holds, from a return. -/
theorem tscRounds_head {P : Array E} {lt w0 : Nat} {F G : Fork} {cl mu eps : E} {t u : Tape}
    {o : Tsc}
    (h : Fl.tscRounds P lt F (⟨some RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: t) =
      some (o, G, u)) :
    o.p.eps = eps ∧ o.p.start = Aff.slot F.next ∧ o.r.size = lt := by
  unfold Fl.tscRounds at h
  obtain ⟨_, _, _, h1, h⟩ := bind_some.mp h
  obtain ⟨hP, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨sCl, G0, u0, h2, h⟩ := bind_some.mp h
  obtain ⟨rfl, rfl⟩ := claimsIn_tape (xs := [cl]) (s := [mu]) rfl h2
  obtain ⟨p0, G1, u1, h3, h⟩ := bind_some.mp h
  obtain ⟨e1, e2⟩ := pscBegin_head h3
  obtain ⟨⟨r, p⟩, G2, u2, h4, h⟩ := bind_some.mp h
  obtain ⟨a, b⟩ := tscLoop_head h4
  obtain ⟨rfl, _, _⟩ := pure_some.mp h
  refine ⟨a.eps.trans e1, a.start.trans e2, ?_⟩
  show r.size = lt
  rw [b, List.length_take, Array.length_toList]
  have : lt ≤ P.size := by simpa using hP
  simp
  omega

/-- **A token sumcheck, at any degree in the further variable**: it returns; it is left open, with
room behind it; nothing below has turned; its slots by number; the drawn eps, the start form and the
number of its challenges. -/
theorem tscInD {F : Fork} {lt n k dY : Nat} (P : Array E) (hP : lt ≤ P.size) (hn : 1 ≤ n)
    (hd : 1 ≤ dY) (h : Room F (1 + (1 + (2 * lt + (dY + n + k))))) (cl mu eps : E) (w0 : Nat)
    (rs : List FlatRound) (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = dY) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = n) (u : Tape) :
    ∃ o G, Fl.tscIn P lt n dY F
        (⟨some RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (o, G, u) ∧
      Open o.p G ∧ o.p.first + taken o.p ≤ G.next ∧ Room G k ∧ Below F G ∧ o.sCl = F.next ∧
      Filled G F.next ∧ o.p.first = F.next + 1 ∧ o.sEnd = F.next + (1 + (1 + (2 * lt + dY))) ∧
      G.next = o.sEnd + n ∧ (∀ i, i < n → Filled G (o.sEnd + i)) ∧
      o.p.eps = eps ∧ o.p.start = Aff.slot F.next ∧ o.r.size = lt ∧
      o.sEnd = o.p.first + taken o.p := by
  obtain ⟨o1, G1, a1, a2, a3, a4, a5, a6, a7⟩ := tscRounds_below P hP h cl mu eps w0 rs hrs hvar
    (⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)
  obtain ⟨e1, e2, e3⟩ := tscRounds_head a1
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR a2 hd hn wY wV sentY vals beta u hsY hvals
  have hh := pscEnds_head d1
  have hnx := d2.next
  have hfi := d2.first
  refine ⟨{ o1 with sEnd := G1.next + dY, p := p2 }, G2, ?_, d2.isOpen, ?_, d2.room,
    a3.trans ⟨d4, fun _ => d2.sized, by omega, d5⟩, a4, ?_, ?_, ?_, hnx, d2.ends,
    hh.eps.trans e1, hh.start.trans e2, e3, hfi⟩
  · unfold Fl.tscIn
    refine bindR a1 ?_
    refine bindR d1 ?_
    rfl
  · show p2.first + taken p2 ≤ G2.next
    omega
  · exact (d5 _ (by omega)).2 a5
  · show p2.first = F.next + 1
    rw [d3, a6]
  · show G1.next + dY = _
    rw [a7]
    omega

/-! ## 4 K4's plain rounds -/

/-- Rounds of one form in a row, from a return: the record's head stays; one challenge a round. -/
theorem roundsFold_head (form : RoundForm) : ∀ {zs : List (E × Nat)} {s : Array E × Psc}
    {r' : Array E} {q : Psc} {F G : Fork} {t u : Tape},
    (zs.foldlM (fun (s : Array E × Psc) z => (do
      let (r, q) ← Fl.roundIn form s.2 z.1 z.2
      pure (s.1.push r, q) : Fl (Array E × Psc))) s) F t = some ((r', q), G, u) →
      Head s.2 q ∧ r'.size = s.1.size + zs.length
  | [], s, r', q, F, G, t, u, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨e, _, _⟩ := pure_some.mp h
    subst e
    exact ⟨Head.refl _, rfl⟩
  | z :: zs, s, r', q, F, G, t, u, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, G1, u1, h1, h⟩ := bind_some.mp h
    obtain ⟨⟨x, p1⟩, G0, u0, h0, h1⟩ := bind_some.mp h1
    obtain ⟨rfl, _, _⟩ := pure_some.mp h1
    obtain ⟨a, b⟩ := roundsFold_head form h
    refine ⟨(roundIn_head h0).trans a, ?_⟩
    rw [b, List.length_cons]
    show (s.1.push x).size + zs.length = _
    rw [Array.size_push]
    omega

/-- **The batched sumcheck's rounds.** -/
theorem plainRounds_returns (st : Stack) (rs : List FlatRound) (F : Fork) (n : Nat) (u : Tape)
    (hl : rs.length = st.lam) (hv : ∀ x ∈ rs, IsVar x) (h : Mid st.p F (2 * st.lam + n)) :
    ∃ st' G, plainRounds engFl st F (rs ++ u) = some (st', G, u) ∧ Mid st'.p G n ∧
      Head st.p st'.p ∧ G.next = F.next + 2 * st.lam ∧ G.ns = F.ns ∧ st'.lam = st.lam ∧
      st'.rs.size = st.lam ∧ ∀ j, Filled G j ↔ Filled F j := by
  have hsl : slotsOf .sum2 (List.replicate st.lam (zeroE, 0)) = 2 * st.lam := by
    unfold slotsOf
    rw [List.map_replicate, List.sum_replicate]
    show st.lam * 2 = _
    omega
  obtain ⟨r', q, G, c1, c2, c3, cN, c4, c5⟩ := roundsFoldN .sum2
    (List.replicate st.lam (zeroE, 0)) rs (#[], st.p) F n u (by rw [hl, List.length_replicate])
    (fun y hy => by
      have h1 := (List.of_mem_zip hy).1
      have h2 := (List.of_mem_zip hy).2
      rw [List.eq_of_mem_replicate h1]
      exact ⟨rfl, hv _ h2⟩) (by rw [hsl]; exact h)
  obtain ⟨a, b⟩ := roundsFold_head .sum2 c1
  refine ⟨{ st with rs := r'.reverse, p := q }, G, ?_, c2, a, by rw [cN, hsl], c4, rfl, ?_, c5⟩
  · unfold plainRounds
    exact bindR c1 rfl
  · show r'.reverse.size = _
    rw [Array.size_reverse, b, List.length_replicate]
    simp

/-- A call made in one case alone, as the do-notation lays it: the rest stands in both arms. -/
theorem bindIte {α β : Type} {c : Prop} [Decidable c] {A B : Fl α} {f : α → Fl β} {F G : Fork}
    {t u : Tape} {a : α} {r : Option (β × Fork × Tape)}
    (h1 : (if c then A else B) F t = some (a, G, u)) (h2 : f a G u = r) :
    (if c then A >>= f else B >>= f) F t = r := by
  by_cases hc : c
  · rw [if_pos hc] at h1 ⊢
    exact bindR h1 h2
  · rw [if_neg hc] at h1 ⊢
    exact bindR h1 h2

/-! ## 5 Forms whose slots have been shown -/

open VerifiableInference.Desc.First.Shape (affSh affSh_addMul affSh_add affSh_sub affSh_slot
  affSh_ofConst AffSh)

/-- Every slot of the form lies below the next slot and is filled. (The library has the like with
"below the number of slots": Named, Johnson/Top/H/Keep/PadNamed.lean.) -/
def Shown (F : Fork) (a : Aff) : Prop := ∀ j ∈ (affSh a).slots, j < F.next ∧ Filled F j

theorem Shown.below {F G : Fork} {a : Aff} (h : Shown F a) (b : Below F G) : Shown G a :=
  fun j hj => ⟨Nat.lt_of_lt_of_le (h j hj).1 b.next, (b.same j (h j hj).1).2 (h j hj).2⟩

theorem Shown.public {F : Fork} {a : Aff} (h : Shown F a) (hn : F.next ≤ F.ns) :
    ∃ T, F.publicPart a = some T :=
  publicPart_some F a fun x hx =>
    have hm : x.1 ∈ (affSh a).slots := List.mem_map.2 ⟨x, hx, rfl⟩
    ⟨Nat.lt_of_lt_of_le (h _ hm).1 hn, (h _ hm).2⟩

theorem shown_const (F : Fork) (v : E) : Shown F (Aff.ofConst v) := fun _ hj => by cases hj

theorem shown_slot {F : Fork} {j : Nat} (h1 : j < F.next) (h2 : Filled F j) :
    Shown F (Aff.slot j) := fun i hi => by
  obtain rfl : i = j := by simpa [affSh_slot, AffSh.slots, AffSh.mk] using hi
  exact ⟨h1, h2⟩

theorem Shown.addMul {F : Fork} {a b : Aff} (ha : Shown F a) (hb : Shown F b) (k : E) :
    Shown F (a.addMul b k) := fun j hj => by
  rw [affSh_addMul] at hj
  rcases List.mem_append.1 hj with h | h
  · exact ha j h
  · exact hb j h

theorem Shown.add {F : Fork} {a b : Aff} (ha : Shown F a) (hb : Shown F b) : Shown F (a + b) :=
  ha.addMul hb _

theorem Shown.sub {F : Fork} {a b : Aff} (ha : Shown F a) (hb : Shown F b) : Shown F (a - b) :=
  ha.addMul hb _

theorem Shown.scale {F : Fork} {a : Aff} (ha : Shown F a) (k : E) : Shown F (a.scale k) :=
  Shown.addMul (fun _ hj => by cases hj) ha k

/-- A fold that adds a multiple of a shown form for each member. -/
theorem shown_foldl {α : Type} {F : Fork} (f : α → Aff) (c : α → E) : ∀ (l : List α) (a : Aff),
    Shown F a → (∀ x ∈ l, Shown F (f x)) →
      Shown F (l.foldl (fun (C : Aff) x => C.addMul (f x) (c x)) a)
  | [], _, ha, _ => ha
  | x :: l, _, ha, h =>
    shown_foldl f c l _ (ha.addMul (h x (List.mem_cons_self ..)) _)
      fun y hy => h y (List.mem_cons_of_mem _ hy)

/-! ## 6 The engine's calls at a tape of the table's shape -/

/-- A round in which a point is drawn. -/
theorem point_tape {r : RoundName} (hr : (r == .batSigma) = false) {n : Nat} {t : Tape}
    (hT : TapeOf [pointRd r n] t) (F : Fork) (u : Tape) :
    ∃ a, engFl.point r n F (t ++ u) = some (a, F, u) ∧ a.size = n := by
  obtain ⟨s, d, t', rfl, a1, a2, h1⟩ := tape_cons hT
  obtain rfl := tape_nil h1
  obtain rfl := len_zero a1
  refine ⟨d.toArray, ?_, by simpa using a2⟩
  show (if (r == .batSigma) = true then fun _ _ => none else Fl.point r n) F _ = _
  rw [hr]
  exact pointR r n _ d a2 F u

/-- Hidden values, then the round that batches rows. -/
theorem claimsBatch_tape {F : Fork} {n rows k : Nat} (h : Room F (n + k)) (hr : rows ≠ 0)
    {t : Tape} (hT : TapeOf [batchRd n rows] t) (u : Tape) :
    ∃ x G, Fl.claimsIn n F (t ++ u) =
        some (F.next, G, ⟨some RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u) ∧
      Fl.batch rows G (⟨some RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u) =
        some (powers x rows, G, u) ∧
      Room G k ∧ Below F G ∧ G.next = F.next + n ∧ ∀ i, i < n → Filled G (F.next + i) := by
  obtain ⟨s, d, t', rfl, a1, a2, h1⟩ := tape_cons hT
  obtain rfl := tape_nil h1
  obtain ⟨x, rfl⟩ := len_one a2
  obtain ⟨G, b1, b2, b3, b4, b5, b6⟩ := claimsInR h (some RoundName.batSigma.name) 0 rows s [] [x]
    u a1
  rw [List.append_nil] at b1
  exact ⟨x, G, b1, batchR rows hr x G u, b2, ⟨b4, fun _ => b2.sized, by omega, b6⟩, b3, b5⟩

/-- The layer's rounds keep the number of challenges, from a return. -/
theorem levelRounds_size {mu : Nat} {rho : Array E} : ∀ {order : List Nat} {r r' : Array E}
    {p q : Psc} {F G : Fork} {t u : Tape},
    Fl.levelRounds mu rho order r p F t = some ((r', q), G, u) → r'.size = r.size
  | [], r, r', p, q, F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨e, _, _⟩ := pure_some.mp h
    obtain rfl : r = r' := congrArg Prod.fst e
    rfl
  | v :: order, r, r', p, q, F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
    obtain ⟨⟨x, p1⟩, _, _, _, h⟩ := bind_some.mp h
    rw [levelRounds_size h]
    simp

theorem levelIn_size {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    L.r.size = mu := by
  unfold Fl.levelIn at h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨⟨r, p1⟩, _, _, h1, h⟩ := bind_some.mp h
  obtain ⟨⟨sL, p2⟩, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨_, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨⟨row, p3⟩, _, _, _, h⟩ := bind_some.mp h
  obtain ⟨rfl, _, _⟩ := pure_some.mp h
  show r.size = mu
  rw [levelRounds_size h1, Array.size_replicate]

/-- A layer of a product tree fills every slot that it takes: its sumcheck's own slots by the claim
that it makes at its end, and the two end values. -/
theorem levelIn_all {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff}
    {T : E} (hT : F.publicPart C = some T) (rho : Array E) (order : List Nat)
    (ho : order.length = mu) (hv : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) (mu0 eps : E)
    (w0 : Nat) (rs : List FlatRound) (hrs : rs.length = mu) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = 2) (wT : Nat) (tau : E) (u : Tape) :
    ∃ L G, Fl.levelIn mu rho C order F
        (⟨some RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
          (rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some RoundName.pscValues.name, 0, wV, vals, []⟩ ::
            ⟨some RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) = some (L, G, u) ∧
      ∀ j, F.next ≤ j → j < G.next → Filled G j := by
  obtain ⟨p0, b1, b2, b3⟩ := pscBeginR h hT mu0 eps w0
    (rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some RoundName.line.name, 0, wT, [], [tau]⟩ :: u)
  rw [← ho] at b2
  obtain ⟨r1, p1, G1, c1, c2, c3, -, -, -⟩ := levelRoundsN mu rho order rs
    (Array.replicate mu zeroE) p0 _ (2 + 2 + k)
    (⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some RoundName.line.name, 0, wT, [], [tau]⟩ :: u) (by rw [hrs, ho]) hvar hv b2
  obtain ⟨p2, G2, d1, d2, d3, -, -⟩ := pscEndsR c2 (by omega) (by omega) wY wV sentY vals beta
    (⟨some RoundName.line.name, 0, wT, [], [tau]⟩ :: u) hsY hvals
  have hfit := d2.fits
  have hnx := d2.next
  have hfi := d2.first
  obtain ⟨H, e1, -, e3, -, e5, e6⟩ := pscRowO d2.isOpen
    (mulE (G2.vp.getD (G1.next + 2) zeroE) (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} u
  have f0 := d2.ends 0 (by omega)
  have f1 := d2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  have hfirst : p2.first = F.next := by rw [d3, c3, b3]
  refine ⟨{ r := r1, sL := G1.next + 2, sR := G1.next + 2 + 1, tau := tau,
            row := p2.rowForm (mulE (G2.vp.getD (G1.next + 2) zeroE)
              (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} }, H, ?_, fun j h1 h2 => ?_⟩
  · unfold Fl.levelIn
    refine bindR (mustR (by simp [ho]) _ _) ?_
    refine bindR b1 ?_
    refine bindR c1 ?_
    refine bindR d1 ?_
    refine bindR (answerR .line wT tau _ u) ?_
    refine bindR (shownR (by omega) f0 u) ?_
    refine bindR (shownR (by omega) f1 u) ?_
    refine bindR e1 ?_
    rfl
  · by_cases hj : j < G1.next + 2
    · exact e5 j (by omega) (by omega)
    · have e : G1.next + 2 + (j - (G1.next + 2)) = j := by omega
      have := d2.ends (j - (G1.next + 2)) (by omega)
      rw [e] at this
      exact (e6 j (Or.inr (by omega))).2 this

/-- **A layer of a product tree**, at a tape of the table's shape. -/
theorem levelIn_tape {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff}
    (hC : Shown F C) (rho : Array E) (order : List Nat) (ho : order.length = mu)
    (hv : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) {t : Tape} (hT : TapeOf (layerRds mu) t)
    (u : Tape) :
    ∃ L G, Fl.levelIn mu rho C order F (t ++ u) = some (L, G, u) ∧ Room G k ∧ Below F G ∧
      G.next = F.next + (1 + (2 * mu + (2 + 2))) ∧ L.sL = F.next + (1 + (2 * mu + 2)) ∧
      L.sR = L.sL + 1 ∧ Filled G L.sL ∧ Filled G L.sR ∧ L.r.size = mu ∧
      ∀ j, F.next ≤ j → j < G.next → Filled G j := by
  unfold layerRds at hT
  obtain ⟨tm, tl, rfl, hm, hl⟩ := tape_append hT
  obtain ⟨s0, eps, rs, sY, beta, vals, rfl, a1, a2, a3, a4, a5⟩ := tape_masked hm
  obtain ⟨mu0, rfl⟩ := len_one a1
  obtain ⟨sl, dl, t', rfl, b1, b2, b3⟩ := tape_cons hl
  obtain rfl := tape_nil b3
  obtain rfl := len_zero b1
  obtain ⟨tau, rfl⟩ := len_one b2
  obtain ⟨T, hT'⟩ := hC.public (by have := h.fits; omega)
  obtain ⟨L, G, c1, c2, c3, c4, c5, c6, c7, c8⟩ := levelIn_below h hT' rho order ho hv mu0 eps 0 rs
    a2 a3 0 sY a4 beta 0 vals a5 0 tau u
  have e : (⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
      (rs ++ [⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩,
        ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩]) ++
      [⟨some RoundName.line.name, 0, 0, [], [tau]⟩] ++ u : Tape) =
      ⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ ::
          ⟨some RoundName.line.name, 0, 0, [], [tau]⟩ :: u) := by simp
  obtain ⟨L', G', c1', hall⟩ := levelIn_all h hT' rho order ho hv mu0 eps 0 rs a2 a3 0 sY a4 beta 0
    vals a5 0 tau u
  obtain rfl : G = G' := by
    have := Option.some.inj (c1.symm.trans c1')
    exact congrArg (fun x => x.2.1) this
  refine ⟨L, G, ?_, c2, c3, c4, c5, c6, c7, c8, levelIn_size c1, hall⟩
  exact e ▸ c1

/-- **A token sumcheck**, at a tape of the table's shape. -/
theorem tscIn_tape {F : Fork} {lt n k dY : Nat} (P : Array E) (hP : lt ≤ P.size) (hn : 1 ≤ n)
    (hd : 1 ≤ dY) (h : Room F (1 + (1 + (2 * lt + (dY + n + k))))) {t : Tape}
    (hT : TapeOf (masked lt 2 dY n) t) (u : Tape) :
    ∃ o G eps, Fl.tscIn P lt n dY F (t ++ u) = some (o, G, u) ∧
      (∃ s0 t', t = ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t') ∧
      Open o.p G ∧ o.p.first + taken o.p ≤ G.next ∧ Room G k ∧ Below F G ∧ o.sCl = F.next ∧
      Filled G F.next ∧ o.p.first = F.next + 1 ∧ o.sEnd = F.next + (1 + (1 + (2 * lt + dY))) ∧
      G.next = o.sEnd + n ∧ (∀ i, i < n → Filled G (o.sEnd + i)) ∧
      o.p.eps = eps ∧ o.p.start = Aff.slot F.next ∧ o.r.size = lt ∧
      o.sEnd = o.p.first + taken o.p := by
  obtain ⟨s0, eps, rs, sY, beta, vals, rfl, a1, a2, a3, a4, a5⟩ := tape_masked hT
  obtain ⟨cl, mu, rfl⟩ : ∃ cl mu, s0 = [cl, mu] := List.length_eq_two.1 a1
  obtain ⟨o, G, c⟩ := tscInD P hP hn hd h cl mu eps 0 rs a2 a3 0 sY a4 beta 0 vals a5 u
  have e : (⟨some RoundName.pscEpsilon.name, 0, 0, [cl, mu], [eps]⟩ ::
      (rs ++ [⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩,
        ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩]) ++ u : Tape) =
      ⟨some RoundName.pscEpsilon.name, 0, 0, [cl, mu], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u) := by simp
  exact ⟨o, G, eps, e ▸ c.1, ⟨_, _, rfl⟩, c.2⟩

/-- Of the slots that a token sumcheck takes just its own, from its first to its end values, are
free behind it. -/
theorem tsc_marks {o : Tsc} {F G : Fork} {n : Nat} (h1 : Open o.p G) (h2 : Filled G F.next)
    (h3 : o.p.first = F.next + 1) (h4 : G.next = o.sEnd + n)
    (h5 : ∀ i, i < n → Filled G (o.sEnd + i)) (h6 : o.sEnd = o.p.first + taken o.p) :
    ∀ j, F.next ≤ j → j < G.next → (Filled G j ↔ ¬ (o.p.first ≤ j ∧ j < o.sEnd)) := by
  intro j a b
  by_cases c1 : j = F.next
  · subst c1
    exact ⟨fun _ hc => by omega, fun _ => h2⟩
  · by_cases c2 : j < o.sEnd
    · exact ⟨fun hf _ => h1.own j (by omega) (by omega) hf, fun hc => absurd ⟨by omega, c2⟩ hc⟩
    · have e : o.sEnd + (j - o.sEnd) = j := by omega
      have := h5 (j - o.sEnd) (by omega)
      rw [e] at this
      exact ⟨fun _ hc => c2 hc.2, fun _ => this⟩

/-- **A sumcheck's claim, made at a ledger at which it is still open**: it returns; the room stays;
below the sumcheck's first slot nothing turns; every slot of the claim has then been shown, where
those of the start form and of the kept terms had been. -/
theorem row_tape {p : Psc} {G : Fork} {k : Nat} (h : Open p G) (hr : Room G k)
    (hp : p.first + taken p ≤ G.next) (S0 : E) {kept : Aff} (hs : Shown G p.start)
    (hk : Shown G kept) (hlow : ∀ j ∈ (affSh p.start).slots ++ (affSh kept).slots, j < p.first)
    (t : Tape) :
    ∃ H, Fl.pscRow p S0 kept G t = some ((p.rowForm S0 kept, { p with rowMade := true }), H, t) ∧
      Room H k ∧ H.next = G.next ∧ H.ns = G.ns ∧ Sized H ∧
      (∀ j, p.first ≤ j → j < p.first + taken p → Filled H j) ∧
      (∀ j, (j < p.first ∨ p.first + taken p ≤ j) → (Filled H j ↔ Filled G j)) ∧
      Shown H (p.rowForm S0 kept) := by
  obtain ⟨H, a1, a2, a3, a4, a5, a6⟩ := pscRowO h S0 kept t
  refine ⟨H, a1, room_row hr hp a2 a3 a4 a6, a3, a4, a2, a5, a6, fun j hj => ?_⟩
  rw [VerifiableInference.Desc.First.Shape.affSh_rowForm, walk_taken h] at hj
  have hj' : j ∈ List.range' p.first (taken p) ++ (affSh p.start).slots ++ (affSh kept).slots := hj
  rw [List.append_assoc] at hj'
  rcases List.mem_append.1 hj' with h1 | h1
  · obtain ⟨b1, b2⟩ := List.mem_range'_1.1 h1
    exact ⟨by rw [a3]; omega, a5 j b1 b2⟩
  · have hl := hlow j h1
    rcases List.mem_append.1 h1 with h2 | h2
    · exact ⟨by rw [a3]; exact (hs j h2).1, (a6 j (Or.inl hl)).2 (hs j h2).2⟩
    · exact ⟨by rw [a3]; exact (hk j h2).1, (a6 j (Or.inl hl)).2 (hk j h2).2⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.tape_nil
#print axioms OnBytes.Desc.First.K4.Rt.tape_cons
#print axioms OnBytes.Desc.First.K4.Rt.tape_append
#print axioms OnBytes.Desc.First.K4.Rt.len_zero
#print axioms OnBytes.Desc.First.K4.Rt.len_one
#print axioms OnBytes.Desc.First.K4.Rt.tape_vars
#print axioms OnBytes.Desc.First.K4.Rt.tape_masked
#print axioms OnBytes.Desc.First.K4.Rt.Head.refl
#print axioms OnBytes.Desc.First.K4.Rt.Head.trans
#print axioms OnBytes.Desc.First.K4.Rt.pscRound_head
#print axioms OnBytes.Desc.First.K4.Rt.roundIn_head
#print axioms OnBytes.Desc.First.K4.Rt.pscEnds_head
#print axioms OnBytes.Desc.First.K4.Rt.tscLoop_head
#print axioms OnBytes.Desc.First.K4.Rt.pscBegin_head
#print axioms OnBytes.Desc.First.K4.Rt.claimsIn_tape
#print axioms OnBytes.Desc.First.K4.Rt.tscRounds_head
#print axioms OnBytes.Desc.First.K4.Rt.tscInD
#print axioms OnBytes.Desc.First.K4.Rt.roundsFold_head
#print axioms OnBytes.Desc.First.K4.Rt.plainRounds_returns
#print axioms OnBytes.Desc.First.K4.Rt.bindIte
#print axioms OnBytes.Desc.First.K4.Rt.Shown.below
#print axioms OnBytes.Desc.First.K4.Rt.Shown.public
#print axioms OnBytes.Desc.First.K4.Rt.shown_const
#print axioms OnBytes.Desc.First.K4.Rt.shown_slot
#print axioms OnBytes.Desc.First.K4.Rt.Shown.addMul
#print axioms OnBytes.Desc.First.K4.Rt.Shown.add
#print axioms OnBytes.Desc.First.K4.Rt.Shown.sub
#print axioms OnBytes.Desc.First.K4.Rt.Shown.scale
#print axioms OnBytes.Desc.First.K4.Rt.shown_foldl
#print axioms OnBytes.Desc.First.K4.Rt.point_tape
#print axioms OnBytes.Desc.First.K4.Rt.claimsBatch_tape
#print axioms OnBytes.Desc.First.K4.Rt.levelRounds_size
#print axioms OnBytes.Desc.First.K4.Rt.levelIn_size
#print axioms OnBytes.Desc.First.K4.Rt.levelIn_all
#print axioms OnBytes.Desc.First.K4.Rt.levelIn_tape
#print axioms OnBytes.Desc.First.K4.Rt.tscIn_tape
#print axioms OnBytes.Desc.First.K4.Rt.tsc_marks
#print axioms OnBytes.Desc.First.K4.Rt.row_tape
