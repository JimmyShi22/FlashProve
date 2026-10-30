-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Returns.lean: the law of kind K5, the other direction: the kind refuses
nothing
but a shape. planOk, the rounds are `rounds p` entry for entry (so many scalars; so many elements
drawn),
the ledger's arrays have their length, and the stretch's slots are there and free: then the hearing
returns, with all rounds used up. So the law is not met by a verifier that says no to all; and no
value
that the prover sends bears on the hearing's return.

Main names:
  `hideRun_returns`, `take_returns`, `close_returns`, `batch_returns`, `sum_returns`: the ledger's
    run
    and the four verbs.
  `hiding_length`: the hiding polynomial has as many coefficients as the part's ownSlots says.
  `hear_of_ran`: the verbs' returns, one after the other, are the hearing's return.
  `hear_returns`, `hear_iff`: the whole; with Att/K5Shape.lean: the hearing returns exactly at the
    rounds' shape.

Premises: PartReturns (Part/MaskedSumLaw.lean) · Sized F · the slots from F.next on are free: facts
that
the fold must carry; not shown in this file or in what it imports.
Sources: what Att/K5SaidAll.lean names, and OnBytes/Tie/Pv/Psc/Run/PscHide.lean (getD_set_other,
Filled).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.Part.MaskedSumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Fit Fits Free PartReturns)

/-! ## The ledger's run returns where its slots are free -/

theorem hideList_returns (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork), Free F first l.length →
    ∃ x, l.foldlM (Fork.hideStep factor) (first, F) = some x
  | [], first, F, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, ⟨h1, h2, h3⟩ => by
    rw [List.length_cons] at h2 h3
    have hh : F.hide first y factor = some { F with
        gotF := F.gotF.set! first true, vp := F.vp.set! first y, mf := F.mf.set! first factor } := by
      unfold Fork.hide
      rw [if_pos]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
      exact ⟨⟨by omega, h1⟩, h3 first (Nat.le_refl _) (by omega)⟩
    have hs : Fork.hideStep factor (first, F) y = some (first + 1, { F with
        gotF := F.gotF.set! first true, vp := F.vp.set! first y, mf := F.mf.set! first factor }) := by
      show (F.hide first y factor).map _ = _
      rw [hh]
      rfl
    rw [List.foldlM_cons, hs]
    refine hideList_returns factor l (first + 1) _ ⟨?_, ?_, fun j hj1 hj2 => ?_⟩
    · show (F.gotF.set! first true).size = F.ns
      simpa using h1
    · show first + 1 + l.length ≤ F.ns
      omega
    · show (F.gotF.set! first true).getD j true = false
      rw [getD_set_other _ _ _ _ _ (by omega)]
      exact h3 j (by omega) (by omega)

theorem hideRun_returns (F : Fork) (first : Nat) (v : Array E) (factor : E) (h : Free F first v.size) :
    ∃ G, F.hideRun first v factor = some G := by
  obtain ⟨x, hx⟩ := hideList_returns factor v.toList first F (by rw [Array.length_toList]; exact h)
  refine ⟨x.2, ?_⟩
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]

/-- Behind a run, the slots outside it are as free as they were. -/
theorem filled_free {F G : Fork} {first : Nat} {l : List E} {factor : E} (a : Filled F G first l factor)
    {b n : Nat} (h : Free F b n) (hd : b + n ≤ first ∨ first + l.length ≤ b) : Free G b n :=
  ⟨by rw [a.sized.got], by rw [a.ns]; exact h.2.1, fun j h1 h2 => by
    rw [(a.other j (by omega)).2.2 true]
    exact h.2.2 j h1 h2⟩

theorem free_sub {F : Fork} {a n b k : Nat} (h : Free F a n) (h1 : a ≤ b) (h2 : b + k ≤ a + n) : Free F b k :=
  ⟨h.1, by have := h.2.1; omega, fun j p q => h.2.2 j (by omega) (by omega)⟩

theorem free_next {F : Fork} {k a n : Nat} (h : Free F a n) : Free ({ F with next := k } : Fork) a n := h

/-! ## Scalars and fits -/

theorem scalars_length : ∀ {l : List Fmt.ItemValue} {s : List E}, MaskedSum.scalars l = some s → l.length = s.length :=
  fun h => by rw [scalars_holds h, List.length_map]

theorem scalars_drop {l : List Fmt.ItemValue} {s : List E} (h : MaskedSum.scalars l = some s) (n : Nat) :
    MaskedSum.scalars (l.drop n) = some (s.drop n) := by
  rw [scalars_holds h, ← List.map_drop]
  exact scalars_map _

theorem Fits.split : ∀ {a b : List Fmt.Entry} {rs : List Fmt.RoundView}, Fits (a ++ b) rs →
    ∃ u v, rs = u ++ v ∧ Fits a u ∧ Fits b v
  | [], _, rs, h => ⟨[], rs, rfl, trivial, h⟩
  | _ :: _, _, r :: _, ⟨h1, h2⟩ => by
    obtain ⟨u, v, e, a1, a2⟩ := Fits.split h2
    exact ⟨r :: u, v, by rw [e]; rfl, ⟨h1, a1⟩, a2⟩
  | _ :: _, _, [], h => h.elim

/-! ## The verbs return -/

/-- n scalars are taken. k: the slots that the later stages need. -/
theorem take_returns {n k lead : Nat} {F : Fork} {r : Fmt.RoundView} {rest : List Fmt.RoundView} {s : List E} (hz : Sized F)
    (hf : Free F F.next (n + k)) (hs : MaskedSum.scalars r.vals = some s) (hl : lead + n ≤ s.length) :
    ∃ G, take n (F, r :: rest, lead) = some (F.next, G, r :: rest, lead + n) ∧ Sized G ∧ Free G G.next k := by
  have h1 : MaskedSum.scalars ((r.vals.drop lead).take n) = some ((s.drop lead).take n) :=
    scalars_take (scalars_drop hs lead) n
  have h2 : ((s.drop lead).take n).length = n := by
    rw [List.length_take, List.length_drop]
    omega
  obtain ⟨G, hG⟩ := hideRun_returns ({ F with next := F.next + n } : Fork) F.next ((s.drop lead).take n).toArray oneE
    (by rw [List.size_toArray, h2]; exact free_next (free_sub hf (Nat.le_refl _) (by omega)))
  have hfill := hideRun_ok _ _ _ _ _ hG ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at hfill
  refine ⟨G, ?_, hfill.sized, ?_⟩
  · unfold take
    simp only [h1, Option.bind_eq_bind, Option.bind_some, h2, beq_self_eq_true, guard, if_true, Option.pure_def, hG]
  · rw [hfill.next]
    show Free G (F.next + n) k
    exact filled_free hfill (free_next (free_sub hf (by omega) (by omega))) (Or.inr (by rw [h2]))

theorem close_returns {n lead : Nat} {F : Fork} {r : Fmt.RoundView} {rest : List Fmt.RoundView} {e : Fmt.Entry} (hf : Fit e r)
    (hm : e.msg = 24 * lead) (hd : e.drawE = n) :
    close n (F, r :: rest, lead) = some (r.drawn.elems.map E.ofTriple, F, rest, 0) := by
  obtain ⟨⟨s, h1, h2⟩, h3⟩ := hf
  have : r.vals.length = lead := by rw [scalars_length h1]; omega
  unfold close
  simp [this, h3, hd]

theorem batch_returns {rows lead : Nat} {F : Fork} {r : Fmt.RoundView} {rest : List Fmt.RoundView} {e : Fmt.Entry} (hf : Fit e r)
    (hm : e.msg = 24 * lead) (hd : e.drawE = 1) :
    ∃ w, batch rows (F, r :: rest, lead) = some (w, F, rest, 0) := by
  have hc := close_returns (F := F) (rest := rest) hf hm hd
  have hl : (r.drawn.elems.map E.ofTriple).length = 1 := by rw [List.length_map, hf.2, hd]
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
  rw [hx] at hc
  exact ⟨_, (bind_some _ _ _ _ _).2 ⟨[x], _, hc, rfl⟩⟩

/-! ## A sumcheck returns -/

theorem powersFrom_length (x : E) : ∀ (n : Nat) (a : E), (MaskedSum.powersFrom x n a).length = n
  | 0, _ => rfl
  | n + 1, a => by rw [MaskedSum.powersFrom, List.length_cons, powersFrom_length x n]

theorem own_fold : ∀ (vs : List Var) (a : Nat),
    vs.foldl (fun n v => n + (v.d - 1)) a = a + (vs.map (·.d - 1)).sum
  | [], a => by simp
  | v :: vs, a => by
    rw [List.foldl_cons, own_fold vs, List.map_cons, List.sum_cons]
    omega

/-- The hiding polynomial has as many coefficients as ownSlots says. -/
theorem hiding_length : ∀ l : List (Var × E), l ≠ [] → (∀ x ∈ l, 1 ≤ x.1.d) →
    (MaskedSum.hidingAt l).1.length = MaskedSum.ownSlots (l.map (·.1))
  | [], h, _ => absurd rfl h
  | [(v, r)], _, hd => by
    have := hd (v, r) List.mem_cons_self
    simp only [MaskedSum.hidingAt, powersFrom_length, MaskedSum.ownSlots, own_fold, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp only at this
    omega
  | (v, r) :: y :: rest, _, hd => by
    have ih := hiding_length (y :: rest) (by simp) fun x hx => hd x (List.mem_cons_of_mem _ hx)
    simp only [MaskedSum.ownSlots, own_fold] at ih ⊢
    rw [MaskedSum.hidingAt]
    · simp only [List.length_append, powersFrom_length, ih, List.map_cons, List.sum_cons]
      omega
    · simp

theorem sum_returns (ret : PartReturns) {C : Aff} {vs : List Var} {e : Ends} {k lead : Nat} {F : Fork}
    {rs : List Fmt.RoundView} {es : List Fmt.Entry} (hz : Sized F) (hsh : MaskedSum.shapeOk ⟨lead, vs, some e⟩ = true)
    (hfit : Fits (MaskedSum.entries ⟨lead, vs, some e⟩ ++ es) rs) (hC : (F.publicPart C).isSome)
    (hf : Free F F.next (MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n + k)) :
    ∃ hh G rest, sum C (.sum vs e) (F, rs, lead) = some (hh, G, rest, 0) ∧ Fits es rest ∧ Sized G ∧
      Free G G.next k := by
  obtain ⟨u, v, e1, f1, f2⟩ := Fits.split hfit
  have hul : u.length = vs.length + 3 := by
    rw [f1.length]
    simp [MaskedSum.entries]
  have htake : rs.take (vs.length + 3) = u := by rw [e1, ← hul, List.take_left']; rfl
  have hdrop : rs.drop (vs.length + 3) = v := by rw [e1, ← hul, List.drop_left']; rfl
  have hsome := ret C lead vs e F u hsh f1 hC (free_sub hf (by omega) (by omega))
  obtain ⟨⟨hh, G1⟩, hh1⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨_, T, R, b1, b2, b3, b4⟩ := MaskedSum.hear_spec hh1
  obtain ⟨r0, used, rv, front, c1, c2, c3, c4, c5⟩ := MaskedSum.readAll_spec b2
  have hall : (⟨lead, vs, some e⟩ : MaskedSum.Call).all = vs ++ [.point zeroE (e.dY + 1)] := rfl
  rw [hall] at b3 b4
  rw [c5.2.1] at b4
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at F1
  -- the row's write
  have hlen : (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length =
      MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) := by
    have hz1 : (hh.vars.zip hh.r).map (·.1) = vs ++ [.point zeroE (e.dY + 1)] := by
      rw [b3]
      exact List.map_fst_zip (by rw [List.length_map, c4.length.2])
    rw [← hz1]
    refine hiding_length _ (fun h0 => ?_) fun x hx => ?_
    · rw [h0] at hz1
      simp at hz1
    · have hm : x.1 ∈ vs ++ [Var.point zeroE (e.dY + 1)] := by
        rw [← hz1]
        exact List.mem_map_of_mem hx
      rcases List.mem_append.1 hm with h1 | h1
      · simp only [MaskedSum.shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsh
        have := (hsh.1 _ h1).1
        omega
      · rw [List.mem_singleton.1 h1]
        show 1 ≤ e.dY + 1
        omega
  have hfirst : hh.first = F.next := by rw [b3]
  have hfree1 : Free G1 hh.first (Array.replicate (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length zeroE).size := by
    rw [Array.size_replicate, hlen, hfirst]
    exact filled_free F1 (free_next (free_sub hf (Nat.le_refl _) (by omega))) (Or.inl (Nat.le_refl _))
  obtain ⟨G, hG⟩ := hideRun_returns G1 hh.first _ (subE zeroE oneE) hfree1
  have F2 := hideRun_ok _ _ _ _ _ hG F1.sized
  rw [Array.toList_replicate] at F2
  refine ⟨hh, G, v, ?_, f2, F2.sized, ?_⟩
  · unfold sum
    simp only [htake, hh1, Option.bind_eq_bind, Option.bind_some, MaskedSum.row, hG, Option.pure_def, hdrop]
  · rw [F2.next, F1.next]
    show Free G (F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n) k
    refine filled_free F2 (filled_free F1 (free_next (free_sub hf (by omega) (by omega)))
      (Or.inr (by rw [c5.2.1]))) (Or.inr ?_)
    rw [List.length_replicate, hlen, hfirst]
    omega

/-! ## A start form that names filled slots alone has a public part -/

theorem shown_some {F : Fork} {j : Nat} {y f : E} (hz : Sized F) (h : Put F j y f) : (F.shown j).isSome := by
  have hj : j < F.ns := by
    rw [← hz.got]
    by_contra hc
    have := h.1
    simp [Array.getD, hc] at this
  unfold Fork.shown
  simp [hj, h.1]

theorem fold_some (F : Fork) : ∀ (l : List (Nat × E)) (v : E), (∀ x ∈ l, (F.shown x.1).isSome) →
    (l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v).isSome
  | [], _, _ => rfl
  | x :: l, v, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    rw [List.foldlM_cons, hy]
    exact fold_some F l _ fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem publicPart_some {F : Fork} {a : Aff} (h : ∀ x ∈ a.slots.toList, (F.shown x.1).isSome) :
    (F.publicPart a).isSome := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact fold_some F _ _ h

theorem slot_some {F : Fork} {j : Nat} (h : (F.shown j).isSome) : (F.publicPart (.slot j)).isSome :=
  publicPart_some fun x hx => by
    have : x = (j, oneE) := by simpa [Aff.slot] using hx
    rw [this]
    exact h

theorem const_some (F : Fork) (c : E) : (F.publicPart (.ofConst c)).isSome :=
  publicPart_some fun x hx => by simp [Aff.ofConst] at hx

theorem batched_slots (w : Array E) (first step off : Nat) : ∀ (n : Nat),
    ∀ x ∈ (batched n w first step off).slots.toList, ∃ b, b < n ∧ x.1 = first + (step * b + off)
  | 0, x, hx => by simp [batched, Aff.ofConst] at hx
  | n + 1, x, hx => by
    have e : batched (n + 1) w first step off =
        (batched n w first step off).addMul (.slot (first + (step * n + off))) (w.getD n zeroE) := by
      unfold batched
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e] at hx
    simp only [Aff.addMul, Aff.slot, List.foldl_toArray', List.foldl_cons, List.foldl_nil, Array.toList_push,
      List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · obtain ⟨b, hb, hb'⟩ := batched_slots w first step off n x h1
      exact ⟨b, by omega, hb'⟩
    · exact ⟨n, by omega, by rw [h1]⟩

theorem batched_some {F : Fork} {n : Nat} {w : Array E} {first step off : Nat}
    (h : ∀ b, b < n → (F.shown (first + (step * b + off))).isSome) :
    (F.publicPart (batched n w first step off)).isSome :=
  publicPart_some fun x hx => by
    obtain ⟨b, hb, e⟩ := batched_slots w first step off n x hx
    rw [e]
    exact h b hb

/-! ## The verbs' returns are the hearing's return -/

theorem ran_listMapM {α β : Type} (f : α → M β) : ∀ (l : List α) (bs : List β) (s s' : St),
    Ran f l bs s s' → l.mapM f s = some (bs, s')
  | [], [], s, s', h => by
    rw [List.mapM_nil, show s' = s from h]
    rfl
  | a :: l, b :: bs, s, s', ⟨s1, h1, h2⟩ => by
    rw [List.mapM_cons]
    exact (bind_some _ _ _ _ _).2 ⟨b, s1, h1, (bind_some _ _ _ _ _).2 ⟨bs, s', ran_listMapM f l bs s1 s' h2, rfl⟩⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

theorem ran_mapM {α β : Type} (f : α → M β) (a : Array α) (bs : Array β) (s s' : St)
    (h : Ran f a.toList bs.toList s s') : a.mapM f s = some (bs, s') := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  exact (bind_some _ _ _ _ _).2 ⟨bs.toList, s', ran_listMapM f _ _ _ _ h, rfl⟩

theorem ran_of_takes (n : Nat) : ∀ (l : List Nat) (js : List Nat) (s s' : St),
    TakesRan n l.length js s s' → Ran (fun _ : Nat => take n) l js s s'
  | [], [], _, _, h => h
  | _ :: l, _ :: js, _, _, ⟨s1, h1, h2⟩ => ⟨s1, h1, ran_of_takes n l js _ _ h2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

theorem ran_of_units : ∀ (l : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan l os s s' →
    Ran (fun u : Nat × Nat => (do
      let seven ← take 7
      pure (seven, ← sum (.slot (seven + 6)) (products u.1 u.2)) : M (Nat × MaskedSum.Heard))) l os s s'
  | [], [], _, _, h => h
  | _ :: l, o :: os, _, _, ⟨s1, ⟨sa, a1, a2⟩, h2⟩ =>
    ⟨s1, (bind_some _ _ _ _ _).2 ⟨o.1, sa, a1, (bind_some _ _ _ _ _).2 ⟨o.2, s1, a2, rfl⟩⟩, ran_of_units l os _ _ h2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- The converse of hear_ran. -/
theorem hear_of_ran {x : Params.AttentionRounds} {s0 s' : St} {h : Heard} (r : HearRan x s0 h s') :
    hear x s0 = some (h, s') := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, hpt, h10, h11, h12, h13, h14, h15, h16⟩ := r.ran
  unfold hear
  simp only
  refine (bind_some _ _ _ _ _).2 ⟨h.remainders, sa, ran_mapM _ _ _ _ _ (ran_of_takes 3 _ _ _ _ (by
    rw [Array.toList_range, List.length_range]; exact ha)), ?_⟩
  refine (bind_some _ _ _ _ _).2 ⟨h.scores, sb, ran_mapM _ _ _ _ _ (ran_of_units _ _ _ _ hb), ?_⟩
  refine (bind_some _ _ _ _ _).2 ⟨_, _, h1, (bind_some _ _ _ _ _).2 ⟨_, _, h2, (bind_some _ _ _ _ _).2 ⟨_, _, h3,
    (bind_some _ _ _ _ _).2 ⟨_, _, h4, (bind_some _ _ _ _ _).2 ⟨_, _, h5, (bind_some _ _ _ _ _).2 ⟨_, _, h6,
    (bind_some _ _ _ _ _).2 ⟨_, _, h7, (bind_some _ _ _ _ _).2 ⟨_, _, h8, (bind_some _ _ _ _ _).2 ⟨_, _, h9,
    (bind_some _ _ _ _ _).2 ⟨_, _, h10, (bind_some _ _ _ _ _).2 ⟨_, _, h11, (bind_some _ _ _ _ _).2 ⟨_, _, h12,
    (bind_some _ _ _ _ _).2 ⟨_, _, h13, (bind_some _ _ _ _ _).2 ⟨_, _, h14, (bind_some _ _ _ _ _).2 ⟨_, _, h15,
    (bind_some _ _ _ _ _).2 ⟨_, _, h16, ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine (pure_some _ _ _ _).2 ⟨?_, rfl⟩
  rw [← hpt]

/-! ## What is carried from stage to stage -/

/-- The slots that a stage takes. -/
def Stage.slots : Stage → Nat
  | .scalars n => n
  | .sum vs e => MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n
  | .batch _ => 0
  | .point _ => 0

/-- The slots that the stages take. -/
def slotsOf : List Stage → Nat
  | [] => 0
  | s :: l => s.slots + slotsOf l

/-- No scalars wait at the end. -/
def closed : List Stage → Bool
  | [] => true
  | .scalars _ :: l => !l.isEmpty && closed l
  | _ :: l => closed l

theorem closed_append : ∀ (l l' : List Stage), l' ≠ [] → closed l' = true → closed (l ++ l') = true
  | [], _, _, h => h
  | .scalars _ :: l, l', hn, h => by
    show (!(l ++ l').isEmpty && closed (l ++ l')) = true
    rw [closed_append l l' hn h]
    cases l <;> cases l' <;> simp_all
  | .sum _ _ :: l, l', hn, h => closed_append l l' hn h
  | .batch _ :: l, l', hn, h => closed_append l l' hn h
  | .point _ :: l, l', hn, h => closed_append l l' hn h

/-- The round in which waiting scalars ride holds at least these. -/
theorem head_scalars : ∀ (l : List Stage) (k : Nat) (rs : List Fmt.RoundView), closed l = true → l ≠ [] →
    Fits (entriesOf k l) rs → ∃ r rest s, rs = r :: rest ∧ MaskedSum.scalars r.vals = some s ∧ k ≤ s.length
  | [], _, _, _, h, _ => absurd rfl h
  | .scalars n :: l, k, rs, hc, _, hf => by
    have hc' : (!l.isEmpty && closed l) = true := hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc'
    obtain ⟨r, rest, s, a1, a2, a3⟩ := head_scalars l (k + n) rs hc'.2 hc'.1 hf
    exact ⟨r, rest, s, a1, a2, by omega⟩
  | .sum vs e :: l, k, r :: rest, _, _, hf => by
    obtain ⟨⟨s, a1, a2⟩, _⟩ := (show Fit (MaskedSum.entry "PSC epsilon" (k + 1) 1 0) r from hf.1)
    have a2' : 24 * (k + 1) = 24 * s.length := a2
    exact ⟨r, rest, s, rfl, a1, by omega⟩
  | .batch rows :: l, k, r :: rest, _, _, hf => by
    obtain ⟨⟨s, a1, a2⟩, _⟩ := hf.1
    have a2' : 24 * k = 24 * s.length := a2
    exact ⟨r, rest, s, rfl, a1, by omega⟩
  | .point n :: l, k, r :: rest, _, _, hf => by
    obtain ⟨⟨s, a1, a2⟩, _⟩ := hf.1
    have a2' : 24 * k = 24 * s.length := a2
    exact ⟨r, rest, s, rfl, a1, by omega⟩
  | .sum _ _ :: _, _, [], _, _, hf => hf.elim
  | .batch _ :: _, _, [], _, _, hf => hf.elim
  | .point _ :: _, _, [], _, _, hf => hf.elim

/-- What is carried: st: the stages still to come. -/
structure Inv (st : List Stage) (s : St) : Prop where
  sized : Sized s.1
  fits : Fits (entriesOf s.2.2 st) s.2.1
  free : Free s.1 s.1.next (slotsOf st)
  closed : closed st = true
  shapes : ∀ vs e, Stage.sum vs e ∈ st → ∀ lead, MaskedSum.shapeOk ⟨lead, vs, some e⟩ = true
  opn : ∃ pre, Open s.2.1 s.2.2 pre

theorem take_inv {n : Nat} {st : List Stage} {s : St} (h : Inv (.scalars n :: st) s) :
    ∃ j s', take n s = some (j, s') ∧ Inv st s' ∧ Stays s.1 s'.1 ∧ ∀ i, i < n → ∃ y f, Put s'.1 (j + i) y f := by
  obtain ⟨F, rs, lead⟩ := s
  have hc : (!st.isEmpty && closed st) = true := h.closed
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
  obtain ⟨r, rest, sc, a1, a2, a3⟩ := head_scalars st (lead + n) rs hc.2 hc.1 h.fits
  subst a1
  obtain ⟨G, b1, b2, b3⟩ := take_returns (rest := rest) (lead := lead) (n := n) h.sized h.free a2 a3
  obtain ⟨pre, ho⟩ := h.opn
  obtain ⟨v, c1, _, c3, _, _, c6, c7, _⟩ := take_said b1 h.sized ho
  exact ⟨F.next, (G, r :: rest, lead + n), b1,
    ⟨b2, h.fits, b3, hc.2, fun vs e hm => h.shapes vs e (List.mem_cons_of_mem _ hm), ⟨_, c3⟩⟩, c6,
    fun i hi => ⟨_, _, c7 i hi⟩⟩

theorem sum_inv (ret : PartReturns) {C : Aff} {vs : List Var} {e : Ends} {st : List Stage} {s : St}
    (h : Inv (.sum vs e :: st) s) (hC : (s.1.publicPart C).isSome) :
    ∃ hh s', sum C (.sum vs e) s = some (hh, s') ∧ Inv st s' ∧ Stays s.1 s'.1 ∧
      ∀ i, i < e.n → ∃ y f, Put s'.1 (hh.sEnd + i) y f := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨hh, G, rest, a1, a2, a3, a4⟩ := sum_returns ret (k := slotsOf st) h.sized
    (h.shapes vs e List.mem_cons_self lead) h.fits hC h.free
  obtain ⟨pre, ho⟩ := h.opn
  obtain ⟨_, H, used, _, sd⟩ := sum_said a1 h.sized ho
  exact ⟨hh, (G, rest, 0), a1, ⟨a3, a2, a4, h.closed, fun vs e hm => h.shapes vs e (List.mem_cons_of_mem _ hm),
    ⟨[], open_zero _⟩⟩, sd.stays, fun i hi => ⟨_, _, sd.ends i hi⟩⟩

theorem batch_inv {rows : Nat} {st : List Stage} {s : St} (h : Inv (.batch rows :: st) s) :
    ∃ w s', batch rows s = some (w, s') ∧ Inv st s' ∧ s'.1 = s.1 := by
  obtain ⟨F, rs, lead⟩ := s
  match rs, h with
  | [], h => exact h.fits.elim
  | r :: rest, h =>
    obtain ⟨w, hw⟩ := batch_returns (rows := rows) (F := F) (rest := rest) (lead := lead) h.fits.1 rfl rfl
    exact ⟨w, (F, rest, 0), hw, ⟨h.sized, h.fits.2, by simpa [slotsOf, Stage.slots] using h.free, h.closed,
      fun vs e hm => h.shapes vs e (List.mem_cons_of_mem _ hm), ⟨[], open_zero _⟩⟩, rfl⟩

theorem close_inv {n : Nat} {st : List Stage} {s : St} (h : Inv (.point n :: st) s) :
    ∃ d s', close n s = some (d, s') ∧ Inv st s' ∧ s'.1 = s.1 := by
  obtain ⟨F, rs, lead⟩ := s
  match rs, h with
  | [], h => exact h.fits.elim
  | r :: rest, h =>
    have hw := close_returns (n := n) (F := F) (rest := rest) (lead := lead) h.fits.1 rfl rfl
    exact ⟨_, (F, rest, 0), hw, ⟨h.sized, h.fits.2, by simpa [slotsOf, Stage.slots] using h.free, h.closed,
      fun vs e hm => h.shapes vs e (List.mem_cons_of_mem _ hm), ⟨[], open_zero _⟩⟩, rfl⟩

theorem takes_return : ∀ (k : Nat) (st : List Stage) (s : St), Inv (List.replicate k (.scalars 3) ++ st) s →
    ∃ js s', TakesRan 3 k js s s' ∧ Inv st s'
  | 0, _, s, h => ⟨[], s, rfl, h⟩
  | k + 1, st, s, h => by
    have h' : Inv (.scalars 3 :: (List.replicate k (.scalars 3) ++ st)) s := by
      rw [List.replicate_succ] at h
      exact h
    obtain ⟨j, s1, a1, a2, _, _⟩ := take_inv h'
    obtain ⟨js, s', b1, b2⟩ := takes_return k st s1 a2
    exact ⟨j :: js, s', ⟨s1, a1, b1⟩, b2⟩

theorem units_return (ret : PartReturns) : ∀ (us : List (Nat × Nat)) (st : List Stage) (s : St),
    Inv ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ st) s → ∃ os s', UnitsRan us os s s' ∧ Inv st s'
  | [], _, s, h => ⟨[], s, rfl, h⟩
  | u :: us, st, s, h => by
    have h' : Inv (.scalars 7 :: products u.1 u.2 :: ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ st)) s := by
      rw [List.flatMap_cons] at h
      exact h
    obtain ⟨j, s1, a1, a2, _, a4⟩ := take_inv h'
    obtain ⟨y, f, hy⟩ := a4 6 (by omega)
    obtain ⟨hh, s2, b1, b2, _, _⟩ := sum_inv ret (C := .slot (j + 6)) a2 (slot_some (shown_some a2.sized hy))
    obtain ⟨os, s', c1, c2⟩ := units_return ret us st s2 b2
    exact ⟨(j, hh) :: os, s', ⟨s2, ⟨s1, a1, b1⟩, c1⟩, c2⟩

/-! ## The whole -/

theorem Fits.unmap {g : Fmt.Entry → Fmt.Entry} (hm : ∀ e, (g e).msg = e.msg) (hd : ∀ e, (g e).drawE = e.drawE) :
    ∀ {es : List Fmt.Entry} {rs : List Fmt.RoundView}, Fits (es.map g) rs → Fits es rs
  | [], [], _ => trivial
  | e :: _, _ :: _, ⟨⟨⟨s, h1, h2⟩, h3⟩, h4⟩ => ⟨⟨⟨s, h1, by rw [← hm, h2]⟩, by rw [← hd, h3]⟩, Fits.unmap hm hd h4⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The stages behind the softmax-table units. -/
def tailStages (x : Params.AttentionRounds) : List Stage :=
  [.scalars 5, .scalars x.lt, .scalars 2, products x.e x.pairs, .batch 2, .scalars 2, products x.valueM x.pairs,
   products x.valueD x.pairs, .point (2 * x.lgk + 2 * x.lt + 4), .scalars x.pairs, .batch x.pairs,
   products x.attained x.pairs, .batch x.pairs, keyStage x, .batch x.pairs, products x.bits x.pairs]

theorem script_eq (x : Params.AttentionRounds) : script x = List.replicate x.planeMessages (.scalars 3) ++
    ((x.score.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ tailStages x) := by
  show List.replicate x.planeMessages (.scalars 3) ++ (x.score.flatMap fun u => [.scalars 7, products u.1 u.2]) ++
    tailStages x = _
  rw [List.append_assoc]

/-- **K5 refuses nothing but a shape.** -/
theorem hear_returns (ret : PartReturns) (p : Par) (hp : planOk p = true) {F : Fork} {rs : List Fmt.RoundView}
    (hz : Sized F) (hfit : Fits ((rounds p).map (·.entry)) rs) (hfree : Free F F.next (slotsOf (script p.own))) :
    ∃ h G, hear p.own (F, rs, 0) = some (h, G, [], 0) := by
  have hfit' : Fits (entriesOf 0 (script p.own)) rs := by
    unfold rounds at hfit
    rw [List.map_map] at hfit
    refine Fits.unmap (g := _) (fun e => ?_) (fun e => ?_) hfit
    · show (if e.drawE == 0 then e else { e with work := p.work }).msg = _
      split <;> rfl
    · show (if e.drawE == 0 then e else { e with work := p.work }).drawE = _
      split <;> rfl
  have I0 : Inv (script p.own) (F, rs, 0) :=
    ⟨hz, hfit', hfree, by
      rw [script_eq, ← List.append_assoc]
      exact closed_append _ _ (by simp [tailStages]) rfl,
      fun vs e hm lead => planOk_shape hp hm lead, ⟨[], open_zero _⟩⟩
  rw [script_eq] at I0
  obtain ⟨js, sa, ha, Ia⟩ := takes_return _ _ _ I0
  obtain ⟨os, sb, hb, Ib⟩ := units_return ret _ _ _ Ia
  obtain ⟨five, s1, h1, I1, _, g1⟩ := take_inv Ib
  obtain ⟨bits, s2, h2, I2, k2, _⟩ := take_inv I1
  obtain ⟨two, s3, h3, I3, k3, _⟩ := take_inv I2
  obtain ⟨y1, f1, p1⟩ := g1 1 (by omega)
  obtain ⟨division, s4, h4, I4, _, _⟩ := sum_inv ret (C := .slot (five + 1)) I3
    (slot_some (shown_some I3.sized (k3 _ _ _ (k2 _ _ _ p1))))
  obtain ⟨gam, s5, h5, I5, _⟩ := batch_inv I4
  obtain ⟨values, s6, h6, I6, _, g6⟩ := take_inv I5
  obtain ⟨y2, f2, p2⟩ := g6 0 (by omega)
  obtain ⟨y3, f3, p3⟩ := g6 1 (by omega)
  obtain ⟨below, s7, h7, I7, k7, _⟩ := sum_inv ret (C := .slot values) I6 (slot_some (shown_some I6.sized p2))
  obtain ⟨on, s8, h8, I8, _, _⟩ := sum_inv ret (C := .slot (values + 1)) I7
    (slot_some (shown_some I7.sized (k7 _ _ _ p3)))
  obtain ⟨pt, s9, h9, I9, _⟩ := close_inv I8
  obtain ⟨maxima, s10, h10, I10, _, g10⟩ := take_inv I9
  obtain ⟨om, s11, h11, I11, e11⟩ := batch_inv I10
  obtain ⟨atIndex, s12, h12, I12, _, g12⟩ := sum_inv ret (C := batched p.own.pairs om maxima 1 0) I11
    (batched_some fun b hb => by
      obtain ⟨y, f, hy⟩ := g10 b hb
      rw [e11, show maxima + (1 * b + 0) = maxima + b by omega]
      exact shown_some I10.sized hy)
  obtain ⟨om', s13, h13, I13, e13⟩ := batch_inv I12
  obtain ⟨key, s14, h14, I14, _, _⟩ := sum_inv ret (C := batched p.own.pairs om' atIndex.sEnd 2 1) I13
    (batched_some fun b hb => by
      obtain ⟨y, f, hy⟩ := g12 (2 * b + 1) (by show 2 * b + 1 < 2 * p.own.pairs; omega)
      rw [e13]
      exact shown_some I12.sized hy)
  obtain ⟨om'', s15, h15, I15, _⟩ := batch_inv I14
  obtain ⟨cells, ⟨G, rest, lead⟩, h16, I16, _, _⟩ := sum_inv ret (C := .ofConst zeroE) I15 (const_some _ _)
  have hh : hear p.own (F, rs, 0) = some ((⟨js.toArray, os.toArray, five, bits, two, division, gam, values, below, on,
      pt.toArray, maxima, om, atIndex, om', key, om'', cells⟩ : Heard), G, rest, lead) :=
    hear_of_ran ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1, h2, h3,
      h4, h5, h6, h7, h8, h9, rfl, h10, h11, h12, h13, h14, h15, h16⟩
  have hl : lead = 0 := hear_lead hh
  have hr : rest = [] := by
    have := I16.fits
    match rest, this with
    | [], _ => rfl
  subst hl hr
  exact ⟨_, G, hh⟩

/-- **The hearing's return is a matter of shape and room alone**: from a ledger with room, under
planOk: it returns with all
rounds used up exactly if the rounds are ROUNDS, entry for entry. -/
theorem hear_iff (ret : PartReturns) (p : Par) (hp : planOk p = true) {F : Fork} {rs : List Fmt.RoundView} (hz : Sized F)
    (hfree : Free F F.next (slotsOf (script p.own))) :
    (∃ h G, hear p.own (F, rs, 0) = some (h, G, [], 0)) ↔ Fits ((rounds p).map (·.entry)) rs :=
  ⟨fun ⟨_, _, hh⟩ => by
    obtain ⟨used, a1, a2⟩ := hear_rounds p hh
    rw [List.append_nil] at a1
    rw [a1]
    exact a2, fun hf => hear_returns ret p hp hz hf hfree⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.sum_returns
#print axioms VerifiableInference.Desc.First.Att.P.hear_of_ran
#print axioms VerifiableInference.Desc.First.Att.P.hear_returns
#print axioms VerifiableInference.Desc.First.Att.P.hear_iff
