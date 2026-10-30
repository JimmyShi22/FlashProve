-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Play.lean: what a chain's rounds show once `play`
(Honest/Frame.lean) has returned. Theorems on `Step.tell` and `play` alone: no description and no
prover is named.

  0  `exBind_ok`, `exMap_ok`, `exIte_ok`   on `Except`
  1  `bare`, `drawFit_bare`, `drawsFit_bare`   a challenge without the sealed digest: the lemmas
     below ask nothing of that digest, so they take their hypothesis at such challenges
  2  `Step.Yields`, `Yields`, `tell_yields`, `play_cons_ok`, `play_yields`   what a played round has
     from its `Step`
  3  `play_append`   `play` over two consecutive lists is `play`, then `play` from the state at
     which the first ends
  4  `itemsFall`, `roundsFit_of_yields`   the played rounds pass `roundsFit`
  5  `ofF_lt`, `ofE_lt`, `col_lt`, `okViewW_of_yields`   every word of a field's element that `play`
     produces is below the prime; an item `.word` is not tested

Limits.
  * No lemma of this file says that a run of `play` returns.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W X : Type}

/-! ## 0 On `Except` -/

theorem exBind_ok {ε α β : Type} {a : Except ε α} {f : α → Except ε β} {y : β}
    (h : a.bind f = .ok y) : ∃ x, a = .ok x ∧ f x = .ok y := by
  cases a with
  | error e => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem exMap_ok {ε α β : Type} {a : Except ε α} {f : α → β} {y : β}
    (h : a.map f = .ok y) : ∃ x, a = .ok x ∧ f x = y := by
  cases a with
  | error e => cases h
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

theorem exIte_ok {ε α : Type} {c : Bool} {e : ε} {t : Except ε α} {y : α}
    (h : (if c = true then Except.error e else t) = .ok y) : c = false ∧ t = .ok y := by
  cases c with
  | true => simp at h
  | false => exact ⟨rfl, by simpa using h⟩

/-! ## 1 A challenge without the sealed digest -/

/-- A challenge without the sealed digest. -/
def bare (R : Fmt.Drawn) : Fmt.Drawn := { R with digest := none }

theorem drawFit_bare (d : Fmt.DeclaredRound) (R : Fmt.Drawn) (h : drawFit d R = true) :
    drawFit d (bare R) = true := by
  simp only [drawFit, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, by simp [bare]⟩

theorem drawsFit_bare : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true → drawsFit ds (Rs.map bare) = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: Rs, h => by
    simp only [drawsFit, Bool.and_eq_true, List.map_cons] at h ⊢
    exact ⟨drawFit_bare d R h.1, drawsFit_bare ds Rs h.2⟩

/-! ## 2 What a played round has from its `Step` -/

/-- What a played round has from its `Step`. `b`: the stored run's round to fall back on. `d`: its
challenge. -/
def Step.Yields (s : Step W X) (b : Option Fmt.RoundView) (d : Fmt.Drawn) (p : Played) : Prop :=
  p.drawn = d ∧ p.place = s.addr.place ∧ p.told = s.move.isSome ∧
    (s.move.isSome = true → p.part = s.addr.part ∧ ∃ x : Sending, x.fits s.decl s.oracles = true ∧
      p.vals = x.vals.map Said.got ∧ p.tables = x.tables.map some) ∧
    (s.move.isSome = false → p.part = 0 ∧ p.vals = (b.map (·.vals)).getD [] ∧
      p.tables = List.replicate s.decl.entry.roots none)

/-- The same for a chain's rounds, one by one; false if the steps, the challenges and the played
rounds differ in number; `back` may be of any length. -/
def Yields : List (Step W X) → List Fmt.Drawn → List Fmt.RoundView → List Played → Prop
  | [], [], _, [] => True
  | s :: ss, d :: ds, back, p :: ps => s.Yields back.head? d p ∧ Yields ss ds back.tail ps
  | _, _, _, _ => False

/-- What a round's message consists of. -/
theorem tell_yields {s : Step W X} {b : Option Fmt.RoundView} {m : Mid W X} {x : Told}
    (h : s.tell b m = .ok x) :
    x.told = s.move.isSome ∧
      (s.move.isSome = true → ∃ z : Sending, z.fits s.decl s.oracles = true ∧
        x.vals = z.vals.map Said.got ∧ x.tables = z.tables.map some) ∧
      (s.move.isSome = false → x.vals = (b.map (·.vals)).getD [] ∧
        x.tables = List.replicate s.decl.entry.roots none) := by
  cases hst : s.stop m.loc s.nth with
  | some e => simp [Step.tell, hst] at h
  | none =>
    cases hmv : s.move with
    | none =>
      simp only [Step.tell, hst, hmv] at h
      cases h
      exact ⟨rfl, fun h => by simp at h, fun _ => ⟨rfl, rfl⟩⟩
    | some mv =>
      cases hz : mv.say () m.shown m.st with
      | error e => simp [Step.tell, hst, hmv, hz] at h
      | ok z =>
        cases hf : z.fits s.decl s.oracles with
        | false => simp [Step.tell, hst, hmv, hz, hf] at h
        | true =>
          simp [Step.tell, hst, hmv, hz, hf] at h
          subst h
          exact ⟨rfl, fun _ => ⟨z, hf, rfl, rfl⟩, fun h => by simp at h⟩

/-- What a run of `play` over a first round and the others consists of. -/
theorem play_cons_ok {s : Step W X} {ss : List (Step W X)} {d : Fmt.Drawn} {ds : List Fmt.Drawn}
    {back : List Fmt.RoundView} {m : Mid W X} {y : List Played × Mid W X}
    (h : play (s :: ss) (d :: ds) back m = .ok y) :
    ∃ x m' z, s.tell back.head? m = .ok x ∧ s.hear x d m = .ok m' ∧
      play ss ds back.tail m' = .ok z ∧
      y = (⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables, d⟩ ::
        z.1, z.2) := by
  rw [play] at h
  obtain ⟨x, hx, h⟩ := exBind_ok h
  obtain ⟨m', hm, h⟩ := exBind_ok h
  obtain ⟨z, hz, h⟩ := exMap_ok h
  exact ⟨x, m', z, hx, hm, hz, h.symm⟩

theorem play_yields : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y → Yields ss ds back y.1
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    exact trivial
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, hx, -, hz, rfl⟩ := play_cons_ok h
    obtain ⟨t1, t2, t3⟩ := tell_yields hx
    have hs : s.Yields back.head? d ⟨s.name, s.addr.place,
        if x.told then s.addr.part else 0, x.told, x.vals, x.tables, d⟩ := by
      unfold Step.Yields
      exact ⟨rfl, rfl, t1, fun hs => ⟨by simp [t1, hs], t2 hs⟩,
        fun hs => ⟨by simp [t1, hs], t3 hs⟩⟩
    exact And.intro hs (play_yields ss ds back.tail m' z hz)

/-! ## 3 Two consecutive lists -/

theorem play_append_aux (l₂ : List (Step W X)) (d₂ : List Fmt.Drawn) :
    ∀ (l₁ : List (Step W X)) (d₁ : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X),
    d₁.length = l₁.length →
    play (l₁ ++ l₂) (d₁ ++ d₂) back m =
      (play l₁ d₁ back m).bind fun y =>
        (play l₂ d₂ (back.drop l₁.length) y.2).map fun z => (y.1 ++ z.1, z.2)
  | [], [], back, m, _ => by
    cases h : play l₂ d₂ back m <;> simp [play, Except.bind, Except.map, h]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | s :: ss, d :: ds, back, m, hl => by
    have hb : back.tail.drop ss.length = back.drop (ss.length + 1) := by cases back <;> simp
    cases hx : s.tell back.head? m with
    | error e => simp [play, hx, Except.bind]
    | ok x =>
      cases hm : s.hear x d m with
      | error e => simp [play, hx, hm, Except.bind]
      | ok m' =>
        have ih := play_append_aux l₂ d₂ ss ds back.tail m' (by simpa using hl)
        rw [hb] at ih
        cases hz : play ss ds back.tail m' with
        | error e =>
          rw [hz] at ih
          simp [play, hx, hm, hz, ih, Except.bind, Except.map]
        | ok z =>
          rw [hz] at ih
          cases hw : play l₂ d₂ (back.drop (ss.length + 1)) z.2 <;>
            simp [play, hx, hm, hz, ih, hw, Except.bind, Except.map]

theorem play_append (l₁ l₂ : List (Step W X)) (d₁ d₂ : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (h : d₁.length = l₁.length) :
    play (l₁ ++ l₂) (d₁ ++ d₂) back m =
      (play l₁ d₁ back m).bind fun y =>
        (play l₂ d₂ (back.drop l₁.length) y.2).map fun z => (y.1 ++ z.1, z.2) :=
  play_append_aux l₂ d₂ l₁ d₁ back m h

/-! ## 4 The rounds -/

/-- Where no prover's side is defined, what is fallen back on shows exactly the items that the
round's entry cuts, except for the roots. With no stored run to fall back on: that entry cuts none.
-/
def itemsFall : List (Step W X) → List Fmt.RoundView → Bool
  | [], _ => true
  | s :: ss, back =>
    (s.move.isSome ||
      ((back.head?.map (·.vals)).getD []).map itemOf == s.decl.items.filter (· != .root)) &&
      itemsFall ss back.tail

theorem roundsFit_of_yields : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → drawsFit (ss.map (·.decl)) (ds.map bare) = true →
    itemsFall ss back = true → roundsFit (ss.map (·.decl)) (roundsOf ps) = true := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h _ _
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h hd hi
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        simp only [List.map_cons, drawsFit, Bool.and_eq_true] at hd
        simp only [itemsFall, Bool.and_eq_true, Bool.or_eq_true] at hi
        obtain ⟨⟨hdr, -, -, htold, hnot⟩, hrest⟩ := h
        obtain ⟨hd1, hd2⟩ := hd
        subst hdr
        simp only [drawFit, Bool.and_eq_true] at hd1
        obtain ⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, -⟩, -⟩ := hd1
        have hcons : roundsFit (s.decl :: ss.map (·.decl)) (⟨p.vals, p.drawn⟩ :: roundsOf ps) =
            true := by
          simp only [roundsFit, Bool.and_eq_true]
          refine ⟨⟨⟨⟨⟨⟨⟨?_, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, ih ds back.tail ps hrest hd2 hi.2⟩
          cases hm : s.move.isSome with
          | true =>
            obtain ⟨-, x, hx, hv, -⟩ := htold hm
            simp only [Sending.fits, Bool.and_eq_true] at hx
            rw [hv, List.map_map]
            exact hx.1
          | false =>
            obtain ⟨-, hv, -⟩ := hnot hm
            rcases hi.1 with h1 | h1
            · rw [hm] at h1
              cases h1
            · rw [hv]
              exact h1
        exact hcons

/-! ## 5 The words -/

/-- The word that is written for an element of the base field is below the prime. -/
theorem ofF_lt (x : Cb.Gl.F) : OnBytes.Slice.ofF x < fieldPrimeWord := by
  have h := OnBytes.Slice.ok_ofF x
  have hp : fieldPrimeWord.toNat = Fmt.Fld.two.p := by decide
  rw [UInt64.lt_iff_toNat_lt, hp]
  exact of_decide_eq_true h

/-- So are the three words that are written for an element of the extension field. -/
theorem ofE_lt (x : Cb.Gl.E) : (OnBytes.Slice.ofE x).1 < fieldPrimeWord ∧
    (OnBytes.Slice.ofE x).2.1 < fieldPrimeWord ∧ (OnBytes.Slice.ofE x).2.2 < fieldPrimeWord :=
  ⟨ofF_lt _, ofF_lt _, ofF_lt _⟩

/-- So is every word of every column of a table. -/
theorem col_lt (t : Table) (x : Nat) : ∀ a ∈ t.col x, a < fieldPrimeWord := by
  intro a ha
  simp only [Table.col, List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact ofF_lt _

theorem okViewW_of_yields : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → drawsFit (ss.map (·.decl)) (ds.map bare) = true →
    viewWordsBelowPrime ⟨back, []⟩ = true → viewWordsBelowPrime ⟨roundsOf ps, []⟩ = true := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h _ _
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h hd hb
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        simp only [List.map_cons, drawsFit, Bool.and_eq_true] at hd
        obtain ⟨⟨hdr, -, -, htold, hnot⟩, hrest⟩ := h
        obtain ⟨hd1, hd2⟩ := hd
        subst hdr
        simp only [drawFit, Bool.and_eq_true] at hd1
        obtain ⟨⟨-, b7⟩, -⟩ := hd1
        have hbt : viewWordsBelowPrime ⟨back.tail, []⟩ = true := by
          cases back with
          | nil => exact hb
          | cons r rs =>
            simp only [viewWordsBelowPrime, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
              List.tail_cons] at hb ⊢
            exact hb.2
        have ihp := ih ds back.tail ps hrest hd2 hbt
        simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true] at ihp hb ⊢
        have hcons : roundsOf (p :: ps) = ⟨p.vals, p.drawn⟩ :: roundsOf ps := rfl
        rw [hcons, List.all_cons, Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨b7, ?_⟩, ihp⟩
        cases hm : s.move.isSome with
        | true =>
          obtain ⟨-, x, -, hv, -⟩ := htold hm
          show (List.all p.vals _) = true
          rw [hv, List.all_map, List.all_eq_true]
          intro v _
          cases v <;> simp [Said.got, OnBytes.Slice.ofE, ofF_lt]
        | false =>
          obtain ⟨-, hv, -⟩ := hnot hm
          show (List.all p.vals _) = true
          rw [hv]
          cases back with
          | nil => rfl
          | cons r rs =>
            rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at hb
            exact hb.1.2

end ProofFile.Honest

#print axioms ProofFile.Honest.exBind_ok
#print axioms ProofFile.Honest.exMap_ok
#print axioms ProofFile.Honest.exIte_ok
#print axioms ProofFile.Honest.drawFit_bare
#print axioms ProofFile.Honest.drawsFit_bare
#print axioms ProofFile.Honest.tell_yields
#print axioms ProofFile.Honest.play_cons_ok
#print axioms ProofFile.Honest.play_yields
#print axioms ProofFile.Honest.play_append_aux
#print axioms ProofFile.Honest.play_append
#print axioms ProofFile.Honest.roundsFit_of_yields
#print axioms ProofFile.Honest.ofF_lt
#print axioms ProofFile.Honest.ofE_lt
#print axioms ProofFile.Honest.col_lt
#print axioms ProofFile.Honest.okViewW_of_yields
#print axioms ProofFile.Honest.bare
#print axioms ProofFile.Honest.Step.Yields
#print axioms ProofFile.Honest.Yields
#print axioms ProofFile.Honest.itemsFall
