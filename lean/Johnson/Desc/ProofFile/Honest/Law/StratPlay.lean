-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratPlay.lean: a chain's transcript as the strategies write it
(`trOf`, Honest/Law/StratChain.lean), read by the library's own readers of a transcript, compared
with what `play` (Honest/Frame.lean) returns at the same challenges. No description and no prover is
named. The main lemma is `trOf_play`.

  1  `trOf_take`, `endOf_take`   of the `Step`s, `trOf` and `endOf` read as many as the data have
     rounds
  2  `yields_tables`, `tables_sent`, `tablesOf_cons`   the n-th table that was sent has the length
     and width of the n-th declared oracle message, if each round declares as many oracle messages
     as its entry counts roots
  3  `RoundFits`, `posAtT_some`, `trOf_play`   if `play` returns with no stored run to fall back on,
     the data fit the `Step`s one by one, a prover's side is defined wherever an item other than a
     root is declared, and each round declares as many oracle messages as its entry counts roots:
     then `rvT` reads the rounds of `play` from `trOf`, `endOf` is the state at which `play` ends,
     and `colAtST` reads the columns of the tables that were sent

Limits.
  * Nothing is said of a whole file or of a view's opened columns.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Play
import Johnson.Desc.ProofFile.Honest.Law.StratChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT roundT drawnT rvT colAtST PosT posAtT colT)
open _root_.Run.PQ (CK PlainOf)

variable {W X Y : Type}

/-! ## 1 As many rounds as the data have -/

theorem trOf_take (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)), trOf C ds ss m ρ = trOf C ds (ss.take ds.length) m ρ
  | [], _, _, _ => rfl
  | _ :: _, [], _, (_, _) => rfl
  | d :: ds, s :: ss, m, (c, ρ) =>
    congrArg (fun (τ : Iop.Tr (uLT C ds)) =>
        ((msgOf C d (tellAt (some s) m), c, τ) : Iop.Tr (uLT C (d :: ds))))
      (trOf_take C ds ss (hearAt (some s) (tellAt (some s) m) (drOf C d c) m) ρ)

theorem endOf_take (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)), endOf C ds ss m ρ = endOf C ds (ss.take ds.length) m ρ
  | [], _, _, _ => rfl
  | _ :: _, [], _, (_, _) => rfl
  | d :: ds, s :: ss, m, (c, ρ) =>
    endOf_take C ds ss (hearAt (some s) (tellAt (some s) m) (drOf C d c) m) ρ

/-! ## 2 The tables that were sent -/

theorem yields_tables {s : Step W X} {b : Option Fmt.RoundView} {d : Fmt.Drawn} {p : Played}
    (h : s.Yields b d p) (ho : s.oracles.length = s.decl.entry.roots) :
    p.tables.length = s.oracles.length ∧ ∀ (n : Nat) (t : Table), p.tables[n]? = some (some t) →
      (s.oracles.map fun o => (o.logLength, o.words))[n]? = some (t.logLength, t.words) := by
  obtain ⟨-, -, -, ht, hn⟩ := h
  cases hm : s.move.isSome with
  | true =>
    obtain ⟨-, x, hx, -, htab⟩ := ht hm
    simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hx
    have e := hx.2
    refine ⟨?_, ?_⟩
    · have h1 := congrArg List.length e
      rw [List.length_map, List.length_map] at h1
      rw [htab, List.length_map, h1]
    · intro n t hnt
      rw [htab, List.getElem?_map] at hnt
      have h1 : x.tables[n]? = some t := by
        cases hx' : x.tables[n]? with
        | none =>
          rw [hx'] at hnt
          cases hnt
        | some t' =>
          rw [hx'] at hnt
          cases hnt
          rfl
      rw [← e, List.getElem?_map, h1]
      rfl
  | false =>
    obtain ⟨-, -, htab⟩ := hn hm
    refine ⟨by rw [htab, List.length_replicate, ho], ?_⟩
    intro n t hnt
    rw [htab] at hnt
    have h1 := (List.mem_replicate.1 (List.mem_of_getElem? hnt)).2
    cases h1

theorem tablesOf_cons (p : Played) (ps : List Played) :
    tablesOf (p :: ps) = (p.tables.map fun t => t.map fun x => (p.place, x)) ++ tablesOf ps := rfl

theorem tables_sent : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    ∀ (n : Nat) (pt : Place × Table), ((tablesOf ps)[n]?).bind id = some pt →
      ((ss.flatMap (·.oracles)).map fun o => (o.logLength, o.words))[n]? =
        some (pt.2.logLength, pt.2.words) := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h _ n pt hn
    cases ps with
    | nil => simp [tablesOf] at hn
    | cons p ps => cases ds <;> simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h ho n pt hn
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        obtain ⟨hl, ht⟩ := yields_tables h.1 (ho s List.mem_cons_self)
        rw [List.flatMap_cons, List.map_append]
        rw [tablesOf_cons] at hn
        by_cases hlt : n < p.tables.length
        · rw [List.getElem?_append_left (by rw [List.length_map]; exact hlt),
            List.getElem?_map] at hn
          rw [List.getElem?_append_left (by rw [List.length_map, ← hl]; exact hlt)]
          cases hp : p.tables[n]? with
          | none =>
            rw [hp] at hn
            cases hn
          | some o =>
            rw [hp] at hn
            cases o with
            | none => cases hn
            | some t =>
              cases hn
              exact ht n t hp
        · have hge : p.tables.length ≤ n := Nat.le_of_not_lt hlt
          rw [List.getElem?_append_right (by rw [List.length_map]; exact hge),
            List.length_map] at hn
          rw [List.getElem?_append_right (by rw [List.length_map, ← hl]; exact hge),
            List.length_map, ← hl]
          exact ih ds back.tail ps h.2 (fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')) _ pt hn

/-! ## 3 The transcript, read -/

/-- A round's data agree with a round's items and declared oracle messages. -/
def RoundFits (d : RDT) (z : Fmt.DeclaredRound × List Oracle) : Prop :=
  d.items = z.1.items ∧ (d.trees.map fun t => (t.a, t.W)) = z.2.map fun o => (o.logLength, o.words)

theorem posAtT_some : ∀ (ts : List Fmt.Shape) (n x : Nat) (s : Fmt.Shape), ts[n]? = some s →
    x < 2 ^ s.a → ∃ p, posAtT ts n x = some p
  | [], _, _, _, h, _ => by simp at h
  | s₀ :: ts, 0, x, s, h, hx => by
    have hs : s₀ = s := by simpa using h
    subst hs
    exact ⟨.inl ⟨x, hx⟩, dif_pos hx⟩
  | s₀ :: ts, n + 1, x, s, h, hx => by
    obtain ⟨p, hp⟩ := posAtT_some ts n x s (by simpa using h) hx
    refine ⟨.inr p, ?_⟩
    show (posAtT ts n x).map Sum.inr = _
    rw [hp]
    rfl

theorem trOf_play (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Mid W Y)
    (ρ : Iop.Rho (uLT C ds)) (y : List Played × Mid W Y),
    play ss (drawnT C ds ρ) [] m = .ok y →
    List.Forall₂ RoundFits ds (ss.map fun s => (s.decl, s.oracles)) →
    itemsFall ss [] = true → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    rvT C ds (trOf C ds ss (some m) ρ) = roundsOf y.1 ∧ endOf C ds ss (some m) ρ = some y.2 ∧
      ∀ (n x : Nat) (pt : Place × Table), ((tablesOf y.1)[n]?).bind id = some pt →
        x < 2 ^ pt.2.logLength → colAtST C ds (trOf C ds ss (some m) ρ) n x = some (pt.2.col x)
  | [], [], m, ρ, y, hp, _, _, _ => by
    have hp' : (Except.ok ([], m) : Except Refusal (List Played × Mid W Y)) = .ok y := hp
    cases hp'
    exact ⟨rfl, rfl, fun n x pt h => by simp [tablesOf] at h⟩
  | [], _ :: _, _, _, _, _, hF, _, _ => by
    rw [List.map_cons] at hF
    cases hF
  | _ :: _, [], _, _, _, _, hF, _, _ => by cases hF
  | d :: ds, s :: ss, m, (c, ρ), y, hp, hF, hi, ho => by
    have hp' : play (s :: ss) (drOf C d c :: drawnT C ds ρ) [] m = .ok y := hp
    obtain ⟨x, m', z, hx, hm, hz, rfl⟩ := play_cons_ok hp'
    rw [List.map_cons] at hF
    obtain ⟨⟨hit, htr⟩, hF'⟩ := List.forall₂_cons.1 hF
    have hi' : ((s.move.isSome ||
        (([] : List Fmt.ItemValue).map itemOf == s.decl.items.filter (· != .root))) &&
        itemsFall ss []) = true := hi
    rw [Bool.and_eq_true, Bool.or_eq_true] at hi'
    obtain ⟨ih1, ih2, ih3⟩ := trOf_play C ds ss m' ρ z hz hF' hi'.2
      fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')
    have hy := play_yields _ _ _ _ _ hp'
    have hy1 : s.Yields none (drOf C d c) ⟨s.name, s.addr.place,
        if x.told then s.addr.part else 0, x.told, x.vals, x.tables, drOf C d c⟩ := hy.1
    obtain ⟨hl, ht⟩ := yields_tables hy1 (ho s List.mem_cons_self)
    have hte : tellAt (some s) (some m) = some x := by
      show (s.tell none m).toOption = some x
      rw [show s.tell none m = .ok x from hx]
      rfl
    have hhe : hearAt (some s) (some x) (drOf C d c) (some m) = some m' := by
      show (s.hear x (drOf C d c) m).toOption = some m'
      rw [hm]
      rfl
    have htrO : trOf C (d :: ds) (s :: ss) (some m) (c, ρ) =
        ((msgOf C d (some x), c, trOf C ds ss (some m') ρ) : Iop.Tr (uLT C (d :: ds))) := by
      show ((msgOf C d (tellAt (some s) (some m)), c, trOf C ds ss
        (hearAt (some s) (tellAt (some s) (some m)) (drOf C d c) (some m)) ρ) :
          Iop.Tr (uLT C (d :: ds))) = _
      rw [hte, hhe]
    have hend : endOf C (d :: ds) (s :: ss) (some m) (c, ρ) = endOf C ds ss (some m') ρ := by
      show endOf C ds ss (hearAt (some s) (tellAt (some s) (some m)) (drOf C d c) (some m)) ρ = _
      rw [hte, hhe]
    have hvals : x.vals.map itemOf = d.items.filter (· != .root) := by
      rw [hit]
      obtain ⟨-, -, -, h1, h2⟩ := hy1
      cases hmv : s.move.isSome with
      | true =>
        obtain ⟨-, u, hu, hv, -⟩ := h1 hmv
        simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hu
        have hv' : x.vals = u.vals.map Said.got := hv
        rw [hv', List.map_map]
        exact hu.1
      | false =>
        obtain ⟨-, hv, -⟩ := h2 hmv
        have hv' : x.vals = [] := hv
        rcases hi'.1 with h3 | h3
        · rw [hmv] at h3
          cases h3
        · rw [hv']
          exact beq_iff_eq.1 h3
    have hlen : x.tables.length = d.trees.length := by
      have h1 := congrArg List.length htr
      rw [List.length_map, List.length_map] at h1
      have h2 : x.tables.length = s.oracles.length := hl
      rw [h2, h1]
    refine ⟨?_, ?_, ?_⟩
    · rw [htrO]
      show (⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (Iop.GPlain.mk d.entry.work (plainOf d.items x.vals) (0 : ℕ))), drOf C d c⟩ : Fmt.RoundView) ::
          rvT C ds (trOf C ds ss (some m') ρ) = ⟨x.vals, drOf C d c⟩ :: roundsOf z.1
      rw [Iop.GPlain.old_mk, gots_plainOf _ _ hvals, ih1]
    · rw [hend]
      exact ih2
    · intro n k pt hn hk
      rw [htrO, OnBytes.Maker.colAtST_cons]
      have hn' : (((x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++
          tablesOf z.1)[n]?).bind id = some pt := hn
      by_cases hlt : n < d.trees.length
      · rw [if_pos hlt]
        rw [List.getElem?_append_left (by rw [List.length_map, hlen]; exact hlt),
          List.getElem?_map] at hn'
        cases hp1 : x.tables[n]? with
        | none =>
          rw [hp1] at hn'
          cases hn'
        | some o =>
          rw [hp1] at hn'
          cases o with
          | none => cases hn'
          | some t =>
            cases hn'
            have h4 := ht n t hp1
            rw [← htr, List.getElem?_map] at h4
            cases hs1 : d.trees[n]? with
            | none =>
              rw [hs1] at h4
              cases h4
            | some sh =>
              rw [hs1] at h4
              have h5 : (sh.a, sh.W) = (t.logLength, t.words) := Option.some.inj h4
              have ha : sh.a = t.logLength := (Prod.mk.inj h5).1
              have hw : t.words = sh.W := (Prod.mk.inj h5).2.symm
              obtain ⟨q, hq⟩ := posAtT_some d.trees n k sh hs1 (by rw [ha]; exact hk)
              rw [hq]
              exact congrArg some (colT_orcOf d.trees x.tables n k q t sh hq hp1 hs1 hw)
      · rw [if_neg hlt]
        have hge : d.trees.length ≤ n := Nat.le_of_not_lt hlt
        rw [List.getElem?_append_right (by rw [List.length_map, hlen]; exact hge),
          List.length_map, hlen] at hn'
        exact ih3 _ k pt hn' hk

end ProofFile.Honest

#print axioms ProofFile.Honest.trOf_take
#print axioms ProofFile.Honest.endOf_take
#print axioms ProofFile.Honest.yields_tables
#print axioms ProofFile.Honest.tablesOf_cons
#print axioms ProofFile.Honest.tables_sent
#print axioms ProofFile.Honest.posAtT_some
#print axioms ProofFile.Honest.trOf_play
