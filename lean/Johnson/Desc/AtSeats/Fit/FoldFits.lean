-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/FoldFits.lean: "KEEPS R AT ROUNDS THAT FIT" ALONG A
LINK's FLAT LIST. WholeF R b: Fits R b (Johnson/Desc/Tidy/Fits.lean: where b's own test on the list
of rounds passes, an accepting decision on rounds that fit keeps R), and each of b's runs of claims
and runs behind the batching keeps R.
  WholeF · wholeF_of_whole · fits_planOk · fit_take | fit_drop · andThen_fitsFF | andThen_wholeF ·
  whole_sameF   NEW, typed by hand
  claimsIn_keepsF · afterIn_keepsF · LinkKeepsF · link_flat_keepsF   carried
CARRIED BY PROGRAM out of Johnson/Desc/FoldKeeps.lean (the library's): each
declaration that is needed for the top and names Decides | Whole is copied under its own name with a
letter behind it (F | W), with Fits | WholeF in that word's place; its docstrings are struck (they
are that file's); where a proof opens the word itself it is turned by hand. THE ORIGINAL IS IMPORTED
AND NOT TURNED: what names neither word is called from it.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.FoldKeeps
import Johnson.Desc.Tidy.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open VerifiableInference.Desc

variable {S Cl : Type}

def WholeF (R : S → S → Prop) (b : Block S Cl) : Prop :=
  Fits R b ∧ (∀ c ∈ b.claims, ∀ n, FnCl R (c.2 n)) ∧ ∀ c ∈ b.after, Fn R c.2

theorem wholeF_of_whole {R : S → S → Prop} {b : Block S Cl} (W : Whole R b) : WholeF R b :=
  ⟨fits_of_decides W.1, W.2.1, W.2.2⟩

theorem fits_planOk {R : S → S → Prop} {b : Block S Cl} (p : Bool) (W : Fits R b) :
    Fits R { b with planOk := b.planOk && p } :=
  fun hp s rs gs s' hf h => W ((Bool.and_eq_true _ _ ▸ hp).1) s rs gs s' hf h

theorem fit_take : ∀ (a b : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit (a ++ b) rs = true → roundsFit a (rs.take a.length) = true
  | [], _, _, _ => by simp [roundsFit]
  | _ :: _, _, [], h => by simp [roundsFit] at h
  | d :: a, b, r :: rs, h => by
    simp only [List.cons_append, roundsFit, Bool.and_eq_true] at h
    simp only [List.length_cons, List.take_succ_cons, roundsFit, Bool.and_eq_true]
    exact ⟨h.1, fit_take a b rs h.2⟩

theorem fit_drop : ∀ (a b : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit (a ++ b) rs = true → roundsFit b (rs.drop a.length) = true
  | [], _, _, h => by simpa using h
  | _ :: _, _, [], h => by simp [roundsFit] at h
  | d :: a, b, r :: rs, h => by
    simp only [List.cons_append, roundsFit, Bool.and_eq_true] at h
    simp only [List.length_cons, List.drop_succ_cons]
    exact fit_drop a b rs h.2

theorem andThen_fitsFF (R : S → S → Prop) (ht : ∀ a b c, R a b → R b c → R a c) (n : String)
    (p q : Block S Cl) (hp : Fits R p) (hq : Fits R q) : Fits R (p.andThen n q) := by
  intro hpl s rs gs s' hfit h
  have hpl' : (p.planOk && q.planOk) = true := hpl
  have hfit' : roundsFit (p.rounds ++ q.rounds) rs = true := hfit
  obtain ⟨a, h1, h2⟩ := ebind_ok
    (x := p.decide s ((rs.map noDigest).take p.rounds.length) (gs.take p.openings)) h
  rw [← List.map_take] at h1
  rw [← List.map_drop] at h2
  exact ht _ _ _ (hp (Bool.and_eq_true _ _ ▸ hpl').1 s _ _ a (fit_take _ _ _ hfit') h1)
    (hq (Bool.and_eq_true _ _ ▸ hpl').2 a _ _ s' (fit_drop _ _ _ hfit') h2)

theorem andThen_wholeF (R : S → S → Prop) (ht : ∀ a b c, R a b → R b c → R a c) (n : String)
    (p q : Block S Cl) (hp : WholeF R p) (hq : WholeF R q) : WholeF R (p.andThen n q) :=
  ⟨andThen_fitsFF R ht n p q hp.1 hq.1,
    fun c hc => (List.mem_append.1 hc).elim (hp.2.1 c) (hq.2.1 c),
    fun c hc => (List.mem_append.1 hc).elim (hp.2.2 c) (hq.2.2 c)⟩

theorem whole_sameF {R : S → S → Prop} {b c : Block S Cl} (W : WholeF R b)
    (e1 : c.decide = b.decide) (e2 : ∀ x ∈ c.claims, x ∈ b.claims) (e3 : c.after = b.after)
    (e4 : c.planOk = true → b.planOk = true) (e5 : c.rounds = b.rounds) : WholeF R c :=
  ⟨fun hp s rs gs s' hf h => W.1 (e4 hp) s rs gs s' (e5 ▸ hf) (e1 ▸ h),
    fun x hx => W.2.1 x (e2 x hx), fun x hx => W.2.2 x (e3 ▸ hx)⟩

section rule
variable (R : S → S → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
include hr ht

theorem claimsIn_keepsF (bs : List (Block S Cl)) (hb : ∀ b ∈ bs, WholeF R b)
    (order : List (Nat × String)) : FnCl R (claimsIn bs order) := by
  intro s y h
  rw [claimsIn_eq] at h
  have key : ∀ (order : List (Nat × String)) (acc : Except String (List Cl × S)),
      (∀ x, acc = .ok x → R s x.2) → ∀ y, order.foldl (stepC bs) acc = .ok y → R s y.2 := by
    intro order
    induction order with
    | nil => intro acc ha y hy; exact ha y hy
    | cons o os ih =>
      intro acc ha y hy
      refine ih (stepC bs acc o) ?_ y hy
      intro x hx
      obtain ⟨a, haa, h1⟩ := ebind_ok hx
      obtain ⟨run, hrun, h2⟩ := ebind_ok h1
      have ho := named_ok hrun
      cases hq : bs[o.1]? with
      | none => simp [hq] at ho
      | some b =>
        simp only [hq, Option.bind_some] at ho
        obtain ⟨n, hn⟩ := lookup_mem _ _ _ ho
        cases hy' : run a.1.length a.2 with
        | error e => simp [hy'] at h2
        | ok z =>
          simp only [hy', Except.ok.injEq] at h2
          subst h2
          exact ht _ a.2 _ (ha a haa)
            ((hb b (List.mem_of_getElem? hq)).2.1 (n, run) hn a.1.length a.2 z hy')
  exact key order _ (fun x hx => by cases hx; exact hr s) y h

theorem afterIn_keepsF (bs : List (Block S Cl)) (hb : ∀ b ∈ bs, WholeF R b)
    (order : List (Nat × String)) : Fn R (afterIn bs order) := by
  intro s y h
  rw [afterIn_eq] at h
  have key : ∀ (order : List (Nat × String)) (acc : Except String S),
      (∀ x, acc = .ok x → R s x) → ∀ y, order.foldl (stepA bs) acc = .ok y → R s y := by
    intro order
    induction order with
    | nil => intro acc ha y hy; exact ha y hy
    | cons o os ih =>
      intro acc ha y hy
      refine ih (stepA bs acc o) ?_ y hy
      intro x hx
      obtain ⟨a, haa, h1⟩ := ebind_ok hx
      obtain ⟨run, hrun, h2⟩ := ebind_ok h1
      have ho := named_ok hrun
      cases hq : bs[o.1]? with
      | none => simp [hq] at ho
      | some b =>
        simp only [hq, Option.bind_some] at ho
        obtain ⟨n, hn⟩ := lookup_mem _ _ _ ho
        cases hy' : run a with
        | error e => simp [hy'] at h2
        | ok z =>
          simp only [hy', Except.ok.injEq] at h2
          subst h2
          exact ht _ _ _ (ha a haa) ((hb b (List.mem_of_getElem? hq)).2.2 _ hn _ _ hy')
  exact key order _ (fun x hx => by cases hx; exact hr s) y h

def LinkKeepsF (L : Link S Cl) : Prop :=
  Fn R L.lay ∧ (∀ b ∈ L.hear, WholeF R b) ∧ (∀ f, FnCl R f → Fits R (L.batch f)) ∧
    (∀ b ∈ L.close, Fits R b) ∧ Fn R L.clear

theorem link_flat_keepsF (L : Link S Cl) (h : LinkKeepsF R L) : ∀ b ∈ L.blocksInOrder, Fits R b := by
  obtain ⟨hl, hh, hbt, hc, hcl⟩ := h
  intro b hb
  unfold Link.blocksInOrder at hb
  rcases List.mem_append.1 hb with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact fun _ s _ _ s' _ hd => hl s s' hd
        · exact (hh b h).1
      · rcases List.mem_cons.1 h with rfl | h
        · exact hbt _ fun s y hy => claimsIn_keepsF R hr ht L.hear hh L.order s y
            (claimsIn_of_claimsInBy L.each L.hear L.order s y hy)
        · rcases List.mem_cons.1 h with rfl | h
          · intro _ s _ _ s' _ hd
            have hd' : L.runBehind s = .ok s' := hd
            unfold Link.runBehind at hd'
            cases ht' : L.tests s with
            | error e => simp [ht'] at hd'
            | ok _ =>
              simp only [ht'] at hd'
              exact afterIn_keepsF R hr ht L.hear hh L.orderAfter s s' hd'
          · cases h
    · exact hc b h
  · rcases List.mem_cons.1 h with rfl | h
    · exact fun _ s _ _ s' _ hd => hcl s s' hd
    · cases h

end rule

section rule2
variable (R : S → S → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
include hr ht

end rule2

end VerifiableInference.Desc.Keeps
