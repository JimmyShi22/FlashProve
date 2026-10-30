-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/GathersPlain.lean: `Gathers` (Johnson/Desc/K8/Honest/FallCount.lean) AT EVERY
SEGMENT WHOSE RUNS OF CLAIMS, BUT FOR "K8.equations", ARE FREE OF THE BATCHING ELEMENT. Statements
and proofs. No prover. Lemmas; none of the library's goals.

The states behind the batching draw at two drawn elements, from one state in front, differ in the
ledger's batching element alone (`drawnAt_re`). Runs that are free of it (`PlainRun`, `PlainBehind`:
Johnson/Desc/K8/Honest/PlainRuns.lean) return the same claims at both. So the plain claims'
coefficients are those of any one yes.
  `runAll_append`, `pre_one`, `pre_two`, `post_one`, `post_two`   a stretch of the order, walked
      once, and walked at two states of which one is the other's image
  `set_re`, `drawnAt_re`, `drawnAt_part`, `set_tl`, `set_funs`   the draw
  `k8_two`      "K8.equations" at two such states: the same first four claims, the same length, and
      the states behind are images with the smallness test's data replaced
  `Walk`, `walk_one`, `walk_two`   a yes of the whole function of claims, cut in its three stretches
  **`gathers_of_plain`**   L's order is pre ++ [(i, "K8.equations")] ++ post; each run that L's
      blocks state at an entry of pre stands under a `PlainRun`, at (i, "K8.equations") under the
      smallness test's own run, at an entry of post under a `PlainBehind`: then at every state s
      that holds data tl and a list of tables funs: `Gathers` at tl and funs, at SOME numbers and
      coefficients
"K8.equations" reads the ledger's count of claims into two fields of the data that it returns, into
no claim.
Limits: which run stands under which is a premise.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law

/-! ## Lists -/

theorem get_front {α : Type} (A B C : List α) (c : Nat) (x : α)
    (h : (A ++ B.take 4)[c]? = some x) : (A ++ B ++ C)[c]? = some x := by
  have e : A ++ B ++ C = (A ++ B.take 4) ++ (B.drop 4 ++ C) := by
    rw [List.append_assoc A (B.take 4), ← List.append_assoc (B.take 4), List.take_append_drop,
      List.append_assoc]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  rw [e, List.getElem?_append_left hlt]
  exact h

theorem get_back {α : Type} (A B C : List α) (c : Nat) :
    (A ++ B ++ C)[A.length + B.length + c]? = C[c]? := by
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ## A stretch of the order -/

section
variable {T Cl : Type}

theorem runAll_append (each : Nat × String → List Cl → T → Except String Unit)
    (bs : List (Block T Cl)) : ∀ (os₁ os₂ : List (Nat × String)) (x : List Cl × T),
    runAll each bs (os₁ ++ os₂) x = (runAll each bs os₁ x).bind (runAll each bs os₂)
  | [], _, _ => rfl
  | o :: os, os₂, x => by
    show (claimsInStep each bs x o).bind (runAll each bs (os ++ os₂)) =
      ((claimsInStep each bs x o).bind (runAll each bs os)).bind (runAll each bs os₂)
    cases claimsInStep each bs x o with
    | error e => rfl
    | ok z => exact runAll_append each bs os os₂ z

end

/-- Each run that L's blocks state at an entry of os stands under a run that is free of the batching
element. -/
def PreOk (L : Link S Claim) (os : List (Nat × String)) : Prop :=
  ∀ o ∈ os, ∀ run, LinkJoin.At L o run → ∃ f, LinkJoin.Under run f ∧ PlainRun f

def PostOk (L : Link S Claim) (os : List (Nat × String)) : Prop :=
  ∀ o ∈ os, ∀ run, LinkJoin.At L o run → ∃ f, LinkJoin.Under run f ∧ PlainBehind f

theorem pre_one (L : Link S Claim) : ∀ (os : List (Nat × String)), PreOk L os →
    ∀ (x z : List Claim × S), runAll L.each L.hear os x = .ok z →
    ∃ c, z.1 = x.1 ++ c ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧ z.2.tl? = x.2.tl? ∧
      z.2.funs? = x.2.funs? ∧
      ∀ a, K9.atS.get? x.2 = some a → ∃ b, K9.atS.get? z.2 = some b ∧ SameSums a.F b.F
  | [], _, x, z, h => by
    obtain rfl : x = z := Except.ok.inj h
    exact ⟨[], by simp, by simp, rfl, rfl, fun a ha => ⟨a, ha, SameSums.refl _⟩⟩
  | o :: os, H, x, z, h => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨f, hu, hp⟩ := H o (by simp) run hat
    have hf := hu _ _ _ _ hy
    obtain ⟨c2, e1, e2, e3, e4, e5⟩ :=
      pre_one L os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) _ z g2
    refine ⟨c ++ c2, by rw [e1, List.append_assoc], ?_, e3.trans (hp.data _ _ _ hf).1,
      e4.trans (hp.data _ _ _ hf).2, ?_⟩
    · intro cl hcl
      rcases List.mem_append.1 hcl with h1 | h1
      · exact hp.plain _ _ _ hf cl h1
      · exact e2 cl h1
    · intro a ha
      obtain ⟨b, hb, s1⟩ := hp.ledger _ _ _ a hf ha
      obtain ⟨b2, hb2, s2⟩ := e5 b hb
      exact ⟨b2, hb2, s1.trans s2⟩

theorem pre_two (L : Link S Claim) : ∀ (os : List (Nat × String)), PreOk L os →
    ∀ (x x' z z' : List Claim × S) (θ : E), x'.1.length = x.1.length → x'.2 = reChi θ x.2 →
    runAll L.each L.hear os x = .ok z → runAll L.each L.hear os x' = .ok z' →
    ∃ c, z.1 = x.1 ++ c ∧ z'.1 = x'.1 ++ c ∧ z'.2 = reChi θ z.2
  | [], _, x, x', z, z', θ, _, hx, h, h' => by
    obtain rfl : x = z := Except.ok.inj h
    obtain rfl : x' = z' := Except.ok.inj h'
    exact ⟨[], by simp, by simp, hx⟩
  | o :: os, H, x, x', z, z', θ, hl, hx, h, h' => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨w', g1', g2'⟩ := bind_ok h'
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨run', c', e', hat', hy', rfl⟩ := step_ok g1'
    obtain rfl : run = run' := Option.some.inj (hat.symm.trans hat')
    obtain ⟨f, hu, hp⟩ := H o (by simp) run hat
    have hf := hu _ _ _ _ hy
    have hf' := hu _ _ _ _ hy'
    rw [hl, hx] at hf'
    have hh := hp.free _ _ θ _ _ hf hf'
    have hc : c' = c := congrArg Prod.fst hh
    have he : e' = reChi θ e := congrArg Prod.snd hh
    rw [hc, he] at g2'
    obtain ⟨c2, e1, e2, e3⟩ :=
      pre_two L os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) (x.1 ++ c, e)
        (x'.1 ++ c, reChi θ e) z z' θ (by simp [hl]) rfl g2 g2'
    exact ⟨c ++ c2, by rw [e1, List.append_assoc], by rw [e2, List.append_assoc], e3⟩

theorem post_one (L : Link S Claim) : ∀ (os : List (Nat × String)), PostOk L os →
    ∀ (x z : List Claim × S), runAll L.each L.hear os x = .ok z →
    ∃ c, z.1 = x.1 ++ c ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧ z.2.tl? = x.2.tl? ∧
      ∀ a, K9.atS.get? x.2 = some a → ∃ b, K9.atS.get? z.2 = some b ∧ SameSums a.F b.F
  | [], _, x, z, h => by
    obtain rfl : x = z := Except.ok.inj h
    exact ⟨[], by simp, by simp, rfl, fun a ha => ⟨a, ha, SameSums.refl _⟩⟩
  | o :: os, H, x, z, h => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨f, hu, hp⟩ := H o (by simp) run hat
    have hf := hu _ _ _ _ hy
    obtain ⟨c2, e1, e2, e3, e5⟩ :=
      post_one L os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) _ z g2
    refine ⟨c ++ c2, by rw [e1, List.append_assoc], ?_, e3.trans (hp.data _ _ (c, e) hf), ?_⟩
    · intro cl hcl
      rcases List.mem_append.1 hcl with h1 | h1
      · exact hp.plain _ _ _ hf cl h1
      · exact e2 cl h1
    · intro a ha
      obtain ⟨b, hb, s1⟩ := hp.ledger _ _ _ a hf ha
      obtain ⟨b2, hb2, s2⟩ := e5 b hb
      exact ⟨b2, hb2, s1.trans s2⟩

theorem post_two (L : Link S Claim) : ∀ (os : List (Nat × String)), PostOk L os →
    ∀ (x x' z z' : List Claim × S) (θ : E) (tl : HTailF2), x'.1.length = x.1.length →
    x'.2 = reBoth θ tl x.2 →
    runAll L.each L.hear os x = .ok z → runAll L.each L.hear os x' = .ok z' →
    ∃ c, z.1 = x.1 ++ c ∧ z'.1 = x'.1 ++ c ∧ z'.2 = reBoth θ tl z.2
  | [], _, x, x', z, z', θ, tl, _, hx, h, h' => by
    obtain rfl : x = z := Except.ok.inj h
    obtain rfl : x' = z' := Except.ok.inj h'
    exact ⟨[], by simp, by simp, hx⟩
  | o :: os, H, x, x', z, z', θ, tl, hl, hx, h, h' => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨w', g1', g2'⟩ := bind_ok h'
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨run', c', e', hat', hy', rfl⟩ := step_ok g1'
    obtain rfl : run = run' := Option.some.inj (hat.symm.trans hat')
    obtain ⟨f, hu, hp⟩ := H o (by simp) run hat
    have hf := hu _ _ _ _ hy
    have hf' := hu _ _ _ _ hy'
    rw [hl, hx] at hf'
    have hh := hp.free _ _ θ tl _ _ hf hf'
    have hc : c' = c := congrArg Prod.fst hh
    have he : e' = reBoth θ tl e := congrArg Prod.snd hh
    rw [hc, he] at g2'
    obtain ⟨c2, e1, e2, e3⟩ :=
      post_two L os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) (x.1 ++ c, e)
        (x'.1 ++ c, reBoth θ tl e) z z' θ tl (by simp [hl]) rfl g2 g2'
    exact ⟨c ++ c2, by rw [e1, List.append_assoc], by rw [e2, List.append_assoc], e3⟩

/-! ## The draw -/

theorem set_re (θ : E) (s : S) (q : K9.Part) :
    K9.atS.set s { q with F := reChiF θ q.F } = reChi θ (K9.atS.set s q) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true <;> simp [K9.atS, reChi, S.fork?, S.putFork, S.putLink, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem set_tl (s : S) (q : K9.Part) : (K9.atS.set s q).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [K9.atS, S.tl?, S.putFork, S.putLink, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem set_funs (s : S) (q : K9.Part) : (K9.atS.set s q).funs? = s.funs? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [K9.atS, S.funs?, S.putFork, S.putLink, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

/-- The states behind the draw at two drawn elements: one is the other with the element replaced. -/
theorem drawnAt_re (p : K9.Where) (s t₁ t₂ : S) (d₁ d₂ : Fmt.Drawn) (h₁ : drawnAt p s d₁ = .ok t₁)
    (h₂ : drawnAt p s d₂ = .ok t₂) : ∃ θ, t₂ = reChi θ t₁ := by
  obtain ⟨a, x₁, o₁, ha, -, hd₁, rfl⟩ := drawnAt_ok p s t₁ d₁ h₁
  obtain ⟨a', x₂, o₂, ha', -, hd₂, rfl⟩ := drawnAt_ok p s t₂ d₂ h₂
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  obtain ⟨e1, e2, e3⟩ := drawn_re _ _ _ _ _ _ _ o₁ o₂ hd₁ hd₂
  refine ⟨E.ofTriple x₂, ?_⟩
  rw [e1, e2, e3]
  exact set_re _ s { a with owed := o₁.owed, L := o₁.L, F := o₁.F }

theorem drawnAt_part (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    (∃ x, K9.atS.get? t = some x) ∧ t.tl? = s.tl? ∧ t.funs? = s.funs? := by
  obtain ⟨a, x, o, ha, -, -, rfl⟩ := drawnAt_ok p s t d h
  obtain ⟨a', ha', -⟩ :=
    K9L.atS_reads s { a with owed := o.owed, L := o.L, F := o.F } (by rw [ha]; rfl)
  exact ⟨⟨a', ha'⟩, set_tl _ _, set_funs _ _⟩

/-! ## "K8.equations" at two states -/

theorem k8_two {n n' : Nat} {tl tl₁ tl₂ : HTailF2} {funs : Array HFun} {F F₁ F₂ : Fork}
    {k₁ k₂ : List Claim} (θ : E) (h₁ : equations n tl funs F = .ok (tl₁, F₁, k₁))
    (h₂ : equations n' tl funs (reChiF θ F) = .ok (tl₂, F₂, k₂)) :
    k₂.take 4 = k₁.take 4 ∧ k₂.length = k₁.length ∧ F₂ = reChiF θ F₁ := by
  obtain ⟨g, Fa, hg, h4, hr, rfl⟩ := K9L.take_four h₁
  obtain ⟨g', Fa', hg', h4', hr', rfl⟩ := K9L.take_four h₂
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain ⟨-, -, -, -, -, l1, -⟩ := k8_cut h₁
  obtain ⟨-, -, -, -, -, l2, -⟩ := k8_cut h₂
  obtain rfl : reChiF θ Fa = Fa' := Option.some.inj ((hideRun_re θ hr).symm.trans hr')
  exact ⟨h4'.trans h4.symm, l2.trans l1.symm, rfl⟩

theorem behind_k8 (θ : E) (e : S) (tl₁ tl₂ : HTailF2) (F₁ : Fork) :
    ((reChi θ e).putTl tl₂).putFork (reChiF θ F₁) = reBoth θ tl₂ ((e.putTl tl₁).putFork F₁) := by
  unfold reBoth
  rw [reChi_putFork, reChi_putTl, putTl_putFork, putTl_putTl]

/-! ## A yes of the whole function of claims -/

/-- A yes of the function of claims at t, cut in its three stretches. -/
structure Walk (L : Link S Claim) (pre post : List (Nat × String)) (t e : S) (cls : List Claim)
    (fr k8 bk : List Claim) (e₁ e₂ : S) (F F₂ : Fork) (tl tl' : HTailF2) (funs : Array HFun) :
    Prop where
  a1 : runAll L.each L.hear pre ([], t) = .ok (fr, e₁)
  a2 : e₁.fork? = some F
  a3 : e₁.tl? = some tl
  a4 : e₁.funs? = some funs
  a5 : equations (F.nClaim + fr.length) tl funs F = .ok (tl', F₂, k8)
  a6 : e₂ = (e₁.putTl tl').putFork F₂
  a7 : runAll L.each L.hear post (fr ++ k8, e₂) = .ok (cls, e)
  a8 : cls = fr ++ k8 ++ bk

theorem walk_one (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (t e : S) (cls : List Claim) (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∃ fr k8 bk e₁ e₂ F F₂ tl tl' funs, Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl' funs := by
  rw [hord, claimsInBy_eq, runAll_append] at hg
  obtain ⟨⟨fr, e₁⟩, g1, g2⟩ := bind_ok hg
  obtain ⟨w, g3, g4⟩ := bind_ok (show (claimsInStep L.each L.hear (fr, e₁) (i, "K8.equations")).bind
    (runAll L.each L.hear post) = .ok (cls, e) from g2)
  obtain ⟨run, k8, e₂, hat, hy, rfl⟩ := step_ok g3
  obtain ⟨F, tl, funs, tl', F₂, b2, b3, b4, b5, b6⟩ := K9L.k8Run_ok _ _ _ _ (tEq run hat _ _ _ _ hy)
  obtain ⟨bk, c1, -⟩ := post_one L post Hpost _ _ g4
  exact ⟨fr, k8, bk, e₁, e₂, F, F₂, tl, tl', funs, ⟨g1, b2, b3, b4, b5, b6, g4, c1⟩⟩

theorem walk_two (L : Link S Claim) (pre post : List (Nat × String)) (Hpre : PreOk L pre)
    (Hpost : PostOk L post) (θ : E) {t e e' : S} {cls cls' fr fr' k8 k8' bk bk' : List Claim}
    {e₁ e₂ e₁' e₂' : S} {F F₂ F' F₂' : Fork} {tl tl₁ tl' tl₁' : HTailF2} {funs funs' : Array HFun}
    (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl₁ funs)
    (W' : Walk L pre post (reChi θ t) e' cls' fr' k8' bk' e₁' e₂' F' F₂' tl' tl₁' funs') :
    fr' = fr ∧ k8'.take 4 = k8.take 4 ∧ k8'.length = k8.length ∧ bk' = bk := by
  obtain ⟨c, c1, c2, c3⟩ := pre_two L pre Hpre ([], t) ([], reChi θ t) _ _ θ rfl rfl W.a1 W'.a1
  have hfr : fr = c := by simpa using c1
  have hfr' : fr' = c := by simpa using c2
  have hff : fr' = fr := hfr'.trans hfr.symm
  have he₁ : e₁' = reChi θ e₁ := c3
  have hF : F' = reChiF θ F := by
    have h := W'.a2
    rw [he₁, reChi_fork, W.a2] at h
    exact (Option.some.inj h).symm
  have htl : tl' = tl := by
    have h := W'.a3
    rw [he₁, reChi_tl, W.a3] at h
    exact (Option.some.inj h).symm
  have hfu : funs' = funs := by
    have h := W'.a4
    rw [he₁, reChi_funs, W.a4] at h
    exact (Option.some.inj h).symm
  have a5' := W'.a5
  rw [hF, htl, hfu] at a5'
  obtain ⟨k4, kl, hF2⟩ := k8_two θ W.a5 a5'
  have he₂ : e₂' = reBoth θ tl₁' e₂ := by
    rw [W'.a6, W.a6, he₁, hF2]
    exact behind_k8 θ e₁ tl₁ tl₁' F₂
  obtain ⟨b, b1, b2, -⟩ := post_two L post Hpost (fr ++ k8, e₂) (fr' ++ k8', e₂') _ _ θ tl₁'
    (by simp [kl, hff]) he₂ W.a7 W'.a7
  have hb : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
  have hb' : bk' = b := List.append_cancel_left (W'.a8.symm.trans b2)
  exact ⟨hff, k4, kl, hb'.trans hb.symm⟩

/-- **The general lemma.** -/
theorem gathers_of_plain (L : Link S Claim) (p : K9.Where) (i : Nat)
    (pre post : List (Nat × String)) (hord : L.order = pre ++ (i, "K8.equations") :: post)
    (Hpre : PreOk L pre) (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (s : S) (tl : HTailF2) (funs : Array HFun) (ht : s.tl? = some tl) (hf : s.funs? = some funs) :
    ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a := by
  by_cases hyes : ∃ (d : Fmt.Drawn) (t e : S) (cls : List Claim), drawnAt p s d = .ok t ∧
      claimsInBy L.each L.hear L.order t = .ok (cls, e)
  · obtain ⟨d₀, t₀, e₀, cls₀, hdr₀, hg₀⟩ := hyes
    obtain ⟨fr₀, k₀, bk₀, u₁, u₂, G, G₂, v, v', w, W₀⟩ :=
      walk_one L i pre post hord Hpost tEq t₀ e₀ cls₀ hg₀
    refine ⟨fr₀.length, bk₀.length, coefAt cls₀, ⟨fun d t e cls hdr hg => ?_⟩⟩
    obtain ⟨θ, rfl⟩ := drawnAt_re p s t₀ t d₀ d hdr₀ hdr
    obtain ⟨fr, k8, bk, e₁, e₂, F, F₂, tl₁, tl', funs₁, W⟩ :=
      walk_one L i pre post hord Hpost tEq _ e cls hg
    obtain ⟨hfr, k4, kl, hbk⟩ := walk_two L pre post Hpre Hpost θ W₀ W
    subst hfr
    subst hbk
    obtain ⟨⟨x, hx⟩, xt, xf⟩ := drawnAt_part p s _ d hdr
    obtain ⟨c, c1, c2, c3, c4, c5⟩ := pre_one L pre Hpre _ _ W.a1
    obtain ⟨x₁, hx₁, s₁⟩ := c5 x hx
    obtain rfl : x₁.F = F := Option.some.inj ((K9.get_fork _ _ hx₁).symm.trans W.a2)
    obtain rfl : tl = tl₁ := by
      have h := W.a3
      rw [c3, xt, ht] at h
      exact Option.some.inj h
    obtain rfl : funs = funs₁ := by
      have h := W.a4
      rw [c4, xf, hf] at h
      exact Option.some.inj h
    obtain ⟨x₂, hx₂, hF₂, -, -, htl₂, -, -⟩ := K9L.get_put e₁ x₁ hx₁ tl' F₂
    obtain ⟨b, b1, b2, b3, b5⟩ := post_one L post Hpost _ _ W.a7
    rw [W.a6] at b3 b5
    obtain ⟨y, hy, s₃⟩ := b5 x₂ hx₂
    have s₂ : SameSums x₁.F x₂.F := by
      rw [hF₂]
      exact SameSums.ofSide (eq_side W.a5)
    have sxy : SameSums x.F y.F := (s₁.trans s₂).trans s₃
    have hplainF : ∀ cl ∈ fr, cl.eqFirst = none := by
      have e0 : fr = c := by simpa using c1
      rw [e0]
      exact c2
    have hplainB : ∀ cl ∈ bk, cl.eqFirst = none := by
      have e0 : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
      rw [e0]
      exact b2
    obtain ⟨g8, -, -, h48, -, -⟩ := K9L.take_four W.a5
    refine ⟨x, y, tl', fr, k8, bk, _, x₁.F, F₂, hx, hy, sxy.core, sxy.frame, b3.trans htl₂, W.a8,
      rfl, rfl, W.a5, s₁.theta, s₁.plan, s₁.frame, ?_, ?_⟩
    · intro j cl hj
      refine ⟨?_, fun t r i => ?_⟩
      · rcases List.mem_append.1 (List.mem_of_getElem? hj) with h1 | h1
        · exact hplainF cl h1
        · rw [h48] at h1
          exact four8_plain _ _ cl h1
      · rw [k4] at hj
        rw [coefAt_some cls₀ j cl (by rw [W₀.a8]; exact get_front _ _ _ _ _ hj)]
    · intro j cl hj
      refine ⟨hplainB cl (List.mem_of_getElem? hj), fun t r i => ?_⟩
      rw [coefAt_some cls₀ _ cl (by rw [W₀.a8, kl, get_back]; exact hj)]
  · exact ⟨0, 0, fun _ _ _ _ => 0,
      ⟨fun d t e cls hdr hg => absurd ⟨d, t, e, cls, hdr, hg⟩ hyes⟩⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pre_two
#print axioms VerifiableInference.Desc.First.K8.Honest.post_two
#print axioms VerifiableInference.Desc.First.K8.Honest.drawnAt_re
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_two
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_of_plain
