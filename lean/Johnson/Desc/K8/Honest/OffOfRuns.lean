-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OffOfRuns.lean: THE SMALLNESS TEST: FROM SENTENCES ON A PLAIN SEGMENT's RUNS
OF CLAIMS, EACH AT THE STATE AT WHICH THE RUN IS CALLED, TO A SENTENCE ON THE WHOLE LIST OF CLAIMS
THAT NAMES NO CUT OF IT; AND FROM THAT SENTENCE TO `PlainOffA`
(Johnson/Desc/K8/Honest/TieBehind.lean). Lemmas; none of the library's goals. No prover stands in
them; nothing on completeness, soundness or hiding. A FRAME: the invariants and the claims' property
are letters.

  **`plainOffA_of_yes`**   under `Gathers`, from one yes of the batching's draw and of the runs:
      where each claim of the list that is added under its own number bears nothing on the entry:
      `PlainOffA` at whatever numbers and letter a meet `Gathers`
  `runAll_all`   a stretch of the order, walked with an invariant on the state and a property of the
      claims. `pre_one`, `post_one` (Johnson/Desc/K8/Honest/GathersPlain.lean) and `core_along`
      (CoreGathers.lean) are the like at fixed properties
  `off_of_walk`   along the runs' own cut (`Walk`, GathersPlain.lean): the claims in front and
      behind; the first four of "K8.equations"; the list's rest is added under numbers handed to it
  **`off_at_link`**   the three together, at a segment whose order is pre ++ [(i, "K8.equations")]
      ++ post
By: `k8_cut` (Johnson/Desc/K8/Honest/FallReads.lean) · `walk_one` (GathersPlain.lean) · `step_ok`,
`bind_ok` (FallFold.lean) · K9L.take_four (Johnson/Desc/First/Batch/Law/K8Four.lean) ·
Meaning.K8.k08_front (Johnson/Meaning/K8Front.lean).
Limits. Nothing on any run's text. Which invariant serves all runs of a segment at once is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.TieBehind
import Johnson.Meaning.K8Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **(i) in the letter of `Gathers`, from one yes**: a sentence on the whole list of claims, which
names no cut of it: each claim that is added under its own number bears nothing on the entry. -/
theorem plainOffA_of_yes {p : K9.Where} {g : S → Except String (List Claim × S)} {s : S}
    {tl : HTailF2} {funs : Array HFun} {nf nb : Nat} {a : Nat → Nat → Nat → Nat → Cb.Gl.E}
    (hG : Gathers p g s tl funs nf nb a) {d : Fmt.Drawn} {t e : S} {cls : List Claim}
    (hdr : drawnAt p s d = .ok t) (hg : g t = .ok (cls, e)) {t₀ r₀ i₀ : Nat}
    (hQ : ∀ cl ∈ cls, cl.eqFirst = none → coefOn cl t₀ r₀ i₀ = 0) :
    PlainOffA a nf nb (tl.NM + (readsList tl funs).length) t₀ r₀ i₀ := by
  obtain ⟨-, -, tl', fr, k8, bk, n₀, F₁, F₂, -, -, -, -, -, gcls, gnf, gnb, geq, -, -, -, gA, gB⟩ :=
    hG.each d t e cls hdr hg
  obtain ⟨-, -, -, -, h4, hk, -⟩ := k8_cut geq
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hlen : j < (fr ++ k8.take 4).length := by
      rw [List.length_append, gnf, h4]
      exact hj
    have hget : (fr ++ k8.take 4)[j]? = some (fr ++ k8.take 4)[j] := List.getElem?_eq_getElem hlen
    obtain ⟨e1, e2⟩ := gA j _ hget
    rw [← e2 t₀ r₀ i₀]
    refine hQ _ ?_ e1
    rw [gcls]
    rcases List.mem_append.1 (List.getElem_mem hlen) with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_take h))
  · have hlen : j < bk.length := by
      rw [gnb]
      exact hj
    have hget : bk[j]? = some bk[j] := List.getElem?_eq_getElem hlen
    obtain ⟨e1, e2⟩ := gB j _ hget
    rw [← hk, ← e2 t₀ r₀ i₀]
    refine hQ _ ?_ e1
    rw [gcls]
    exact List.mem_append_right _ (List.getElem_mem hlen)

/-- **A stretch of the order, walked with an invariant**: where each run that the blocks state at
an entry of the stretch keeps Inv and makes claims with Q alone, so does the stretch. -/
theorem runAll_all (L : Link S Claim) (Inv : S → Prop) (Q : Claim → Prop) :
    ∀ (os : List (Nat × String)),
    (∀ o ∈ os, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim), Inv u →
      run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv u') →
    ∀ (x z : List Claim × S), runAll L.each L.hear os x = .ok z → Inv x.2 →
    ∃ c, z.1 = x.1 ++ c ∧ (∀ cl ∈ c, Q cl) ∧ Inv z.2
  | [], _, x, z, h, hi => by
    obtain rfl : x = z := Except.ok.inj h
    exact ⟨[], by simp, by simp, hi⟩
  | o :: os, H, x, z, h, hi => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨q1, i1⟩ := H o (by simp) run hat _ _ _ _ hi hy
    obtain ⟨c2, e1, q2, i2⟩ :=
      runAll_all L Inv Q os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) _ z g2 i1
    refine ⟨c ++ c2, by rw [e1, List.append_assoc], fun cl hcl => ?_, i2⟩
    rcases List.mem_append.1 hcl with h1 | h1
    · exact q1 cl h1
    · exact q2 cl h1

/-- **Along the runs' own cut**: the claims in front and behind have Q; so have the first four of
the list "K8.equations"; the list's rest is added under numbers handed to it: so every claim of the
whole list that is added under its own number has Q. -/
theorem off_of_walk {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
    {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F F₂ : Fork} {tl tl' : HTailF2} {funs : Array HFun}
    (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl' funs) (Q : Claim → Prop)
    (hfr : ∀ cl ∈ fr, Q cl) (hbk : ∀ cl ∈ bk, Q cl)
    (h4 : ∀ g, tl.heard = some g → ∀ cl ∈ K9L.four8 tl g, Q cl) :
    ∀ cl ∈ cls, cl.eqFirst = none → Q cl := by
  intro cl hcl hn
  rw [W.a8] at hcl
  rcases List.mem_append.1 hcl with h | h
  · rcases List.mem_append.1 h with h | h
    · exact hfr cl h
    · obtain ⟨g, -, hg, e4, -, -⟩ := K9L.take_four W.a5
      obtain ⟨four, rest, ek, hl, -, hr⟩ := Meaning.K8.k08_front _ _ _ _ _ _ _ W.a5
      have et : k8.take 4 = four := by
        rw [ek, ← hl, List.take_left]
      rw [ek] at h
      rcases List.mem_append.1 h with h | h
      · exact h4 g hg cl (by rw [← e4, et]; exact h)
      · have k := hr cl h
        rw [hn] at k
        exact absurd k (by simp)
  · exact hbk cl h

/-- **AT A PLAIN SEGMENT: FROM SENTENCES ON THE RUNS, EACH AT THE STATE AT WHICH IT IS CALLED, TO
THE SENTENCE ON THE WHOLE LIST.** Inv: what holds behind the batching's draw and is kept by each run
in front of "K8.equations"; Inv₂: the like behind it. -/
theorem off_at_link (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (Inv Inv₂ : S → Prop) (Q : Claim → Prop)
    (hpre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv u')
    (hk8 : ∀ (u : S) (tl tl' : HTailF2) (F F₂ : Fork) (funs : Array HFun) (k8 : List Claim)
      (n : Nat), Inv u → u.fork? = some F → u.tl? = some tl → u.funs? = some funs →
      equations n tl funs F = .ok (tl', F₂, k8) →
      (∀ g, tl.heard = some g → ∀ cl ∈ K9L.four8 tl g, Q cl) ∧ Inv₂ ((u.putTl tl').putFork F₂))
    (hpost : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv₂ u')
    (t e : S) (cls : List Claim) (ht : Inv t)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∀ cl ∈ cls, cl.eqFirst = none → Q cl := by
  obtain ⟨fr, k8, bk, e₁, e₂, F, F₂, tl, tl', funs, W⟩ :=
    walk_one L i pre post hord Hpost tEq t e cls hg
  obtain ⟨c, c1, c2, c3⟩ := runAll_all L Inv Q pre hpre _ _ W.a1 ht
  have hfr : fr = c := by simpa using c1
  obtain ⟨k1, k2⟩ := hk8 e₁ tl tl' F F₂ funs k8 _ c3 W.a2 W.a3 W.a4 W.a5
  obtain ⟨b, b1, b2, -⟩ := runAll_all L Inv₂ Q post hpost _ _ W.a7 (by rw [W.a6]; exact k2)
  have hbk : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
  exact off_of_walk W Q (by rw [hfr]; exact c2) (by rw [hbk]; exact b2) k1

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.plainOffA_of_yes
#print axioms VerifiableInference.Desc.First.K8.Honest.runAll_all
#print axioms VerifiableInference.Desc.First.K8.Honest.off_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.off_at_link
