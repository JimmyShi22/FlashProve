-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ExpsAt.lean: THE TEST ON THE EXPONENTS (`LinkOwes.hok`) AT EACH OF THE
THREE SORTS OF LINK, at the assembly's tables of terms (PayLayers.lean: `tmL`; PayAttention.lean:
`tmA`; PayHead.lean: `tmH`). Theorems, over LinkExps.lean and the batching kind's K8Disc.lean.

What is said.
  `valsStill_len`, `valsFront_len`, `valsBack_len`, `valsMerge_len`: a plain run's table has at most
    as many values as its number of claims says. `EqTake`: what the entry with equations and the two
    numbers take, at a fixed part q: the smallness test's record and functions and a snapshot are
    there; the rows' shapes; the first four claims' terms are numbered; THE TWO NUMBERS: the runs'
    claims are at most the plan's number; the plan's number and the equations' are at most d + 1.
    `eq_duty`: that entry's duty. `hok_layers`, `hok_attention`, `hok_head`: **`TermsOk` of the
    link's terms at d, at each sort**, from `EqTake` and, as it stands, `PlainE` of the lookup's
    entries. `hokF_layers`, `hokF_attention`, `hokF_head`: the same in the form of `LinkOwes`' own
    field.

Limits. IMPLICATIONS. `hokF_layers`, `hokF_attention`, `hokF_head` end in `LinkOwes.hok`'s own form:
they ask `EqTake` of `fixed9 φ s` at every s that is ready: so its six clauses come out of Ok (the
book-keeping gives the snapshot alone). THE TWO NUMBERS ARE TESTED BY NO TEXT IN FRONT OF THE DRAW:
they are meant to be taken out of the promise and opened by the door's yes
(Johnson/Desc/First/Batch/Law/RowsNumber.lean), not to be promised by the table of conditions.
`tieAt` is keyed by the entry's name, as the tables of terms are (LinkLawAt.lean: `names_once`).
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkExps
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead
import Johnson.Desc.First.Batch.Law.K8Disc
import Johnson.Desc.First.K4.RunsLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.K11Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K4Values (backForms frontForms)
open K5Law

variable {β : Type}

/-! ## A plain run's table has at most as many values as claims -/

theorem valsStill_len {α K : Type} [Field K] (ρ : Reading K)
    (fs : α × Option Pub9 → Option (List Aff)) (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) : (valsStill ρ fs ent q y).length ≤ lenStill fs q := by
  unfold valsStill lenStill
  cases q.2 <;> simp

theorem valsMerge_len {α K : Type} [Field K] (ρ : Reading K) (π : α → Option WsForkOut)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K) (q : α × Option Pub9) (y : Bound K) :
    (valsMerge ρ π ent q y).length ≤ 1 := by
  unfold valsMerge
  cases π q.1 <;> cases q.2 <;> simp

theorem valsBack_len {α K : Type} [Field K] (ρ : Reading K) (π : α → Option Layer.Own)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K) (q : α × Option Pub9) (y : Bound K) :
    (valsBack ρ π ent q y).length ≤ 4 := by
  unfold valsBack
  cases π q.1 <;> cases q.2 <;> simp [backForms, OnBytes.Desc.First.K4.back]

theorem valsFront_len {α K : Type} [Field K] (ρ : Reading K) (p : OnBytes.Desc.First.K4.Par)
    (π : α → Option Layer.Own) (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) :
    (valsFront ρ p π ent q y).length ≤ lenFront p π q := by
  unfold valsFront lenFront
  cases hπ : π q.1 with
  | none => simp
  | some o =>
    cases hq : q.2 with
    | none => simp
    | some u =>
      show (match frontForms (!p.k3Runs) p.P p.g o u.F with
        | some l => l.map fun (f : Aff) =>
          f.value ρ (K4Values.refWorld ρ u.F (K4Values.frontWins o) (ent q y) y)
        | none => []).length ≤ OnBytes.Desc.First.K4.frontLen (!p.k3Runs) p.g o
      cases hf : frontForms (!p.k3Runs) p.P p.g o u.F with
      | none => exact Nat.zero_le _
      | some l =>
        show (l.map _).length ≤ _
        rw [List.length_map]
        unfold frontForms at hf
        obtain ⟨sh, _, hf⟩ := Option.bind_eq_some_iff.1 hf
        obtain ⟨pp, _, hf⟩ := Option.bind_eq_some_iff.1 hf
        exact Nat.le_of_eq (OnBytes.Desc.First.K4.front_length hf)

/-! ## The entry with equations, and the two numbers -/

/-- What the entry with equations and the two numbers take, at a fixed part q. -/
structure EqTake (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (q : Q β) (y : Bound GE8)
    (len d : ℕ) (tlb : HTailF2) (funs : Array HFun) (v : Pub9) : Prop where
  /-- the smallness test's record and functions are there -/
  h1 : pi8 q.1 = (some tlb, some funs)
  /-- a snapshot is there -/
  h2 : q.2 = some v
  /-- the symbols' arrays have the rows that their sizes ask -/
  hmS : ∀ mu, mu < tlb.NM → (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m
  /-- the first four claims' terms are four values, numbered: the same four at every number -/
  h4 : ∃ l4 : List GE8, l4.length = 4 ∧ ∀ n, tm4 n q y = numbered n l4
  /-- THE FIRST NUMBER: the runs' claims are at most the plan's number -/
  hlen : len ≤ v.F.planClaimsF
  /-- THE SECOND NUMBER: the plan's number and the equations' are at most d + 1 -/
  hd : v.F.planClaimsF + top8 tlb funs ≤ d + 1

/-- The duty of the entry with equations. -/
theorem eq_duty {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {q : Q β} {y : Bound GE8}
    {len d : ℕ} {tlb : HTailF2} {funs : Array HFun} {v : Pub9}
    (E : EqTake tm4 q y len d tlb funs v) (n : ℕ) (hn : n + len8 pi8 q ≤ v.F.planClaimsF) :
    ((tm4 n q y ++ tmRest pi8 q y).map (·.1)).Nodup ∧
      ∀ x ∈ tm4 n q y ++ tmRest pi8 q y,
        InWin n (len8 pi8 q) v.F.planClaimsF 0 (top8 tlb funs) x.1 := by
  obtain ⟨l4, hl4, e4⟩ := E.h4
  rw [e4 n]
  refine k8_disc pi8 q y tlb funs v n l4 E.h1 E.h2 E.hmS hl4 ?_
  have e : len8 pi8 q = 4 + (tlb.NM + (readsList tlb funs).length) := by
    unfold len8
    rw [E.h1]
  omega

/-- The number of equations by the entry: the smallness test's alone has some. -/
def tieAt (top : ℕ) (o : ℕ × String) : ℕ := if o.2 == "K8.equations" then top else 0

/-- **hok AT A LAYERS' LINK.** -/
theorem hok_layers {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) (p : OnBytes.Desc.First.K4.Par)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) (y : Bound GE8) (d : ℕ) (tlb : HTailF2) (funs : Array HFun) (v : Pub9)
    (E : EqTake tm4 q y (lenRuns q (rlOf L (tmL p ent tm4 t3) (lenL p l3))) d tlb funs v)
    (h3 : ∀ o ∈ [(1, "objects"), (6, "objects")], PlainE (tmL p ent tm4 t3) (lenL p l3) q y o) :
    Desc.TermsOk Cb.Gl.E (termsOf q y
      (moves₁ L (rlOf L (tmL p ent tm4 t3) (lenL p l3)) ++ moves₂ (α := Phi β) L) 0) d := by
  refine hok_order (tmL p ent tm4 t3) (lenL p l3) L (tieAt (top8 tlb funs)) q y v.F.planClaimsF d
    [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")]
    (4, "K8.equations") (order_at hL).1 ?_ ?_ (fun n hn => eq_duty E n hn) E.hlen E.hd
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨h3 _ (by simp), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsFront_len _ p _ _ q y), rfl⟩
    · exact ⟨h3 _ (by simp), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · intro o ho
    obtain rfl := List.mem_singleton.1 ho
    exact ⟨plainE_of _ _ q y _ _ rfl (valsBack_len _ _ _ q y), rfl⟩

/-- **hok AT AN ATTENTION LINK.** -/
theorem hok_attention {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) (y : Bound GE8) (d : ℕ) (tlb : HTailF2) (funs : Array HFun) (v : Pub9)
    (E : EqTake tm4 q y (lenRuns q (rlOf L (tmA rd c ent tm4 t3) (lenA rd c l3))) d tlb funs v)
    (h3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      PlainE (tmA rd c ent tm4 t3) (lenA rd c l3) q y o) :
    Desc.TermsOk Cb.Gl.E (termsOf q y
      (moves₁ L (rlOf L (tmA rd c ent tm4 t3) (lenA rd c l3)) ++ moves₂ (α := Phi β) L) 0) d := by
  refine hok_order (tmA rd c ent tm4 t3) (lenA rd c l3) L (tieAt (top8 tlb funs)) q y
    v.F.planClaimsF d
    [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"), (2, "second"),
      (1, "planes"), (6, "objects"), (6, "guests")] [] (4, "K8.equations") (order_at hL).1 ?_
    (fun _ h => nomatch h) (fun n hn => eq_duty E n hn) E.hlen E.hd
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h3 _ (by simp), rfl⟩
  · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · exact ⟨h3 _ (by simp), rfl⟩
  · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · exact ⟨h3 _ (by simp), rfl⟩
  · exact ⟨h3 _ (by simp), rfl⟩
  · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩

/-- **hok AT THE HEAD's LINK.** -/
theorem hok_head {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ)
    (p : Kinds.Head.Par) (kap : Phi β → Option Kinds.Head.Law.Seen)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) (y : Bound GE8) (d : ℕ) (tlb : HTailF2) (funs : Array HFun) (v : Pub9)
    (E : EqTake tm4 q y
      (lenRuns q (rlOf L (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3))) d tlb funs v)
    (h3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")],
      PlainE (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) q y o) :
    Desc.TermsOk Cb.Gl.E (termsOf q y
      (moves₁ L (rlOf L (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3)) ++
        moves₂ (α := Phi β) L) 0) d := by
  refine hok_order (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) L (tieAt (top8 tlb funs)) q
    y v.F.planClaimsF d
    [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"),
      (7, "objects"), (7, "guests")] [(3, "logits"), (8, "the merge")] (5, "K8.equations")
    (order_at hL).1 ?_ ?_ (fun n hn => eq_duty E n hn) E.hlen E.hd
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨h3 _ (by simp), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨h3 _ (by simp), rfl⟩
    · exact ⟨h3 _ (by simp), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsStill_len _ _ _ q y), rfl⟩
    · exact ⟨plainE_of _ _ q y _ _ rfl (valsMerge_len _ _ _ q y), rfl⟩

/-! ## In the form of LinkOwes' own field -/

/-- **LinkOwes.hok AT A LAYERS' LINK, IN ITS OWN FORM.** -/
theorem hokF_layers {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop)
    (p : OnBytes.Desc.First.K4.Par) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s) (rlOf L (tmL p ent tm4 t3) (lenL p l3))) d tlb funs v ∧
      ∀ o ∈ [(1, "objects"), (6, "objects")],
        PlainE (tmL p ent tm4 t3) (lenL p l3) (fixed9 (phiAll u ψ) s) y o) :
    ∀ s y, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) →
      Desc.TermsOk Cb.Gl.E (termsOf (fixed9 (phiAll u ψ) s) y
        (moves₁ L (rlOf L (tmL p ent tm4 t3) (lenL p l3)) ++ moves₂ (α := Phi β) L) 0) d := by
  intro s y hs
  obtain ⟨tlb, funs, v, h⟩ := E s hs
  exact hok_layers hL p ent tm4 t3 l3 _ y d tlb funs v (h y).1 (h y).2

/-- **LinkOwes.hok AT AN ATTENTION LINK, IN ITS OWN FORM.** -/
theorem hokF_attention {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s) (rlOf L (tmA rd c ent tm4 t3) (lenA rd c l3))) d tlb funs
        v ∧
      ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")],
        PlainE (tmA rd c ent tm4 t3) (lenA rd c l3) (fixed9 (phiAll u ψ) s) y o) :
    ∀ s y, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) →
      Desc.TermsOk Cb.Gl.E (termsOf (fixed9 (phiAll u ψ) s) y
        (moves₁ L (rlOf L (tmA rd c ent tm4 t3) (lenA rd c l3)) ++ moves₂ (α := Phi β) L) 0) d := by
  intro s y hs
  obtain ⟨tlb, funs, v, h⟩ := E s hs
  exact hok_attention hL rd c ent tm4 t3 l3 _ y d tlb funs v (h y).1 (h y).2

/-- **LinkOwes.hok AT THE HEAD's LINK, IN ITS OWN FORM.** -/
theorem hokF_head {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s)
          (rlOf L (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3))) d tlb funs v ∧
      ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")],
        PlainE (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) (fixed9 (phiAll u ψ) s) y o) :
    ∀ s y, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) →
      Desc.TermsOk Cb.Gl.E (termsOf (fixed9 (phiAll u ψ) s) y
        (moves₁ L (rlOf L (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3)) ++
          moves₂ (α := Phi β) L) 0) d := by
  intro s y hs
  obtain ⟨tlb, funs, v, h'⟩ := E s hs
  exact hok_head hL h iU3 p kap ent tm4 t3 l3 _ y d tlb funs v (h' y).1 (h' y).2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.valsFront_len
#print axioms VerifiableInference.Desc.LinkJoin.eq_duty
#print axioms VerifiableInference.Desc.LinkJoin.hok_layers
#print axioms VerifiableInference.Desc.LinkJoin.hok_attention
#print axioms VerifiableInference.Desc.LinkJoin.hok_head
#print axioms VerifiableInference.Desc.LinkJoin.hokF_layers
#print axioms VerifiableInference.Desc.LinkJoin.hokF_attention
#print axioms VerifiableInference.Desc.LinkJoin.hokF_head
