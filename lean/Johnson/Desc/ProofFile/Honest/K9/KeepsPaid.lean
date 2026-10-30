-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsPaid.lean: WHAT K9's MEMBER LEAVES OF THE STATE, WITH THE PREMISE "EACH RUN OF
THE ORDER KEEPS IT" PAID OUT OF THE SEALED LIBRARY. Definitions, statements and proofs ON THE VERIFIER's TEXT; no
prover is in this file, and no goal is stated.
  **`fieldRun_layers`**, **`fieldRun_att`**, **`fieldRun_head`**   at a link with the library's `LayersOwesC`,
      `AttOwesC`, `HeadOwesC` (Johnson/Desc/First/Link/Law/LinkRestAtSort4C.lean): for every reading f of the state
      that rests under the library's four writings (`FieldRests f`, KeepsAny.lean): at every yes of every run that the
      order names, at whatever state: f reads the same behind as in front. The library's `run_layers`,
      `run_attention`, `run_head` (RunRel.lean), called at `runRests_of_rel (relRests_of_field R)`; the lookups' runs
      by the field k3p ("the state behind is the state in front with a ledger laid")
  `sevenOf`, `rests_seven`, `setLeaves_iff`   seven fields of the state in a row (st · book · roots · failed · check ·
      out · req); they rest
  `headOf`, `rests_headOf`   in the head's segment three fields of the head's own part (x · t · wo), else nothing; it
      rests
  `set_headOf`   K9's own share: laying K9's part leaves `headOf`
  **`K9Keeps.seven_of`**   K9's clause and "each run keeps `sevenOf`" ⊢ `setLeaves s s'`: so s'.out = s.out
  `rests_own`, `set_own`, `putLink_headOf`, `head_form`   the like for what a feed-forward segment's
      own rounds returned (`S.own?`); a small law on the laying of a segment's book-keeping (its sister on `S.own?` is
      the library's `LinkJoin.putLink_own`); the step to the riders' form
  **`K9Keeps.own_of`**   K9's clause and "each run keeps `S.own?`" ⊢ s'.own? = s.own?
  **`K9Keeps.head_of`**   K9's clause and "each run keeps `headOf`" ⊢ ∀ a, s.here = .head a → ∃ a', s'.here = .head a'
      ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo
The premise of the three corollaries is what the first three end in, up to the text of "the run that stands at the
entry" (`LinkJoin.At` is `claimsRunOf` at the link's list of hearing blocks). No member. The first three and the three
corollaries are called by Honest/K9/KeepsAtHead.lean, where the step from "the run that stands at the entry" to
`claimsRunOf` is made; `putLink_headOf`, `set_…` and `head_form` also by Honest/K9/CloseLeaves.lean; `rests_headOf`
and `set_headOf` also by Honest/K9/GoodHead.lean.
WHAT IS NOT CLAIMED. The three structures at any link. K9's clause at any pair of states. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Keeps
import Johnson.Desc.First.Link.Law.LinkRestAtSort4C
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.KeepsAny
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.K8.LawFunsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll

section
variable {β γ : Type} {m : ℕ} {Kx : Phi β × Option Pub9 → Prop}
  {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {l3 : ℕ × String → Phi β × Option Pub9 → ℕ} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ}
  {p : Desc.K9.Where} {tlD : HTailF2} {f : S → γ}

/-- **Run by run, at a feed-forward segment.** -/
theorem fieldRun_layers (R : FieldRests f) {p4 : OnBytes.Desc.First.K4.Par}
    (O : LayersOwesC m p4 Kx t3 l3 L u ψ nU p tlD) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e :=
  (run_layers (runRests_of_rel (relRests_of_field R)) O.seg (take_of_layersOwesC O)
    fun o ho run h n e c e₁ hr => by
      obtain ⟨G, rfl⟩ := O.k3p o ho run h n e c e₁ hr
      exact R.fork e G).1

/-- **Run by run, at an attention segment.** -/
theorem fieldRun_att (R : FieldRests f) {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} (O : AttOwesC m rd c Kx t3 l3 L u ψ nU p tlD) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → f e₁ = f e :=
  (run_attention (runRests_of_rel (relRests_of_field R)) O.seg (take_of_attOwesC O)
    fun o ho run h n e c' e₁ hr => by
      obtain ⟨G, rfl⟩ := O.k3p o ho run h n e c' e₁ hr
      exact R.fork e G).1

/-- **Run by run, at the head's segment.** -/
theorem fieldRun_head (R : FieldRests f) {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p6 : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (O : HeadOwesC m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e :=
  (run_head (runRests_of_rel (relRests_of_field R)) O.seg (take_of_headOwesC O)
    fun o ho run h n e c e₁ hr => by
      obtain ⟨G, rfl⟩ := O.k3p o ho run h n e c e₁ hr
      exact R.fork e G).1

end

/-- Seven fields of the state, in a row. -/
def sevenOf (s : S) := (s.st, s.book, s.roots, s.failed, s.check, s.out, s.req)

/-- They rest under the four writings. -/
theorem rests_seven : FieldRests sevenOf where
  tl s tl := by obtain ⟨x, e⟩ := putTl_here s tl; rw [e]; rfl
  fork s G := by obtain ⟨x, e⟩ := putFork_here s G; rw [e]; rfl
  wrote _ _ _ _ hw := by obtain ⟨_, rfl⟩ := hw; rfl
  head _ _ _ _ := rfl

/-- The two forms of "the seven are the same". -/
theorem setLeaves_iff (u v : S) : setLeaves u v ↔ sevenOf v = sevenOf u := by
  unfold setLeaves sevenOf
  simp only [Prod.mk.injEq]

/-- In the head's segment: three fields of the head's own part. -/
def headOf (s : S) : Option (Option Head.Heard × Option Head.Tables × Option WsForkOut) :=
  match s.here with
  | .head a => some (a.x, a.t, a.wo)
  | _ => none

/-- It rests under the four writings. -/
theorem rests_headOf : FieldRests headOf where
  tl s tl := by
    unfold headOf S.putTl
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  fork s G := by
    unfold headOf S.putFork
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold headOf
    simp [h1]
  head s a G h := by
    unfold headOf
    simp [h]

/-- **K9's own share at the head**: laying K9's part leaves these three. -/
theorem set_headOf (s : S) (q : Desc.K9.Part) : headOf (Desc.K9.atS.set s q) = headOf s := by
  show headOf { (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } = headOf s
  unfold headOf S.putFork S.putLink
  cases h : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [h, ho]
  | _ => simp [h]

/-- What a feed-forward segment's own rounds returned rests under the four writings. -/
theorem rests_own : FieldRests S.own? where
  tl := First.K8.putTl_own
  fork := LinkJoin.putFork_own
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.own?
    simp [h1]
  head s a G h := by
    unfold S.own?
    simp [h]

/-- Laying a segment's book-keeping leaves the head's three. -/
theorem putLink_headOf (s : S) (L : LinkCtx) : headOf (s.putLink L) = headOf s := by
  unfold headOf S.putLink
  cases h : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [h, ho]
  | _ => simp [h]

/-- K9's own share: laying K9's part leaves it. -/
theorem set_own (s : S) (q : Desc.K9.Part) : (Desc.K9.atS.set s q).own? = s.own? := by
  show S.own? ((s.putLink q.L).putFork q.F) = s.own?
  rw [LinkJoin.putFork_own, LinkJoin.putLink_own]

/-- From "the three are the same" to the form that a rider on the head's own part takes. -/
theorem head_form {s s' : S} (e : headOf s' = headOf s) :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  intro a ha
  have e1 : headOf s = some (a.x, a.t, a.wo) := by
    unfold headOf
    rw [ha]
  rw [e1] at e
  unfold headOf at e
  cases h : s'.here with
  | head a' =>
    rw [h] at e
    have e2 := Option.some.inj e
    exact ⟨a', rfl, congrArg (·.1) e2, congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  | _ =>
    rw [h] at e
    exact nomatch e

/-- **The seven, with the runs' share in the library's form.** -/
theorem K9Keeps.seven_of {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s')
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      sevenOf e₁ = sevenOf e) : setLeaves s s' :=
  H.seven fun o ho run hr n e z hz => (setLeaves_iff e z.2).2 (hrun o ho run hr n e z.1 z.2 hz)

/-- **The head's three, in the form that a rider on the head's own part takes.** -/
theorem K9Keeps.head_of {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s')
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      headOf e₁ = headOf e) :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  have e : headOf s' = headOf s :=
    H.left (fun v z => headOf z = headOf v) (fun _ => rfl) (fun _ _ _ h h' => h'.trans h)
      (fun v _ q _ _ => set_headOf v q) fun o ho run hr n v z hz => hrun o ho run hr n v z.1 z.2 hz
  exact head_form e

/-- **What a feed-forward segment's own rounds returned is left by the batching's member.** -/
theorem K9Keeps.own_of {p : Desc.K9.Where} {each : ℕ × String → List Claim → S → Except String Unit}
    {bs : List (Block S Claim)} {order : List (ℕ × String)} {s s' : S}
    (H : K9Keeps p (claimsInBy each bs order) s s')
    (hrun : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      e₁.own? = e.own?) : s'.own? = s.own? :=
  H.left (fun v z => z.own? = v.own?) (fun _ => rfl) (fun _ _ _ h h' => h'.trans h)
    (fun v _ q _ _ => set_own v q) fun o ho run hr n v z hz => hrun o ho run hr n v z.1 z.2 hz

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.fieldRun_layers
#print axioms ProofFile.Honest.K9.fieldRun_att
#print axioms ProofFile.Honest.K9.fieldRun_head
#print axioms ProofFile.Honest.K9.rests_seven
#print axioms ProofFile.Honest.K9.setLeaves_iff
#print axioms ProofFile.Honest.K9.rests_headOf
#print axioms ProofFile.Honest.K9.set_headOf
#print axioms ProofFile.Honest.K9.rests_own
#print axioms ProofFile.Honest.K9.putLink_headOf
#print axioms ProofFile.Honest.K9.set_own
#print axioms ProofFile.Honest.K9.head_form
#print axioms ProofFile.Honest.K9.K9Keeps.own_of
#print axioms ProofFile.Honest.K9.K9Keeps.seven_of
#print axioms ProofFile.Honest.K9.K9Keeps.head_of
#print axioms ProofFile.Honest.K9.sevenOf
#print axioms ProofFile.Honest.K9.headOf
