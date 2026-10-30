-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HitemsHead.lean (kind K9): `TableOwes.hitems` (LinkTable.lean; the field hitems of `CoreRest2`, LinkRestAtSort2.lean) AT THE SEAT's OWN READERS (`K9.readersAt`) AT THE HEAD's LINK: the like of
HitemsJoin.lean (beside this file), which stands at a layers' and at an attention link. Theorems: a join of the items' clauses that lie (`items_head`, HitemsAt.lean; `item_small_head`, HitemsSmall.lean).

WHY THE HEAD's LINK WAS LEFT OUT. Every clause that lies takes «the readers' second hole says nothing at the entry» (H.silent o.1 o.2 a.1 = none). Away from the head's link the seat's second hole is empty: so it holds outright.
AT THE HEAD's LINK THE HOLE IS FILLED (`k6Silent` P states := fun b name s => (withTables P s).bind (readerOf states b name): general in (b, name)): so there its silence is no longer had outright. BY READING, SHOWN NOWHERE: it
may answer just where the run answers, and the premise then fails at honest states (so found, of the lookup's files' theorems, at the head's digits; of these six entries this is not known).
THE CURE. `readersOfLink` asks the second hole ONLY WHERE THE RUN ITSELF IS SILENT. So where the run answers, the readers with the hole filled and the readers with the hole empty give one answer; and an item's clause reads
the readers at its own entry and state alone. So the clause is had at the empty hole and carried over.

What is said.
  `forms_of_run`: where the run itself answers at (b, name, s), name not the smallness test's: the readers' answer there does not hang on the second hole. `forms_of_small`: at the smallness test's entry it is the first hole's.
  `formsIn_congr`, `itemIn_congr`: the table's public test, and an item's clause, read the readers at the entry and the state alone.
  `hitems_head`: **the field's own text at the head's link**, at φ := phiAll u ψ, the head's tables of terms at entUnit, Rd := K9.readersAt lk X mH mH. Behind it an `example`: Lean's own check that the end is `TableOwes`' field.
PREMISES. As HitemsJoin.lean's: the sort's Take · hAt at (5, "K8.equations") · h4 · hit · hon · hin · k3i (the clauses at the lookup's entries and the join: four). **AND hrun: AT EVERY STATE OF on0 THE RUN ITSELF ANSWERS AT EACH OF
THE SIX ENTRIES guests (2 | 7) · norm · policy · logits · the merge THAT IS LISTED**: in the place of the hole's silence.

Limits. IMPLICATIONS. hon, hin, hrun and k3i are shown of no state here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open K5Law

variable {α β W : Type} {F : Frame}

/-- Where the run itself answers, the readers' answer does not hang on the second hole. -/
theorem forms_of_run (H H' : K9.LinkHoles) (L : Link S Claim) (b : ℕ) (name : String) (s : S)
    (hne : (name == "K8.equations") = false)
    (hr : (K9.readerOf (K9.statesOfLink L) b name s).isSome = true) :
    (K9.readersOfLink H L).forms b name s = (K9.readersOfLink H' L).forms b name s := by
  show (if name == "K8.equations" then H.small s
    else match K9.readerOf (K9.statesOfLink L) b name s with
      | some R => some R
      | Option.none => H.silent b name s) =
    (if name == "K8.equations" then H'.small s
    else match K9.readerOf (K9.statesOfLink L) b name s with
      | some R => some R
      | Option.none => H'.silent b name s)
  rw [hne]
  cases e : K9.readerOf (K9.statesOfLink L) b name s with
  | none =>
    rw [e] at hr
    exact nomatch hr
  | some R => rfl

/-- At the smallness test's entry the answer is the first hole's. -/
theorem forms_of_small (H H' : K9.LinkHoles) (L : Link S Claim) (b : ℕ) (s : S)
    (hs : H.small = H'.small) :
    (K9.readersOfLink H L).forms b "K8.equations" s =
      (K9.readersOfLink H' L).forms b "K8.equations" s := by
  unfold K9.readersOfLink
  simp [hs]

/-- The table's public test reads the readers at the entry and the state alone. -/
theorem formsIn_congr {Rd Rd' : K9.Readers} (own : List (ℕ × ℕ)) (b : ℕ) (name : String) (s : S)
    (h : Rd'.forms b name s = Rd.forms b name s) :
    K9.formsIn Rd' own b name s = K9.formsIn Rd own b name s := by
  unfold K9.formsIn
  rw [h]

/-- So does an item's clause. -/
theorem itemIn_congr {L : Link S Claim} {φ : S → α}
    {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {lenOf : ℕ × String → α × Option Pub9 → ℕ} {Rd Rd' : K9.Readers} {own : List (ℕ × ℕ)}
    {rdW : W → ℕ × ℕ → MsgQ} {a : S × F.E.Str} {w : W} {e : ℕ × String}
    (h : Rd'.forms e.1 e.2 a.1 = Rd.forms e.1 e.2 a.1)
    (I : ItemIn L φ tmOf lenOf Rd own rdW a w e) : ItemIn L φ tmOf lenOf Rd' own rdW a w e := by
  obtain ⟨b, R, rs, h1, h2, h3, h4, h5⟩ := I
  exact ⟨b, R, rs, h1, h2, h.trans h3, (formsIn_congr own e.1 e.2 a.1 h).trans h4, h5⟩

section
variable (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH : ℕ)
  {L : Link S Claim} (hlk : lk mH = some L) {u : HTailF2} {ψ : S → β}
  {Ok : Q β → Prop} {Fu : S → Prop} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
include hlk

/-- **hitems AT THE HEAD's LINK.** -/
theorem hitems_head (hL : SegAt mH .head L) {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (5, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (hit : ∀ e ∈ items, e ∈ [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"),
      (3, "policy"), (2, "planes"), (7, "objects"), (7, "guests"), (5, "K8.equations"),
      (3, "logits"), (8, "the merge")])
    (hon : ∀ a, on0 a → (atS.get? a.1).isSome = true ∧ Ok (fixed9 (phiAll u ψ) a.1))
    (hin : ∀ a, on0 a → ∀ e ∈ items, K9.formsIn (K9.readersAt lk X mH mH) own e.1 e.2 a.1 = true)
    (hrun : ∀ a, on0 a → ∀ e ∈ items, e ∈ [(2, "guests"), (3, "norm"), (3, "policy"),
      (3, "logits"), (7, "guests"), (8, "the merge")] →
      (K9.readerOf (K9.statesOfLink L) e.1 e.2 a.1).isSome = true)
    (k3i : ∀ a w, on0 a → ∀ e ∈ [(2, "objects"), (3, "join"), (2, "planes"), (7, "objects")],
      ItemIn L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
        (K9.readersAt lk X mH mH) own rdW a w e) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3)
      (lenH h iU3 p kap l3) (K9.readersAt lk X mH mH) own rdW a w e := by
  intro a w ha e he
  obtain ⟨b, St⟩ := stmt_of_part (phiAll u ψ) Ok a (hon a ha).1 (hon a ha).2
  have hi := hin a ha e he
  have k3 := k3i a w ha
  have hr := hrun a ha e he
  rw [K9.readersAt_some lk X mH mH L hlk] at hi k3 ⊢
  have own6 := items_head (K9.withSmall K9.LinkHoles.none) hL A own rdW a w b St
  have ho : (5, "K8.equations") ∈ L.order := by
    rw [(order_at hL).1]
    decide
  -- one of the six: had at the empty hole, carried over
  have six : ∀ o : ℕ × String, o = e → o ∈ [(2, "guests"), (3, "norm"), (3, "policy"),
      (3, "logits"), (7, "guests"), (8, "the merge")] → (o.2 == "K8.equations") = false →
      ItemIn L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
        (K9.readersOfLink (K9.holesAt X mH mH L) L) own rdW a w e := by
    intro o ho' hm hne
    subst ho'
    have e1 := forms_of_run (K9.holesAt X mH mH L) (K9.withSmall K9.LinkHoles.none) L o.1 o.2 a.1
      hne (hr hm)
    exact itemIn_congr e1
      (own6 o hm rfl ((formsIn_congr own o.1 o.2 a.1 e1.symm).trans hi)).toIn
  have hmem := hit e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k3 _ (by simp)
  · exact six _ rfl (by simp) rfl
  · exact six _ rfl (by simp) rfl
  · exact k3 _ (by simp)
  · exact six _ rfl (by simp) rfl
  · exact k3 _ (by simp)
  · exact k3 _ (by simp)
  · exact six _ rfl (by simp) rfl
  · have e1 := forms_of_small (K9.holesAt X mH mH L) (K9.withSmall K9.LinkHoles.none) L 5 a.1 rfl
    exact itemIn_congr e1 (item_small_head K9.LinkHoles.none L u ψ h iU3 p kap entUnit tm4 t3 l3
      own rdW 5 ho run hAt v4 h4 a w b St.part
      ((formsIn_congr own 5 "K8.equations" a.1 e1.symm).trans hi))
  · exact six _ rfl (by simp) rfl
  · exact six _ rfl (by simp) rfl

end

/-- Lean's own check that the end is `TableOwes`' field. -/
example (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH : ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ)
    (p : Kinds.Head.Par) (kap : Phi β → Option Kinds.Head.Law.Seen)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 on1 on2 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (T : TableOwes L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3) on0 on1
      on2 (K9.readersAt lk X mH mH) own rdW items) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3)
      (lenH h iU3 p kap l3) (K9.readersAt lk X mH mH) own rdW a w e :=
  T.hitems

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.forms_of_run
#print axioms VerifiableInference.Desc.LinkJoin.forms_of_small
#print axioms VerifiableInference.Desc.LinkJoin.formsIn_congr
#print axioms VerifiableInference.Desc.LinkJoin.itemIn_congr
#print axioms VerifiableInference.Desc.LinkJoin.hitems_head
