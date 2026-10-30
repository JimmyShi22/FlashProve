-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Pure.lean: the kind "lookup" (K3): the statement
`GoodGives` (Honest/K3/GoodDrawsLaw.lean) once more, for forms that are made of what was heard
alone: no ledger behind the hearing is asked to take the leaves' late row. With it: a form that does
not name a slot, and rules on coefficients that the files on the seated runs use. Definitions and
theorems.

Terms. Honest/K3/GLOSSARY.md ("form", "slot", "window", "good samples", "run (of claims): objects,
guests, planes, join"). In this file: `sc a j` is the coefficient with which the form a names slot
j, read in the library's field (Honest/K3/Good/Coef.lean).

What is defined and shown.
  `leadsOf g r`: the forms of a run, of what was heard alone: the heard rows; the row of the leaves'
    sumcheck with nothing kept (`rowAff`, Johnson/Desc/Part/MaskedSumTie.lean) and the slot of the
    bits' end value; the key side's last forms.
  `gives_pure`: where `goodRun f r` accepts the rounds' samples, each slot in the window of the run
    r is named, with a coefficient that is not 0, by a form of `leadsOf g r`.
  `Clear a j`: the form a names slot j in no pair. `sc_clear`: then its coefficient there is 0.
  `clear_ofConst`, `clear_empty`, `clear_slot`, `clear_addMul`, `clear_scale`, `clear_add`,
    `clear_sub`, `clear_of_in`, `clear_fold`: rules.
  `sc_fold`: a sum of forms none of which has a coefficient on slot j leaves the coefficient as it
    was.
  `sc_leaves`: the coefficient of the verifier program's row form of the leaves' sumcheck, with a
    scaled form kept, is that of `rowAff` with nothing kept plus a multiple of the kept form's.
  `live_of_sc`, `unnamed_of_clear`: from forms to the claims that a seat makes of them.

Hypotheses that remain. `gives_pure`: those of `GoodGives` but for the return of `planesV`: the face
has a level on the table side (`hd`); the samples are such as the rounds can sample (`hc`); the
hearing returns (`hh`); the run's test accepts (`hg`); j is in the run's window (`hj`).
`live_of_sc`, `unnamed_of_clear`: the seat's claim of a form has that form (`hf`), and (in the
first) takes its own number (`hc`); `h`: some form of the list has a coefficient on slot j that is
not 0, or none names it.
In the rules: `h`, `ha`, `hb`: the forms that go in are `Clear` at j; `hs`: (in `clear_fold`) the
step keeps `Clear`; that the start form is `Clear` stands there without a name, in front of an arrow
(in `clear_slot`: i ≠ j; in `clear_of_in`, with `hj`: the form names slots from lo to hi alone and j
lies outside; in `sc_fold`, `hb`: no summand has a coefficient on slot j).

How the proof goes. `goodGives` (Honest/K3/Good/Gives.lean) uses the return of `planesV` for one
equation alone: what the three claims' leads are. Its two lemmas `own_live` and `ends_live` take
that equation as a hypothesis. Here they are called at a list of three claims that is written down.
`sc_leaves` follows from `worth_leaves` (Honest/K3/Law/SeatedWorth.lean) in two worlds.

Users. Honest/K3/Good/Live/Runs.lean.

Limits. Rules on forms and one sentence on what was heard. Nothing on a seated run.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Gives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (rowAff)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV toPsc Seat)
open VerifiableInference.Desc.K9H (slotCoef liveAt liveAt_iff unnamedAt unnamedIn)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (In)

/-! ## The statement, for forms of what was heard alone -/

/-- The forms of a run, of what was heard alone. At "planes" the third claim's lead is left out: it is
a constant, which names no slot. -/
def leadsOf (g : HeardV) : Run → List Aff
  | .objects => g.rows.toList
  | .planes => [rowAff g.leaves oneE {}, Aff.slot g.sBit]
  | .join => g.keys.map (·.2)

/-- **Where a run's test accepts, each slot in its window is named, not with 0, by one of these
forms.** -/
theorem gives_pure {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hd : 1 ≤ f.d)
    (hc : canDraw f (rs.map (·.drawn)) = true) (hh : hearV f F rs = some (g, G)) (r : Run)
    (hg : goodRun f r (rs.map (·.drawn)) = true) {j : Nat} (hj : j ∈ windowOf f r) :
    ∃ a ∈ leadsOf g r, sc a (F.next + j) ≠ 0 := by
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  have hok : Ok rs := fun r0 hr0 x hx =>
    ok_of_fit _ _ hc r0.drawn (List.mem_map.2 ⟨r0, hr0, rfl⟩) x hx
  have H := heard_out hokf hok hm
  have hpl : ([⟨rowAff g.leaves oneE {}, zeroE, []⟩, ⟨Aff.slot g.sBit, zeroE, []⟩,
      ⟨Aff.ofConst zeroE, zeroE, []⟩] : List PlaneClaim).map (·.lead) =
      [rowAff g.leaves oneE {}, Aff.slot g.sBit, Aff.ofConst zeroE] := rfl
  have key : ∃ a ∈ formsOf g [⟨rowAff g.leaves oneE {}, zeroE, []⟩, ⟨Aff.slot g.sBit, zeroE, []⟩,
      ⟨Aff.ofConst zeroE, zeroE, []⟩] r, sc a (F.next + j) ≠ 0 := by
    unfold windowOf at hj
    obtain ⟨s, hs, hj⟩ := List.mem_flatMap.1 hj
    rcases List.mem_append.1 hj with h1 | h1
    · split at h1
      · rename_i hr
        obtain rfl : runOf f s false = r := by simpa using hr
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
        rw [← Nat.add_assoc]
        exact own_live H hpl hs hg (List.mem_range.1 hi)
      · simp at h1
    · split at h1
      · rename_i hr
        obtain rfl : runOf f s true = r := by simpa using hr
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
        have e : F.next + (firstSlot f s + s.own f + i) = endOf f F.next s + i := by
          unfold endOf
          omega
        rw [e]
        exact ends_live hokf hd H hpl hs hg (List.mem_range.1 hi)
      · simp at h1
  obtain ⟨a, ha, hne⟩ := key
  cases r with
  | objects => exact ⟨a, ha, hne⟩
  | join => exact ⟨a, ha, hne⟩
  | planes =>
    have ha' : a ∈ [rowAff g.leaves oneE {}, Aff.slot g.sBit, Aff.ofConst zeroE] := ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., hne⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hne⟩
    · exact absurd (sc_ofConst _ _) hne

/-! ## A form that does not name a slot -/

/-- The form a names slot j in no pair. -/
def Clear (a : Aff) (j : Nat) : Prop := ∀ x ∈ a.slots.toList, x.1 ≠ j

theorem sc_clear {a : Aff} {j : Nat} (h : Clear a j) : sc a j = 0 :=
  VerifiableInference.Desc.K9H.slotCoef_unnamed Reading.gl ({ form := a } : Claim) j
    (List.all_eq_true.2 fun x hx => by simpa using h x hx)

theorem clear_ofConst (v : E) (j : Nat) : Clear (Aff.ofConst v) j := by
  intro x hx
  simp [Aff.ofConst] at hx

theorem clear_empty (j : Nat) : Clear {} j := by
  intro x hx
  simp at hx

theorem clear_slot {i j : Nat} (h : i ≠ j) : Clear (Aff.slot i) j := by
  intro x hx
  have e : x = (i, oneE) := by simpa [Aff.slot] using hx
  rw [e]
  exact h

theorem clear_addMul {a b : Aff} {j : Nat} (ha : Clear a j) (hb : Clear b j) (k : E) :
    Clear (Aff.addMul a b k) j := by
  intro x hx
  have hx' : x ∈ (b.slots.foldl (fun l y => l.push (y.1, mulE y.2 k)) a.slots).toList := hx
  rw [OnBytes.Model.foldl_push_toList (fun y : Nat × E => (y.1, mulE y.2 k))] at hx'
  rcases List.mem_append.1 hx' with h | h
  · exact ha x h
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact hb y hy

theorem clear_scale {a : Aff} {j : Nat} (ha : Clear a j) (k : E) : Clear (Aff.scale a k) j :=
  clear_addMul (clear_empty j) ha k

theorem clear_add {a b : Aff} {j : Nat} (ha : Clear a j) (hb : Clear b j) : Clear (a + b) j :=
  clear_addMul ha hb oneE

theorem clear_sub {a b : Aff} {j : Nat} (ha : Clear a j) (hb : Clear b j) : Clear (a - b) j :=
  clear_addMul ha hb (subE zeroE oneE)

/-- A form that names slots from lo on and below hi alone names no slot outside. -/
theorem clear_of_in {lo hi : Nat} {a : Aff} (h : In lo hi a) {j : Nat} (hj : j < lo ∨ hi ≤ j) :
    Clear a j := by
  intro x hx
  have := h x hx
  omega

/-- A fold whose steps keep it keeps it. -/
theorem clear_fold {j : Nat} (step : Aff → Nat → Aff)
    (hs : ∀ f c, Clear f j → Clear (step f c) j) :
    ∀ (l : List Nat) (a : Aff), Clear a j → Clear (l.foldl step a) j
  | [], _, h => h
  | c :: l, a, h => clear_fold step hs l _ (hs a c h)

/-! ## Rules on coefficients -/

/-- A sum of forms none of which has a coefficient on slot j leaves the coefficient as it was. -/
theorem sc_fold (b : Nat → Aff) (w : Nat → E) (j : Nat) (hb : ∀ c, sc (b c) j = 0) :
    ∀ (l : List Nat) (a : Aff),
      sc (l.foldl (fun (f : Aff) c => Aff.addMul f (b c) (w c)) a) j = sc a j
  | [], _ => rfl
  | c :: l, a => by
    rw [List.foldl_cons, sc_fold b w j hb l, sc_addMul, hb c]
    ring

/-- **The verifier program's row form of the leaves' sumcheck, with a scaled form kept.** -/
theorem sc_leaves (hd : MaskedSum.Heard) (a0 : Aff) (A : E) (j : Nat) :
    sc ((toPsc hd).rowForm oneE (Aff.scale a0 A)) j =
      sc (rowAff hd oneE {}) j + vl (mulE hd.eps A) * sc a0 j := by
  rw [sc_eq, sc_eq, sc_eq, worth_leaves, worth_leaves]
  unfold vl
  ring

/-! ## From forms to a seat's claims -/

/-- A list of forms one of which has a coefficient other than 0 on slot j makes claims that are live
there. -/
theorem live_of_sc {S : Type} (seat : Seat S Claim) (hf : ∀ a, (seat.claim a).form = a)
    (hc : ∀ a, (seat.claim a).eqFirst = none) {l : List Aff} {j : Nat}
    (h : ∃ a ∈ l, sc a j ≠ 0) : liveAt (l.map seat.claim) j = true := by
  obtain ⟨a, ha, hne⟩ := h
  refine (liveAt_iff _ _).2 ⟨seat.claim a, List.mem_map.2 ⟨a, ha, rfl⟩, hc a, ?_⟩
  have e : slotCoef Reading.gl (seat.claim a) j = sc a j := by
    unfold sc slotCoef
    rw [hf a]
  rw [e]
  exact hne

/-- A list of forms none of which names slot j makes claims none of which names it. -/
theorem unnamed_of_clear {S : Type} (seat : Seat S Claim) (hf : ∀ a, (seat.claim a).form = a)
    {l : List Aff} {j : Nat} (h : ∀ a ∈ l, Clear a j) : unnamedAt (l.map seat.claim) j = true := by
  unfold unnamedAt
  rw [List.all_map, List.all_eq_true]
  intro a ha
  show unnamedIn (seat.claim a) j = true
  unfold unnamedIn
  rw [hf a, List.all_eq_true]
  intro x hx
  simpa using h a ha x hx

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.gives_pure
#print axioms ProofFile.Honest.K3.Good.Live.sc_clear
#print axioms ProofFile.Honest.K3.Good.Live.clear_ofConst
#print axioms ProofFile.Honest.K3.Good.Live.clear_empty
#print axioms ProofFile.Honest.K3.Good.Live.clear_slot
#print axioms ProofFile.Honest.K3.Good.Live.clear_addMul
#print axioms ProofFile.Honest.K3.Good.Live.clear_scale
#print axioms ProofFile.Honest.K3.Good.Live.clear_add
#print axioms ProofFile.Honest.K3.Good.Live.clear_sub
#print axioms ProofFile.Honest.K3.Good.Live.clear_of_in
#print axioms ProofFile.Honest.K3.Good.Live.clear_fold
#print axioms ProofFile.Honest.K3.Good.Live.sc_fold
#print axioms ProofFile.Honest.K3.Good.Live.sc_leaves
#print axioms ProofFile.Honest.K3.Good.Live.live_of_sc
#print axioms ProofFile.Honest.K3.Good.Live.unnamed_of_clear
