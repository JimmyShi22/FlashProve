--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumJoint.lean: the masked sumcheck's soundness law IN THE LEDGER's WORLD, at
any call: the joint of the law over the part's text (Johnson/Desc/Part/MaskedSumTruth.lean:
sound_true) and of what lies under the part's slots (Johnson/Desc/Part/MaskedSumLedger.lean:
ledger_own, ledger_D2). Statements and proofs. The sumcheck is not proved anew.

In words. Fixed first: the reading, the call k (any: variables summed plainly or at a point, any
degrees that the text takes, ends or none), THE MASK ROW, n (the ledger's next slot in front of the
hearing), the summand S with its sum sigma over the call's variables.
Then there are bad sets, indexed by two things that stand in front of the first draw: T, the claimed
form's public part; Cv, its hidden value. They have sound_true's sizes and are empty at the truth.
Then, for all entries of virtual rows (these stand BEHIND the sets) and all runs: if hear returns at
F, row returns at a ledger F' whose arrays have their size and hands back G', H is later than F and
than G', the row's form is worth 0 in the ledger's world of H, the summand at the challenges is S0
and the kept terms in that world, and no drawn element is bad: then the claimed form's value in that
world is sigma.
  frontValue  : the claimed form's hidden value by what stands in front of the hearing.
  front_value : it is the form's value in the world of every later ledger.
  heard_r, heard_front : what the hearing hands back, by what was read and by what stands in front.
  joint_at    : the law with the claimed form's value as a FREE LETTER Cv: also for a claimed form
                with entries of virtual rows. NOT SAFE BY ITSELF: it serves only a caller who shows
                Cv fixed in front of eps: see its comment for the run that fools any other.
  joint       : the law: joint_at at frontValue.
  whole_feeds : a return of whole gives joint's premises on hear and row, with S0 the end term on
                what the hearing read.
THE WORLD is the landed function Fork.worldOf of H, the mask row and the entries: it is not taken by
a "there is". (The law itself begins with four: the sum of the hiding polynomial, the two families
of sets, the true round polynomials.)
THE CLAIMED FORM OF joint HAS NO ENTRIES OF VIRTUAL ROWS (C.ents = #[]): with such entries its
hidden value would hang on what stands behind the sets. The kept terms may have entries: they enter
at the end.
THAT THE CLAIMED FORM's SLOTS ARE FILLED AT F is no premise: hear's return gives it: behind its
tests on the plan it takes Fork.publicPart, which refuses a slot that is not filled (the landed
publicPart_value). So the factors that frontValue reads at F are those of every later ledger (the
landed value_later_public).
NOTHING TIES F', the ledger at which row is called, TO THE HEARING's: the law holds at any F' at
which row returns, if one ledger H is later than both F and G'.
readAll k rs = some R is no free premise: hear's return gives such an R; the premise names it.
THE INDICES T, Cv (and mu) of muT and tq come from the order in which they are chosen: they are no
claim that these hang on them.
THE CALLER's DUTY, which no type here can bar: that C, F, the call's points, S and sigma hang on
nothing that is drawn OR COMMITTED behind eps. WITH A LEAD, F is the ledger behind the caller's
taking of its lead, and the lead lies in the first message of rs: so F, T and frontValue are made of
the state in front AND of that message: it stands in front of eps, but a kind with a lead has to
show that F is a function of these two alone.
What is not said.
  That mask is the committed mask row: the same letter as in the chain's one equation.
  That the row's form is worth 0. The end's equation. That H is later (a law of every block
  between). whole_feeds hands Later F G' and not Later at the caller's H: the caller adds the landed
  Later.trans.
  EMPTY AT THE TRUTH: that no eps is bad where Cv = sigma can be spent as it stands. The two other
  clauses speak of polynomials over K: tq is a letter under "there is", and nothing here joins the
  polynomial that the text completes from what was sent to it: they show that the sets are not
  padded at the truth, not that an honest file meets no bad draw.
  THE SETS ARE SETS OF VALUES IN K; THE DRAWS ARE ELEMENTS OF E. A reading is by its laws neither
  one-to-one nor onto: the sizes bound the bad VALUES; how many drawn elements read into them hangs
  on the reading on the draw's range. No rule on raw rounds is given.
  The sets come behind mask, S and sigma: a rule round by round wants these read off the prefix.
  One call, one law: nothing adds errors over several calls, or says that two calls' slots part.
  Nothing on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumTruth
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## At every call -/

/-- Every variable of a call that passes the tests on the plan has two coefficients or more. -/
theorem two_le_allK {k : Call} (hk : shapeOk k = true) : ∀ v ∈ k.all, 2 ≤ v.d := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | some e => exact two_le_all hk
  | none =>
    intro v hv
    unfold shapeOk at hk
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
    exact (hk.1 v hv).1

/-- A call without ends: the rounds that were read are the variables' rounds. -/
theorem readAll_none_vars {lead : Nat} {vs : List Var} {rs : List Fmt.RoundView} {R : Read}
    (h : readAll ⟨lead, vs, none⟩ rs = some R) : ∃ used, VarsRead vs used R.rounds := by
  unfold readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · rename_i x mu eps l h1 h2 h3
      have e := Option.some.inj h
      subst e
      obtain ⟨used, _, a2⟩ := varRounds_spec _ _ _ _ h2
      exact ⟨used, a2⟩
    · rename_i h3
      cases h3
    · cases h

/-- What was read has the variables' lengths. -/
theorem readAll_lens {k : Call} {rs : List Fmt.RoundView} {R : Read} (hk : shapeOk k = true)
    (hR : readAll k rs = some R) : Lens k.all R.rounds := by
  have hv := two_le_allK hk
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | some e =>
    obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := readAll_spec hR
    exact lens_of_read hvr hv
  | none =>
    obtain ⟨_, hvr⟩ := readAll_none_vars hR
    exact lens_of_read hvr hv

/-! ## The claimed form's value -/

/-- The claimed form's hidden value, by what stands in front of the hearing: its public part T, less
coefficient times factor times mask entry over its slots; the factors are read in the ledger in
front. -/
def frontValue (mask : ℕ → K) (C : Aff) (F : Fork) (T : E) : K :=
  ρ.val T - (C.slots.toList.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum

/-- It is the form's value in the world of every later ledger. -/
theorem front_value (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {C : Aff} {k : Call} {F G H : Fork}
    {rs : List Fmt.RoundView} {h : Heard} (hh : hear C k F rs = some (h, G)) (hC : C.ents = #[])
    (hl : OnBytes.PscRun.Later F H) :
    C.value ρ (H.worldOf ρ mask entry) = frontValue ρ mask C F h.target := by
  have e := ledger_D2 ρ mask entry hh hC hl
  obtain ⟨_, _, _, _, _, he, _⟩ := hear_spec hh
  have e2 : h.start = C := by rw [he]
  rw [e2] at e
  unfold frontValue
  rw [← e]
  ring

/-! ## What the hearing hands back, by what was read -/

/-- The challenges that the hearing hands back are those of the rounds that were read. -/
theorem heard_r {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} {R : Read}
    (hh : hear C k F rs = some (h, G)) (hR : readAll k rs = some R) :
    h.r = R.rounds.map (·.2) ∧ h.eps = R.eps := by
  obtain ⟨_, _, R', _, hR', hrec, _⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  subst hRR
  constructor <;> rw [hrec]

/-- The sumcheck's first slot is the ledger's next one; the target is the claimed form's public part
at the ledger in front; the form that is handed back is the claimed one. -/
theorem heard_front {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) :
    h.first = F.next ∧ F.publicPart C = some h.target ∧ h.start = C ∧ h.vars = k.all := by
  obtain ⟨_, _, _, hT, _, hrec, _⟩ := hear_spec hh
  refine ⟨by rw [hrec], ?_, by rw [hrec], by rw [hrec]⟩
  rw [hrec]
  exact hT

/-! ## The joint -/

/-- **The law with the claimed form's value as a free letter Cv.** The claimed form may have entries
of virtual rows. IT SERVES ONLY A CALLER WHO SHOWS THAT Cv IS FIXED IN FRONT OF eps: the sets are
indexed by Cv, and the premise that C is worth Cv is taken in a world whose entries stand behind the
sets: nothing here bars a Cv that hangs on them.
THE RUN THAT FOOLS ANY OTHER CALLER (a reader's; a sketch over K, not checked in the program's
elements): the claimed form has an entry that the prover lays behind eps. It sends any mu other than
the hiding polynomial's sum muT, and on eps lays the entry so that Cv = sigma - (mu - muT) / eps.
Then the run of the true round polynomials begins at the verifier's claim, and no round's challenge
is bad. So, whatever sets have the law, eps lies in badE T Cv mu AT EVERY eps other than 0: each set
has at most one member, and the event has probability about 1. -/
theorem joint_at (k : Call) (hk : shapeOk k = true) (mask : ℕ → K) (n : ℕ) (S : List K → K)
    (sigma : K) (hS : IsSum (k.all.map (Var.wt ρ)) S sigma) :
    ∃ (muT : K → K → K) (badE : K → K → K → Finset K) (tq : K → K → K → K → List K → K[X])
      (bad : K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ T Cv, IsSum (k.all.map (Var.wt ρ))
        (hid (k.all.map (Var.wt ρ)) fun i => mask (n + i)) (muT T Cv)) ∧
      (∀ T Cv mu, (badE T Cv mu).card ≤ 1) ∧
      (∀ T Cv mu eps pre g,
        (bad T Cv mu eps pre g).card < dAt (k.all.map (Var.wt ρ)) pre.length) ∧
      (∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G F' G' H : Fork) (rs : List Fmt.RoundView) (h : Heard)
        (R : Read) (S0 : E) (kept f : Aff) (Cv : K),
        F.next = n → hear C k F rs = some (h, G) → readAll k rs = some R →
        C.value ρ (H.worldOf ρ mask entry) = Cv →
        OnBytes.PscRun.Sized F' → row h S0 kept F' = some (f, G') → OnBytes.PscRun.Later G' H →
        f.value ρ (H.worldOf ρ mask entry) = 0 →
        S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ (H.worldOf ρ mask entry) →
        ρ.val R.eps ∉ badE (ρ.val h.target) Cv (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val h.target) Cv (ρ.val R.mu) (ρ.val R.eps))
          (movesOf ρ k.all R.rounds (addE R.mu (mulE R.eps h.target)))) →
        Cv = sigma) ∧
      (∀ T Cv, Cv = sigma → ∀ mu, badE T Cv mu = ∅) ∧
      (∀ T Cv mu eps pre, bad T Cv mu eps pre (tq T Cv mu eps (pre.map (·.2))) = ∅) ∧
      (∀ T Cv, Cv = sigma → ∀ (mu eps : K) (xs : List K),
        xs.length = (k.all.map (Var.wt ρ)).length →
        Chain (k.all.map (Var.wt ρ)) (honest (tq T Cv mu eps) [] xs) (muT T Cv + eps * T)
          (hid (k.all.map (Var.wt ρ)) (fun i => mask (n + i)) xs + eps * S xs +
            eps * (T - Cv) * psiProd (k.all.map (Var.wt ρ)) xs)) := by
  have hv := two_le_allK hk
  choose muT badE tq bad h1 h2 h3 h4 h5 h6 h7 using fun (T Cv : K) =>
    sound_true ρ k.all hv (fun i => mask (n + i)) S sigma hS T Cv
  refine ⟨muT, badE, tq, bad, h1, h2, h3, ?_, h5, h6, h7⟩
  intro entry C F G F' G' H rs h R S0 kept f Cv hn hh hR hCv hF' hr hlG hzero hend hne hnb
  obtain ⟨_, _, R', _, hR', hrec, _⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  subst hRR
  have e1 : h.vars = k.all := by rw [hrec]
  have e2 : h.r = R'.rounds.map (·.2) := by rw [hrec]
  have e3 : h.eps = R'.eps := by rw [hrec]
  have e4 : h.start = C := by rw [hrec]
  have e5 : h.claim = after k.all R'.rounds (addE R'.mu (mulE h.eps h.target)) := by rw [hrec]
  have hsl : ∀ i, i < ownSlots k.all →
      (H.worldOf ρ mask entry).slot (h.first + i) = (fun i => mask (n + i)) i := by
    intro i hi
    rw [← hn]
    exact ledger_own ρ mask entry hh hF' hr hlG i hi
  refine h4 (ρ.val h.target) Cv (H.worldOf ρ mask entry) h
    R'.mu R'.rounds S0 kept F' G' f e1 (readAll_lens hk hR) e2 e5 rfl (by rw [e4]; exact hCv)
    hsl hr hzero ?_ (by rw [e3]; exact hne) (by rw [e3]; exact hnb)
  rw [← hend, e2, List.map_map]
  rfl

/-- **THE LAW IN THE LEDGER's WORLD, AT ANY CALL.** n: the ledger's next slot in front of the
hearing: a letter in front, because a summand with ends may name the masks under the end values'
slots. -/
theorem joint (k : Call) (hk : shapeOk k = true) (mask : ℕ → K) (n : ℕ) (S : List K → K)
    (sigma : K) (hS : IsSum (k.all.map (Var.wt ρ)) S sigma) :
    ∃ (muT : K → K → K) (badE : K → K → K → Finset K) (tq : K → K → K → K → List K → K[X])
      (bad : K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ T Cv, IsSum (k.all.map (Var.wt ρ))
        (hid (k.all.map (Var.wt ρ)) fun i => mask (n + i)) (muT T Cv)) ∧
      (∀ T Cv mu, (badE T Cv mu).card ≤ 1) ∧
      (∀ T Cv mu eps pre g,
        (bad T Cv mu eps pre g).card < dAt (k.all.map (Var.wt ρ)) pre.length) ∧
      (∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G F' G' H : Fork) (rs : List Fmt.RoundView) (h : Heard)
        (R : Read) (S0 : E) (kept f : Aff),
        F.next = n → hear C k F rs = some (h, G) → readAll k rs = some R → C.ents = #[] →
        OnBytes.PscRun.Sized F' → row h S0 kept F' = some (f, G') →
        OnBytes.PscRun.Later F H → OnBytes.PscRun.Later G' H →
        f.value ρ (H.worldOf ρ mask entry) = 0 →
        S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ (H.worldOf ρ mask entry) →
        ρ.val R.eps ∉ badE (ρ.val h.target) (frontValue ρ mask C F h.target) (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val h.target) (frontValue ρ mask C F h.target) (ρ.val R.mu) (ρ.val R.eps))
          (movesOf ρ k.all R.rounds (addE R.mu (mulE R.eps h.target)))) →
        C.value ρ (H.worldOf ρ mask entry) = sigma) ∧
      (∀ T Cv, Cv = sigma → ∀ mu, badE T Cv mu = ∅) ∧
      (∀ T Cv mu eps pre, bad T Cv mu eps pre (tq T Cv mu eps (pre.map (·.2))) = ∅) ∧
      (∀ T Cv, Cv = sigma → ∀ (mu eps : K) (xs : List K),
        xs.length = (k.all.map (Var.wt ρ)).length →
        Chain (k.all.map (Var.wt ρ)) (honest (tq T Cv mu eps) [] xs) (muT T Cv + eps * T)
          (hid (k.all.map (Var.wt ρ)) (fun i => mask (n + i)) xs + eps * S xs +
            eps * (T - Cv) * psiProd (k.all.map (Var.wt ρ)) xs)) := by
  obtain ⟨muT, badE, tq, bad, h1, h2, h3, h4, h5, h6, h7⟩ := joint_at ρ k hk mask n S sigma hS
  refine ⟨muT, badE, tq, bad, h1, h2, h3, ?_, h5, h6, h7⟩
  intro entry C F G F' G' H rs h R S0 kept f hn hh hR hC hF' hr hlF hlG hzero hend hne hnb
  have hCv := front_value ρ mask entry hh hC hlF
  rw [hCv]
  exact h4 entry C F G F' G' H rs h R S0 kept f _ hn hh hR hCv hF' hr hlG hzero hend hne hnb

/-! ## For a caller of whole -/

/-- A return of whole gives joint's premises on hear and row: S0 is the end term on the challenges
and on what the hearing read as end values; there are no kept terms; row's ledger is the one that
the hearing hands back. -/
theorem whole_feeds {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hF : OnBytes.PscRun.Sized F)
    (hw : whole C k endTerm F rs = some (h, f, G')) :
    ∃ (G : Fork) (R : Read), hear C k F rs = some (h, G) ∧ readAll k rs = some R ∧
      OnBytes.PscRun.Sized G ∧ row h (endTerm h.r R.values) {} G = some (f, G') ∧
      OnBytes.PscRun.Later F G' := by
  obtain ⟨e, G, sh, he, hh, hs, hr⟩ := whole_parts hw
  obtain ⟨_, _, R, _, hR, _, _⟩ := hear_spec hh
  obtain ⟨lead, vs, ends⟩ := k
  have he' : ends = some e := he
  subst he'
  have hs2 := ledger_shownEnds hF hh hR (OnBytes.PscRun.Later.refl G)
  rw [hs] at hs2
  have e1 : sh = R.values := Option.some.inj hs2
  subst e1
  exact ⟨G, R, hh, hR, (hear_keeps hh).sized hF, hr, whole_keeps hw⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.front_value
#print axioms VerifiableInference.Desc.Part.MaskedSum.heard_r
#print axioms VerifiableInference.Desc.Part.MaskedSum.heard_front
#print axioms VerifiableInference.Desc.Part.MaskedSum.joint_at
#print axioms VerifiableInference.Desc.Part.MaskedSum.joint
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_feeds
