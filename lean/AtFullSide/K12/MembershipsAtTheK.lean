-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what the kind's gather asks of the kinds' rows, at theK over our later rows.
/-
AtFullSide/K12/MembershipsAtTheK.lean: CONDITIONAL: AT EVERY E AND apart: NO VALUE OF THESE TWO IS
LAID. THE ROW IS NOT PAID.

Can the hypotheses be met together? h: YES at the named files: there a head stands at a return of
the maker (`k12_bud₁_premises_met`, AtFullSide/K12/FirstBudK12.lean). E, apart: letters: thirteen
entries at the base filling, each with two proofs, and that their lots' names are apart: NO VALUE IS
LAID HERE, so the K of record is not written here [a reader of ours has counted thirteen lots with
names apart in the filling, so such entries can be had; the thirteen of record are another house's
text, unridden, its apart not shown: by its letter; not read]. slot₁₂ (of the last two statements):
that E's entry for the kind K12 holds the lot's value `simulatorLot` [another house has an entry
whose slot is that value by rfl, by its letter; not read]. Of the last statement's other premises:
pays lies at this very K at another house, under two public premises and four equations on E
(`theK_pays_four_ofReturn`, AtFullSide/M1/K12AtK.lean; not imported; not read by us); on₁ and left₃:
NO FAMILY Th IS KNOWN THAT MEETS THEM; hM: as at AtFullSide/K12/ShareK12.lean's head.

What is here. THE FIVE PREMISES ON THE KINDS' ROWS K THAT THE KIND K12's GATHER AND ITS bud₁ ASK
(hK₁ to hK₄ of `k12_share_at_theGOfReturn`, AtFullSide/K12/ShareK12.lean; hK₀ of
`k12_bud₁_at_theGOfReturn`, AtFullSide/K12/FirstBudK12.lean), AT K := `theK` E apart (`laterOurs` A
h.head) (E2E/TheKOfRecord.lean; AtFullSide/M1/KRecord.lean: other houses' files): the form of the K
at which the row is to be counted, general in the thirteen entries E and in apart. No definition;
six statements.

  `k12_hK₁_at_theK`   each row of the kind in K's shared chain is a row of the lot at the test on
      G_u or of the lot at the test on G_omega: K's shared rows are `sharedOurs`
      (AtFullSide/M1/GOurs.lean: six rows, then these two lots' rows), and none of the six is of the
      kind (`base_not_K12`, AtFullSide/K14/Sim/AtBase.lean).
  `k12_hK₂_at_theK`   K lays a row at each side of the kind of the filling's shared chain:
      `shared_fit` (AtFullSide/M1/GOurs.lean): the rows' sides are the filling's.
  `k12_hK₃_at_theK`   each row in K's last chain is a row of the lot at the request's own test: by
      the texts.
  `k12_hK₄_at_theK`   K lays a row at each side of the filling's last chain: `second_fit`.
  `k12_hK₀_at_theK`   the lot's value at the first chain's test is among K's lots, from slot₁₂
      (`mem_theK`); at all later rows R.
  `k12_share_at_theK`   A TEST OF FIT: the gather called at this K with the four, and with bud₁ from
      AtFullSide/K12/FirstBudK12.lean: so that Lean holds the five against the binders that ask
      them.

WHAT IT DOES NOT SAY. MEMBERSHIPS ARE NO PAYMENT. THE ROW IS NOT PAID: `k12_share_at_theK` keeps
pays · on₁ · hM · left₃ as premises, in the gather's own text; pays is itself a premise on K's rows;
on₁ and left₃ speak of the family Th, a binder. The law that pays the field pays asks two more
memberships of K, in the other direction (that the lots' rows are among K's); they are not here. The
second and the fourth statement hold of every side, of whatever kind; the binder's clause on the
kind is not used; the third likewise. ALL FOUR CAN HOLD FOR NOTHING: each lot lays one row at most
and none where a guard of its fails; that the filling has a side of the kind in a later chain is not
said here. Nothing is said of E's twelve other entries. The names at which the row is to be counted
(the thirteen of record, the threads' parts, the relation and the family of record) are not named
here: E, apart, T, Ry and Th are letters.

Every letter under "there are": in the ends of the second and the fourth statement the row r is tied
by its membership in K's chain and by the equation on its place.

THE LABEL "NOT IN FRONT OF A LAW OVER COINS" (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's
head). `k12_share_at_theK` calls the gather; the gather calls `k12_on₃_at_base`
(AtFullSide/K12/SecondShareK12.lean), which calls `onAtRun_W_six_paid` (Sim2/ListWSixPaid.lean),
which bears it. OUR READING, WHICH IS NO RULING: it is not inherited here. The letters that stay:
Th, M, Ry, with a thread and a companion under "there are" in left₃. on₁ and left₃ bind the
committer's randomness and the run's coins by "for all" inside the premise, and hM names no coin: so
no premise here holds at some coins and fails at others at a fixed letter. Ry is of the rule's
second kind: it narrows the inputs, and a law in front of which the term stands has to name it.
The five memberships name no coin and call no law that bears the label [by reading].

Limits. All limits of the files called. At the base filling, the matrices, Sz.ref, `openHonest` and
the format's second hash function alone. Other houses' values (`laterOurs`, `sharedOurs`, `secondOurs`,
`theK`) may turn, and then this file turns with them. Nothing on completeness, soundness or hiding.
No property of the protocol is claimed.
-/
import AtFullSide.M1.KRecord
import AtFullSide.K12.ShareK12
import AtFullSide.K12.FirstBudK12

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput tableCoins baseFilling baseMaker theGAtBase)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.TheSides AtPublicFiles.TheG AtPublicFiles.Bridge AtPublicFiles.Along
open FlashProve
open LPFD.Full (XF instanceAsPlainRecord)

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **hK₁ AT theK**, to the letter of the gather's binder: each row of the kind K12 in K's shared
chain is a row of the lot at the test on G_u or of the lot at the test on G_omega. From h (a head at
a return of the maker), at every E and apart. -/
theorem k12_hK₁_at_theK (h : HeadAtReturn files A) (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) :
    ∀ r ∈ (theK E apart (AtFullSide.M1.laterOurs A h.head)).shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G := by
  intro r hr hk
  have hr' : r ∈ AtFullSide.M1.sharedOurs A.Z h.places A.G := hr
  rcases List.mem_append.1 hr' with h₁ | h₁
  · exact (ProofFile.Honest.Term.base_not_K12 (files := files) h.head r h₁ hk).elim
  · rcases List.mem_append.1 h₁ with h₂ | h₂
    · exact .inl h₂
    · exact .inr h₂

/-- **hK₂ AT theK**, to the letter of the gather's binder: K lays a row at each side of the kind K12
of the filling's shared chain. From h (a head at a return of the maker), at every E and apart. -/
theorem k12_hK₂_at_theK (h : HeadAtReturn files A) (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) :
    ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ (theK E apart (AtFullSide.M1.laterOurs A h.head)).shared, r.place = g.place := by
  intro g hg _
  have hg' : g ∈ (AtFullSide.M1.sharedOurs A.Z h.places A.G).map (·.half) := by
    rw [AtFullSide.M1.shared_fit h.head A.G]
    exact hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg'
  exact ⟨r, hr, rfl⟩

/-- **hK₃ AT theK**, to the letter of the gather's binder: each row of the kind K12 in K's last
chain is a row of the lot at the request's own test. By the texts, at every h, E and apart. -/
theorem k12_hK₃_at_theK (h : HeadAtReturn files A) (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) :
    ∀ r ∈ (theK E apart (AtFullSide.M1.laterOurs A h.head)).second, r.place.kind = KindName.K12 →
      r ∈ (lotW Face.own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).rows
        A.Z A.G :=
  fun _ hr _ => hr

/-- **hK₄ AT theK**, to the letter of the gather's binder: K lays a row at each side of the kind K12
of the filling's last chain. At every h, E and apart. -/
theorem k12_hK₄_at_theK (h : HeadAtReturn files A) (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) :
    ∀ g ∈ (baseFilling files).second A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ (theK E apart (AtFullSide.M1.laterOurs A h.head)).second, r.place = g.place := by
  intro g hg _
  have hg' : g ∈ (AtFullSide.M1.secondOurs A.Z A.G).map (·.half) := by
    rw [AtFullSide.M1.second_fit A.Z A.G]
    exact hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg'
  exact ⟨r, hr, rfl⟩

/-- CONDITIONAL on slot₁₂. **hK₀ AT theK**: where E's entry for the kind K12 holds the lot's value
at the first chain's test, that value is among K's lots; at every E, apart and later rows R. -/
theorem k12_hK₀_at_theK (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling files) A.Z A.G)
    (slot₁₂ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ (theK E apart R).lots :=
  slot₁₂ ▸ mem_theK (e := E.k12) (by simp [TheThirteen.entries]) apart R

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see this file's head. THE ROW IS NOT PAID. **A TEST OF FIT: THE GATHER AT theK**:
the kind K12's three shares as one term at G := `theGOfReturn` made h T K, K := `theK` E apart
(`laterOurs` A h.head). No membership in K is left as a premise but slot₁₂ (and apart on E); pays
still speaks of K's rows. From made · h · slot₁₂ · pays · on₁ · hM · left₃. -/
theorem k12_share_at_theK (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (E : TheThirteen (baseFilling files) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (slot₁₂ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)
    (Ry : FullSizeMatrix → XF → Prop)
    (Th : ∀ w₀ rc x, K12Rel files Ry w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x k R)
    (pays : VerifiableInference.Compilation.KindPays (theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))) KindName.K12)
    (on₁ : ∀ w₀ rc x (hrel : K12Rel files Ry w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x k = .ok R) ρ r,
      ρ.due A.F = true →
      silentAt A.F ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x ρ = none →
      runC A.F A.B ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x k ρ = .ok r →
      ∀ L ∈ (theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))).first,
        L.place.kind = KindName.K12 →
        OnAtRun₁ (G := (theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))))
          (H := A.H) (Th w₀ rc x hrel k R hR) ρ r L)
    (M : ManyJob (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW OnBytes.HonestTrace.Sz.ref (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain)
      enterOwn openHonest.pile (K1.lotNo OnBytes.secondHashFunction A.Z)
      (fun w => ⟨w.trace, matrixInput.weights A.Z w.w₀, w.rc⟩)
      (fun w => matrixInput.weights A.Z w.w₀) (fun P' w => randAt P' w.rc) A.Z A.G = some M)
    (left₃ : ∀ w₀ rc x (hrel : K12Rel files Ry w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made h T
        (theK E apart (AtFullSide.M1.laterOurs A h.head))).prover A.H) w₀ rc x k = .ok R),
      ∃ (Th₃ : Thread A.B A.F.S₃ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst
                            Cells) Unit ProofFile.Inst)
        (Said : ℕ → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop),
        (Th w₀ rc x hrel k R hR).I₃ 2 = ThrS Th₃ Said 2 ∧
        OwnTestDebts A.F A.Z h.places h.firstChain A.H k M Th₃ Said) :
    KindShare A (theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))) A.H
      (K12Rel files Ry) Th KindName.K12 :=
  k12_share_at_theGOfReturn made h T (theK E apart (AtFullSide.M1.laterOurs A h.head))
    (k12_hK₁_at_theK h E apart) (k12_hK₂_at_theK h E apart) (k12_hK₃_at_theK h E apart)
    (k12_hK₄_at_theK h E apart) Ry Th pays on₁
    (k12_bud₁_at_theGOfReturn made h T _ (k12_hK₀_at_theK E apart _ slot₁₂)) M hM left₃

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_hK₁_at_theK
#print axioms AtFullSide.K12.k12_hK₂_at_theK
#print axioms AtFullSide.K12.k12_hK₃_at_theK
#print axioms AtFullSide.K12.k12_hK₄_at_theK
#print axioms AtFullSide.K12.k12_hK₀_at_theK
#print axioms AtFullSide.K12.k12_share_at_theK
