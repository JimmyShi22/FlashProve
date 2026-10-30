-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's three shares of the online row, gathered into one term.
/-
AtFullSide/K12/ShareK12.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together? NOT KNOWN. No value of K (the kinds' rows at the base filling)
is laid here; hK₁ to hK₄ are met at `theK` with the later rows `laterOurs`
(AtFullSide/K12/MembershipsAtTheK.lean). pays, on₁, bud₁ are premises here; they are stated apart,
each under premises of its own: pays at `theK`, under the scope, the live test and four equations on
its entries, in `theK_pays_four_ofReturn` (AtFullSide/M1/K12AtK.lean); on₁, under a premise on the
family's first member, in `k12_on₁_at_the_g` (Honest/K12/Sim2/K12OnAtTheG.lean); bud₁ in
`k12_bud₁_at_theGOfReturn` (AtFullSide/K12/FirstBudK12.lean). left₃ follows at the family of
invariants that `TheThreadsHalf` names, UNDER PREMISES THAT STAY THERE: a value O of that structure,
of which none is laid there or beneath, and hRel (the relation lies in the tied requests):
`k12_left₃_at_the_threads` (AtFullSide/K12/ShareK12AtTheThreads.lean) with `rowsSay_at_the_letters`
(AtFullSide/K12/RowsSayAtTheLetters.lean). Th is a binder: the third share reads its third family at
border 2 (left₃'s equation), so it does not hold at every family. A SHARE CAN HOLD FOR NOTHING:
where G has no list of the kind, or no part of a test is called at any run, the clauses are over
nothing: that the four rows stand in G with a side is not said here.


What is here. THE ONE TERM THAT THE TOP STATEMENT ON ZERO KNOWLEDGE ASKS OF THE KIND K12 IN ITS FORM
BY KINDS: `KindShare` A G A.H Rel Th .K12 (Honest/Law/RowDebtsByKind.lean, another house's: pays ·
bud · on) at G := `theGOfReturn` made h T K (E2E/TheG.lean), general in the threads' parts T and the
kinds' rows K. A GATHER OF THE KIND's FOUR PLACES; A SORTING OF HYPOTHESES: IT PAYS NOTHING BEYOND
WHAT THE LAWS CALLED PAY. One definition; three statements.

  `K12Rel`   the relation at the base, with the clause on the request a letter.
  `k12_hrows₃_at_theG`, `k12_hrows₃_at_theGOfReturn`   each list of the kind in G's last chain takes
      its four fields from a row of `lotW`: from hK₃, hK₄.
  `k12_share_at_theGOfReturn`   the term.

WHAT EACH FIELD RESTS ON. pays A PREMISE (fits, exact, fresh of `Good` at every list of the kind).
bud first chain: A PREMISE (bud₁) · shared chain: `k12_bud₂_at_theGOfReturn` · last chain:
`k12_bud₃_at_base`: these two from the head and hK₁ to hK₄ alone. on first chain: A PREMISE (on₁) ·
shared chain (the tests on G_u and on G_omega): `k12_on₂_at_theGOfReturn`
(AtFullSide/K12/SharedShareAtTheGOfReturn.lean): NO PREMISE ON VALUES, at every family · last chain
(the request's own test): `k12_on₃_at_base` (AtFullSide/K12/SecondShareK12.lean) from hM and left₃.

THE PREMISES, SORTED. THE MAKER AND THE HEAD: made · h. ON K: hK₁ · hK₂ (shared chain) · hK₃ · hK₄
(last chain): the rows that K lays at places of the kind are the three lots', and K lays one at each
such place of the filling. ANOTHER HOUSE's SHARES: pays · on₁ · bud₁. AT THE OWN TEST: hM · left₃:
at each input of the relation, all coins and each return of ready there are a thread and a companion
such that the family's third member at border 2 is theirs, with `OwnTestDebts`. Under "there are" in
left₃ (a hypothesis): Th₃ and Said are tied to the family by the equation at border 2.

WHAT A REVIEWER ASKS BESIDE A SHARE, AND WHERE IT STANDS HERE. (a) No premise but memberships in K,
at every h, T, Th: NOT MET: pays, on₁, bud₁, hM and left₃ stand beside hK₁ to hK₄; Th is a binder,
and the last chain's need of it is ONE EQUATION ON ITS OWN FIELD BY NAME, (Th …).I₃ 2 = ThrS Th₃
Said 2; the first chain's like need lies inside on₁. (b) "Bear": every list of the kind in G is its
own row, simulators, On and bud included: `k12_hrows_at_theGOfReturn` at the shared chain,
`k12_hrows₃_at_theGOfReturn` at the last; at the first chain not here. (c) "Stands": by the plan
FOUR lists are meant: one in G's first chain, two in the shared, one in the last: THAT THEY STAND
THERE WITH A SIDE IS NOT TYPED HERE.
(d) The owners of what the kind's tests spend [counted
elsewhere by the kernel over the written book; not read here]: the first chain's test spends of
the kind K2's switch; the request's own test of a sender of the kind K1; the test on G_u of "send
o_u", of the kind K1; the test on G_omega spends nothing.

`K12Rel` is an abbreviation of `imageRel` (Johnson/T3/OwedThru.lean) at `relAt`
(Honest/Law/Rule/Tied.lean): at Ry := the served requests it is the text of the top statement's own
relation at the base (its file is not imported here; that the two are one is not shown here).


Limits. All limits of the files beneath, the limit on the committer's randomness at the test on G_u
first (AtFullSide/K12/OnAtRunUAtCommittersKey.lean's head): the row binds the input first and ranges
then over the lent coins and the challenges alone. The rule moves the debt and pays none of it.
Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.SharedShareAtTheGOfReturn
import AtFullSide.K12.SecondShareK12
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.T3.OwedThru

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

local instance (priority := high) shareK12Pad : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **The relation at the base**, in the text of the top statement's own (`imageRel` at `relAt`):
the image, under the identity and the map by which the online filling reads its randomness, of "the
instance is written of a request that Ry holds of at the matrix and of the object's sample there at
some seed". Ry: a letter. -/
abbrev K12Rel (files : VerifierAndGoals.PublicFiles) (Ry : FullSizeMatrix → XF → Prop) : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop :=
  ProofFile.Honest.imageRel id (tableCoins files)
    (ProofFile.Honest.relAt (ansAt (AZ files) PadZ (holdZ files)) Ry instanceAsPlainRecord)

/-- CONDITIONAL on hK₃ and hK₄. **hrows at the last chain, at G at the base.** -/
theorem k12_hrows₃_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G)
    (hK₃ : ∀ r ∈ K.second, r.place.kind = KindName.K12 →
      r ∈ (lotW Face.own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).rows
        A.Z A.G)
    (hK₄ : ∀ g ∈ (baseFilling files).second A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.second, r.place = g.place) :
    ∀ L ∈ (theGAtBase h T K).second, L.place.kind = KindName.K12 →
      K12RowAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G L := by
  intro L hL hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
  have hk' : (overlayRow K.second g).place.kind = KindName.K12 := hk
  cases e : K.second.find? (fun r => r.place == g.place) with
  | none =>
    exfalso
    have eb : overlayRow K.second g = bareUnlettered g := by
      unfold overlayRow
      rw [e]
    rw [eb] at hk'
    obtain ⟨r₀, hr₀, ep⟩ := hK₄ g hg hk'
    have := List.find?_eq_none.1 e r₀ hr₀
    simp [ep] at this
  | some r₀ =>
    have er : overlayRow K.second g = r₀ := by
      unfold overlayRow
      rw [e]
    rw [er] at hk' ⊢
    exact ⟨r₀, hK₃ r₀ (List.mem_of_find?_eq_some e) hk', rfl, rfl, rfl, rfl⟩

/-- CONDITIONAL on hK₃ and hK₄. **hrows at the last chain, at the G of the return.** -/
theorem k12_hrows₃_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₃ : ∀ r ∈ K.second, r.place.kind = KindName.K12 →
      r ∈ (lotW Face.own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).rows
        A.Z A.G)
    (hK₄ : ∀ g ∈ (baseFilling files).second A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.second, r.place = g.place) :
    ∀ L ∈ (theGOfReturn made h T K).second, L.place.kind = KindName.K12 →
      K12RowAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G L :=
  castSides_of (atPure_at_laid h.head.laid made).2
    (Q := fun _ G => ∀ L ∈ G.second, L.place.kind = KindName.K12 →
      K12RowAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G L)
    (k12_hrows₃_at_theG h T K hK₃ hK₄)

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **THE KIND K12's THREE SHARES OF THE ONLINE ROW, AS ONE TERM, AT THE
G OF THE RETURN.** A SORTING: pays, on₁, bud₁ and left₃ are premises. -/
theorem k12_share_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place)
    (hK₃ : ∀ r ∈ K.second, r.place.kind = KindName.K12 →
      r ∈ (lotW Face.own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).rows
        A.Z A.G)
    (hK₄ : ∀ g ∈ (baseFilling files).second A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.second, r.place = g.place)
    (Ry : FullSizeMatrix → XF → Prop)
    (Th : ∀ w₀ rc x, K12Rel files Ry w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R)
    -- another house's: fits, exact and fresh of Good at every list of the kind
    (pays : VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K12)
    -- the first chain's test: another house's two shares
    (on₁ : ∀ w₀ rc x (hrel : K12Rel files Ry w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R) ρ r,
      ρ.due A.F = true → silentAt A.F ((theGOfReturn made h T K).prover A.H) w₀ rc x ρ = none →
      runC A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k ρ = .ok r →
      ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = KindName.K12 →
        OnAtRun₁ (G := (theGOfReturn made h T K)) (H := A.H) (Th w₀ rc x hrel k R hR) ρ r L)
    (bud₁ : ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed A.F L)
    -- the request's own test: the job, and what is left at each input, coins and return of ready
    (M : ManyJob (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW OnBytes.HonestTrace.Sz.ref (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain)
      enterOwn openHonest.pile (K1.lotNo OnBytes.secondHashFunction A.Z)
      (fun w => ⟨w.trace, matrixInput.weights A.Z w.w₀, w.rc⟩)
      (fun w => matrixInput.weights A.Z w.w₀) (fun P' w => randAt P' w.rc) A.Z A.G = some M)
    (left₃ : ∀ w₀ rc x (hrel : K12Rel files Ry w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R),
      ∃ (Th₃ : Thread A.B A.F.S₃ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst
                            Cells) Unit ProofFile.Inst)
        (Said : ℕ → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop),
        (Th w₀ rc x hrel k R hR).I₃ 2 = ThrS Th₃ Said 2 ∧
        OwnTestDebts A.F A.Z h.places h.firstChain A.H k M Th₃ Said) :
    KindShare A (theGOfReturn made h T K) A.H (K12Rel files Ry) Th KindName.K12 where
  pays := pays
  bud := ⟨bud₁, k12_bud₂_at_theGOfReturn made h T K hK₁ hK₂,
    k12_bud₃_at_base h.head.toAtMg matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.F
      (atPure_at_laid h.head.laid made).2 A.G (k12_hrows₃_at_theGOfReturn made h T K hK₃ hK₄)⟩
  on := fun w₀ rc x hrel k R hR ρ r hρ hs hrun =>
    ⟨on₁ w₀ rc x hrel k R hR ρ r hρ hs hrun,
      k12_on₂_at_theGOfReturn made h T K hK₁ hK₂ Ry w₀ rc x hrel k R hR (Th w₀ rc x hrel k R hR) ρ
        r hρ hrun,
      by
        obtain ⟨Th₃, Said, hI₃, debts⟩ := left₃ w₀ rc x hrel k R hR
        exact k12_on₃_at_base h.head matrixInput OnBytes.HonestTrace.Sz.ref openHonest made A.F
          (atPure_at_laid h.head.laid made).2 (theGOfReturn_prover made h T K)
          (Th w₀ rc x hrel k R hR) hρ hR hrun M hM Th₃ Said hI₃ debts
          (k12_hrows₃_at_theGOfReturn made h T K hK₃ hK₄)⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.K12Rel
#print axioms AtFullSide.K12.k12_hrows₃_at_theG
#print axioms AtFullSide.K12.k12_hrows₃_at_theGOfReturn
#print axioms AtFullSide.K12.k12_share_at_theGOfReturn
