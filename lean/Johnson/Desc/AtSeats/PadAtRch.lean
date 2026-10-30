-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/PadAtRch.lean: **padAt_at_reads**: THE CLAUSE `PadAt` (Johnson/Desc/AtSeats/LayEntsAtRch.lean: what the lookup on
the calls left names no entry) ALONG THE STATES THAT THE VERIFIER REACHES, IN FRONT OF EACH FEED-FORWARD LINK's READS.
FROM THE GOALS' SCOPE AND hOk (each sub-protocol's test on the plan says yes).
HOW: BY POSITION, at l = 2 g: behind the first place with "opened" joined (14 l + 2) the ledger is the one from which
a sub-proof starts: it has its sizes (`startFork_sized`, Johnson/Desc/First/StartsSized.lean;
`openLay_ok` | `openLayZero_ok`, Johnson/Top/H0/Walk/FrameLaw.lean) · an accept of the seated lookup on the calls (14 l + 3) holds an accept of the kind's own
block (`Meaning.…theStated_calls_yes`, Johnson/Meaning/HeardCalls.lean, under its test on the plan) ·
`Fo.Tp.decide_named` (Johnson/Top/H/Keep/K3Named.lean): what it lays has PadNames · K4 (14 l + 4) leaves what the lookup
heard (`Rest`).
  `sized_behind_first` · `pad_behind_look` · `pad_front_reads`   along Reach
  `padAt_at_reads`   **along RchAt**: jLay2_at_reads' premise hPad (the promise is not spent)
  `jLay2_paid`       **JLay2 along "reached" with all that is paid laid in**: left: hS hR O hOk · hDlk hlk hWX (on letters) ·
                   layKB XV 0 = true (one test on public data, Johnson/Desc/AtSeats/LayLinesAt.lean)
What is not claimed. That the scope can be met. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.LayLinesAt
import Johnson.Desc.First.StartsSized
import Johnson.Meaning.HeardCalls
import Johnson.Top.H.Keep.K3Named
import Johnson.Desc.First.Look.K3CallsTurnsSharp
import Johnson.Desc.K1.Law.ReadersPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open OnBytes.Road.K4 (KeptAtS kept_atS)
open OnBytes.PscRun (Sized)
open IM (Open k1Ix)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **Behind a feed-forward link's first place the ledger has its sizes.** -/
theorem sized_behind_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1) a) : ∃ F₀, a.2.fork? = some F₀ ∧ Sized F₀ := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, k, _, b, b', _, hf, _, _, _, _, _, iB, hk, _, ep, hj, _, _, _⟩ :=
    hh (2 * g) (by omega)
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, _, hX, hkX, hgX, _⟩ := nam g hg
  obtain ⟨bX, hbX, ek, eg⟩ := built_of_ground O.blank hX
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨fs', f', m, hfs', hf', d1, _, d2, _, _⟩ := hj.yes hd
    rcases IM.frames_arms hfs' (2 * g) f' hf' with ⟨X2, h2, k2, _⟩ | ⟨l0, Pa, _, _, hop, _⟩ |
      ⟨Pa, nLin, hfa, _⟩ | ⟨Pa, hfa, _, hop, _⟩
    · obtain rfl : bX = X2 := Option.some.inj (hbX.symm.trans h2)
      rw [ek, hkX] at k2
      cases k2
    · rw [hop] at d2
      obtain ⟨_, _, _, _, _, _, hF, _⟩ := Law.openLayZero_ok d2
      exact ⟨_, hF, startFork_sized _ _⟩
    · unfold Seat.frameAt at hfa
      rw [hbX] at hfa
      simp only [Option.bind_eq_bind, Option.bind_some, ek, hkX, eg, hgX] at hfa
      split at hfa
      · cases hfa
      · simp only [show ((0 : ℕ) == 1) = false from rfl, Bool.false_eq_true, if_false,
          beq_self_eq_true, if_true] at hfa
        obtain ⟨q, _, e⟩ := Option.bind_eq_some_iff.1 hfa
        cases Option.some.inj e
    · rw [hop] at d2
      obtain ⟨_, _, _, _, _, _, hF, _⟩ := Law.openLay_ok d2
      exact ⟨_, hF, startFork_sized _ _⟩

/-- What the lookup on the calls has laid, in a feed-forward link. -/
def PadLaid (s : S) : Prop :=
  ∀ b₁, s.here = .lay b₁ → ∃ g G, b₁.fo = some g ∧ b₁.lookHeard = some g ∧ Fo.Tp.PadNames g G

/-- **Behind the lookup on the calls.** -/
theorem pad_behind_look (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1 + 1) a) : PadLaid a.2 := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix (2 * g) false)] at iB
  have hix : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  have hpo : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact (hOk b (List.mem_of_getElem? iB)).1
  rw [hix] at iB
  have hpc : K3.pieceAt Bs.G₀.W (2 * g) false = 2 := by
    unfold K3.pieceAt K3.isHead
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hS hR O.public
    rw [p4, ng, if_neg (by simp; omega)]
    rfl
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans (by
      rw [show 14 * (2 * g) + 1 + 2 = 14 * (2 * g) + 2 + 1 by omega]
      exact hb₁))
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hd' := ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
    have h3' : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
        ⟨1, some (2 * g), K3.pieceAt Bs.G₀.W (2 * g) false, .K3⟩ = some b' := by
      rw [hpc]
      have h4 := h3
      unfold IM.k3Place at h4
      rw [hix] at h4
      exact h4
    obtain ⟨p, laid, sent, rs', gs', _, hb⟩ :=
      Meaning.Planes.theStated_calls_yes K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape (2 * g) h3' hpo
        hd'
    obtain ⟨F₁, x, hF₁, hn, rfl, hN⟩ := VerifiableInference.OnPublicFiles.decide_named _ _ _ _ _ _ _ _ _ _ hb
    obtain ⟨F₀, hF₀, hZ⟩ := sized_behind_first hS hR O g hg (z, s) h1
    have eF : F₁ = F₀ := Option.some.inj (hF₁.symm.trans hF₀)
    have N := hN (eF ▸ hZ)
    intro b₂ hb₂
    have hb₃ : ((s.putFork x.2).hearLook x.1).here = .lay b₂ := hb₂
    have hn' : s.lookHeard? = none := hn
    have T := VerifiableInference.OnPublicFiles.putCalls_turns K3Lot.ofForm s x.1 F₁ x.2 hF₁ hn
    rcases T.part with ⟨a₀, _, _, hs, _⟩ | ⟨a₀, Fq, gq, _, h'⟩ | ⟨a₀, Fq, gq, _, _, xq, h'⟩
    · have hl : a₀.lookHeard = none := by
        unfold S.lookHeard? at hn'
        rw [hs] at hn'
        exact hn'
      have e1 : (s.putFork x.2).here = .lay { a₀ with F := x.2 } := by
        unfold S.putFork
        rw [hs]
      unfold S.hearLook at hb₃
      rw [e1] at hb₃
      simp only [hl, Option.isSome_none, Bool.false_eq_true, if_false] at hb₃
      obtain rfl := First.Here.lay.inj hb₃
      exact ⟨x.1, x.2, rfl, rfl, N⟩
    · exfalso
      exact nomatch h'.symm.trans hb₂
    · exfalso
      exact nomatch h'.symm.trans hb₂

/-- **Behind K4: in front of the reads.** -/
theorem pad_front_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1 + 1 + 1) a) : PadAt a.2 := by
  obtain ⟨Lk, b, x, e1, e2, _, hla, _⟩ := IM.k4_of hS hR O g hg
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 2] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans (by
      rw [show 14 * (2 * g) + 2 + 2 = 14 * (2 * g) + 2 + 1 + 1 by omega]
      exact hb₁))
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hd' := ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
    have K : KeptAtS { x.2 with k3Runs := true } s s' := kept_atS (rs := rs) (cols := gs) hd'
    obtain ⟨a₀, _, _, _, ha, _, _, _, _, _, _, _, hRest, _⟩ := K
    obtain ⟨gq, G, hfo, hlh, N⟩ := pad_behind_look hS hR O hOk g hg (z, s) h1 a₀ ha
    obtain ⟨a', ha', _, efo, _, elh⟩ := hRest.here a₀ ha
    refine ⟨fun b₀ fo hs hf => ?_, fun g' hg' f hf => ?_⟩
    · obtain rfl : b₀ = a' := First.Here.lay.inj (hs.symm.trans ha')
      obtain rfl : fo = gq := Option.some.inj (hf.symm.trans (efo.trans hfo))
      exact ⟨G, N⟩
    · have e0 : S.lookHeard? s' = a'.lookHeard := by
        unfold S.lookHeard?
        rw [ha']
      obtain rfl : g' = gq := Option.some.inj (hg'.symm.trans (e0.trans (elh.trans hlh)))
      exact N.noEntry f hf

/-- **ALONG "REACHED", IN FRONT OF EACH FEED-FORWARD LINK's READS**: jLay2_at_reads' premise hPad. -/
theorem padAt_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) {W : Type} {Fr : Frame} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → (linksFull[l]?).getD .layers = ModelPart.layers →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → PadAt a.1.2 := by
  intro l hl hsub a hr _ _
  obtain ⟨e, hg⟩ := layIsEven l hl hsub
  have hk : k1Ix l false = 3 := by
    show (if false = true then 5 else 3) + (if l = 24 then 1 else 0) = 3
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  have hr' := rchAt_raw hr
  rw [hk, e, show 14 * (2 * (l / 2)) + 3 + 2 = 14 * (2 * (l / 2)) + 2 + 1 + 1 + 1 by omega] at hr'
  exact pad_front_reads hS hR O hOk (l / 2) hg a.1 hr'

/-- **JLay2 ALONG "REACHED", WITH ALL THAT IS PAID LAID IN**: in hJ's own letters. -/
theorem jLay2_paid {Xi Tok : Type} {rows cols nR : ℕ} {XV : Verify.Public}
    (Dm : Sound.MgData Xi ProofFile.InstPub Tok rows cols nR XV) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (hKB : layKB XV 0 = true)
    {W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → JLay2 Dm a.1.2 :=
  jLay2_at_reads Dm hS hR O hDlk hlk (hWX ▸ headLink_open hS hR O) hWX
    (layLines_scope hS hR O hWX hKB) N Mg (padAt_at_reads hS hR O hOk N Mg)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sized_behind_first
#print axioms VerifiableInference.Desc.K1.pad_behind_look
#print axioms VerifiableInference.Desc.K1.pad_front_reads
#print axioms VerifiableInference.Desc.K1.padAt_at_reads
#print axioms VerifiableInference.Desc.K1.jLay2_paid
