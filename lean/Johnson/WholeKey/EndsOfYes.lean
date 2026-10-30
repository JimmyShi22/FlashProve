-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/EndsOfYes.lean: from the compiled verifier's yes, at what the whole-key scheme's
committer and prover hand out behind their coins (commitAt, proveAt, Johnson/WholeKey/Defs.lean), to
the ends of the prover of a whole request (`Ends`, Johnson/Prover/All/Good.lean). The way back of
`yes_of_not_ev` (Johnson/WholeKey/Complete.lean), at the same terms.

Main names.
  `accept_back`    (namespace OnBytes.Prover) the converse of `accept_at`.
  `accept_of_yes`  (namespace OnBytes.Prover) the converse of the last clause of `yes_of_prove`:
      where the compiled prover has returned and the compiled verifier says yes, the decision says
      yes at the prover's own transcript.
  `shown_some`, `pack_of_ok`, `parts_of_VRA`   (namespace OnBytes.WholeKey) what a shown proof, a
      packed proof and a yes at written parts hold.
  `ends_of_yes`    (namespace OnBytes.WholeKey) THE STATEMENT. Fix the oracle functions and all
      coins. Asked: the compiled verifier says yes at the key and the proof handed out · the laws of
      the wires (`WiresFit`) · the drawn place holds the copy · the lengths of the first table's
      salts and of what is drawn (`DrawFit`). Out: all three compiled runs have returned; the low
          proof is
      the proof of the prover of a whole request at the sample that the coins make up, and the low
      key is its first table's root with the honest out-of-domain sample; `Ends` holds there; the
      key's test and the session's interactive verifiers accept at their transcripts; the test of
      the copy's number says yes. No accept is asked.

Limits. At letters: any wires, any honest side. Pointwise in the oracle functions: no probability,
and no yes is shown: it is the premise. NOT CONCLUDED: the accept of the link's interactive
verifier, the two tests on the seeds, and that no stop has fired. Nothing on bytes. Nothing on
soundness. It states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Complete
import Johnson.Prover.YesOfProve
import OnBytes.Prover.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The converse of accept_at -/

section Converse
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable (sMT sFS : ℕ) (t : _root_.Compile.Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (y : E.Str)
  (xt : ℕ → TreeK lam L) (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- The converse of `accept_at`: if the decision says yes at what the verifier builds from the
prover's openings, it says yes at the external strings y and the transcript as the prover has hashed
it. -/
theorem accept_back (g : Fam (typedOracleFamily lam K L)) (kp : Kept lam L Q.loc.shape)
    (R : RootsOfChain lam Q.loc.shape) (ρ : Rho Q.loc.shape)
    (hR : RoundsAt g sMT Q.loc.shape Q.ann wq.sh embS kp R) (hC : Q.ann.Coherent) (hw : wq.OKG)
    (hloc : Q.loc.IsLocal)
    (hacc : Q.loc.accept x
      (wq.ext.build fun p => ((extK wq.ext y xt (rdE Q wq x ρ)) p).map Opening.sym)
      (mkTr Q.loc.shape Q.ann wq.sh R (trK Q.loc.shape kp ρ).plains ρ
        (opensK Q.loc.shape Q.ann wq.sh kp
          (rdS Q wq x (trK Q.loc.shape kp ρ).plains ρ R))) = true) :
    Q.loc.accept x y (trK Q.loc.shape kp ρ) = true := by
  obtain ⟨he, hrd⟩ := mkTr_at g sMT Q.loc.shape Q.ann wq.sh embS kp R ρ
    (rdS Q wq x (trK Q.loc.shape kp ρ).plains ρ R) hR hC hw.sh
  have hρ : (trK Q.loc.shape kp ρ).rho = ρ := rho_trK _ kp ρ
  refine (hloc x y _ _ _ ?_ ?_ ?_ ?_).trans hacc
  · rw [hρ, TypedOracleCompiler.Compile.Batch.mkTr_rho]
  · rw [TypedOracleCompiler.Compile.Batch.mkTr_plains, he]
  · intro p hp
    rw [hρ] at hp
    have hr : rdE Q wq x ρ p = true := by
      letI := wq.ext.dec
      exact decide_eq_true hp
    have e : extK wq.ext y xt (rdE Q wq x ρ) p =
        some ((xt (wq.ext.which p)).opening (wq.ext.leaf p) (E.rd y p)) := if_pos hr
    refine (hw.ext.build_rd _ p _ ?_).symm
    exact congrArg (Option.map Opening.sym) e
  · intro p hp
    rw [hρ] at hp
    refine (hrd p ?_).symm
    have hp' : p ∈ Q.loc.reads x ρ
        (effPlains Q.loc.shape Q.ann R (trK Q.loc.shape kp ρ).plains) := by
      rw [he]
      exact hp
    letI := wq.decO
    exact decide_eq_true hp'

/-- **The converse of the last clause of `yes_of_prove`.** Where the compiled prover has returned
(π, τ) and the compiled verifier says yes at π, the decision says yes at y and τ. -/
theorem accept_of_yes (g : Fam (typedOracleFamily lam K L)) (hw : wq.OKG) (hJ : FewJ Q.loc.shape Q.ann wq.sh)
    (h0 : Few0 Q.loc.shape Q.ann wq.sh) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hF : Q.ann.Fmt) (hDe : wq.ext.depth ≤ wq.maxDepth) (hfit : co.Fit sMT sFS depthReq)
    (hx : ExtAt g sMT wq.ext embE cms y xt) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (hp : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ))
    (hy : (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true) :
    Q.loc.accept x y τ = true := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 hp
  obtain ⟨R, hc⟩ := chain_at g sMT t cms (xin x) co cap hfit.leaf Q.loc.shape Q.ann wq.sh embS
    embP 0 .first σ z hz hF hJ h0 (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
  have heff := (mkTr_at g sMT Q.loc.shape Q.ann wq.sh embS z.2.1 R z.1 (fun _ =>
    true) hc.rounds hC hw.sh).1
  have hrd : rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R =
      (haveI := wq.decO
       fun p => decide (p ∈ Q.loc.reads x z.1 (trK Q.loc.shape z.2.1 z.1).plains)) := by
    unfold rdS
    rw [heff]
  have ho : Opened sMT Q.loc.shape Q.ann wq.sh R
      (rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R)
      (finish Q wq x y xt co z).opens := by
    show Opened sMT Q.loc.shape Q.ann wq.sh R
      (rdS Q wq x (trK Q.loc.shape z.2.1 z.1).plains z.1 R) (opensK Q.loc.shape Q.ann wq.sh z.2.1 _)
    rw [hrd]
    exact opened_at g sMT Q.loc.shape Q.ann wq.sh embS z.2.1 R _ hc.rounds hw.sh
  have hoE : OpenedE sMT wq.maxDepth wq.ext (rdE Q wq x z.1) (finish Q wq x y xt co z).ext :=
    openedE_at g sMT wq.maxDepth E wq.ext embE cms y xt _ hx hDe
  obtain ⟨s1, Fs, f1, fit1⟩ := ho.cuts hw.sh hw.depth embS
  obtain ⟨sE, Fe, fE, fitE⟩ := hoE.cuts embE cms
  rw [TypedOracleCompiler.Run.verifyBS_det] at hy
  unfold TypedOracleCompiler.Run.verifyF at hy
  have hch : TypedOracleCompiler.Run.chainF g t cms (xin x) (finish Q wq x y xt co z).salt
      (finish Q wq x y xt co z).rtreq Q.loc.shape Q.ann wq.sh embP 0 Phase.first
      (finish Q wq x y xt co z).roots (finish Q wq x y xt co z).plains = some (z.1, R, z.2.2.1) :=
    hc.chain
  rw [hch] at hy
  dsimp only at hy
  split at hy
  · unfold TypedOracleCompiler.Run.afterBOF at hy
    rw [forests_at f1 fE] at hy
    dsimp only at hy
    split at hy
    · have hacc := (Bool.and_eq_true_iff.1 hy).2
      refine accept_back sMT Q wq embS x y xt g z.2.1 R z.1 hc.rounds hC hw hloc ?_
      rw [hrd]
      exact hacc
    · exact absurd hy (by simp)
  · exact absurd hy (by simp)

end Converse

end OnBytes.Prover

/-! ## From the yes at what the scheme hands out, to the runs -/

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Runs
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- A shown proof comes from a run that returned and did not stop. -/
theorem shown_some {P : Type} {s : Shape} {stop : Rho s → Bool} {run : Res (P × Tr s)} {proof : P}
    (h : shown stop run = some proof) :
    ∃ value, run = .ok value ∧ value.1 = proof ∧ stop value.2.rho = false := by
  cases run with
  | ok value =>
    by_cases hs : stop value.2.rho = true
    · simp [shown, hs] at h
    · refine ⟨value, rfl, ?_, Bool.eq_false_iff.2 hs⟩
      simpa [shown, hs] using h
  | noFormat => simp [shown] at h
  | ranOut j => simp [shown] at h

/-- The proof that `pack` makes where all three runs have returned. -/
theorem pack_of_ok (i : I) {Kap : Type} (d : Draw lam L Bd aT aL Kap) (y : Raw lam L aT aL)
    (a : OneProtocolProof lam (batTC L aT) × Tr L.offline.shape) (b : OneProtocolProof lam (batLC L aL) × Tr L.link.shape)
    (c : OneProtocolProof lam L.onlineBatch × Tr L.onlineBatch.loc.shape) (ha : y.2.2.2.1 = .ok a) (hb : y.2.2.2.2.1 = .ok b)
    (hc : y.2.2.2.2.2 = .ok c) :
    pack i d y = .ok (⟨d.n, some a.1, (y.1.2, L.recOf i d.r y.2.2.1, some b.1), some c.1⟩,
      y.2.1, y.2.2.1, a.2, b.2, c.2) := by
  unfold pack
  rw [ha, hb, hc]
  rfl

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (side : HonestSide lam L Bd aT aL)
  (oracles : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- What a yes of the compiled verifier at a written proof holds. -/
theorem parts_of_VRA (k : KeyRoot lam L) (request : X) (copy : ℕ)
    (proofT : Option (OneProtocolProof lam (batTC L aT))) (root : Dig lam) (record : L.Rec)
    (proofL : Option (OneProtocolProof lam (batLC L aL))) (proofB : Option (OneProtocolProof lam L.onlineBatch))
    (verifierSaysYes : (verifyAtKeyRoot W S cA r₀ p k request ⟨copy, proofT, (root, record, proofL),
                    proofB⟩).det oracles = true) :
    ∃ πT πL πB, proofT = some πT ∧ proofL = some πL ∧ proofB = some πB ∧
      S.num copy πB.plains = true ∧ (verifyOfflineProof W cA p k.cm k.rcd πT).det oracles = true ∧
      (verifyOnlineProof W cA r₀ p root request record πB).det oracles = true := by
  cases proofT with
  | none => exact absurd verifierSaysYes (by simp [verifyAtKeyRoot, verifyAtFullKey, KeyRoot.full, OfflineLinkOnlineProof.low, OComp.det])
  | some πT =>
    cases proofL with
    | none => exact absurd verifierSaysYes (by simp [verifyAtKeyRoot, verifyAtFullKey, KeyRoot.full, OfflineLinkOnlineProof.low,
        OComp.det])
    | some πL =>
      cases proofB with
      | none => exact absurd verifierSaysYes (by simp [verifyAtKeyRoot, verifyAtFullKey, KeyRoot.full, OfflineLinkOnlineProof.low,
          OComp.det])
      | some πB =>
        have copyCoins : ((outOfDomainSeedIs W S k.cm k.rcd.1).bind fun s0 =>
            (outOfDomainSeedIs W S root record.1).bind fun sj =>
            (verifyOfflineProof W cA p k.cm k.rcd πT).bind fun a =>
            (verifyLinkProof W cA p k.cm root k.rcd record πL).bind fun b =>
            (verifyOnlineProof W cA r₀ p root request record πB).bind fun committerCoins =>
            OComp.pure (S.num copy πB.plains && s0 && sj && a && b && committerCoins)).det oracles
                = true := verifierSaysYes
        simp only [OComp.det_bind, OComp.det, Bool.and_eq_true] at copyCoins
        exact ⟨πT, πL, πB, rfl, rfl, rfl, copyCoins.1.1.1.1.1, copyCoins.1.1.2, copyCoins.2⟩

/-- **From the compiled verifier's yes at what the committer and the prover behind their coins hand
out, to the ends of the prover of a whole request at the sample that the coins make up.** Fixed
oracle functions. What is asked: the laws of the wires, the place of the drawn copy, and the lengths
of the salts and of what is drawn. No accept of an interactive verifier is asked: two of the three,
the key's test and the session's, are read off the yes. -/
theorem ends_of_yes (wires : WiresFit W cA) (index : I) (request : X) (committerCoins : DrawC lam L
    Bd aT aL side.KT side.KL)
    (copyCoins : DrawCopy lam L Bd aT aL side.KL) (proverCoins : DrawP lam L Bd aT aL side.KB)
    (atPlace : committerCoins.copies[proverCoins.j]? = some copyCoins)
    (saltLengths : ∀ j, j < L.wordLength → (cutS (2 ^ W.depth) committerCoins.s j).length = p.sMT)
    (drawFits : DrawFit W p (drawOf W side committerCoins copyCoins proverCoins))
    (verifierSaysYes : (verifyW W S cA r₀ p ((commitAt W S cA side index committerCoins).det
        oracles).1 request
      ((proveAt W cA r₀ side ((commitAt W S cA side index committerCoins).det oracles).2 request
          proverCoins).det oracles)).det oracles = true) :
    ∃ (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape) (τL : Tr L.link.shape)
      (τB : Tr L.onlineBatch.loc.shape),
      π = lowPrf ((commitAt W S cA side index committerCoins).det oracles).1
        ((proveAt W cA r₀ side ((commitAt W S cA side index committerCoins).det oracles).2 request
            proverCoins).det oracles) ∧
      lowKey ((commitAt W S cA side index committerCoins).det oracles).1 =
        ⟨((committerTreeKeptByProver W side.b₀ (L.encodeIndex index committerCoins.r) (cutS (2 ^ W.depth)
                                      committerCoins.s)).det oracles).root,
          L.recOf index committerCoins.r e₁⟩ ∧
      Ends W S cA r₀ side.b₀ side.st.joint side.capT side.capL side.capB oracles index
          committerCoins.r (cutS (2 ^ W.depth) committerCoins.s) request
        (drawOf W side committerCoins copyCoins proverCoins) π e₁ e₂ τT τL τB ∧
      L.offline.accept (L.recOf index committerCoins.r e₁) (L.encodeIndex index committerCoins.r) τT = true ∧
      L.onlineBatch.loc.accept (request, L.recOf index copyCoins.r e₂) (L.encodeIndex index copyCoins.r) τB = true ∧
      S.num (side.nm proverCoins.j) τB.plains = true := by
  have ft : ((commitAt W S cA side index committerCoins).det oracles).2.copies[proverCoins.j]? =
      some (tabG W S side oracles index copyCoins.r copyCoins.s) := by
    rw [det_commitAt]
    show (committerCoins.copies.map fun copyCoins => tabG W S side oracles index copyCoins.r
        copyCoins.s)[proverCoins.j]? = _
    rw [List.getElem?_map, atPlace]
    rfl
  have fl : ((commitAt W S cA side index committerCoins).det oracles).1.links[proverCoins.j]? =
      some ((linkO W cA side index (tabG W S side oracles index committerCoins.r committerCoins.s)
          (tabG W S side oracles index copyCoins.r copyCoins.s) copyCoins).det oracles) := by
    rw [det_commitAt]
    show (committerCoins.copies.map fun copyCoins =>
      (linkO W cA side index (tabG W S side oracles index committerCoins.r committerCoins.s) (tabG
          W S side oracles index copyCoins.r copyCoins.s) copyCoins).det oracles)[proverCoins.j]? =
          _
    rw [List.getElem?_map, atPlace]
    rfl
  have hi : ((commitAt W S cA side index committerCoins).det oracles).2.i = index := by
    rw [det_commitAt]
  have hkey : lowKey ((commitAt W S cA side index committerCoins).det oracles).1 =
      ⟨(tabG W S side oracles index committerCoins.r committerCoins.s).tree.root,
        L.recOf index committerCoins.r (tabG W S side oracles index committerCoins.r
            committerCoins.s).seed⟩ := by
    rw [det_commitAt]
    rfl
  have hproof := det_proveAt W cA r₀ side oracles ((commitAt W S cA side index committerCoins).det
      oracles).2 request proverCoins _ ft
  rw [hi] at hproof
  have hlow : lowPrf ((commitAt W S cA side index committerCoins).det oracles).1
      ((proveAt W cA r₀ side ((commitAt W S cA side index committerCoins).det oracles).2 request
          proverCoins).det oracles) =
      ⟨side.nm proverCoins.j, ((commitAt W S cA side index committerCoins).det oracles).1.piT,
        (linkO W cA side index (tabG W S side oracles index committerCoins.r committerCoins.s)
            (tabG W S side oracles index copyCoins.r copyCoins.s) copyCoins).det oracles,
        shown (side.st.stopB index copyCoins.r (tabG W S side oracles index copyCoins.r
            copyCoins.s).seed request (side.nm proverCoins.j))
          ((proveBA W cA r₀ (fun _ => (tabG W S side oracles index copyCoins.r copyCoins.s).tree)
            (side.dressB (side.rvB proverCoins.κ) proverCoins.co) side.capB (tabG W S side oracles
                index copyCoins.r copyCoins.s).tree.root request
            (L.recOf index copyCoins.r (tabG W S side oracles index copyCoins.r copyCoins.s).seed)
                (L.encodeIndex index copyCoins.r)
            (side.st.B index copyCoins.r (tabG W S side oracles index copyCoins.r copyCoins.s).seed
                request (side.nm proverCoins.j) proverCoins.κ)).det oracles)⟩ := by
    rw [hproof]
    unfold lowPrf
    dsimp only
    rw [fl, Option.getD_some]
    rfl
  have hpiT : ((commitAt W S cA side index committerCoins).det oracles).1.piT =
      shown (side.st.stopT index committerCoins.r (tabG W S side oracles index committerCoins.r
          committerCoins.s).seed)
        ((proveTA W cA (fun _ => (tabG W S side oracles index committerCoins.r
            committerCoins.s).tree)
          (side.dressT (side.rvT committerCoins.κ) committerCoins.co) side.capT
          (tabG W S side oracles index committerCoins.r committerCoins.s).tree.root (L.recOf index
              committerCoins.r (tabG W S side oracles index committerCoins.r committerCoins.s).seed)
          (L.encodeIndex index committerCoins.r) (side.st.T index committerCoins.r (tabG W S side oracles
                      index committerCoins.r committerCoins.s).seed committerCoins.κ)).det oracles) := by
    rw [det_commitAt]
  have hv' := verifierSaysYes
  unfold verifyW at hv'
  rw [hkey, hlow, hpiT, det_linkO] at hv'
  obtain ⟨πT, πL, πB, h1, h2, h3, hn, vT, vB⟩ := parts_of_VRA W S cA r₀ p oracles _ request _ _ _ _
      _ _ hv'
  obtain ⟨a, ha, rfl, -⟩ := shown_some h1
  obtain ⟨b, hb, rfl, -⟩ := shown_some h2
  obtain ⟨u, hu, rfl, -⟩ := shown_some h3
  have hy := det_allY_parts W S cA r₀ side oracles index committerCoins.r committerCoins.s request
      (drawOf W side committerCoins copyCoins proverCoins) copyCoins.s rfl
  have hx : (allX W S cA r₀ side.b₀ side.st.joint side.capT side.capL side.capB
      (index, committerCoins.r, cutS (2 ^ W.depth) committerCoins.s) request (drawOf W side
          committerCoins copyCoins proverCoins)).det oracles = _ :=
    (det_allX W S cA r₀ side.b₀ side.st.joint side.capT side.capL side.capB oracles _ request
        _).trans
      ((congrArg (pack index (drawOf W side committerCoins copyCoins proverCoins)) hy).trans
        (pack_of_ok index (drawOf W side committerCoins copyCoins proverCoins) _ a b u ha hb hu))
  have hE := all_ends W S cA r₀ p side.b₀ side.st.joint side.capT side.capL side.capB oracles index
      committerCoins.r
    (cutS (2 ^ W.depth) committerCoins.s) request (drawOf W side committerCoins copyCoins
        proverCoins) _ _ _ _ _ _ wires saltLengths drawFits hx
  have extT : ExtAt oracles p.sMT (wTC W).ext W.embE
      (cmsTA cA (tabG W S side oracles index committerCoins.r committerCoins.s).tree.root
        (L.recOf index committerCoins.r (tabG W S side oracles index committerCoins.r
            committerCoins.s).seed).2) (L.encodeIndex index committerCoins.r)
      (fun _ => (tabG W S side oracles index committerCoins.r committerCoins.s).tree) := by
    unfold tabG
    dsimp only
    rw [root_committerTreeKeptByProver]
    exact extAt_key W cA oracles p.sMT side.b₀ _ _ _ wires.oka.base saltLengths
  have extB : ExtAt oracles p.sMT (wBC W).ext W.embE
      (cmsBA cA (tabG W S side oracles index copyCoins.r copyCoins.s).tree.root
        (L.recOf index copyCoins.r (tabG W S side oracles index copyCoins.r copyCoins.s).seed).2)
            (L.encodeIndex index copyCoins.r)
      (fun _ => (tabG W S side oracles index copyCoins.r copyCoins.s).tree) := by
    unfold tabG
    dsimp only
    rw [root_committerTreeKeptByProver]
    exact extAt_session W cA oracles p.sMT side.b₀ _ _ _ wires.oka.base drawFits.s
  have acceptT := accept_of_yes p.sMT p.sFS Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    W.embE W.depthReqT _ _ _ _ _ _ _ oracles wires.oka.T wires.fewT.1 wires.fewT.2 wires.loc.1
        wires.coh.1 wires.fmt.1
    (le_of_eq_of_le wires.oka.base.extDepth.1 wires.oka.base.depthT) drawFits.T extT a.1 a.2 ha vT
  have acceptB := accept_of_yes p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
    W.embE W.depthReq _ _ _ _ _ _ _ oracles wires.oka.B wires.fewB.1 wires.fewB.2 wires.loc.2.2
        wires.coh.2.2
    wires.fmt.2.2 (le_of_eq_of_le wires.oka.base.extDepth.2.2 wires.oka.base.depthB) drawFits.B
        extB u.1 u.2 hu vB
  have plainsB := (vBA_yes_of_prove W cA r₀ p _ _ side.capB oracles wires.oka _ _ _ _ _
      wires.fewB.1 wires.fewB.2
    wires.loc.2.2 wires.coh.2.2 wires.fmt.2.2 drawFits.B extB u.1 u.2 hu).2.2.1
  refine ⟨_, _, _, _, _, _, ?_, hkey, hE, acceptT, acceptB, ?_⟩
  · rw [hlow, hpiT, det_linkO, h1, h2, h3]
    rfl
  · rw [← plainsB]
    exact hn

end Runs

end OnBytes.WholeKey

#print axioms OnBytes.Prover.accept_back
#print axioms OnBytes.Prover.accept_of_yes
#print axioms OnBytes.WholeKey.shown_some
#print axioms OnBytes.WholeKey.pack_of_ok
#print axioms OnBytes.WholeKey.parts_of_VRA
#print axioms OnBytes.WholeKey.ends_of_yes
