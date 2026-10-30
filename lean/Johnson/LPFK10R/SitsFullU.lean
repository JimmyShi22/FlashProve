-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsFullU.lean: AT EACH SEATED BLOCK OF K10 IN THE FIRST CHAIN OF THE PROOF FILE's DESCRIPTION, AT THE FULL SIZE: K10's LAW WITH ITS TWO EQUATIONS READ OFF THE YES, AT THE WRITTEN GROUP OF THE
LINK OF THE SAME NUMBER; AND THE PLACE's k IS THE GROUP's. A definition, statements and proofs. SitsFull.lean (beside this file), by program, at the law k10_any_u (Johnson/Desc/First/Close/Law/KOfYes.lean).
  K10FullLawAtU lo hlo gs hgs kb b Q   k10_full_any_u_lay's statement (Law/K10FullAnyU.lean) behind its premises on b, on gs.k and hPr, all other letters bound: at R := groupFullLayK lo hlo gs hgs kb, AT THE PROMISE K10OnU.
  k10FullLawAtU_of    it holds of every b that is LaidAlone .. (K9.closing Q).retype .. at an address that is not K7's, where gs.k = kLay lo kb and Q.k is the typed stage's number of row variables.
  k10Par_kh           the lot's numbers of K10: Q.k and Q.h are those of the FIRST RECORD's frame's record of the group number p.link. k9At_link: K9's numbers at segment l bear that l.
  k10_law_sits_full_u in scope, UNDER hZ (at each l < 25 the first record's frame's group number l has the k of the program's own group number l of the written shape): at EVERY block b of c.blocksInOrder whose place is of the kind K10: l < 25, p, Q, gs in frontFull (pinned by k and slots) with
                      **Q.k = gs.k**, c.blocksInOrder[14 l + n + 5]? = some b, and K10FullLawAtU at these. Q.k = gs.k: k10Par_kh; hZ; RealAt's second clause (Law/ReqKept.lean: the layout's formula at the written list and flags gives
                      the k of the program's own group of the written shape: by the kernel at all 25); realAt_group.
WHAT TURNS AGAINST SitsFull.lean: the promise has no equation on the frame's record of the group (K10OnU); and its Limit (2) ("nothing ties Q's numbers to gs's") IS MET FOR k, under hZ.
LIMITS. (1) hZ IS A PREMISE, ON 25 NUMBERS: evaluated at the shipped public files of the full size by a run (no theorem): the written shape is the planner's by a run too;
that the first record's frame holds reqGroups of its own shape is the program's text: not drawn here. (2) Q.h is tied to nothing here: K10OnU asks the stage's h of the STATEMENT's layout. (3) THE PAIRING IS STILL BY THE NUMBER l: now through p.link = l and the
l-th group of the written shape. (4) All other limits of SitsFull.lean, KOfYes.lean, SitsLaw.lean, SitsAll.lean, Sits.lean. Nothing on soundness of the protocol.

-/
import Johnson.LPFK10R.SitsFull
import Johnson.Desc.First.Close.Law.K10FullAnyU
import Johnson.Desc.First.Close.Law.ReqKept

set_option autoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Place KindName)
open IM (LaidAlone)

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupFullLayK lo hlo gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))

/-- **K10's law at a block b, at the written group**: `k10_full_any_u_lay`'s statement behind its premises
on b and on gs.k, all other letters bound. -/
def K10FullLawAtU (b : Block VerifiableInference.Desc.First.S ProofFile.Cl) (Q : Par) : Prop :=
  ∀ (N : SlotNames RF) (keep : (SF).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
    (num : (RF).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ (((SF).sub
    ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num)).kp).Msg × Wp)) (w₀ : (SF).Wit ×
    Wp) (w₁ : LdBrW (RF).G ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num)).kp Wp) (L
    : List (BatFoldCaller GE)) (dB dE dR : RDT) (ρ : Rd ((RF).foldCaller keep (SbV RF B) (slV RF
    (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (wT dB) (wT dE)
    (wT dR)) (hρ : ρ = realRd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num)
    fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) dB dE dR (oneOf id) (oneOf id)) (pS : ∀ as
    : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE) {W : Type} {F
    : Frame} (base : ℕ) (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two)
    (dB :: dE :: List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n
    num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR)) → W → W) (err : Err (uLT (ckP
    .two) (dB :: dE :: List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV
    RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR))) (fa :
    VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src ((RF).foldCaller keep (SbV RF
    B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).X ×
    ((kBatFoldRide L).src ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
    (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).E.Str) {na nb : String} (iE : IsRd (toRD dE)
    (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb)) (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD
    dB) (Fmt.M2.rBatN n)),
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf
      RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext
      err).ior.red.Leads (K10OnU RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁ L pS Q fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE
      dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV
      RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2 τ = true
      ∧ closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Q) ((sView (ckP .two) (pieceOn
      (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF))
      (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2
      τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧
      ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK
      a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt RF N keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
        gs.k).bC (placeFull gs.k).bZ w₀ w₁ L (fa a) (rdBK a'.1).1.rows → (∃ m : (SF).Msg, ∀ i,
        (SF).decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m : (SF).Msg, (∀ i, (SF).decs (fa
        a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? =
        some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
        ∀ (r : (RF).G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j,
        rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList[i]
        j * ((RF).Sh.rho.up ((RF).G.msg m, r)).1 j = readE (runRows (rdK a.1).2.2
        G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).ds))

theorem k10FullLawAtU_of {same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool}
    {b : Block VerifiableInference.Desc.First.S ProofFile.Cl} {Q : Par} {name : String} {a₀ : Place}
    (hL : LaidAlone same b
      (VerifiableInference.Desc.K9.closing Q : Block VerifiableInference.Desc.First.S Unit).retype name a₀)
    (hk7 : a₀.kind ≠ KindName.K7) (hk : gs.k = kLay lo kb)
    (hPr : Q.k = (RF).s.h + (RF).s.g) :
    K10FullLawAtU lo hlo gs hgs kb b Q := by
  intro N keep _ B _ n num Kc St₀ Wp E₀ A₀ w₀ w₁
    L dB dE dR ρ hρ pS W F base ext err fa na nb iE iR hn57 iB
  exact
    k10_full_any_u_lay lo hlo gs hgs kb hk N keep n num A₀ w₀ w₁ L dB dE dR ρ hρ pS Q b (fun s rs gs'
      s' h => (LPFK10.seated_yes hL hk7 s s' rs gs' h).1) hPr base ext err fa iE iR hn57 iB

end

end VerifiableInference.Desc.First.Close

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par K10FullLawAtU k10FullLawAtU_of kbAt kLay keptRows RealAt
  real_full closingsOf)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit frontFull dryProofFull)
open ProofFile (Cl)
open IM

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- What the lot's numbers of K10 read of the first record: the frame's record of the group. -/
theorem k10Par_kh {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × ℕ)}
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} (h : ProofFile.k10Par Z xs p = some Q) :
    ∃ Gr, Z.s₀.check.frame.groups[p.link]? = some Gr ∧ Q.k = Gr.k ∧ Q.h = Gr.h := by
  unfold ProofFile.k10Par at h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Gr, hG, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact ⟨Gr, hG, rfl, rfl⟩
  · cases h

/-- K9's numbers at segment l bear that l. -/
theorem k9At_link {l : ℕ} {p : VerifiableInference.Desc.K9.Where} (h : k9At Z l = some p) :
    p.link = l := by
  unfold k9At ProofFile.k9Where at h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨d, _, h⟩ := Option.map_eq_some_iff.1 h
  rw [← h]

/-- **AT EACH SEATED BLOCK OF K10, THE LAW WITH ITS TWO EQUATIONS READ OFF THE YES, AT THE WRITTEN
GROUP OF THE LINK OF THE SAME NUMBER, AND THE PLACE's k TIED TO THE GROUP's**: as
`k10_law_sits_full` (SitsFull.lean), at the promise `K10OnU`; hPr (the lot's Q.k is the typed
stage's number of row variables) IS PAID, under hZ: at each l < 25 the first record's frame's group
number l has the k of the group number l that the program makes of the written request's shape. -/
theorem k10_law_sits_full_u (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hZ : ∀ l, l < 25 → (Z.s₀.check.frame.groups[l]?).map (·.k) =
      ((OnBytes.reqGroups shapeFull)[l]?).map (·.k)) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l, ∃ hl : l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par)
        (gs : OnBytes.Params.GroupSize) (hgs : gs ∈ frontFull),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        c.blocksInOrder[ixK10 l]? = some b ∧ Q.k = gs.k ∧
        gs.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) ∧
        gs.slots = 2 ^ OnBytes.ceilLog2
          (keptRows (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) + 1) ∧
        K10FullLawAtU (linksFullLit.getD l []) (links_mem l hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l [])) b Q := by
  intro b hb hk
  obtain ⟨l, hl, Lk, p, Q, -, h2, h3, -, h5, h6⟩ := k10_sits_each hS hR O b hb hk
  obtain ⟨gs, hgs, hgk, hsl⟩ := realAt_group (real_full l hl)
  obtain ⟨Gr, hGr, ek, -⟩ := k10Par_kh h3
  rw [k9At_link h2] at hGr
  have hz := hZ l hl
  rw [hGr, Option.map_some] at hz
  obtain ⟨Gw, hGw, ew⟩ := Option.map_eq_some_iff.1 hz.symm
  have e1 : ((OnBytes.reqGroups shapeFull).getD l {}).k = Gr.k := by
    rw [Array.getD_eq_getD_getElem?, hGw]
    exact ew
  have eQ : Q.k = gs.k := by
    rw [ek, ← e1, ← (real_full l hl).2.1, hgk]
  refine ⟨l, hl, p, Q, gs, hgs, h2, h3, h5, eQ, hgk, hsl,
    k10FullLawAtU_of _ (links_mem l hl) gs hgs _ h6 (by simp) hgk ?_⟩
  rw [eQ]
  have es := (VerifiableInference.Desc.First.Close.frontFull_place gs hgs).2
  show gs.k = (Johnson.Top.H.stageOf gs 219).h + (Johnson.Top.H.stageOf gs 219).g
  rw [← es]
  show gs.k = 0 + gs.k
  omega

end LPFK10

#print axioms VerifiableInference.Desc.First.Close.k10FullLawAtU_of
#print axioms LPFK10.k10Par_kh
#print axioms LPFK10.k10_law_sits_full_u
