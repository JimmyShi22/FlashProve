-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsFull.lean: AT EACH SEATED BLOCK OF K10 IN THE FIRST CHAIN OF THE PROOF FILE's DESCRIPTION, AT THE FULL SIZE: K10's LAW AT THE WRITTEN GROUP OF THE LINK OF THE SAME NUMBER. A
definition, statements and proofs.
  K10FullLawAt lo hlo gs hgs kb b Q   k10_full_any_lay's statement (Johnson/Desc/First/Close/Law/K10FullAny.lean) behind its premises on b and on gs.k, all other letters bound: at R := groupFullLayK lo hlo gs hgs kb.
  k10FullLawAt_of   it holds of every b that is LaidAlone .. (K9.closing Q).retype .. at an address that is not K7's, where gs.k = kLay lo kb.
  links_mem         [kernel] the written list number l, l < 25, is a member of the written lists.
  k10_law_sits_full in scope: at EVERY block b of c.blocksInOrder whose place is of the kind K10: there are l < 25, p, Q (the lot's own numbers), gs in frontFull with gs.k = kLay AND gs.slots = 2 ^ ceilLog2 (1 + the kept rows) (so gs IS PINNED: RealAt's fourth clause: there is just one such; k alone repeats in frontFull) at the l-th written list and the flags
                    kbAt shapeFull l (realAt_group at Law/ReqKept.lean's real_full), c.blocksInOrder[14 l + n + 5]? = some b, and K10FullLawAt at these.
WHAT IS PAID AGAINST K10LawAt (SitsLaw.lean): the law's premises on the typed group's numbers: it fits; the radius is Johnson's; the counts; the two written places' prices; the pull; the fixed coefficient; the
group's data are in order at the program's own layout. So that "for all" has a member of these premises.
LIMITS. (1) THE PAIRING IS BY THE NUMBER l ALONE: l numbers the description's links (the driver's row of sorts) AND the written lists and the written shape's links: that the description's link l is the request's
link l is not shown; what holds the written records together link by link is RealAt (ReqKept.lean), among written records. (2) NOTHING TIES Q's NUMBERS TO gs's: Q.k | Q.h are read by the lot off the first
state's frame; gs is frontFull's written group. In the law the tie is asked IN THE PROMISE: K10OnS's
first two clauses (the record's k and h are the typed stage's): of no statement is that shown.
(3) Left as premises:
n's bound and that the three rounds' data are the format's own (hn57 · iB · iE · iR); left as letters: the names of the slots, the numbering, pS, fa, the kept messages' joint, base, ext, err. (4) "The flags" are
those that joinersAt makes of the written shape, which is the planner's by a run. (5) The full size alone. All limits of SitsLaw.lean, SitsAll.lean, Sits.lean. Nothing on soundness of the protocol.

-/
import Johnson.LPFK10R.SitsLaw
import Johnson.Desc.First.Close.Law.K10FullAny
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

/-- **K10's law at a block b, at the written group**: `k10_full_any_lay`'s statement behind its premises
on b and on gs.k, all other letters bound. -/
def K10FullLawAt (b : Block VerifiableInference.Desc.First.S ProofFile.Cl) (Q : Par) : Prop :=
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
      err).ior.red.Leads (K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull
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

theorem k10FullLawAt_of {same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool}
    {b : Block VerifiableInference.Desc.First.S ProofFile.Cl} {Q : Par} {name : String} {a₀ : Place}
    (hL : LaidAlone same b
      (VerifiableInference.Desc.K9.closing Q : Block VerifiableInference.Desc.First.S Unit).retype name a₀)
    (hk7 : a₀.kind ≠ KindName.K7) (hk : gs.k = kLay lo kb) :
    K10FullLawAt lo hlo gs hgs kb b Q := by
  intro N keep _ B _ n num Kc St₀ Wp E₀ A₀ w₀ w₁
    L dB dE dR ρ hρ pS W F base ext err fa na nb iE iR hn57 iB
  exact
    k10_full_any_lay lo hlo gs hgs kb hk N keep n num A₀ w₀ w₁ L dB dE dR ρ hρ pS Q b (fun s rs gs'
      s' h => (LPFK10.seated_yes hL hk7 s s' rs gs' h).1) base ext err fa iE iR hn57 iB

end

end VerifiableInference.Desc.First.Close

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par K10FullLawAt k10FullLawAt_of kbAt kLay keptRows RealAt
  real_full closingsOf)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit frontFull dryProofFull)
open ProofFile (Cl)
open IM

set_option maxRecDepth 100000 in
/-- The written list of each of the 25 links is a member of the written lists. -/
theorem links_mem : ∀ l, l < 25 → linksFullLit.getD l [] ∈ linksFullLit := by
  decide +kernel

/-- `RealAt.group` (Law/ReqKept.lean) WITH THE SLOTS: the group in front has the layout's k AND the slots
2 ^ ceilLog2 (1 + the kept rows): by `RealAt`'s fourth clause there is just one such. -/
theorem realAt_group {s : OnBytes.Params.ReqShape}
    {links : List (List (OnBytes.OracleShape × ℕ))} {front : List OnBytes.Params.GroupSize}
    {closings : List (ℕ × Option ℕ)} {l : Nat} (h : RealAt s links front closings l) :
    ∃ gs ∈ front, gs.k = kLay (links.getD l []) (kbAt s l (links.getD l [])) ∧
      gs.slots = 2 ^ OnBytes.ceilLog2 (keptRows (links.getD l []) (kbAt s l (links.getD l [])) + 1) := by
  obtain ⟨-, -, -, h4⟩ := h
  obtain ⟨g, hg⟩ := List.length_eq_one_iff.1 h4
  have hm : g ∈ front.filter fun g => g.k == kLay (links.getD l []) (kbAt s l (links.getD l [])) &&
      g.slots == 2 ^ OnBytes.ceilLog2
        (keptRows (links.getD l []) (kbAt s l (links.getD l [])) + 1) := by
    rw [hg]
    exact List.mem_singleton.2 rfl
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hm
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨g, h1, h2.1, h2.2⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **AT EACH SEATED BLOCK OF K10, THE LAW AT THE WRITTEN GROUP OF ITS OWN LINK**: in scope, at every
block b of c.blocksInOrder whose place is of the kind K10: with l its link: at the l-th written list of
messages, the flags that the program's two rules give at the written request's shape, and a group in
front that has the layout's k there: K10's law holds at the piece of b, with the premises on THE TYPED
GROUP's numbers paid. THE NUMBER l PAIRS THE DESCRIPTION's LINK WITH THE WRITTEN LIST BY ORDER ALONE, and
nothing here ties Q's numbers to gs's: see the head. -/
theorem k10_law_sits_full (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l, ∃ hl : l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (gs : OnBytes.Params.GroupSize)
        (hgs : gs ∈ frontFull),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        c.blocksInOrder[ixK10 l]? = some b ∧
        gs.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) ∧
        gs.slots = 2 ^ OnBytes.ceilLog2
          (keptRows (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) + 1) ∧
        K10FullLawAt (linksFullLit.getD l []) (links_mem l hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l [])) b Q := by
  intro b hb hk
  obtain ⟨l, hl, Lk, p, Q, -, h2, h3, -, h5, h6⟩ := k10_sits_each hS hR O b hb hk
  obtain ⟨gs, hgs, hgk, hsl⟩ := realAt_group (real_full l hl)
  exact ⟨l, hl, p, Q, gs, hgs, h2, h3, h5, hgk, hsl,
    k10FullLawAt_of _ (links_mem l hl) gs hgs _ h6 (by simp) hgk⟩

end LPFK10

#print axioms VerifiableInference.Desc.First.Close.k10FullLawAt_of
#print axioms LPFK10.links_mem
#print axioms LPFK10.realAt_group
#print axioms LPFK10.k10_law_sits_full
