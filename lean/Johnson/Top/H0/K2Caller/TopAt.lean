-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TopAt.lean: THE CODE SWITCH's LAW AT A PLACE, ASSEMBLED: the law of the code
    switch at a
seated block, in the form that the rule of composition asks (`Piece.GoodIn`), at any extractor, with
every letter that can be made, made, and ONE condition in front. Words: «the verifier's state» is
what a block reads and hands on (the type `Rec`); r : `SwRow` is a Lean structure: the typed entry
of a written table for the place; a stored sample row holds an out-of-domain (OOD) sample's form and
answer.

Main names:
  `inXTop`, `strsTop`: the typed statement and the typed strings in front BY MAKE: the two halves of
    `faAt` (CarryK2.lean), at the front that the text makes of the verifier's state and at that
    front's own frame. `lawFa_top`: at a front with a frame the law's reading IS `faAt`: one text
    for the law and for the table of joints' sentence «carry».
  `Pub12`: the twelve public clauses of `FrontAtL` (Johnson/Top/H0/K2Hands/TieLight.lean), as one
    structure.
  `frontOnL_top`: `FrontOnL` at the made readings, from `Pub12` and the clause on the held samples:
    the clauses on the open word's string (`strIs_made`), the carried claim's target and its vector
    hold by the make.
  `OnTop`: THE ONE CONDITION IN FRONT: at the front: `Pub12` at the place's frame W₀ · each held
    sample is a stored sample row, read · the number of messages is n0 · the sending's notices are
    the typed list; and `KeptFree` (PlainGood.lean).
  `k02_good_top`: the assembly: by `k2_good_plain_any` (GoodAny.lean), `lawAfter_light`
    (AfterMade.lean) and `frontOnL_top`. WHAT IS LEFT, each by name: r.ok · r.writtenOK · r.sizedB
    (three tests with code on r) · `P2At` · two written rounds with the block's declared entries and
    kinds · the kind's test on the plan · each new member's tree is one that the first written round
    sends · `CallerAt` at W₀ and the readings memK, rowK, plK W₀ · `KeysFit` · B declares the kind's
    rounds and sits on the kind's block behind the door · `DoorKeeps`. LETTERS THAT STAY: iJ, iQ ·
    smp (the held samples off the stored sample rows) · W₀, n0, aOf, iOf · which tree and tenant
    holds a member, G, base · wtOf · three defaults that are read nowhere under the condition.
Limits. A SENTENCE WITH PREMISES: none is shown here; by other files' theorems each has a payer or a
file that is to pay it. `OnTop` is a promise on the verifier's state and the oracles: who makes
it true along the chain is not said. R' asks what stands behind at EVERY statement with `OnTop`: the
    condition pins the three numbers that it reads of a front: the number of messages, the group,
    that group's number of rows. Whether R
under «there is» is enough for the table's tie in front: GoodAny.lean's limit. No member. It is no
soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.AfterMade
import Johnson.Top.H0.K2Caller.GoodAny
import Johnson.Top.H0.K2Caller.CarryK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Y : Type} (p : K2.P2) (orc : Y → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str)

/-- **The typed statement in front BY MAKE, off the verifier's state**: the first half of `faAt`
(CarryK2.lean) at the front that the text makes of the state and at that front's own frame; a
letter's value where there is none. -/
noncomputable def inXTop (y₀ : Y) (t : Rec) : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ
    iQ).sw).X :=
  match K2.frontAt p t with
  | some fx =>
    match K2.frameAt fx with
    | some W => (faAt r H p orc smp (t, fx, W) y₀).1
    | none => d₀.1
  | none => d₀.1

/-- **The typed strings in front BY MAKE, off the verifier's state and the oracles**: the second
    half. -/
noncomputable def strsTop (a : Rec × Y) : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ
    iQ).sw).Ex.Str :=
  match K2.frontAt p a.1 with
  | some fx =>
    match K2.frameAt fx with
    | some W => (faAt r H p orc smp (a.1, fx, W) a.2).2
    | none => d₀.2
  | none => d₀.2

variable {p}

/-- At a front with a frame the law's reading IS the table's: one text for both. -/
theorem lawFa_top (y₀ : Y) (a : Rec × Y) {fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    (h1 : K2.frontAt p a.1 = some fx) (h2 : K2.frameAt fx = some W₀) :
    lawFa (Letters.plain r H) iJ iQ (strsTop iJ iQ p orc smp d₀) (inXTop iJ iQ p orc smp d₀ y₀) a =
      faAt r H p orc smp (a.1, fx, W₀) a.2 := by
  show (inXTop iJ iQ p orc smp d₀ y₀ a.1, strsTop iJ iQ p orc smp d₀ a) = _
  unfold inXTop strsTop
  simp only [h1, h2]
  rfl

/-- FrontAtL's twelve public clauses, as one structure. -/
structure Pub12 (W₀ : SwitchFrame) (fx : _root_.Tw.K2.Front) : Prop where
  frameIs : K2.frameAt fx = some W₀
  z32 : W₀.zk.logN ≤ 32
  twoOld : ∀ (a a' : ℕ) (k k' : KeptPlace), W₀.kept[a]? = some k → W₀.kept[a']? = some k' →
    k.old = k'.old → a = a'
  codes : fx.st.codes = r.cs
  keptPos : K2.KeptPos fx.T
  keptRows : fx.f.rows.keptRows = (W₀.kept.map (·.rows)).sum
  ell : ∀ (a : ℕ) (k : KeptPlace), W₀.kept[a]? = some k →
    (fx.st.codes.base.getD (fx.st.oracles.getD k.old default).shape.code default).ell = W₀.code.ell
  first : ∃ g0 : 0 < r.l.length, (r.l.get ⟨0, g0⟩).1 = fx.T.shape
  next : ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < r.l.length,
    (r.l.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape
  mainVars : ∀ v ∈ fx.f.rows.c.tensors, v.vars = W₀.code.logEll
  d0 : (fx.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell
  d1 : (fx.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell

set_option maxHeartbeats 1000000 in
/-- **`FrontOnL` AT THE MADE READINGS**: from the twelve public clauses and the clause on the held
samples; the clauses on the open word's string, the carried claim's target and its vector hold by
    the
make. -/
theorem frontOnL_top (y₀ : Y) (W₀ : SwitchFrame)
    (aOf : (selLoc (Letters.plain r H) iJ iQ).hd.K → ℕ)
    (iOf : ∀ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S → ℕ) (on : Rec × Y → Prop)
    (h12 : ∀ a, on a → ∀ fx, K2.frontAt p a.1 = some fx → Pub12 (r := r) W₀ fx)
    (hS : ∀ a, on a → ∀ fx, K2.frontAt p a.1 = some fx →
      ∀ ks : Σ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S, ∃ (k : KeptPlace) (sm :
          OnBytes.Row),
        W₀.kept[aOf ks.1]? = some k ∧ (samplesOf fx.st k)[iOf ks.1 ks.2]? = some sm ∧
          (smp fx W₀ ks.1).2 ks.2 = readE sm.target ∧
          pushTo ((selLoc (Letters.plain r H) iJ iQ).hd.sJ ks.1)
              (((selLoc (Letters.plain r H) iJ iQ).hd.o ks.1).Z.mat (smp fx W₀ ks.1).1 ks.2) =
            slotVec (selR (Letters.plain r H)).s (selR (Letters.plain r H)).Kp memK rowK (aOf ks.1)
                k.rowBits (formOn sm))
    (a : Rec × Y) (ha : on a) :
    FrontOnL (selR (Letters.plain r H)) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
        (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
        (Letters.plain r H).Z
      (Letters.plain r H).A₀ r.cs r.l iJ iQ (baseCount r.set .request r.g) (Letters.plain r H).w₀
      (portCode r.cs r.rider) p (strsTop iJ iQ p orc smp d₀) (inXTop iJ iQ p orc smp d₀ y₀)
      (fun a => orc a.2) W₀ memK rowK (plK W₀) aOf iOf a := by
  intro fx hfx
  have P := h12 a ha fx hfx
  have e := lawFa_top iJ iQ orc smp d₀ y₀ a hfx P.frameIs
  have e1 : inXTop iJ iQ p orc smp d₀ y₀ a.1 = (faAt r H p orc smp (a.1, fx, W₀) a.2).1 :=
    congrArg Prod.fst e
  have e2 : strsTop iJ iQ p orc smp d₀ a = (faAt r H p orc smp (a.1, fx, W₀) a.2).2 :=
    congrArg Prod.snd e
  rw [e1, e2]
  exact ⟨P.frameIs, P.z32, P.twoOld, P.codes, P.keptPos, P.keptRows, P.ell, P.first, P.next,
    P.mainVars, P.d0, P.d1,
    strIs_made (selR (Letters.plain r H)) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
        (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
        (Letters.plain r H).Z
      (Letters.plain r H).A₀ r.cs r.l iJ iQ (baseCount r.set .request r.g) (Letters.plain r H).w₀
      p a.1 fx (orc a.2) _, rfl, rfl, hS a ha fx hfx⟩

end

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (p : K2.P2) (orc : F.E.Str → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)

/-- **THE ONE CONDITION IN FRONT**, of the verifier's state and the oracles in front of the switch:
    at
the front that the text makes of the state: the twelve public clauses at the place's frame W₀ · each
held sample is a stored sample row, read · the number of messages is n0 · the sending's notices are
the typed list · the front's group is grp and has rows rows; and no kept slot of the open word has a
    collision at its stored sample's seed. -/
def OnTop (W₀ : SwitchFrame) (n0 grp rows : ℕ) (aOf : (selLoc (Letters.plain r H) iJ iQ).hd.K → ℕ)
    (iOf : ∀ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S → ℕ) (a : Rec × F.E.Str) : Prop :=
  (∀ fx, K2.frontAt p a.1 = some fx → Pub12 (r := r) W₀ fx ∧
    (∀ ks : Σ k, ((selLoc (Letters.plain r H) iJ iQ).hd.o k).Z.S, ∃ (k : KeptPlace) (sm :
        OnBytes.Row),
      W₀.kept[aOf ks.1]? = some k ∧ (samplesOf fx.st k)[iOf ks.1 ks.2]? = some sm ∧
        (smp fx W₀ ks.1).2 ks.2 = readE sm.target ∧
        pushTo ((selLoc (Letters.plain r H) iJ iQ).hd.sJ ks.1)
            (((selLoc (Letters.plain r H) iJ iQ).hd.o ks.1).Z.mat (smp fx W₀ ks.1).1 ks.2) =
          slotVec (selR (Letters.plain r H)).s (selR (Letters.plain r H)).Kp memK rowK (aOf ks.1)
              k.rowBits (formOn sm)) ∧
    fx.st.oracles.size = n0 ∧ Tied r.l (switchNotices fx.T fx.others) ∧
    fx.f.group = grp ∧ ∃ G, fx.st.groups[grp]? = some G ∧ G.rows.size = rows) ∧
  KeptFree iJ iQ (strsTop iJ iQ p orc smp d₀) (inXTop iJ iQ p orc smp d₀ y₀) a

end

set_option maxHeartbeats 4000000 in
/-- **THE CODE SWITCH's LAW AT A PLACE, ASSEMBLED**: the law of the code switch at a seated block,
    in the form
    that
the rule of composition asks, at any extractor, with every letter that can be made, made, and one
condition in front. -/
theorem k02_good_top {W' Cl Cl₀ Cl₁ Xi : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (hz : r.sizedB = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (p : K2.P2)
    (hp : P2At r p) (he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry))
    (hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind)
    (hpl : (K2.codeSwitchKind (Cl := Cl₁) p).planOk = true)
    (hseat : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r (r.ok_says h))).held.Smp)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (W₀ : SwitchFrame) (n0 grp rows : ℕ) (aOf : (selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.K
        → ℕ)
    (iOf : ∀ k, ((selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.o k).Z.S → ℕ)
    (C : CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK rowK (plK W₀) W₀)
    (hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ
        iQ G seat base d₁ F) p base
      idExt)
    (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ p leave
      (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G
          seat)
        (fun _ => ((), ()))))
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).tgt.W) :
    (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
        seat base d₁ F) p base
      idExt) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧
        OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp
            d₀ y₀ W₀ n0 grp rows aOf iOf (t, a.2))
      (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ
          iQ n0 b₀ (fun _ i => isEmptyElim i)
        (strMadeB iJ iQ G seat) (fun _ => ((), ())) b))
      (fun a _ => ∀ t, enter a.1 = .ok t →
        ∃ u, ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
            (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
                (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp d₀)
              (inXTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
                  y) smp d₀ y₀) (t, a.2)) u)
      (fun b w => ∀ a, OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base
          [d₁, d₂]) y) smp d₀ y₀ W₀ n0 grp rows aOf iOf a →
        lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a
          (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i)
              (strMadeB iJ iQ G seat)
            (fun _ => ((), ())) b) (wtOf b w)) :=
  k2_good_plain_any h hW iJ iQ G seat base d₁ d₂ (k2Wr_of hp he hk) p hseat _ _ _
    (fun _ ha => ha.2)
    (lawAfter_light (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p
        base idExt _ _
      (k2Wr_of hp he hk) hp hpl hz W₀ memK rowK (plK W₀) aOf iOf _ C
      (frontOnL_top iJ iQ (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
          smp d₀ y₀ W₀ aOf iOf _
        (fun _ ha fx hfx => (ha.1 fx hfx).1) (fun _ ha fx hfx => (ha.1 fx hfx).2.1)) hkeys)
    n0 b₀ (fun _ ha fx hfx => ⟨(ha.1 fx hfx).1.codes, (ha.1 fx hfx).2.2.1, (ha.1 fx hfx).2.2.2.1⟩)
    B enter leave hr hs hD ext' wtOf

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_good_top
#print axioms VerifiableInference.Desc.First.K2Caller.frontOnL_top
#print axioms VerifiableInference.Desc.First.K2Caller.lawFa_top
