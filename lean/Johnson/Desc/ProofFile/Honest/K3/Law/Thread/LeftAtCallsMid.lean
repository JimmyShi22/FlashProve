-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LeftAtCallsMid.lean: at a lookup on the calls of a
group's layers, the hypothesis `hM` of `left_at_layers_head`
(Honest/K3/Law/Thread/LeftAtCalls.lean): the specification's relation `Data.Mid` at the site's data:
follows from named hypotheses on the public part, the trace and the input's two readers.
Conditional. Theorems; no definition. `hM` is exchanged, not shown: nine named hypotheses stand in
the stead of one.

Terms. Honest/K3/GLOSSARY.md ("site", "trace's bundles"). In this file: the site's data is
`siteData` (Honest/K3/Law/AtSite.lean); the seated filling is `tiedOwnSources`
(Honest/K3/WitOwner.lean).

It adds no argument of its own. It joins:
  `mid_of_meets` (Honest/K3/Law/MeetsMid.lean): `Data.Mid` out of `FoNums.ok` and `LookIn.Meets`;
  `ownG_meets` (Honest/K3/Law/WitOwnerFull.lean): `LookIn.Meets` of the seated filling's own term at
    a group's layers, at the trace's cells and the index's entries;
  `site_layers` (Honest/K3/Law/SiteShapes.lean): at such a site the plan's shape is X.y.fo, the
    site's lm is X.y.h.lmb, and the row is handed the layers' structure of the site's group;
  `sites_ok` (Honest/K3/FastLaw/Sites.lean): a site's shape passes `FoNums.ok`.

What is shown.
  `mid_at_layers`: **conditional: `Data.Mid` at the site's data**, at every public part, every input
    t and all challenges.
  `left_at_layers_head_mid`: **conditional: `left_at_layers_head` without `hM`**, the hypotheses of
    `mid_at_layers` in its stead, at the input m.st.input.

Hypotheses that come in the stead of `hM`, each by name: nine: four on the public part, three on the
trace, two on the input's readers.
  On the public part alone: `PlanLabels X` (Honest/K3/WitPlan.lean) · `PlanOwners X`
    (Honest/K3/Law/WitOwnerFull.lean) · `LookPub X` · `hg`: the site's group is below 12.
  On a trace T, an index i and an instance x₀ of the library's honest trace: `NamesFit X T` ·
    `MeetsAll X i x₀ T` · `PlanesLaid X i x₀ T` (OnBytes.HonestTrace).
  On the input's two readers: `hC`: the cells' reader yields at the input's trace the cells of T
    (`cellOf X T`) · `hW`: the weights' reader yields at the input's index the entries of i
    (`entryOf i`).
  `ShapeIsFs X s` (`hB`) was a hypothesis of `left_at_layers_head` already.
  By their letters: `B`, `O`, `Q` (`Qp` in the second theorem): `PlanLabels`, `PlanOwners`,
    `LookPub`; `N`, `M`, `L`: `NamesFit`, `MeetsAll`, `PlanesLaid`. The others (`hs` or `hsite`,
    `hd`, `hc`, `R`, `hb`, `hA`, `hdr`, `hSt`): as in LeftAtCalls.lean.

Which of the nine have a theorem that yields them, in files that this one does not import.
  `PlanLabels X`: from a test with code on the public part: `labelsOk_holds`
    (Honest/K3/Law/WitOwnerMember.lean [not in this library]); also `planLabels_of_marks`
    (Johnson/HonestTrace/PlanLabelsOfMarks.lean).
  `PlanOwners X`: from a test with code: `ownersOk_holds` (the same file of ours); also
    `planOwners_marks` (Honest/K3/Law/WitOwnerMarks.lean [not in this library]).
  `PlanesLaid X i x₀ T` at the library's own trace T := `theTrace X i x₀`: `planesLaid_theTrace`
    (Johnson/HonestTrace/FullPlanes.lean), from `PlanesIn X` and `LookPub X`.
  For `NamesFit`, `MeetsAll`, `LookPub` and `hg` this file names no such theorem.
  `hC` and `hW` say that the prover's input holds the library's honest trace and index: at a
    prover's own readers they have not been shown.

Imported. Honest/K3/Law/Thread/LeftAtCalls.lean; Honest/K3/Law/MeetsMid.lean;
Honest/K3/Law/WitOwnerFull.lean; Honest/K3/FastLaw/Sites.lean.


Limits. The layers' calls alone: attention's, the head's and the digits' sites are not treated. The
bundles on the trace speak of the full size (g < 12). No instance of these hypotheses is exhibited
in this file: no trace, index and input are laid at which hC and hW hold.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftAtCalls
import Johnson.Desc.ProofFile.Honest.K3.Law.MeetsMid
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Ends (jointKey)
open VerifiableInference.Desc (Block Chain OpenedColumn Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open OnBytes.HonestTrace (cellOf entryOf NamesFit LookPub MeetsAll PlanesLaid)
open Inst.Model (Instance ppref)

section
variable {W₀ Rc Xi Tr : Type} {i : Cm.Idx} {x₀ : Instance ppref} {T : OnBytes.HonestTrace.Tr}

/-- **Conditional: the specification's relation at the site's data, at a lookup on the calls of a
group's layers, at the seated filling.** No instance of these hypotheses is exhibited in this file.
-/
theorem mid_at_layers (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .layers) (hB : ShapeIsFs Z.p.X s) (cells : Tr → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat)
    (t : Local W₀ Rc Xi Tr) (B : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (Q : LookPub Z.p.X) (M : MeetsAll Z.p.X i x₀ T) (L : PlanesLaid Z.p.X i x₀ T)
    (hg : s.group < 12) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩) (hW : weights t.w₀ = ⟨entryOf i⟩)
    (heard ds : List Fmt.Drawn) :
    (siteData s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t) heard ds).Mid := by
  obtain ⟨e1, e2, e3⟩ := Spec.site_layers Z s hs hd hc
  have hsh : Z.p.X.y.fo = s.shape := by
    unfold ShapeIsFs at hB
    rw [e1] at hB
    exact Option.some.inj hB
  have hok : FoNums.ok s.shape = true := (FastLaw.sites_ok Z s hs).2
  have hm := ownG_meets B O N Q M L hg cells weights
    (fun y : Xi => headPub Z.p.X (req y).1 (req y).2)
  rw [hsh, ← e2] at hm
  rw [e3]
  show (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
    ((tiedOwnSources Z.p.X cells weights req).layers s.group (cells t.trace)
      (weights t.w₀)).hidden (ptsOf s.at_.face s.at_.base (heard ++ ds))).Mid
  rw [hC, hW]
  exact mid_of_meets _ s.shape s.p.lm s.p.first hok hm _

end

section
variable {Zl : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xP : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Zl Dw r Zp Np cF xP) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {W₀' Rc' Xi' Tr' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  {i : Cm.Idx} {x₀ : Instance ppref} {T : OnBytes.HonestTrace.Tr}

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **Conditional: `left_at_layers_head` without `hM`.** In its stead: `PlanLabels`, `PlanOwners`,
`NamesFit`, `LookPub`, `MeetsAll`, `PlanesLaid`, hg, hC, hW. At the full size alone. No instance of
these hypotheses is exhibited in this file. -/
theorem left_at_layers_head_mid (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : ProofFile.Inst → OnBytes.Model.Head.Covered × Array Nat) (src : Sources W₀' Xi' Tr')
    (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = false) (hc : s.caller = .layers)
    (hB : ShapeIsFs Zp.p.X s) (lot : Block TS ProofFile.Cl)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked
      (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s)))
    {blk : Block TS ProofFile.Cl} (hb : (LH).bs[borderOf s.link s.digits]? = some blk) {k : Coins Bk}
    {st st' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hA : Thr (LH).thread (borderOf s.link s.digits) k st m E)
    (hdr : drawsFit blk.rounds ds = true)
    (hSt : (LH).thread.Stepped blk k st m E ds y cols st')
    (B : PlanLabels Zp.p.X) (O : PlanOwners Zp.p.X) (N : NamesFit Zp.p.X T) (Qp : LookPub Zp.p.X)
    (M : MeetsAll Zp.p.X i x₀ T) (L : PlanesLaid Zp.p.X i x₀ T) (hg : s.group < 12)
    (hC : cells m.st.input.trace = ⟨cellOf Zp.p.X T⟩)
    (hW : weights m.st.input.w₀ = ⟨entryOf i⟩) :
    CallsLeft (LH).thread.chain k blk s ((fastFill (Rc := Rc') src).jobs s).asked
        (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s)) Zp.p.X.layers.y.fo st st' m
        ds ∧
      ∀ x, (siteData s (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s) m.st.input)
          m.st.heard ds).key x =
        jointKey Zp.p.X.layers.y.fo
          (keysG Zp.p.X (cells m.st.input.trace) (weights m.st.input.w₀) s.group)
          (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x :=
  left_at_layers_head h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w cells weights req src s hsite hd
    hc hB lot R hb hA hdr hSt
    (mid_at_layers Zp s hsite hd hc hB cells weights req m.st.input B O N Qp M L hg hC hW
      m.st.heard ds)

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.mid_at_layers
#print axioms ProofFile.Honest.K3.Law.AtThr.left_at_layers_head_mid
