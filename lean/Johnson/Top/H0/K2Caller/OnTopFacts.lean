-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/OnTopFacts.lean: the code switch: THE JOIN OF FILES FOR THE
LAW's CONDITION IN FRONT AND ITS PREMISE ON THE CALLER: so that `k02_good_fam` (TopFam.lean) is
called with tests with code, one invariant and one promise.

Main names:
  `Renumbered W W₀`: W₀ is the written frame W with other numbers of messages: the family of a
    place's frames.
  `keptAt_renumber`, `keptBits_renumber`: two tests by place feel no renumbering.
  `iJW`, `iQW`: the two maps of names, made off the written frame.
  `caller_fam`: `CallerAt` at every frame of the family, at the law's own three readings memK, rowK,
    plK W₀: from three tests with code at the written frame (`callerAt_renumbered_idx`, `plRe_idx`:
    Johnson/Top/H0/K2Hands/CallerIdx.lean).
  `onTop_of_tests`: `OnTop` (TopAt.lean) at some frame of the family, with the held OOD samples made
    off the stored sample rows: from six closed facts at a written front and its frame · at the
    front that the text makes of the verifier's state: there are numbers of the kept old messages,
    none twice, at which `frontB2` accepts; the notices are the typed list; the invariant
    `SampleGoodS`; the test `storedB` · `KeptFree`. By `pub12_of_twelve`, `nums_of_twelve`
    (PubOfTwelve.lean) and `onTop_samples` (Johnson/G/SwitchFrontOnTop.lean).
Limits. Who makes the facts on the front true along the chain is not said. `SampleGoodS` and
`KeptFree` have no code. No member. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.TopFam
import Johnson.Top.H0.K2Caller.PubOfTwelve
import Johnson.Top.H0.K2Hands.CallerIdx
import Johnson.G.SwitchFrontOnTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB onTop_samples)
open _root_.Tw.K2 (switchNotices)

/-- The frames of a place's family: a written frame with other numbers of messages. -/
def Renumbered (W W₀ : SwitchFrame) : Prop := ∃ g olds anew, W₀ = renumber W g olds anew

theorem keptAt_renumber (r : SwRow) (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ) :
    r.keptAt (renumber W g olds anew) = r.keptAt W := by
  unfold SwRow.keptAt
  rw [renumber_rows]

theorem keptBits_renumber (r : SwRow) (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ) :
    keptBitsB r (renumber W g olds anew) = keptBitsB r W := by
  have e : (renumber W g olds anew).kept.map (·.rowBits) = W.kept.map (·.rowBits) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map, List.getElem?_map, renumber_kept]
    cases W.kept[i]? <;> rfl
  unfold keptBitsB
  rw [e]

section
variable {r : SwRow} (H : r.OK) {W : SwitchFrame} (hk : r.keptAt W = true)
  (hc : codesAt r W = true) (hf : fitAt r W = true)

/-- The map of names of the rows' entries, off the written frame. -/
noncomputable abbrev iJW : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain
    r H).oZ).keep r.kp).Sh.Cf.J →
    (sigOf r.cs r.l).Ent :=
  Johnson.Top.H.iJ (stageOf r.g (Letters.plain r H).t₀) W (memI H (Letters.plain r H).t₀
      (Letters.plain r H).oM (Letters.plain r H).oZ)
    (rowI H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ) (plI H
        (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ W) r.cs r.l
    (fit_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ hf).nameJ

/-- The map of names of the positions' entries, off the written frame. -/
noncomputable abbrev iQW : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain
    r H).oZ).keep r.kp).Sh.Cf.Q →
    (sigOf r.cs r.l).Ent :=
  Johnson.Top.H.iQ (stageOf r.g (Letters.plain r H).t₀) W (memI H (Letters.plain r H).t₀
      (Letters.plain r H).oM (Letters.plain r H).oZ)
    (rowI H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ) r.cs r.l
    (fit_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ hf).nameQ

include hc in
/-- **`CallerAt` AT EVERY FRAME OF THE FAMILY, AT THE LAW's OWN THREE READINGS**: three tests with
code at the written frame. -/
theorem caller_fam (W₀ : SwitchFrame) (hW : Renumbered W W₀) :
    CallerAt (selR (Letters.plain r H)) r.cs r.l (iJW H hk hf) (iQW H hk hf) memK rowK (plK W₀) W₀
        := by
  obtain ⟨g, olds, anew, rfl⟩ := hW
  have C := callerAt_renumbered_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM
      (Letters.plain r H).oZ hc hf g olds anew
  rw [plRe_idx H hk (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ g olds
      anew] at C
  exact C

end

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (p : K2.P2) (orc : F.E.Str → ℕ → ℕ → List UInt64)
  (x₀ : (vecD (plainD r H)).held.Smp)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)

/-- **THE CONDITION IN FRONT AT SOME FRAME OF THE FAMILY**, from: six closed facts at a written
    front f₀
and its frame W · at the front that the text makes of the verifier's state: there are numbers olds
of the kept old messages, none twice, at which the test `frontB2` accepts; the notices are the typed
list; the invariant on stored sample rows; the test `storedB` · no collision at the kept slots. -/
theorem onTop_of_tests (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 grp rows : ℕ)
    (h0 : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true) (hk : r.keptAt W = true)
    (hb : keptBitsB r W = true) (hs : keptShapeB r = true) (a : Rec × F.E.Str)
    (hf : ∀ fx, K2.frontAt p a.1 = some fx → ∃ olds : List ℕ, olds.Nodup ∧
      frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
      K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true)
    (hfree : KeptFree iJ iQ (strsTop iJ iQ p orc (smpTop r H iJ iQ (baseCount r.set .request r.g)
        x₀) d₀)
      (inXTop iJ iQ p orc (smpTop r H iJ iQ (baseCount r.set .request r.g) x₀) d₀ y₀) a) :
    ∃ W₀, Renumbered W W₀ ∧
      OnTop iJ iQ p orc (smpTop r H iJ iQ (baseCount r.set .request r.g) x₀) d₀ y₀ W₀ n0 grp rows
          (aOfK r H)
        (fun _ _ => 0) a := by
  cases hfx : K2.frontAt p a.1 with
  | none =>
    exact ⟨renumber W 0 #[] #[], ⟨0, #[], #[], rfl⟩,
      ⟨fun fx h => absurd (hfx.symm.trans h) (by simp), hfree⟩⟩
  | some fx =>
    obtain ⟨olds, hn, hB, hT, hG, hS⟩ := hf fx hfx
    refine ⟨placeFrame W n0 olds, ⟨_, _, _, rfl⟩, ?_⟩
    refine onTop_samples iJ iQ x₀ d₀ p orc y₀ (placeFrame W n0 olds) n0 grp rows a ?_ hfree
      ((keptAt_renumber r W _ _ _).trans hk) ((keptBits_renumber r W _ _ _).trans hb) hs
    intro fx' hfx'
    have e : fx' = fx := Option.some.inj (hfx'.symm.trans hfx)
    subst e
    obtain ⟨n1, n2, n3⟩ := nums_of_twelve h0 hcs hpub hn hT hB
    exact ⟨pub12_of_twelve h0 hcs hpub hn hT hB, hG, hS, n1, hT, n2, n3⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.caller_fam
#print axioms VerifiableInference.Desc.First.K2Caller.onTop_of_tests
