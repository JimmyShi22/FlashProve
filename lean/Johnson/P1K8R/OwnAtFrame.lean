-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/OwnAtFrame.lean: THE HONEST SIDE's FRAME, AT THE TWELVE LAYERS' SEGMENTS: AT THE
STATES THAT ITS FIELD hP' HANDS IN FRONT OF THE BATCHING: WHAT THE SEGMENT's OWN KIND's SUB-PROTOCOL
RETURNED HOLDS, AS HEARD BY THE LOOKUP ON THE CALLS, A POINT zx NO COORDINATE OF WHICH IS 0 OR 1:
FROM THE SILENCE OF THAT LOOKUP's SECOND MARK. UNDER THE DESCRIPTION's HEAD. A lemma; NONE OF THE
LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.
Why. At a layers' segment the tables of reads on which `readsLive`
(Johnson/Desc/K8/Honest/LinkedFew.lean) hangs are made at that return's field H.fo, not at the
state's own field of what the lookup heard.

  **`ownFine_handed`**   `calls_handed` (Johnson/P1K8R/ZxAtFrame.lean); `own_behind_calls`
      (OwnBetween.lean)
Limits. The head h is a hypothesis; the full size alone. That the walk returns, that its start obeys
the frame's law, that the lists named are among the marks asked and that these have been silent are
premises. IT SAYS NOTHING OF `readsLive` ITSELF. It is not laid into a member of `FirstAsks` here.
It stands over the files of the kind "lookup" on the honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.ZxAtFrame
import Johnson.P1K8R.OwnBetween

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W Y : Type}
include h

/-- **AT THE TWELVE LAYERS' SEGMENTS, AT THE STATES THAT THE FRAME's FIELD hP' HANDS IN FRONT OF THE
BATCHING: NO COORDINATE OF THE POINT zx OF WHAT THE SEGMENT's OWN KIND's RETURN HOLDS AS HEARD BY
THE LOOKUP ON THE CALLS IS 0 OR 1.** The premises of `zx_handed` (Johnson/P1K8R/ZxAtFrame.lean) at l
= 2 g. The end stands unfolded, in the form of a premise that another author's files on `readsLive`
at the layers' segments ask under the name OwnFine, and
this file does not import them. -/
theorem ownFine_handed (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∀ o, s'.own? = some o →
      ∀ w ∈ o.H.fo.zx.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  have n24 : ¬ 2 * g = 24 := by omega
  have hA' : A.length = 14 * (2 * g) + (if 2 * g = 24 then 11 else 9) := by
    rw [hA, if_neg n24]
  obtain ⟨-, -, -, -, blk, sj, sk, R, c, r₂, r₃, c₂, c₃, gH, hblk, g3, hr1, hgH, hfine, -,
    hfold⟩ := calls_handed h G₀ (by omega : 2 * g < 25) ms hsub hall hfit hA' hpos L hft hm ha hn
      hq hz hv
  have hb : borderOf (2 * g) false = 14 * (2 * g) + 3 := by
    rw [border_calls, if_neg n24]
  rw [hb] at hblk hr1 hfold
  rw [hA] at hfold
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨o, ho, e⟩ := own_behind_calls h.scope h.reads O h.laid.planOk hg hblk g3 hr1 hgH hfold
  intro o' ho' w hw
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  rw [e] at hw
  exact hfine w hw

end

end P1K8

#print axioms P1K8.ownFine_handed
