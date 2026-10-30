-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/KeyFitsAtMg.lean: WHO PAYS THE FIELD SH OF `tables_fit` AT THE HEAD:
    **`AtMg.sh_of_start`**: hk (below) → ∀ p, h.rc p → 𝔏.Pm.shape 0 (start₂ p.1) = true: since the
    rider beside "reached" is "the public part is a typed instance's" (FourAtMg.lean),
    hK is no premise of the
tower. BENEATH: "THE KEY FITS AT EVERY TYPED INSTANCE".


  `AtMg.start₂_at`: at a typed instance the seated term's shared chain starts at `first` ‹the seat's
      codes› ‹the instance's key›: by unfolding.
  **`AtMg.kf_of_start`**: hK IS, AT ANY Pm, the fact
      "𝔏.Pm.shape 0 (first ‹the seat's codes› (instanceAsPlainRecord z).pub.key) = true, for all z" : a fact on ONE
      closed first state a typed key: no run, no prover.
    AT THE MEANT Pm (Sh.pm (planAt Z N G) O) that fact is, by reading, the
        lemma Sh.shape_start_at (Johnson/Desc/K14/Law/SharedConstStart.lean), under its test AtFull
        on the made sizes: NOT JOINED HERE: its cone is not in the build on which this was written.
  `AtMg.shape1_at`: "the key fits" at the seat's own parameters, from the head alone:
      `LPFD.Full.instOf_key_fits`; the index's three numbers out of PlanOk's named test on
      the shape (`full_index`).
  `AtMg.kf_met`: the case of a Pm whose word at border 0 is "the key fits and no message is noted" .
      THAT IS THE INNERMOST LAYER (pmZ) OF THE MEANT Pm ALONE: by Sh.shape_zero
      the whole Pm asks two
    tests more at border 0 (layX, X): so kf_met's premise hPm is not that Pm's text, and holds of it
        only
    if these two accept wherever the first two do: not shown, not expected (by
        reading): kf_met stays as a corollary; the road that counts is kf_of_start.
Limits. It exhibits neither an AtMg nor an 𝔏. Of an instance that is not instanceAsPlainRecord of a typed sample
    nothing is said. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FourAtMg
import Johnson.Desc.Laid.ProofInstFits
import Johnson.Desc.Sound.PointAtK14Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Inst.Model
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Chain)
open Desc.K14 (p14Of beforePointOf first)
open Desc.K14.Law (shape1 notedU full_index)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- At a typed instance the shared chain starts at the seat's codes and the instance's key. -/
theorem AtMg.start₂_at (_ : AtMg o Z D r Zp Np cF) (z : LPFD.Full.XF × RecFull) :
    (F0T o Zp Np cF).start₂ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) =
      first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key := rfl

/-- **THE NEW PREMISE IS A FACT ON THE SHARED CHAIN's FIRST STATE AT A TYPED INSTANCE's KEY**:
    whatever Pm is. -/
theorem AtMg.kf_of_start (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (hk : ∀ z : LPFD.Full.XF × RecFull, 𝔏.Pm.shape 0
      (first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true)
    (z : LPFD.Full.XF × RecFull) : h.kf 𝔏 ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) := by
  show 𝔏.Pm.shape 0 ((F0T o Zp Np cF).start₂ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) = true
  rw [h.start₂_at z]
  exact hk z

/-- **THE PAYER OF tables_fit's FIELD SH AT THE HEAD**: with h.rc in hand (the public part is a
    typed instance's) the shared chain's first state has the shape that the shared table asks at its
    first
border: from the one fact hk. -/
theorem AtMg.sh_of_start (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (hk : ∀ z : LPFD.Full.XF × RecFull, 𝔏.Pm.shape 0
      (first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true)
    (p : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (hp : h.rc p) :
    𝔏.Pm.shape 0 ((F0T o Zp Np cF).start₂ p.1) = true := by
  obtain ⟨-, z, e⟩ := hp
  rw [e]
  exact h.kf_of_start 𝔏 hk z

/-- "The key fits" at the seat's own parameters, from the head alone. -/
theorem AtMg.shape1_at (h : AtMg o Z D r Zp Np cF) (z : LPFD.Full.XF × RecFull) :
    shape1 (p14Of Zp.p.chains (beforePointOf Np)).par
      (first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true := by
  have e := full_index _ h.plan.shape
  exact LPFD.Full.instOf_key_fits z _ (by rw [e]; rfl) (by rw [e]) (by
    rw [e]
    exact (by decide +kernel :
      (⟨⟨32, 402653184, 44040191⟩, 11, 1, 0⟩ : OnBytes.Params.IndexShape).cubeBits = 29))

/-- The case of the INNERMOST layer of the meant Pm (its word at border 0: the key fits, no message
    is noted). NOT THE WHOLE MEANT Pm. -/
theorem AtMg.kf_met (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (hPm : ∀ s, 𝔏.Pm.shape 0 s =
      (shape1 (p14Of Zp.p.chains (beforePointOf Np)).par s && !notedU s))
    (z : LPFD.Full.XF × RecFull) : h.kf 𝔏 ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) :=
  h.kf_of_start 𝔏 (fun z => by rw [hPm, h.shape1_at z]; rfl) z

end P5J

#print axioms P5J.AtMg.start₂_at
#print axioms P5J.AtMg.kf_of_start
#print axioms P5J.AtMg.sh_of_start
#print axioms P5J.AtMg.shape1_at
#print axioms P5J.AtMg.kf_met
