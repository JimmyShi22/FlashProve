-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsO.lean: K01_law: THE FIELD inOrder OF FillL (Johnson/Desc/K1/Law/KeepAtLater.lean) («"in order" holds behind a later sending's accept»), AS A CALL, AT FillsK1 (Johnson/Desc/K1/Law/FillsK1.lean) IN THE FORM Mg.inOrder a = (io0 a && inOrderK13 …): the second conjunct rides by
inOrderK13AtLater (Johnson/Desc/K1/Law/InOrderAtLater.lean), where K1's own sub-protocol's test on the plan accepts (hPlan: in the top: from the description's own planOk); the first is left as ONE premise: «io0 rides» (hIo).
  ownL · laterOwn_blkL · roundsOwn_blkL · hOrder_of
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.K1.Law.InOrderAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (Mem MsgT linksFull)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Xi Cells Tok : Type}

/-- K1's own sub-protocol at (l, d). -/
def ownL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (arrs : Option (List ℕ)) : Block S Unit :=
  match d with
  | true => laterAt G.first (gpOf Z) l (k1Ix l true + 1) 2 arrs
  | false => laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs

theorem laterOwn_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : Later (blkL Z G l d X arrs) (ownL Z G l d arrs) := by
  cases d with
  | true => exact .digits _ _ _ _ _
  | false => exact .reads _ _ _ _ _ _

theorem roundsOwn_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : (blkL Z G l d X arrs).rounds = (ownL Z G l d arrs).rounds := by
  cases d with
  | true => rfl
  | false =>
    show (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs : Block S Unit).rounds ++
      (IM.k1Quiet G l X).rounds = _
    rw [rounds_k1Quiet, List.append_nil]
    rfl

section
variable {D : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf D.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {base : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP Mg : Meaning Pp (Wit Cells Tok MsgT)}

/-- **hOrder, to the binder's letter.** -/
theorem hOrder_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg) (N : Numbers)
    (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (hIo : ∀ x x', YesOf (blkL Z G₀ l d X arrs) x x' → io0 x = true → io0 x' = true)
    (hPlan : (ownL Z G₀ l d arrs).planOk = true) (x x' : Pp × S) (y : Strs)
    (hy : YesOf (blkL Z G₀ l d X arrs) x x')
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y) :
    Mg.inOrder x' = true := by
  have h0 : Mg.inOrder x = true := by
    obtain ⟨⟨_, hr⟩, hm⟩ := hIn
    rcases hr with hx | ⟨h1, _, _, _⟩
    · exact absurd hm hx
    · simp only [Bool.and_eq_true] at h1
      exact h1.1.1.2
  rw [h.inOrder] at h0 ⊢
  simp only [Bool.and_eq_true] at h0 ⊢
  obtain ⟨a1, a4⟩ := h0
  have hy' := hy
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy'
  exact ⟨hIo x x' hy a1, inOrderK13AtLater _ _ (laterOwn_blkL Z G₀ l d X arrs) hPlan _ _ _ _ _ rs gs
    (by rw [← roundsOwn_blkL Z G₀ l d X]; exact hfit) hd a4⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hOrder_of
