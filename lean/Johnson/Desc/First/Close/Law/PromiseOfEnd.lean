-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PromiseOfEnd.lean: FROM K10's LAW's END TO THE TABLE's PROMISE BEHIND
THE BLOCK. One statement and its proof: `k10_promise_at` (PromiseAt.lean) at what the law's end
`K10EndS` (GoodOf.lean) holds. Both beside this file. A file BESIDE the table of joints: it turns
nothing of it.

  `k10_promise_of_end`: a, a' with `K10EndS` between them: the end holds a yes of `closeFrame` at
    what K10 reads of a's record, and that a'.1 is K10's writing of what it returned. So: from
    `onAt` at ps[k]? and the k-th open set at (z, a.1): `onAt` at ps[k + 1]? and the (k + 1)-th open
    set at (z, a'.1): THE SECOND TIE's FORM, with the law's end in the place of the kind's own
    promise behind.
Limits. Those of PromiseAt.lean: "what is kept lies in its group"; the plan's two numbers; THE SIX
SENTENCES ON THE MEANING's LETTERS, here at (z, a.1) and (z, a'.1). z (what was handed to the chain)
is the same on both sides: by the statement's form. y, y' are letters: that they are the strings in
front of and behind the piece is the caller's. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PromiseAt
import Johnson.Desc.First.Close.Law.GoodOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers Item Pub Meaning ModelPart onAt openSets start closersFit
  closersNext pubHeld sampledIn k10_promise_at)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_promise_of_end {Pz Wt : Type}
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a a' : VerifiableInference.Desc.First.S × F.E.Str)
    (hE : K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err fa a a')
    (Nu : Numbers) (Mg : Meaning Pz Wt) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10)
    (hKept : ∀ t ∈ Nu.keptOf (p.link.getD 0), t ∈ Nu.group (p.link.getD 0))
    (ht : Nu.treesAt ps[k + 1]? = Nu.treesAt ps[k]?)
    (hm : Nu.msgsAt ps[k + 1]? = Nu.msgsAt ps[k]?)
    (Q Q' : List Pub) (z : Pz) (y y' : Strs)
    (ha : onAt Nu Mg links ps[k]? ((openSets links ps (start links))[k]?.getD []) Q (z, a.1) y)
    (hDec : Mg.decodes (z, a.1) y → Mg.decodes (z, a'.1) y')
    (hIn : a.1.failed = none → Mg.inOrder (z, a.1) = true → Mg.inOrder (z, a'.1) = true)
    (hPub : a.1.failed = none →
      pubHeld Mg ((openSets links ps (start links))[k]?.getD []) Q (z, a.1) = true →
      pubHeld Mg ((openSets links ps (start links))[k + 1]?.getD []) Q' (z, a'.1) = true)
    (hPP : a.1.failed = none → (∀ q ∈ Q, Mg.pubP q (z, a.1)) → ∀ q ∈ Q', Mg.pubP q (z, a'.1))
    (hHeld : a.1.failed = none →
      ∀ t ∈ sampledIn Nu ((openSets links ps (start links))[k]?.getD []),
        Mg.held t.1 t.2 (z, a.1) = true → Mg.held t.1 t.2 (z, a'.1) = true)
    (hSN : a.1.failed = none →
      ∀ t ∈ sampledIn Nu ((openSets links ps (start links))[k]?.getD []),
        Mg.shown t.1 t.2 y ∧ Mg.noColl t.1 t.2 (z, a.1) y →
          Mg.shown t.1 t.2 y' ∧ Mg.noColl t.1 t.2 (z, a'.1) y') :
    onAt Nu Mg links ps[k + 1]? ((openSets links ps (start links))[k + 1]?.getD []) Q'
      (z, a'.1) y' := by
  obtain ⟨⟨τ, -, -, hcf⟩, hw, -⟩ := hE
  rw [hw] at hDec hIn hPub hPP hHeld hSN ⊢
  exact k10_promise_at Nu Mg links ps k p hF hX hk hK hKept ht hm Q Q' (z, a.1) z y y' _ _ _ hcf
    ha hDec hIn hPub hPP hHeld hSN

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_promise_of_end
