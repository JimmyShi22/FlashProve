-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AsksOfMg.lean: WHAT K10's SECOND TIE TO THE TABLE OF JOINTS ASKS OF A
MEANING, AS ONE STRUCTURE; AND THE TIE's TERM FROM IT. Definitions, one statement and its proof. A
file BESIDE the table: it turns nothing of it.

Why. The table's files compose the meaning of all kinds' layers in one term, and give each kind's
files one lemma: "your premises on the meaning hold at the composed meaning". So each kind's law is
to be typed over a LETTER for the meaning, under its own premises on that letter as ONE structure.
  `K10Step s s'`: s' is K10's writing at a yes of the frame's closing at what K10 reads of s. What
    of the record rides along such a step is said, field by field, in `k10_rides` (RidesBehind.lean,
    beside this file).
  `K10Asks N Mg O O' Q Q' St`: SIX SENTENCES ON THE LETTER Mg, each along a `K10Step` from an
    unmarked record (but the first): "decodes" rides; "in order" rides; the public items behind hold
    (`pubHeld` at O', Q' from `pubHeld` at O, Q); what they say beside their Bools (`pubP`); "held"
    rides at the sampled tenants of O; "shown" and "no collision" ride as a pair there. O, O': the
    open sets in front and behind; Q, Q': the open public items; St y y': how the strings behind
    stand to the strings in front: a letter.
  `k10_promise_of_asks`: from `K10Asks` at the k-th and (k + 1)-th open sets, the law's end
    `K10EndS` between a and a', St y y', the two tests on the table, "what is kept lies in its
    group" and the plan's two numbers: the table's promise behind from the table's promise in front:
    `k10_promise_of_end` (PromiseOfEnd.lean) with its six premises drawn from the structure.
Limits. `K10Asks` is shown of no meaning here. It holds what the SECOND tie asks alone: the first,
third, fourth and fifth ties ask more of the meaning (the rows' and pins' sentences, "carry"): not
in this structure yet. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PromiseOfEnd

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
  closersNext pubHeld sampledIn)

/-- s' is K10's writing at a yes of the frame's closing at what K10 reads of s. -/
def K10Step (s s' : VerifiableInference.Desc.First.S) : Prop :=
  ∃ es rs x, closeFrame (recOf s).owed (recOf s).frame (recOf s).st es rs = .ok x ∧
    s' = putRec s ⟨none, x.1, x.2⟩

/-- **What K10's second tie asks of a meaning.** -/
structure K10Asks {Pz Wt : Type} (Nu : Numbers) (Mg : Meaning Pz Wt) (O O' : List Item)
    (Q Q' : List Pub) (St : Strs → Strs → Prop) : Prop where
  dec : ∀ z s s' y y', K10Step s s' → St y y' → Mg.decodes (z, s) y → Mg.decodes (z, s') y'
  inOrder : ∀ z s s', K10Step s s' → s.failed = none → Mg.inOrder (z, s) = true →
    Mg.inOrder (z, s') = true
  pub : ∀ z s s', K10Step s s' → s.failed = none → pubHeld Mg O Q (z, s) = true →
    pubHeld Mg O' Q' (z, s') = true
  pubP : ∀ z s s', K10Step s s' → s.failed = none → (∀ q ∈ Q, Mg.pubP q (z, s)) →
    ∀ q ∈ Q', Mg.pubP q (z, s')
  held : ∀ z s s', K10Step s s' → s.failed = none → ∀ t ∈ sampledIn Nu O,
    Mg.held t.1 t.2 (z, s) = true → Mg.held t.1 t.2 (z, s') = true
  shown : ∀ z s s' y y', K10Step s s' → St y y' → s.failed = none → ∀ t ∈ sampledIn Nu O,
    Mg.shown t.1 t.2 y ∧ Mg.noColl t.1 t.2 (z, s) y →
      Mg.shown t.1 t.2 y' ∧ Mg.noColl t.1 t.2 (z, s') y'

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_promise_of_asks {Pz Wt : Type}
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
    (Q Q' : List Pub) (St : Strs → Strs → Prop)
    (A : K10Asks Nu Mg ((openSets links ps (start links))[k]?.getD [])
      ((openSets links ps (start links))[k + 1]?.getD []) Q Q' St)
    (z : Pz) (y y' : Strs) (hy : St y y')
    (ha : onAt Nu Mg links ps[k]? ((openSets links ps (start links))[k]?.getD []) Q (z, a.1) y) :
    onAt Nu Mg links ps[k + 1]? ((openSets links ps (start links))[k + 1]?.getD []) Q'
      (z, a'.1) y' := by
  have hs : K10Step a.1 a'.1 := by
    obtain ⟨⟨τ, -, -, hcf⟩, hw, -⟩ := hE
    exact ⟨_, _, _, hcf, hw⟩
  exact k10_promise_of_end R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err fa a
      a' hE Nu Mg
    links ps k p hF hX hk hK hKept ht hm Q Q' z y y' ha (A.dec z _ _ y y' hs hy)
    (A.inOrder z _ _ hs) (A.pub z _ _ hs) (A.pubP z _ _ hs) (A.held z _ _ hs)
    (A.shown z _ _ y y' hs hy)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_promise_of_asks
