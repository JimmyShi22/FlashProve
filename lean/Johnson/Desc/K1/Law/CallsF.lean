-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsF.lean: THE CALL THAT STRIKES k01_law's
BINDER hl' (the reader gives one answer in front of and behind a later sub-protocol of kind K1): it
follows from the binder hRd (ReadersStay: what a reader answers in front it answers behind), which
the top asks anyhow. Statements with their proofs: calls of Johnson/Desc/K1/Law/ReadersFwd.lean.

OBJECT. One later place of kind K1 (blkL Z G₀ l d X arrs at the place noL l d), under LaidK1.
USER. Johnson/Desc/K1/Law/K01Law.lean, at aForms_at: it passes
(hl_at hL l d X arrs (hRd l hl d X arrs hX)) in hl's place. No binder hl' stands in that file.
PROVED HERE.
  hl_at: **hl' in aForms_at's own letters, from hRd in hPub_at's own letters.**
  aForms_at_fwd: aForms_at with hRd in hl's place.
PREMISES THAT STAY. hRd: each run's kind's law (Fwd, Johnson/Desc/Reads/FormsPass.lean, at each run:
readersStay_iff_fwd). It stands behind the accept and the promise in front. hwt, hmeet: as before.
What is not claimed. ReadersStay of any reader. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.CallsG
import Johnson.Desc.K1.Law.ReadersFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData pubAll flatPlacesOf
  rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (Mem MsgT linksFull smpNamed Stated CellsQ)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Xi Tok : Type} {rows cols : ℕ} {XV : Model.Verify.Public}

variable {N : Numbers} {Dp : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf Dp.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option (CellsQ rows cols)}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {pb : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)} {seats : List (ℕ × ℕ)} {St : Stated}
  {after : ℕ → S → Except String S}
  {wt : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {rwB : ℕ → S → Bool} {hd : ℕ}
  {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
  {H : P5J.HidAt XV Pp (Wit (CellsQ rows cols) Tok MsgT) rows cols}
  {headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop}
  {digitsPart : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop}
  {fI : Pub} {fB : TreeBook → Bool}
  {Mg0 Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **hl'**, from hRd: the promise in front holds the public item formsIn m j r wherever forms m j r
is open, so the reader answers in front. -/
theorem hl_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (hRd : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        Pub.formsInT m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dp D3) m j r x.2 x'.2) :
    ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      ∀ p ∈ Dp.runs m j r, (Dp.Rd m).forms p.1 p.2 x'.2 = (Dp.Rd m).forms p.1 p.2 x.2 := by
  intro x x' y m j r hy hIn ho
  have hm := formsIn_open
    ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) m j r ho
  have hin := inAt_pub hIn _ hm
  rw [hL.fills.pub] at hin
  exact one_of_stay (dK Dp D3) pb m j r x x'.2 hin (hRd x x' y m j r hy hIn (Or.inl hm))

/-- **aForms**, the readers asked one direction alone. LEFT: hRd · hwt · hmeet. -/
theorem aForms_at_fwd
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (base : ℕ)
    (hRd : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        Pub.formsInT m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dp D3) m j r x.2 x'.2)
    (hwt : ∀ x x' y y' w m j, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      wt m x' y' w → wt m x y w)
    (hmeet : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      ∀ p ∈ Dp.runs m j r, Dp.ah p.1 p.2 = true →
      AheadMeets (N.sent m) (N.group m) (idsOf (parL Z G₀ l d) x.2.st.oracles.size).toList x.2
        x'.2) :
    ∀ (x x' : Pp × S) y y' w m k r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.forms m k r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      Mg.forms m k r x' y' w → Mg.forms m k r x y w :=
  aForms_at hL l d X arrs base (hl_at hL l d X arrs hRd) hwt hmeet

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hl_at
#print axioms VerifiableInference.Desc.K1.aForms_at_fwd
