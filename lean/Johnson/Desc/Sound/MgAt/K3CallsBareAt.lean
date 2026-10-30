-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3CallsBareAt.lean: the lookup on a link's CALLS, AT THE COMPOSED MEANING
mgAll: THE KEPT ROWS ARE BARE BEHIND AN ACCEPT OF THE SEATED SUB-PROTOCOL: the premise hBare of
objects_att_mgAll_facts and objects_lay_mgAll_facts (Johnson/Desc/Sound/MgAt/K3CallsObjFacts.lean)
IN ITS OWN TEXT. General in the data Dm and in the sort of segment.
Statements and proofs: joinings.

OBJECT: the piece strictAt B' q over the block that K3.theStated lays at the calls' place of link l.
Used by K3CallsPaid.lean (Johnson/Desc/Sound/MgAt/) · K03BareAt.lean (Johnson/P5J/).
LETTERS: Dm, Mg, Rch, claim, a, k, l, sub, x, q, b', readers, codes, shape free.
Compiled with the whole library.

Main names:
  calls_hBare_core: at any numbers, meaning, list of segments and places: from "the promise in front
    gives k3OnIn" and "an accept of the piece is an accept of K3.block's decide".
  calls_hBare_mgAll: THE END.

EACH PREMISE OF calls_hBare_mgAll, AND OF WHAT KIND IT IS.
  h, hOk: term and test: the block at the address is the kind's own, and its test on the plan says
    yes · hback: test on the piece · hlook: test: the place of the lookup · hi, hsub, hpcT, hpc, hk:
    tests on the table and the address · hfit: test on the table and the meaning's list of extra
    public tests.
Limits. Nothing on what the rows are worth.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.First.Look.K3CallsMeanOf
import Johnson.Desc.First.Look.K3DigitsTies
import Johnson.Top.H.Keep.RowsAreBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers shift pubFit)

/-- **The kept rows are bare behind an accept**, at any letters. -/
theorem calls_hBare_core {P W Cl : Type} {Fr : Frame} (claim : Aff → Cl) (N : Numbers)
    (Mg : Meaning P W) (links : List ModelPart) (ps : List Desc.Place) (pi : P) (k : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
    (Rc : Desc.First.S × Fr.E.Str → Prop) (p : Desc.First.Look.P)
    (hIn : ∀ a : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a →
      a.1.failed = none → Desc.K3.k3OnIn p a.1 = true)
    (hY : ∀ a b, Yes a b → ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
      (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
      (cols : List (List (ℕ × List UInt64))),
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide a.1 rs cols =
        .ok b.1) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b →
      ∀ g, (Desc.K3.seatCalls claim).heard b.1 = some g → ∀ f ∈ g.rows.toList, Bare f := by
  intro a b ha _ hun hy g hg
  obtain ⟨Fk, hf, hz, -⟩ := k3OnIn_ledger (hIn a ha hun)
  obtain ⟨piece, laid, before, guests, rs, cols, hd⟩ := hY a b hy
  obtain ⟨g', hg', hb⟩ := calls_bare claim piece laid before p guests a.1 b.1 rs cols hd hf hz
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  exact hb

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **hBare AT THE COMPOSED MEANING**, at a calls' place of any sort of segment. -/
theorem calls_hBare_mgAll (a : Desc.Place) (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
      (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hlook : lookAt X l false = some x) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 2 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l false) (hk : PS[k]? = some a)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f := by
  have e2 : 2 + shift sub = Desc.K3.pieceAt X l false := hpcT.symm.trans hpc
  have hOpen := calls_asks_open (mgAll Dm Mg).more linksFull PS k a l sub hfit hk hi hsub hpcT
    (.lookIn l (2 + shift sub)) (by simp)
  intro B' hN z
  refine calls_hBare_core claim Dm.N (mgAll Dm Mg) linksFull PS z k
    (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) (fun u => Rch k ((z, u.1), u.2))
    (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) ?_ ?_
  · intro u hu hun
    obtain ⟨-, hor⟩ := hu
    rcases hor with hbad | ⟨hBb, -, -, -⟩
    · exact absurd hun hbad
    · simp only [Bool.and_eq_true] at hBb
      have hp : (mgAll Dm Mg).pub (.lookIn l (2 + shift sub)) (z, u.1) = true :=
        List.all_eq_true.1 hBb.1.2 _ (List.mem_append_left _ hOpen)
      rw [e2] at hp
      exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z u.1 hp)
  · intro u v hy
    obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
      seat_yes claim readers codes shape h hOk hi hpc (placeAt_iff.2 ⟨x, hlook, rfl⟩) hback B' hN
        u v hy
    exact ⟨piece, laid, before, guests, rs, cols, hd⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_hBare_core
#print axioms VerifiableInference.OnPublicFiles.calls_hBare_mgAll
