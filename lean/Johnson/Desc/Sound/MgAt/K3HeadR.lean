-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3HeadR.lean: the kind "lookup" (K3), the lookup argument on the calls at
the output head's link: `HeadAtTableR` (Johnson/Desc/First/Look/K3HeadAtTableR.lean: what the row's
law asks of the table's meaning, second form) AT THE COMPOSED MEANING `mgAll 𝔇 Mg`
(Johnson/Desc/Sound/MgAll.lean: the small door; worth at the head's calls
under the guard; the committed table's three letters fixed).

Main names:
  `head_row_ins`, `head_row_outs`, `head_row_ctx`: the row's three lists at the full size's lists.
  `headMg_pubIn`, `headMg_worthG`: the public item lookIn and the three sentences on worth, at the
    term.
  `headGotR_mgAll`: `HeadGotR` (Johnson/Desc/First/Look/K3HeadRestR.lean: TWENTY-THREE of the 26
    fields) AT THE TERM, at Rc := Rch at the border and the public part in hand, from: sits (the
    lookup's files' `ListSits`: cf, pinIn and, with the pins' openness, seats) · parts (their
    `BehindPartsR` at the piece 3, with hs and hY: behind) · F (`K3Fold`, MgAt/K3OwnIn.lean: THE
    TIGHT LIST of what the kind spends of the facts along the fold: ownIn by its field ownIs;
    tokIn's last step by its field replyNat) ·
    and SIX plain premises: the public parameters have the head's place; the head's link is number
    24; the meaning beneath adds nothing to the door; the decoder does not read the first chain's
    state; the reader of OOD samples reads the state's statement alone; what segment 24 sends at
    moment 0 was sent before the piece (`k03_fenced` pays it).
  `headAtTableR_mgAll`: with `HeadLeftR` (the three that have no payer: objects, model,
    smallBack): `HeadAtTableR` at the term.

PAID, BY WHOM: ins, outs, ctx (the table's text) · askIn (MgAt/K3Open.lean, by the kernel) · seats
(MgAt/K3Pins.lean) · pubIn · qIn (Q := `k3QAny`) · tokIn (MgAt/K3HeadIn.lean) · freeIn
(MgAt/K3HeadFree.lean) · worthP, worthK, worthR
(K3HeadFillG.lean) · cf, pinIn (K3CallsFill.lean) · pinBack (MgAt/K3Sig.lean) · tabIn, pinWIn,
pinWOut (K3StoredAtMean.lean) · ownIn (MgAt/K3OwnIn.lean) · free, pinWBack (MgAt/K3Guard.lean) ·
behind (K3HeadBehindR.lean) · decodes (MgAt/K3Decodes.lean).

Why the second form of "behind". F is the tight list `K3Fold`, not all the facts along the fold.
For "behind" the structure `BehindPartsR` is taken, not `BehindParts` (Johnson/Desc/First/Look/K3CallsBehind.lean). With the first form as a
premise the list of premises is empty: that structure asks that the name
"frame.liveIs" be open at the border; under "the meaning beneath adds nothing to the door" the
composed meaning's door has it open at none of the fifty (`MgAt.live_not_open`, Johnson/Desc/Sound/MgAt/K3Open.lean, by the kernel): the two
premises contradict each other. The second form
of that structure names no such item.

Limits: sits, parts, F, the plain premises and `HeadLeftR` are premises: shown at no 𝔇; NEITHER
ALONE NOR TOGETHER TRIED FOR EMPTINESS (no example meets them). Rch is a letter. The full size's
written lists alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Look.K3HeadRestR
import Johnson.Desc.First.Look.K3HeadFillG
import Johnson.Desc.First.Look.K3StoredAtMean
import Johnson.Desc.First.Look.K3CallsFill
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.Sound.MgAt.K3Guard
import Johnson.Desc.Sound.MgAt.K3Sig
import Johnson.Desc.Sound.MgAt.K3Pins
import Johnson.Desc.Sound.MgAt.K3HeadIn
import Johnson.Desc.Sound.MgAt.K3HeadFree
import Johnson.Desc.Sound.MgAt.K3OwnIn
import Johnson.Desc.First.Look.K3HeadBehindR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubAll)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-! ## The row -/

theorem head_row_ins : (rowQ linksFull PS (k3K 24 false)).ins =
    [.constr 24 .lookCallsHeard, .constr 24 .rider] := by
  unfold rowQ
  rw [K3Lot.k03_at_full 24 (by decide) false]
  rfl

theorem head_row_outs : (rowQ linksFull PS (k3K 24 false)).outs =
    [.formsT 24 3 "objects", .worth 24 3 "planes", .worth 24 3 "keys", .worth 24 3 "rider"] := by
  unfold rowQ
  rw [K3Lot.k03_at_full 24 (by decide) false]
  rfl

theorem head_row_ctx : (rowQ linksFull PS (k3K 24 false)).ctx =
    [.pin 24 0, .constr 24 .small, .pinW] := by
  unfold rowQ
  rw [K3Lot.k03_at_full 24 (by decide) false]
  rfl

/-- The head's place bears the head's link's number. -/
theorem headAt_link {X : Verify.Public} {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) : x.link = headLink X := by
  unfold Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
  subst hx
  have e := lookAt_link h1
  exact e

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **pubIn.** -/
theorem headMg_pubIn {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S)
    (h : (mgAll 𝔇 Mg).pub (.lookIn (headLink X) 3) (z, s) = true) :
    k3LookIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x)
      (𝔇.sent.arrayOf.getD x.link #[]) s = true := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  letI := 𝔇.rq z
  rw [mgAll_pub, Desc.First.pubAll_lookIn 𝔇.pubD Mg.pub (headLink X) 3 false (sort_head X)] at h
  have h2 : k3LookInAt X 𝔇.sent (headLink X) false s = true := h
  unfold k3LookInAt at h2
  rw [placeAt_headAt hx] at h2
  rw [headAt_link hx]
  exact h2

/-- The term's worth at the head's calls is the guarded layer's. -/
theorem headMg_worthG (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth (headLink X) 3 r a y w =
      (letI := k3SizesAt X
       letI := k3PolicyAt X
       (fillK3HeadG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq (fun w => Flat.InRange w.cells) Mg).worth
         (headLink X) 3 r a y w) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 (fillK3HeadG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq
    (fun w => Flat.InRange w.cells) Mg)).worth (headLink X) 3 r a y w = _
  rw [fillAll_over_headG]

/-! ## What is owed, and the assembly -/

variable {Fr : Frame} {Cl : Type} (claim : Aff → Cl) (x : Desc.First.Look.Place)
  (smp : Desc.First.S → (i : Fin (sigListCalls 𝔇.sent 𝔇.l3.rad x.link).length) →
    Option ((attSg x 𝔇.sent 𝔇.l3.rad).om i).Smp)
  (z : P) (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (p : Piece (ckP .two) Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT))

/-- **TWENTY-THREE OF THE 26 FIELDS AT THE TERM.** -/
theorem headGotR_mgAll (s₀ : Desc.First.S) (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (h24 : headLink X = 24) (hM : Mg.more = {}) (hS : Stored.NoRec 𝔇.decT)
    (hsmp : ∀ (z : P) (s s' : Desc.First.S), s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s))
    (hbase : ∀ t ∈ 𝔇.N.sent 24 0, t.1 < p.base)
    (sits : ListSits 𝔇.G x 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.smp smp
      𝔇.ms 𝔇.N 24)
    (F : K3Fold Rch 𝔇.sent)
    {arrs : Array (Nat × String)} {pl pl' : Desc.Place} {told : List (List Desc.Oracle)}
    (hs : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs)
    (hY : ∀ a c, (∃ τ, p.ior.red.out a τ = some c) →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) guests).decide a.1 rs
          cols = .ok c.1)
    (parts : BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
      (k3K 24 false) 24 3 arrs pl pl' told (fun a c => ∃ τ, p.ior.red.out a τ = some c)
      (fun a => Rch (k3K 24 false) ((z, a.1), a.2))) :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadGotR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr smp
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun a => Rch (k3K 24 false) ((z, a.1), a.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun a c => ∃ τ, p.ior.red.out a τ = some c) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  letI := 𝔇.rq z
  have SP := stored_paid (Fr := Fr) (Mg := mgAll 𝔇 Mg) (decT := 𝔇.decT) s₀ (mgAll_decodes 𝔇 Mg)
    (mgAll_pinW 𝔇 Mg) hS
  refine ⟨head_row_ins, head_row_outs, head_row_ctx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, SP.tabIn z, SP.pinWIn z, SP.pinWOut z, ?_, ?_, ?_, ?_, ?_⟩
  · -- askIn
    rw [mgAll_more_closed 𝔇 Mg hM]
    exact (MgAt.k3_open_calls (l := 24) (by decide)).1
  · -- seats
    intro i
    exact MgAt.sampled_calls 𝔇.N (l := 24) (by decide) _ (sits.sent i)
  · -- pubIn
    intro s h
    exact headMg_pubIn 𝔇 Mg hx z s (by rw [h24]; exact h)
  · -- qIn
    intro _ _ _ _ _ _
    trivial
  · -- tokIn
    intro a ha hr hu
    exact MgAt.headMg_tokIn 𝔇 Mg hM z a ha hu (F.replyNat ((z, a.1), a.2) hr hu)
  · -- freeIn
    intro a ha _ hu
    exact MgAt.headMg_freeIn 𝔇 Mg claim hx h24 hM z a ha hu
  · -- worthP
    intro s y w h hg
    have h' : (mgAll 𝔇 Mg).worth (headLink X) 3 "planes" (z, s) y w := by
      rw [h24]
      exact h
    rw [headMg_worthG] at h'
    exact headP_fillG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq _ Mg claim hx z s y w h' hg
  · -- worthK
    intro s y w h hg
    have h' : (mgAll 𝔇 Mg).worth (headLink X) 3 "keys" (z, s) y w := by
      rw [h24]
      exact h
    rw [headMg_worthG] at h'
    exact headK_fillG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq _ Mg claim hx z s y w h' hg
  · -- worthR
    intro s y w h hg
    have h' : (mgAll 𝔇 Mg).worth (headLink X) 3 "rider" (z, s) y w := by
      rw [h24]
      exact h
    rw [headMg_worthG] at h'
    exact headR_fillG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq _ Mg claim hx z s y w h' hg
  · -- cf
    intro i s y _ _ h
    exact calls_cf 𝔇.G sits z i s y h
  · -- pinIn
    intro s y w h
    exact calls_pinIn 𝔇.G 𝔇.l3.arr sits z s y w h
  · -- pinBack
    exact k3Mg_pinBack 𝔇 Mg hsmp z p 24 hbase
  · -- ownIn
    intro a _ hr hu
    rw [(headAt_link hx).trans h24]
    exact F.ownIs 24 (by decide) false ((z, a.1), a.2) hr hu
  · -- free
    exact fun a w hg hw => headMg_free 𝔇 Mg 24 z a w hg hw
  · -- pinWBack
    exact k3Mg_pinW_back_yes 𝔇 Mg hS z p
  · -- behind
    exact head_behindR k3QAny claim hs hY parts
  · -- decodes
    exact k3Mg_decodes_yes 𝔇 Mg hS z p

/-- **`HeadAtTableR` AT THE TERM, FROM THE THREE THAT HAVE NO PAYER.** -/
theorem headAtTableR_mgAll (s₀ : Desc.First.S)
    (A : letI := k3SizesAt X
      letI := k3PolicyAt X
      letI := 𝔇.rq z
      HeadGotR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr smp
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun a => Rch (k3K 24 false) ((z, a.1), a.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun a c => ∃ τ, p.ior.red.out a τ = some c))
    (B : letI := k3SizesAt X
      letI := k3PolicyAt X
      letI := 𝔇.rq z
      HeadLeftR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr smp
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun a => Rch (k3K 24 false) ((z, a.1), a.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadAtTableR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr smp
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun a => Rch (k3K 24 false) ((z, a.1), a.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun a c => ∃ τ, p.ior.red.out a τ = some c) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  letI := 𝔇.rq z
  exact headAtTableR_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.head_row_ins
#print axioms VerifiableInference.OnPublicFiles.head_row_outs
#print axioms VerifiableInference.OnPublicFiles.head_row_ctx
#print axioms VerifiableInference.OnPublicFiles.headAt_link
#print axioms VerifiableInference.OnPublicFiles.headMg_pubIn
#print axioms VerifiableInference.OnPublicFiles.headMg_worthG
#print axioms VerifiableInference.OnPublicFiles.headGotR_mgAll
#print axioms VerifiableInference.OnPublicFiles.headAtTableR_mgAll
