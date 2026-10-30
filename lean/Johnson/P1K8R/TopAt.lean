-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TopAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE KIND'S
SHARE OF THE CHAIN OF PROMISES, IN THE FORM WITH "REACHED", AT THE DESCRIPTION'S OWN 25 PLACES, FROM
ALL THAT LIES AND ONE STRUCTURE OF WHAT IS LEFT. NO SOUNDNESS.

The pieces: `k08_kindTiedR` (P1K8R/TiedReach.lean): the kind's share from `K8OwesR` at each place;
`k08_owesR` (P1K8R/OwesAt.lean): `K8OwesR` from `K8Fill`; `k08_here` (P1K8R/FillAt.lean) and
`k08_makes` (P1K8R/MakesAt.lean): two fields of `K8Fill` from this folder's theorems at the fold.
Here they are joined, with one more:
  `opens_small`: behind a yes of the draw from a reached state the caller's list of tables is the
    structure's own (`k8FunsAreR`, P1K8R/FunsAtSeat.lean; the draw writes neither): so a filling
    whose sentence on the run "small" gives `SmallAt` at `cellsAhead` WHEREVER the two lists are one
    gives it there.
  `K8Left`: WHAT IS LEFT AT ONE PLACE, field by field: the piece as one equation; 128 combinations;
    the row's three lists; `DrawBlind`; the filling's `pin`, `smpStay`, `closes`, `forms`, `digits`;
    `HereOwes`; `MakesOwes`.
  `k08_fill`: `K8Left` gives `K8Fill`, in the goals' scope, under the description's `planOk` and the
    tests `namesDoorB`, `planFitsAllB`.
  `k08_top`: **IN THE GOALS' SCOPE, UNDER THESE THREE TESTS: `K8Left` AT EACH OF THE 25 PLACES GIVES
    `KindTiedR'` … K8 AT EVERY CONDITION Rch THAT GIVES `RchAt`**: what is left is asked ALONG THAT
    CONDITION ALONE (a
    law's premises along "reached" do not go down with its end).
Limits. `K8Left` is shown at no filling: NOT TO BE TOLD AS "TIED". AT `OnBytes.secondHashFunction` ALONE. That
Rch holds at the start and is handed on by every sub-protocol is owed by whoever calls the chain's
rule (at `RchAt`: `rchAt_zero`, `rchAt_hand`). Nothing on soundness.

-/
import Johnson.P1K8R.MakesAt

set_option autoImplicit false
set_option maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open VerifiableInference.Desc.K9 (Readers formsInA)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

section
variable {Cells Tok : Type} {Fr : Frame} (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
  (c : Chain S Cl) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
  (smpT : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
  (rad : OracleShape → ℕ) (Wp : Verify.Public) (Rd : Readers) (bN pc l : ℕ)
  (q : Piece (Run.ckP .two) Fr (ProofFile.InstPub × S) Claim (Wit Cells Tok MsgT)) (p : ParW)
  (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)

/-- What the draw must make behind itself. -/
abbrev oSAt : ProofFile.InstPub → S → Strs → Prop :=
  fun _ t _ => formsInA Rd (N.sent l) (N.group l) bN "K8.equations" t = true

/-- "Reached", in the type of the table's letter. -/
abbrev RchD : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop := fun k a => RchAt (FD Z A B c) k a

/-- **WHAT IS LEFT AT ONE PLACE.** -/
structure K8Left : Prop where
  piece : ∀ B' : Block S Claim,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) Fr S Claim (Wit Cells Tok MsgT)) =
    ⟨below B', q.base, [rdt p.toPar], [], fun _ _ w => w,
      Err.cap 128 (uLT (Run.ckP .two) [rdt p.toPar])⟩
  tau : p.tau = 128
  ins : (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).ins =
    [.constr l .small, .tie l]
  outs : (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).outs =
    [.forms l pc "small", .constr l .lookDigits]
  ctx : (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).ctx = [.pin l 0, .pin l 1]
  blind : DrawBlind N Mg linksFull (flatPlacesOf linksFull true) (drawAt l) q.base
    (oSAt N Rd bN l)
  pin : ∀ j t a y w, Mg.pin j t a y w → pinJT cs (FD Z A B c) arr smpT ms j t a y w
  smpStay : ∀ (z : ProofFile.InstPub) (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat),
    s.tl? = some tl → smpT (z, s.putTl { tl with cfF := mm, cfFirst := f }) = smpT (z, s)
  closes : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    TieAt (cellsAt cs arr ms N l (z, a.1)) a.1 w →
    Mg.constr l .small (z, a.1) (strsOf Fr a.2) w ∧ Mg.tie l (z, a.1) (strsOf Fr a.2) w
  forms : ∀ (z : ProofFile.InstPub) (s : S) (y : Strs) w (tl : HTailF2), s.tl? = some tl →
    s.funs? = some tl.funs → Mg.forms l pc "small" (z, s) y w →
    SmallAt (cellsAhead cs arr ms N l (z, s)) s w
  digits : ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str) w,
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
    Mg.constr l .lookDigits (z, b.1) (strsOf Fr b.2) w →
    DigitsAt (cellsAhead cs arr ms N l (z, b.1)) b.1 w
  here : HereOwes Z A B c cs smpT ms N Mg rad l q.base Rch
  makes : MakesOwes N Mg Wp Rd bN p.toPar l Rch

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Cells Tok : Type} {Fr : Frame} {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ}
  {smpT : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp}
  {ms : List Mem} {N : Numbers} {Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)}
  {rad : OracleShape → ℕ} {Rd : Readers} {bN pc l : ℕ}
  {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}

/-- **Behind a yes of the draw from a reached state the two lists of tables are one.** -/
theorem opens_small (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hl : l ≤ 24) (p₀ : Par)
    (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
    (hr : RchAt (FD Z A B c) (drawAt l) ((z, a.1), a.2))
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p₀).decide a.1 rs gs = .ok b.1) :
    ∃ tl, b.1.tl? = some tl ∧ b.1.funs? = some tl.funs := by
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (FD Z A B c) (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hr
  obtain ⟨tl, ht, hfu⟩ := P1K8S.k8FunsAreR hS hR O hx ((z, a.1), a.2) hr'
  obtain ⟨rs, gs, hd⟩ := hy
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlay⟩ := decide_ok atS p₀ a.1 b.1 rs gs hd
  obtain ⟨tl', ht', hb⟩ := atS_lay a.1 b.1 _ _ hlay
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  rw [hb]
  exact ⟨_, putTl_tl a.1 tl _ ht, by rw [putTl_funs]; exact hfu⟩

/-- **`K8Left` gives `K8Fill`.** -/
theorem k08_fill (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) (hW : planFitsAllB Bs.G₀.W = true) (hl : l ≤ 24) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl)
    {q : Piece (Run.ckP .two) Fr (ProofFile.InstPub × S) Claim (Wit Cells Tok MsgT)}
    (hRch : ∀ k a, Rch k a → RchAt (FD Z A B c) k a)
    (H : K8Left Z A B c cs arr smpT ms N Mg rad Bs.G₀.W Rd bN pc l q (ProofFile.k8ParW Z Bs.G₀ Xl l)
      Rch) :
    K8Fill (FD Z A B c) cs arr smpT ms N Mg linksFull (flatPlacesOf linksFull true) Rch (drawAt l)
      l pc q (ProofFile.k8ParW Z Bs.G₀ Xl l) rad (oSAt N Rd bN l) where
  piece := H.piece
  tau := H.tau
  ins := H.ins
  outs := H.outs
  ctx := H.ctx
  blind := H.blind
  makes := fun z a b ha hr hm hy =>
    k08_makes hS hR O hP hD hW hl e3 hRch H.makes z a b ha hr hm hy
  pin := H.pin
  smpStay := H.smpStay
  closes := H.closes
  opens := fun z a b w ha hr hm hy hf hd => by
    obtain ⟨tl, ht, hfu⟩ := opens_small hS hR O hl _ z a b (hRch _ _ hr) hy
    exact ⟨H.forms z b.1 _ w tl ht hfu hf, H.digits z a b w ha hr hm hy hd⟩
  here := fun z a ha hr hm => k08_here hS hR O hP hD hW hl e3 hRch H.here z a ha hr hm

end

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, FROM WHAT IS LEFT.** -/
theorem k08_top {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) (hW : planFitsAllB Bs.G₀.W = true) {D : WholeD}
    {all : List LeftT} {X₁ X₂ Cells Tok : Type}
    {T : ThreeAt (Run.ckP .two) D all (FD Z A B c) X₁ X₂ (Wit Cells Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (smpT : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (rad : OracleShape → ℕ) (Rd : ℕ → Readers) (bN pc : ℕ → ℕ)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (hRch : ∀ k a, Rch k a → RchAt (FD Z A B c) k a)
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8Left Z A B c cs arr smpT ms N Mg rad Bs.G₀.W (Rd l) (bN l) (pc l) l q
        (ProofFile.k8ParW Z Bs.G₀ Xl l) Rch) :
    KindTiedR' N Mg linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁) KindName.K8 :=
  k08_kindTiedR hS hR O hT N Mg Rch E hE fun l Xl q hl e3 hq =>
    k08_owesR (k08_fill hS hR O hP hD hW hl e3 hRch (H l Xl q hl e3 hq))

end P1K8T

#print axioms P1K8T.opens_small
#print axioms P1K8T.k08_fill
#print axioms P1K8T.k08_top
