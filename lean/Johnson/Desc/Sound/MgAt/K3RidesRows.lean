--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS: rides_calls_row, rides_digits_row: no parameters and no place are shown
here at which their premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesRows.lean: the kind "lookup" (K3): THE FIELD rides OF THE KIND's
LEDGER (Johnson/Desc/Sound/MgAt/K3Owed.lean, K3Mean.lean), AT THE LEDGER's OWN LETTERS (the border
k3K l d, the place IM.k3Place l d, the value k3Const X codes shape l d, the piece pieces[k3K l
d]), WITH WHAT THE LEDGER's OWN OTHER FIELDS AND THE FACTS ON THE PIECES PAY LAID IN: the place:
by Lean's kernel · q.back = [] and planOk: K3Pieces (Johnson/Desc/First/Look/K3Base.lean) · "the
index's tree lies below the piece's base": index_lt_at (K3RidesBase.lean) from the field base |
hbaseS's own text · an accepting is SameBut: calls_seated_sameBut · at the digits hLed: led_mgAll.
AND EXAMPLES in which Lean takes these premises out of given structures (T.base, T.hbaseS; V.es,
V.hD, V.hd, V.hM) and lays the end back into rides. Statements and proofs: joinings; one
evaluation by Lean's kernel. No error term. NO SOUNDNESS IS CLAIMED.

OBJECT: RidesAtR at the ledger's letters.
USER: nobody yet. Meant: the kind's lead's assembly of its ledger.
LETTERS: Dm, Mg, Rch, codes, shape, pieces, seats; l, sub, q, b', x, hs.

Main names:
  `k3PlacesOkB`, `k3PlacesOk_full`, `k3Border_calls`, `k3Border_digits`: at each of the fifty
    borders stands K3's own place; the calls' at piece 3 or below, the digits' at 7 or above.
  `rides_calls_row`: THE FIELD AT THE CALLS (attention, the layers, the head).
  `rides_digits_row`: THE FIELD AT THE DIGITS.

WHAT IS LEFT. BOTH: hpc (the place's piece is the kind's own pieceAt) · lookAt · hReq · hHead ·
the ledger's own es, hD, hd · the field base | hbaseS. THE DIGITS: hM · the shape · hFwd (payers:
fwd_step_layers | _att | _head, K3RidesDigFwd.lean, K3RidesDigFwd2.lean, at Cl := Desc.Claim) ·
hWt.
Limits. At the head's calls the structure HeadRestR has no field of base's text: there hbase stays
a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesLedger
import Johnson.Desc.Sound.MgAt.K3RidesDigStep
import Johnson.Desc.Sound.MgAt.K3RidesLed
import Johnson.Desc.Sound.MgAt.K3RidesBase
import Johnson.Desc.Sound.MgAt.K3Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets start sampledIn)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-! ## 1 The fifty places -/

/-- At each border stands K3's own place; the calls' at piece 3 or below, the digits' at 7 or
above. -/
def k3PlacesOkB : Bool :=
  (List.range 25).all fun l =>
    decide ((PS)[k3K l false]? = some (IM.k3Place l false)) &&
      decide ((IM.k3Place l false).piece ≤ 3) &&
      decide ((PS)[k3K l true]? = some (IM.k3Place l true)) &&
      decide (7 ≤ (IM.k3Place l true).piece)

set_option maxRecDepth 100000 in
theorem k3PlacesOk_full : k3PlacesOkB = true := by decide +kernel

theorem k3Border_calls {l : ℕ} (hl : l < 25) :
    (PS)[k3K l false]? = some (IM.k3Place l false) ∧ (IM.k3Place l false).piece ≤ 3 := by
  have h := List.all_eq_true.1 k3PlacesOk_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem k3Border_digits {l : ℕ} (hl : l < 25) :
    (PS)[k3K l true]? = some (IM.k3Place l true) ∧ 7 ≤ (IM.k3Place l true).piece := by
  have h := List.all_eq_true.1 k3PlacesOk_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

/-! ## 2 The rows -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl
    (Desc.Wit (CellsQ rows cols) Tok MsgT)))

/-- **THE FIELD rides AT THE CALLS, AT THE LEDGER's OWN LETTERS.** -/
theorem rides_calls_row
    (Pc : K3Pieces X codes shape pieces) {l : ℕ} (hl : l < 25) (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    {q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hq : pieces[k3K l false]? = some q) {b' : Desc.Block Desc.First.S ProofFile.Cl}
    (hb' : k3Const X codes shape l false = some b') {x : Desc.First.Look.Place}
    (hlook : lookAt X l false = some x)
    (hpc : (IM.k3Place l false).piece = Desc.K3.pieceAt X l false)
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k3K l false]?.getD []),
      t.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i)) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l false) q b' :=
  ridesAtR_calls_ledger Dm Mg seats es hD hd Rch (k3K l false) q b' (k3Border_calls hl).1 rfl
    (k3Border_calls hl).2 (Pc.back l hl false q hq)
    (calls_seated_sameBut K3Lot.ofForm (K3Lot.readersAt X) X codes shape (IM.k3Place l false) b'
      hb' (Pc.planOk l hl false b' hb') l rfl hpc
      (by
        unfold placeAt
        rw [hlook]
        rfl) q (Pc.back l hl false q hq))
    (index_lt_at Dm.N hl false hbase) hReq hHead

/-- **THE FIELD rides AT THE DIGITS, AT THE LEDGER's OWN LETTERS.** -/
theorem rides_digits_row
    (Pc : K3Pieces X codes shape pieces) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) (hM : Mg.more = {}) (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    {q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hq : pieces[k3K l true]? = some q) {b' : Desc.Block Desc.First.S ProofFile.Cl}
    (hb' : k3Const X codes shape l true = some b') {x : Desc.First.Look.Place}
    (hlook : lookAt X l true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (hpc : (IM.k3Place l true).piece = Desc.K3.pieceAt X l true)
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k3K l true]?.getD []),
      t.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk r) →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk r) →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk "weights") →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk "weights") →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b' :=
  ridesAtR_digits_step Dm Mg seats es hD hd Rch (k3K l true) l q b' (k3Border_digits hl).1 rfl
    (k3Border_digits hl).2 rfl (Pc.back l hl true q hq) K3Lot.ofForm (K3Lot.readersAt X) codes shape
    hb' (Pc.planOk l hl true b' hb') hpc hlook hsh (index_lt_at Dm.N hl true hbase) hReq hHead
    (led_mgAll Dm Mg Rch hM hl hsub) hFwd hWt

/-! ## 3 Lean takes the premises out of the ledger's own structures -/

/-- The ledger's type of claims is the description's. -/
example : ProofFile.Cl = Desc.Claim := rfl

/-- At attention's calls: T.base into hbase; the end back into rides. -/
example (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (tls : ℕ → HTailF2)
    (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V) (a' : Desc.Place)
    (A : Attention.Shape)
    (tl : HTailF2) (told : List (List Desc.Oracle))
    (Pc : K3Pieces X codes shape pieces) {l : ℕ} (hl : l < 25) (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    {q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hq : pieces[k3K l false]? = some q) {b' : Desc.Block Desc.First.S ProofFile.Cl}
    (hb' : k3Const X codes shape l false = some b') {x : Desc.First.Look.Place}
    (hlook : lookAt X l false = some x)
    (hpc : (IM.k3Place l false).piece = Desc.K3.pieceAt X l false)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (smp : Desc.First.S → (i : Fin (sigListCalls Dm.sent Dm.rad3 x.link).length) →
      Option ((attSg x Dm.sent Dm.rad3).om i).Smp)
    (T : AttOwedR Dm Mg Rch K3Lot.ofForm num idx tls tok (IM.k3Place l false) a' (k3K l false) l x
      A tl smp q b' told) :
    AttOwedR Dm Mg Rch K3Lot.ofForm num idx tls tok (IM.k3Place l false) a' (k3K l false) l x A tl
      smp q b' told :=
  { T with
    rides := rides_calls_row Dm Mg Rch codes shape pieces Pc hl seats es hD hd hq hb' hlook hpc
      T.base hReq hHead }

/-- At the digits: T.hbaseS into hbase; the end back into rides. -/
example (a' : Desc.Place) (tl : HTailF2) (told : List (List Desc.Oracle))
    (Pc : K3Pieces X codes shape pieces) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) (hM : Mg.more = {}) (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    {q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hq : pieces[k3K l true]? = some q) {b' : Desc.Block Desc.First.S ProofFile.Cl}
    (hb' : k3Const X codes shape l true = some b') {x : Desc.First.Look.Place}
    (hlook : lookAt X l true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (hpc : (IM.k3Place l true).piece = Desc.K3.pieceAt X l true)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk r) →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk r) →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk "weights") →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk "weights") →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w)
    (smp : Desc.First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (T : DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms
      (IM.k3Place l true) a' (k3K l true) l sub x tl smp q b' told) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true) a'
      (k3K l true) l sub x tl smp q b' told :=
  { T with
    rides := rides_digits_row Dm Mg Rch codes shape pieces Pc hl hsub hM seats es hD hd hq hb'
      hlook hsh hpc T.hbaseS hReq hHead hFwd hWt }

/-- The ledger's own sentences on Dm and Mg into es, hD, hd. -/
example (sts : List (ℕ × ℕ)) (s₀ : Desc.First.S) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ)
    (tls : ℕ → HTailF2) (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
    (told : List (List Desc.Oracle)) (arrs : Array (Nat × String))
    (V : K3OwedR Dm Mg Rch codes shape pieces sts s₀ num idx tls tok told arrs)
    (Pc : K3Pieces X codes shape pieces) {l : ℕ} (hl : l < 25)
    {q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hq : pieces[k3K l false]? = some q) {b' : Desc.Block Desc.First.S ProofFile.Cl}
    (hb' : k3Const X codes shape l false = some b') {x : Desc.First.Look.Place}
    (hlook : lookAt X l false = some x)
    (hpc : (IM.k3Place l false).piece = Desc.K3.pieceAt X l false)
    (hbase : ∀ t ∈ sampledIn Dm.N ((openSets linksFull PS (start linksFull))[k3K l false]?.getD []),
      t.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i)) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l false) q b' :=
  rides_calls_row Dm Mg Rch codes shape pieces Pc hl sts V.es V.hD V.hd hq hb' hlook hpc hbase
    hReq hHead

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3PlacesOk_full
#print axioms VerifiableInference.OnPublicFiles.k3Border_calls
#print axioms VerifiableInference.OnPublicFiles.k3Border_digits
#print axioms VerifiableInference.OnPublicFiles.rides_calls_row
#print axioms VerifiableInference.OnPublicFiles.rides_digits_row
